#![no_std]
#![allow(clippy::redundant_closure_call)] // https://github.com/rust-lang/rust-clippy/issues/1553
#![allow(clippy::useless_transmute)]
#![warn(rust_2018_idioms)]
#![warn(macro_use_extern_crate, meta_variable_misuse, missing_abi)]
#![warn(unused_lifetimes, unused_macro_rules, unused_qualifications)]

pub mod config;
pub mod ext_cpb;

use core::{
	cell::Cell,
	fmt::{self, Debug},
	iter::FusedIterator,
	marker::PhantomData,
	mem::size_of,
	ops::Range,
	ptr::NonNull,
};

#[repr(C, align(4))]
pub struct MsixTableEntry {
	message_addr_lo: u32,
	message_addr_hi: u32,
	message_data: u32,
	vector_control: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncPos(pub u16);

impl FuncPos {
	pub const fn new(bus: u8, device: u8, func: u8) -> Self {
		Self((func & 7) as u16 | ((device as u16 & 0x1F) << 3) | ((bus as u16) << 8))
	}

	pub const fn bus(self) -> u8 {
		(self.0 >> 8) as u8
	}

	pub const fn device(self) -> u8 {
		(self.0 >> 3) as u8 & 0x1F
	}

	pub const fn func(self) -> u8 {
		self.0 as u8 & 7
	}

	#[must_use]
	pub const fn add_func(self, val: u16) -> Self {
		Self(u16::wrapping_add(self.0, val))
	}

	#[must_use]
	pub const fn add_device(self, val: u16) -> Self {
		Self(u16::wrapping_add(self.0, val << 3))
	}
}

pub struct FuncPosIter<P: Ptr> {
	base_ptr: P,
	current: FuncPos,
	end: FuncPos,
}

impl<P: Ptr> FuncPosIter<P> {
	/// If `end_bus` is zero, all 256 buses will be iterated over.
	pub fn new(base_ptr: P, end_bus: u8) -> Self {
		Self {
			base_ptr,
			current: FuncPos::new(0, 1, 0),
			end: FuncPos::new(end_bus, 0, 0),
		}
	}

	#[inline]
	pub fn skip_device(&mut self) {
		assert!(self.current != self.end, "there is no device to skip");
		self.current = self.current.add_func(8 - self.current.func() as u16);
	}
}

impl<P: Ptr> Iterator for FuncPosIter<P> {
	type Item = config::HeaderRef<P>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.current == self.end {
			return None;
		}
		let header = unsafe {
			config::HeaderRef::new(self.base_ptr.offset(P::func_pos_to_offset(self.current)))
		};
		if self.current.func() != 0 || {
			let ty = header.header_type();
			ty != config::HeaderType::INVALID && ty.multi_func()
		} {
			self.current = self.current.add_func(1);
		} else {
			self.current = self.current.add_device(1);
		}
		Some(header)
	}
}

impl<P: Ptr> FusedIterator for FuncPosIter<P> {}

pub trait Ptr: Clone + Debug + Eq {
	fn func_pos_to_offset(pos: FuncPos) -> i32;
	fn offset_to_func_pos(offset: i32) -> FuncPos;
	fn to_func_pos(&self) -> FuncPos;
	unsafe fn offset(&self, offset: i32) -> Self;
	unsafe fn read8(&self) -> u8;
	unsafe fn read16(&self) -> u16;
	unsafe fn read32(&self) -> u32;
	unsafe fn write8(&self, val: u8);
	unsafe fn write16(&self, val: u16);
	unsafe fn write32(&self, val: u32);
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EcamPtr(NonNull<u8>);

impl EcamPtr {
	/// # Safety
	/// - The input has to point to a valid PCI configuration space.
	/// - Only one thread can access the configuration space at a time.
	pub unsafe fn new(base_ptr: NonNull<u8>) -> Self {
		Self(base_ptr)
	}

	pub fn as_ptr(&self) -> NonNull<u8> {
		self.0
	}
}

impl Ptr for EcamPtr {
	fn func_pos_to_offset(pos: FuncPos) -> i32 {
		(pos.0 as i32) << 0x0C
	}
	fn offset_to_func_pos(offset: i32) -> FuncPos {
		FuncPos((offset >> 0x0C) as u16)
	}
	fn to_func_pos(&self) -> FuncPos {
		FuncPos((self.0.as_ptr() as usize >> 0x0C) as u16)
	}

	#[inline]
	unsafe fn offset(&self, offset: i32) -> Self {
		Self(NonNull::new_unchecked(
			self.0.as_ptr().offset(offset as isize),
		))
	}

	#[inline]
	unsafe fn read8(&self) -> u8 {
		self.0.as_ptr().read_volatile()
	}
	#[inline]
	unsafe fn read16(&self) -> u16 {
		(self.0.as_ptr() as *mut u16).read_volatile()
	}
	#[inline]
	unsafe fn read32(&self) -> u32 {
		(self.0.as_ptr() as *mut u32).read_volatile()
	}
	#[inline]
	unsafe fn write8(&self, val: u8) {
		self.0.as_ptr().write_volatile(val);
	}
	#[inline]
	unsafe fn write16(&self, val: u16) {
		(self.0.as_ptr() as *mut u16).write_volatile(val);
	}
	#[inline]
	unsafe fn write32(&self, val: u32) {
		(self.0.as_ptr() as *mut u32).write_volatile(val);
	}
}

impl fmt::Pointer for EcamPtr {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Pointer::fmt(&self.0.as_ptr(), f)
	}
}

impl Debug for EcamPtr {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Pointer::fmt(&self.0.as_ptr(), f)
	}
}

struct Offset<Base, Field>(i32, PhantomData<fn(Base) -> Field>);

struct TPtr<P: Ptr, T: 'static>(P, PhantomData<&'static Cell<T>>);

impl<P: Ptr, T: 'static> TPtr<P, T> {
	#[inline]
	unsafe fn new(ptr: P) -> Self {
		Self(ptr, PhantomData)
	}

	#[inline]
	fn offset<Field>(&self, Offset(offset, _): Offset<T, Field>) -> TPtr<P, Field> {
		TPtr(unsafe { self.0.offset(offset) }, PhantomData)
	}

	#[inline]
	unsafe fn raw_offset(&self, offset: i32) -> TPtr<P, T> {
		Self(unsafe { self.0.offset(offset) }, PhantomData)
	}

	#[inline]
	unsafe fn cast<T2>(&self) -> TPtr<P, T2> {
		TPtr(self.0.clone(), PhantomData)
	}
}

impl<P: Ptr, T: 'static, const N: usize> TPtr<P, [T; N]> {
	#[inline]
	fn index(&self, idx: usize) -> TPtr<P, T> {
		assert!(idx < N);
		TPtr(
			unsafe { self.0.offset(i32::try_from(idx * size_of::<T>()).unwrap()) },
			PhantomData,
		)
	}
}

impl<P: Ptr, T: ReprPrimitive> TPtr<P, T> {
	#[inline]
	fn read(&self) -> T::Repr {
		unsafe { T::Repr::read_from(&self.0) }
	}

	#[inline]
	fn write(&self, val: T::Repr) {
		unsafe {
			T::Repr::write_to(core::mem::transmute(val), &self.0);
		}
	}
}

impl<P: Ptr, T: ReprPrimitive<Repr = u16>> TPtr<P, T> {
	#[inline]
	fn read16_le(&self) -> u16 {
		u16::from_le(self.read())
	}

	#[inline]
	fn write16_le(&self, val: u16) {
		self.write(val.to_le())
	}
}

impl<P: Ptr, T: ReprPrimitive<Repr = u32>> TPtr<P, T> {
	#[inline]
	fn read32_le(&self) -> u32 {
		u32::from_le(self.read())
	}

	#[inline]
	fn write32_le(&self, val: u32) {
		self.write(val.to_le())
	}
}

impl<P: Ptr, T: 'static> Clone for TPtr<P, T> {
	#[inline]
	fn clone(&self) -> Self {
		Self(self.0.clone(), PhantomData)
	}
}
impl<P: Ptr + Copy, T: 'static> Copy for TPtr<P, T> {}

impl<P: Ptr, T: 'static> Debug for TPtr<P, T> {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.0.fmt(f)
	}
}

impl<P: Ptr, T: 'static> PartialEq for TPtr<P, T> {
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}
impl<P: Ptr, T: 'static> Eq for TPtr<P, T> {}

trait Primitive {
	unsafe fn read_from<P: Ptr>(ptr: &P) -> Self;
	unsafe fn write_to<P: Ptr>(self, ptr: &P);
}

impl Primitive for u8 {
	#[inline]
	unsafe fn read_from<P: Ptr>(ptr: &P) -> Self {
		ptr.read8()
	}
	#[inline]
	unsafe fn write_to<P: Ptr>(self, ptr: &P) {
		ptr.write8(self)
	}
}

impl Primitive for u16 {
	#[inline]
	unsafe fn read_from<P: Ptr>(ptr: &P) -> Self {
		ptr.read16()
	}
	#[inline]
	unsafe fn write_to<P: Ptr>(self, ptr: &P) {
		ptr.write16(self)
	}
}

impl Primitive for u32 {
	#[inline]
	unsafe fn read_from<P: Ptr>(ptr: &P) -> Self {
		ptr.read32()
	}
	#[inline]
	unsafe fn write_to<P: Ptr>(self, ptr: &P) {
		ptr.write32(self)
	}
}

unsafe trait ReprPrimitive: 'static + Copy {
	type Repr: Primitive;
}

unsafe impl ReprPrimitive for u8 {
	type Repr = u8;
}

unsafe impl ReprPrimitive for u16 {
	type Repr = u16;
}

unsafe impl ReprPrimitive for u32 {
	type Repr = u32;
}

trait BitManip {
	fn bit_range(self, range: Range<u32>) -> Self;
	fn from_bit_range_masked(val: Self, range: Range<u32>) -> Self;
	fn new_bit_mask(range: Range<u32>) -> Self;
}

macro_rules! impl_bit_manip {
	($($ty:ty),+) => {$(
		impl BitManip for $ty {
			#[inline]
			fn bit_range(self, range: Range<u32>) -> Self {
				self << (Self::BITS - range.end) >> (Self::BITS + range.start - range.end)
			}

			#[inline]
			fn from_bit_range_masked(val: Self, range: Range<u32>) -> Self {
				val << (Self::BITS + range.start - range.end) >> (Self::BITS - range.end)
			}

			#[inline]
			fn new_bit_mask(range: Range<u32>) -> Self {
				Self::from_bit_range_masked(Self::MAX, range)
			}
		}
	)+};
}

impl_bit_manip!(u8, u16, u32, u64);

macro_rules! accessors {
	{
		use $strct:ident;
		$($(#[$attr:meta])* $name:ident: $ty:ty { get $(=> $map_get:expr)?; $(set $set_name:ident $(=> $map_set:expr)?;)? })+
	} => {
		$(accessors!(@single $(#[$attr])* $strct::$name: $ty, { get $(=> $map_get)?; $(set $set_name $(=> $map_set)?;)? });)+
	};
	(@single $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, { get $(=> $map_get:expr)?; $(set $set_name:ident $(=> $map_set:expr)?;)? }) => {
		accessors!(@get $(#[$attr])* $strct::$name: $ty, $($map_get)?);
		accessors!(@set $(#[$attr])* $strct::$name: $ty, $($set_name, $($map_set)?)?);
	};
	(@get $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(&self) -> $ty {
			unsafe { core::mem::transmute(self.0.offset($strct::$name).read()) }
		}
	};
	(@get $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(&self) -> $ty {
			$map_get(unsafe { core::mem::transmute(self.0.offset($strct::$name).read()) })
		}
	};
	(@set $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty,) => {};
	(@set $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, $set_name:ident, $($map_set:expr)?) => {
		$(#[$attr])*
		#[inline]
		pub fn $set_name(&self, val: $ty) {
			$(let val = $map_set(val);)?
			unsafe {
				self.0.offset($strct::$name).write(core::mem::transmute::<$ty, <$ty as ReprPrimitive>::Repr>(val));
			}
		}
	};
}

macro_rules! bit_accessors {
	($($(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal $($mask:ident)?)? { get $(=> $map_get:expr)?; $($set_kw:ident $set_name:ident $(=> $map_set:expr)?;)? })+) => {
		$(bit_accessors!(@single $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)? { get $(=> $map_get)?; $($set_kw $set_name $(=> $map_set)?;)? });)+
	};
	(@single $(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal $($mask:ident)?)? { get $(=> $map_get:expr)?; $($set_kw:ident $set_name:ident $(=> $map_set:expr)?;)? }) => {
		bit_accessors!(@get $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)?, $($map_get)?);
		bit_accessors!(@set $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)?, $($set_kw $set_name, $($map_set)?)?);
	};
	(@get $(#[$attr:meta])* $name:ident: $pos:literal,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> bool {
			<Self as ReprPrimitive>::Repr::from_le(self.0) & (1 << $pos) != 0
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			crate::BitManip::bit_range(<Self as ReprPrimitive>::Repr::from_le(self.0), $start..$end) as _
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			$map_get(crate::BitManip::bit_range(<Self as ReprPrimitive>::Repr::from_le(self.0), $start..$end))
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			(<Self as ReprPrimitive>::Repr::from_le(self.0) & mask) as _
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal)?,) => {};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: bool) -> Self {
			Self(
				(self.0 & !((1 as <Self as ReprPrimitive>::Repr) << $pos).to_le())
					| ((val as <Self as ReprPrimitive>::Repr) << $pos).to_le()
			)
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			debug_assert!((val as u128) < (1_u128 << ($end - $start)), "invalid {}", stringify!($name));
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ((val as <Self as ReprPrimitive>::Repr) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ($map_get(val) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			debug_assert_eq!(val & mask, val, "invalid {}", stringify!($name));
			Self((self.0 & !mask.to_le()) | (val & mask).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set1 $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self) -> Self {
			Self(self.0 | ((1 as <Self as ReprPrimitive>::Repr) << $pos).to_le())
		}
	};
}

macro_rules! struct_offsets {
	{
		$vis:vis struct $name:ident {
			$($field_name:ident: $ty:ty,)+
		}
	} => {
		struct_offsets!(@offset: $vis $name, 0, $($field_name: $ty,)+);
	};
	(@offset: $vis:vis $name:ident, $offset:expr,) => {
		$vis struct $name([u8; $offset]);
	};
	(@offset: $vis:vis $name:ident, $offset:expr, $field_name0:ident: $ty0:ty, $($field_name:ident: $ty:ty,)*) => {
		impl $name {
			#[allow(non_upper_case_globals, unused_qualifications)]
			pub const $field_name0: crate::Offset<Self, $ty0> = crate::Offset($offset as i32, core::marker::PhantomData);
		}
		struct_offsets!(@offset: $vis $name, $offset + core::mem::size_of::<$ty0>(), $($field_name: $ty,)*);
	};
}

use {accessors, bit_accessors, struct_offsets};
