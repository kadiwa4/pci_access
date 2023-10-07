#![no_std]
#![allow(clippy::redundant_closure_call)] // https://github.com/rust-lang/rust-clippy/issues/1553
#![allow(clippy::useless_transmute)]
#![warn(rust_2018_idioms)]
#![warn(macro_use_extern_crate, meta_variable_misuse, missing_abi)]
#![warn(unused_lifetimes, unused_macro_rules, unused_qualifications)]

pub mod config;
pub mod ext_cpb;

use core::{
	fmt::{self, Debug},
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
	pub const fn new(func: u8, device: u8, bus: u8) -> Self {
		Self((func & 7) as u16 | ((device as u16 & 0x1F) << 3) | ((bus as u16) << 8))
	}

	pub const fn func(self) -> u8 {
		self.0 as u8 & 7
	}

	pub const fn device(self) -> u8 {
		(self.0 >> 3) as u8 & 0x1F
	}

	pub const fn bus(self) -> u8 {
		(self.0 >> 8) as u8
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

macro_rules! struct_offsets {
	{
		struct $name:ident {
			$($field_name:ident: $ty:ty,)+
		}
	} => {
		#[allow(non_snake_case, non_upper_case_globals)]
		mod $name {
			use super::*;

			struct_offsets!(@offset: 0, $($field_name: $ty,)+);
		}
	};
	(@offset: $offset:expr,) => {};
	(@offset: $offset:expr, $field_name0:ident: $ty0:ty, $($field_name:ident: $ty:ty,)*) => {
		pub const $field_name0: i32 = ($offset) as i32;
		struct_offsets!(@offset: $offset + core::mem::size_of::<$ty0>(), $($field_name: $ty,)*);
	};
}

use struct_offsets;

pub trait Ptr: Clone + Debug + Eq {
	fn func_pos_to_offset(pos: FuncPos) -> i32;
	fn offset_to_func_pos(offset: i32) -> FuncPos;
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
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Pointer::fmt(&self.0.as_ptr(), f)
	}
}

impl Debug for EcamPtr {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Pointer::fmt(&self.0.as_ptr(), f)
	}
}

trait PtrExt: Ptr {
	unsafe fn read16_le(&self) -> u16;
	unsafe fn read32_le(&self) -> u32;
	unsafe fn write16_le(&self, val: u16);
	unsafe fn write32_le(&self, val: u32);
}

impl<P: Ptr> PtrExt for P {
	#[inline]
	unsafe fn read16_le(&self) -> u16 {
		u16::from_le(self.read16())
	}
	#[inline]
	unsafe fn read32_le(&self) -> u32 {
		u32::from_le(self.read32())
	}
	#[inline]
	unsafe fn write16_le(&self, val: u16) {
		self.write16(val.to_le())
	}
	#[inline]
	unsafe fn write32_le(&self, val: u32) {
		self.write32(val.to_le())
	}
}

trait Primitive {
	unsafe fn read_from<P: Ptr>(ptr: P) -> Self;
	unsafe fn write_to<P: Ptr>(self, ptr: P);
}

impl Primitive for u8 {
	unsafe fn read_from<P: Ptr>(ptr: P) -> Self {
		ptr.read8()
	}
	unsafe fn write_to<P: Ptr>(self, ptr: P) {
		ptr.write8(self)
	}
}

impl Primitive for u16 {
	unsafe fn read_from<P: Ptr>(ptr: P) -> Self {
		ptr.read16()
	}
	unsafe fn write_to<P: Ptr>(self, ptr: P) {
		ptr.write16(self)
	}
}

impl Primitive for u32 {
	unsafe fn read_from<P: Ptr>(ptr: P) -> Self {
		ptr.read32()
	}
	unsafe fn write_to<P: Ptr>(self, ptr: P) {
		ptr.write32(self)
	}
}

unsafe trait ReprPrimitive {
	type Repr;
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
