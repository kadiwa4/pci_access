#![no_std]
#![allow(clippy::redundant_closure_call)] // https://github.com/rust-lang/rust-clippy/issues/1553
#![warn(rust_2018_idioms)]
#![warn(macro_use_extern_crate, meta_variable_misuse, missing_abi)]
#![warn(unused_lifetimes, unused_macro_rules, unused_qualifications)]

pub mod config;
pub mod ext_cpb;

use core::ops::Range;

use volatile::access::ReadWrite;

type VolatilePtr<T, A = ReadWrite> = volatile::VolatilePtr<'static, T, A>;

#[repr(C, align(4))]
pub struct MsixTableEntry {
	message_addr_lo: u32,
	message_addr_hi: u32,
	message_data: u32,
	vector_control: u32,
}

macro_rules! map {
	($this:ident.$field:ident) => {{
		#[allow(unused_unsafe)]
		let v = unsafe {
			$this.map(|p| {
				core::ptr::NonNull::new_unchecked(core::ptr::addr_of_mut!((*p.as_ptr()).$field))
			})
		};
		v
	}};
	($this:ident->$field:ident) => {{
		#[allow(unused_unsafe)]
		let v = unsafe {
			$this.0.map(|p| {
				core::ptr::NonNull::new_unchecked(core::ptr::addr_of_mut!((*p.as_ptr()).$field))
			})
		};
		v
	}};
	(($this:expr).$field:ident) => {{
		#[allow(unused_unsafe)]
		let v = unsafe {
			$this.map(|p| {
				core::ptr::NonNull::new_unchecked(core::ptr::addr_of_mut!((*p.as_ptr()).$field))
			})
		};
		v
	}};
	(($this:expr)[$idx:expr]) => {{
		#[allow(unused_unsafe, clippy::ptr_offset_with_cast)]
		let v = unsafe {
			$this.map(|p| core::ptr::NonNull::new_unchecked(p.as_ptr().offset($idx as isize)))
		};
		v
	}};
}

macro_rules! cast {
	($val:expr $(=> $ty:ty)?) => {{
		#[allow(unused_unsafe)]
		let v = unsafe {
			$val.map(core::ptr::NonNull::cast $(::<$ty>)?)
		};
		v
	}};
}

use {cast, map};

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
