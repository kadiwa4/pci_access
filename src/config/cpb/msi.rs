//! MSI capability structure.

use num_enum::TryFromPrimitive;

use crate::{
	config::{bit_accessors, ReprPrimitive},
	struct_offsets, Ptr, PtrExt,
};

pub const ID: u8 = 5;

struct_offsets! {
	struct Part0 {
		_common: [u8; 2],
		message_control: MessageControl,
		message_addr_lo: u32,
	}
}

struct_offsets! {
	struct Part1 {
		message_data: u16,
		extended_message_data: u16,
		mask: u32,
		pending: u32,
	}
}

struct_offsets! {
	struct Msi32 {
		_part0: [u8; 4],
		part1: [u8; 0x0C],
	}
}

struct_offsets! {
	struct Msi64 {
		_part0: [u8; 4],
		message_addr_hi: u32,
		part1: [u8; 0x0C],
	}
}

/// Reference to an MSI capability structure.
#[derive(Clone, Copy, Debug)]
pub struct MsiRef<P: Ptr> {
	ptr: P,
	addr_64bit: bool,
	per_vector_masking: bool,
}

impl<P: Ptr> MsiRef<P> {
	pub(super) fn new(ptr: P) -> Self {
		let message_control =
			MessageControl(unsafe { ptr.offset(Part0::message_control).read16() });
		Self {
			ptr,
			addr_64bit: message_control.addr_64bit_support(),
			per_vector_masking: message_control.per_vector_masking_support(),
		}
	}

	#[inline]
	pub fn message_control(&self) -> MessageControl {
		MessageControl(unsafe { self.ptr.offset(Part0::message_control).read16() })
	}

	#[inline]
	pub fn set_message_control(&self, MessageControl(val): MessageControl) {
		unsafe {
			self.ptr.offset(Part0::message_control).write16(val);
		}
	}

	pub fn message_addr(&self) -> u64 {
		unsafe {
			let mut val = self.ptr.offset(Part0::message_addr_lo).read32_le() as u64;
			if self.addr_64bit {
				let hi = self.ptr.offset(Msi64::message_addr_hi).read32_le();
				val |= (hi as u64) << 0x20;
			}
			val
		}
	}

	pub fn set_message_addr(&self, val: u64) {
		unsafe {
			self.ptr
				.offset(Part0::message_addr_lo)
				.write32_le(val as u32);
			if self.addr_64bit {
				self.ptr
					.offset(Msi64::message_addr_hi)
					.write32_le((val >> 0x20) as u32);
			} else {
				debug_assert!(u32::try_from(val).is_ok(), "invalid message address");
			}
		}
	}

	fn part1(&self) -> P {
		let offset = if self.addr_64bit {
			Msi64::part1
		} else {
			Msi32::part1
		};
		unsafe { self.ptr.offset(offset) }
	}

	pub fn message_data(&self) -> u16 {
		unsafe { self.part1().offset(Part1::message_data).read16_le() }
	}

	pub fn set_message_data(&self, val: u16) {
		unsafe {
			self.part1().offset(Part1::message_data).write16_le(val);
		}
	}

	pub fn extended_message_data(&self) -> u16 {
		unsafe {
			self.part1()
				.offset(Part1::extended_message_data)
				.read16_le()
		}
	}

	pub fn set_extended_message_data(&self, val: u16) {
		unsafe {
			self.part1()
				.offset(Part1::extended_message_data)
				.write16_le(val);
		}
	}

	pub fn mask(&self) -> u32 {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		unsafe { self.part1().offset(Part1::mask).read32_le() }
	}

	pub fn set_mask(&self, val: u32) {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		unsafe {
			self.part1().offset(Part1::mask).write32_le(val);
		}
	}

	pub fn pending(&self) -> u32 {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		unsafe { self.part1().offset(Part1::pending).read32_le() }
	}
}

/// Message control value of an [MSI capability structure](MsiRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct MessageControl(u16);

impl MessageControl {
	bit_accessors! {
		enabled: 0 { get; set enable; }
		vectors_requested: VectorCount, 1..4 {
			get => |val| VectorCount::try_from(val as u8).expect("reserved value");
		}
		vectors_allocated: VectorCount, 4..7 {
			get => |val| VectorCount::try_from(val as u8).expect("reserved value");
			set with_vectors_allocated;
		}
		addr_64bit_support: 7 { get; }
		per_vector_masking_support: 8 { get; }
		extended_message_data_support: 9 { get; }
		extended_message_data: 0x0A { get; set with_extended_message_data; }
	}
}

unsafe impl ReprPrimitive for MessageControl {
	type Repr = u16;
}

/// Value of [`MessageControl::vectors_requested`] and
/// [`MessageControl::vectors_allocated`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum VectorCount {
	C1,
	C2,
	C4,
	C8,
	C16,
	C32,
}

impl VectorCount {
	pub fn from_count(val: u8) -> Option<Self> {
		Self::try_from(val.checked_ilog2()? as u8).ok()
	}

	pub fn count(self) -> u8 {
		1 << (self as u8)
	}
}
