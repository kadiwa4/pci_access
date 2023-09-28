//! MSI capability structure.

use num_enum::TryFromPrimitive;

use crate::{
	cast,
	config::{bit_accessors, BitField},
	map, VolatilePtr,
};

#[derive(Debug)] // FIXME: remove
#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct Part0 {
	_common: [u8; 2],
	message_control: MessageControl,
	message_addr_lo: u32,
}

#[repr(C)]
struct Part1 {
	message_data: u16,
	extended_message_data: u16,
	mask: u32,
	pending: u32,
}

#[repr(C)]
struct Msi32 {
	_part0: Part0,
	part1: Part1,
}

#[repr(C)]
struct Msi64 {
	_part0: Part0,
	message_addr_hi: u32,
	part1: Part1,
}

/// Reference to an MSI capability structure.
#[derive(Clone, Copy, Debug)]
pub struct MsiRef {
	ptr: VolatilePtr<Part0>,
	addr_64bit: bool,
	per_vector_masking: bool,
}

impl MsiRef {
	pub const ID: u8 = 5;

	pub(super) fn new(ptr: VolatilePtr<Part0>) -> Self {
		let message_control = map!(ptr.message_control).read();
		Self {
			ptr,
			addr_64bit: message_control.addr_64bit_support(),
			per_vector_masking: message_control.per_vector_masking_support(),
		}
	}

	#[inline]
	pub fn message_control(self) -> MessageControl {
		map!((self.ptr).message_control).read()
	}

	#[inline]
	pub fn set_message_control(self, val: MessageControl) {
		map!((self.ptr).message_control).write(val);
	}

	pub fn message_addr(self) -> u64 {
		let mut val = u32::from_le(map!((self.ptr).message_addr_lo).read()) as u64;
		if self.addr_64bit {
			let ptr: VolatilePtr<Msi64> = cast!(self.ptr);
			let hi = u32::from_le(map!(ptr.message_addr_hi).read());
			val |= (hi as u64) << 0x20;
		}
		val
	}

	pub fn set_message_addr(self, val: u64) {
		map!((self.ptr).message_addr_lo).write((val as u32).to_le());
		if self.addr_64bit {
			let ptr: VolatilePtr<Msi64> = cast!(self.ptr);
			map!(ptr.message_addr_hi).write(((val >> 0x20) as u32).to_le());
		} else {
			assert!(u32::try_from(val).is_ok(), "invalid message address");
		}
	}

	fn part1(self) -> VolatilePtr<Part1> {
		if self.addr_64bit {
			map!((cast!(self.ptr => Msi64)).part1)
		} else {
			map!((cast!(self.ptr => Msi32)).part1)
		}
	}

	pub fn message_data(self) -> u16 {
		u16::from_le(map!((self.part1()).message_data).read())
	}

	pub fn set_message_data(self, val: u16) {
		map!((self.part1()).message_data).write(val.to_le());
	}

	pub fn extended_message_data(self) -> u16 {
		u16::from_le(map!((self.part1()).message_data).read())
	}

	pub fn set_extended_message_data(self, val: u16) {
		map!((self.part1()).message_data).write(val.to_le());
	}

	pub fn mask(self) -> u32 {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		u32::from_le(map!((self.part1()).mask).read())
	}

	pub fn set_mask(self, val: u32) {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		map!((self.part1()).mask).write(val.to_le());
	}

	pub fn pending(self) -> u32 {
		assert!(self.per_vector_masking, "per-vector masking not supported");
		u32::from_le(map!((self.part1()).pending).read())
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

impl BitField for MessageControl {
	type Inner = u16;
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
