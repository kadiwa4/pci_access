//! Flattening portal bridge capability structure.

use num_enum::TryFromPrimitive;

use crate::{
	config::{accessors, bit_accessors, ReprPrimitive},
	struct_offsets, Ptr, PtrExt,
};

pub const ID: u8 = 0x15;

struct_offsets! {
	struct Fpb {
		_common: [u8; 2],
		_reserved: [u8; 2],
		cpbs: FpbCpbs,
		rid_vector_control1: RidVectorControl1,
		rid_vector_control2: RidVectorControl2,
		mem_lo_vector_control: MemLoVectorControl,
		mem_hi_vector_control: MemHiVectorControl,
		mem_hi_vector_start_addr_hi: u32,
		vector_access_control: u32,
		vector_access_data: u32,
	}
}

/// Reference to a flattening portal bridge capability structure.
#[derive(Clone, Copy, Debug)]
pub struct FpbRef<P: Ptr>(pub(super) P);

impl<P: Ptr> FpbRef<P> {
	accessors! {
		use Fpb;
		cpbs: FpbCpbs { get; }
		rid_vector_control1: RidVectorControl1 { get; set set_rid_vector_control1; }
		rid_vector_control2: RidVectorControl2 { get; set set_rid_vector_control2; }
		mem_lo_vector_control: MemLoVectorControl { get; set set_mem_lo_vector_control; }
		mem_hi_vector_control: MemHiVectorControl { get; set set_mem_hi_vector_control; }
	}

	pub fn mem_hi_vector_start_addr(&self) -> u64 {
		let lo = u32::from_le(self.mem_hi_vector_control().0) & 0xF000_0000;
		let hi = unsafe { self.0.offset(Fpb::mem_hi_vector_start_addr_hi).read32_le() };
		((hi as u64) << 0x20) | lo as u64
	}

	pub fn set_mem_hi_vector_start_addr(&self, val: u64) {
		debug_assert_eq!(val % 0x1000_0000, 0, "invalid mem_hi_vector_start_addr");
		self.set_mem_hi_vector_control(MemHiVectorControl(
			(self.mem_hi_vector_control().0 & 0x0FFF_FFFF_u32.to_le())
				| (val as u32 & 0xF000_0000).to_le(),
		));
		unsafe {
			self.0
				.offset(Fpb::mem_hi_vector_start_addr_hi)
				.write32_le((val >> 0x20) as u32);
		}
	}

	pub fn vector_read(&self, select: VectorSelect, offset: u8) -> u32 {
		self.set_vector_access_control(select, offset);
		unsafe { self.0.offset(Fpb::vector_access_data).read32_le() }
	}

	pub fn vector_write(&self, select: VectorSelect, offset: u8, val: u32) {
		self.set_vector_access_control(select, offset);
		unsafe {
			self.0.offset(Fpb::vector_access_data).write32_le(val);
		}
	}

	pub fn vector_replace(&self, select: VectorSelect, offset: u8, val: u32) -> u32 {
		self.set_vector_access_control(select, offset);
		unsafe {
			let ret = self.0.offset(Fpb::vector_access_data).read32_le();
			self.0.offset(Fpb::vector_access_data).write32_le(val);
			ret
		}
	}

	fn set_vector_access_control(&self, select: VectorSelect, offset: u8) {
		let val = ((select as u32) << 0x0E) | offset as u32;
		unsafe {
			self.0.offset(Fpb::vector_access_control).write32_le(val);
		}
	}
}

/// [Flattening portal bridge](FpbRef) capabilities value.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct FpbCpbs(u32);

impl FpbCpbs {
	bit_accessors! {
		rid_decode: 0 { get; }
		mem_lo_decode: 1 { get; }
		mem_hi_decode: 2 { get; }
		secondary_bridge_side_device_count: u8, 3..8 {
			get => |val| val as u8 + 1;
		}
		rid_vector_bit_size: u16, 8..0x0B {
			get => |exponent| {
				assert!(matches!(exponent, 0 | 2 | 5), "reserved value");
				0x0100 << exponent
			};
		}
		max_rid_vector_granularity: RidVectorGranularity, 8..0x0B {
			get => |val| RidVectorGranularity::try_from(u8::wrapping_sub(RidVectorGranularity::G256 as u8, val as u8)).expect("reserved value");
		}
		mem_lo_vector_bit_size: u16, 0x10..0x13 {
			get => |exponent| {
				assert!(exponent < 5, "reserved value");
				0x0100_u16 << exponent
			};
		}
		max_mem_lo_vector_granularity: MemLoVectorGranularity, 0x10..0x13 {
			get => |val| {
				MemLoVectorGranularity::try_from(u8::wrapping_sub(MemLoVectorGranularity::G16Mib as u8, val as u8)).expect("reserved value")
			};
		}
		mem_hi_vector_bit_size: u16, 0x18..0x1B {
			get => |exponent| {
				assert!(exponent < 6, "reserved value");
				0x0100_u16 << exponent
			};
		}
	}
}

unsafe impl ReprPrimitive for FpbCpbs {
	type Repr = u32;
}

/// RID vector control 1 value of a
/// [flattening portal bridge capability structure](FpbRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct RidVectorControl1(u32);

impl RidVectorControl1 {
	bit_accessors! {
		decode_enabled: 0 { get; set enable_decode; }
		granularity: RidVectorGranularity, 4..8 {
			get => |val| RidVectorGranularity::try_from(val as u8).expect("reserved value");
			set with_granularity;
		}
		start_offset: u16, 0x13..0x20 {
			get => |val| (val << 3) as u16;
			set with_start_offset => |val| {
				debug_assert_eq!(val % 8, 0, "invalid start_offset");
				val as u32 >> 3
			};
		}
	}
}

unsafe impl ReprPrimitive for RidVectorControl1 {
	type Repr = u32;
}

/// Value of [`RidVectorControl1::granularity`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum RidVectorGranularity {
	G8,
	G64 = 3,
	G256 = 5,
}

impl RidVectorGranularity {
	pub fn from_units(val: u16) -> Option<Self> {
		Self::try_from(u8::checked_sub(val.checked_ilog2()? as u8, 3)?).ok()
	}

	pub fn units(self) -> u16 {
		8 << self as u8
	}
}

/// RID vector control 2 value of a
/// [flattening portal bridge capability structure](FpbRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct RidVectorControl2(u32);

impl RidVectorControl2 {
	bit_accessors! {
		secondary_start_offset: u16, 3..0x10 {
			get => |val| (val << 3) as u16;
			set with_secondary_start_offset => |val| {
				debug_assert_eq!(val % 8, 0, "invalid start_offset");
				val as u32 >> 3
			};
		}
	}
}

unsafe impl ReprPrimitive for RidVectorControl2 {
	type Repr = u32;
}

/// MEM low vector control value of a
/// [flattening portal bridge capability structure](FpbRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct MemLoVectorControl(u32);

impl MemLoVectorControl {
	bit_accessors! {
		decode_enabled: 0 { get; set enable_decode; }
		granularity: MemLoVectorGranularity, 4..8 {
			get => |val| MemLoVectorGranularity::try_from(val as u8).expect("reserved value");
			set with_granularity;
		}
		start_addr: u32, 0x14..0x20 mask { get; set with_start_addr; }
	}
}

unsafe impl ReprPrimitive for MemLoVectorControl {
	type Repr = u32;
}

/// Value of [`MemLoVectorControl::granularity`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum MemLoVectorGranularity {
	G1Mib,
	G2Mib,
	G4Mib,
	G8Mib,
	G16Mib,
}

impl MemLoVectorGranularity {
	pub fn from_bytes(val: u32) -> Option<Self> {
		Self::try_from(u8::checked_sub(val.checked_ilog2()? as u8, 0x14)?).ok()
	}

	pub fn bytes(self) -> u32 {
		0x10_0000 << self as u8
	}
}

/// MEM high vector control 1 value of a
/// [flattening portal bridge capability structure](FpbRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct MemHiVectorControl(u32);

impl MemHiVectorControl {
	bit_accessors! {
		decode_enabled: 0 { get; set enable_decode; }
		granularity: MemHiVectorGranularity, 4..8 {
			get =>|val| MemHiVectorGranularity::try_from(val as u8).expect("reserved value");
			set with_granularity;
		}
	}
}

unsafe impl ReprPrimitive for MemHiVectorControl {
	type Repr = u32;
}

/// Value of [`MemHiVectorControl::granularity`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum MemHiVectorGranularity {
	G256Mib,
	G512Mib,
	G1Gib,
	G2Gib,
	G4Gib,
	G8Gib,
	G16Gib,
	G32Gib,
}

impl MemHiVectorGranularity {
	pub fn from_bytes(val: u64) -> Option<Self> {
		Self::try_from(u8::checked_sub(val.checked_ilog2()? as u8, 0x1C)?).ok()
	}

	pub fn bytes(self) -> u64 {
		0x1000_0000 << self as u8
	}
}

/// Which vector you want to read from or write to.
///
/// See [`FpbRef::vector_read`] and [`FpbRef::vector_write`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
#[non_exhaustive]
pub enum VectorSelect {
	Rid,
	MemLo,
	MemHi,
}
