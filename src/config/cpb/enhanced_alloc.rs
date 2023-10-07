//! Enhanced allocation capability structure.

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
	mem::replace,
};

use num_enum::TryFromPrimitive;

use crate::{
	config::{accessors, bit_accessors, ReprPrimitive},
	struct_offsets, Ptr, PtrExt,
};

pub const ID: u8 = 0x14;

struct_offsets! {
	struct Part0 {
		_common: [u8; 2],
		entry_count: u8,
		_reserved: u8,
	}
}

struct_offsets! {
	struct Part1 {
		secondary_bus_num: u8,
		subordinate_bus_num: u8,
		_reserved: [u8; 2],
	}
}

struct_offsets! {
	struct EnhancedAllocT0 {
		_part0: [u8; 4],
		array: [Entry; 0],
	}
}

struct_offsets! {
	struct EnhancedAllocT1 {
		_part0: [u8; 4],
		part1: [u8; 4],
		array: [Entry; 0],
	}
}

/// Reference to an enhanced allocation capability structure.
#[derive(Clone, Copy, Debug)]
pub struct EnhancedAllocRef<P: Ptr> {
	pub(super) ptr: P,
	pub(super) type1: bool,
}

impl<P: Ptr> EnhancedAllocRef<P> {
	#[inline]
	fn part1(&self) -> Option<P> {
		self.type1
			.then(|| unsafe { self.ptr.offset(EnhancedAllocT1::part1) })
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn secondary_bus_num(&self) -> Option<u8> {
		self.part1()
			.map(|p| unsafe { p.offset(Part1::secondary_bus_num).read8() })
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn subordinate_bus_num(&self) -> Option<u8> {
		self.part1()
			.map(|p| unsafe { p.offset(Part1::subordinate_bus_num).read8() })
	}

	pub fn entries(&self) -> EntriesIter<P> {
		let offset = if self.type1 {
			EnhancedAllocT1::array
		} else {
			EnhancedAllocT0::array
		};
		let ptr = unsafe { self.ptr.offset(offset) };
		EntriesIter {
			current: ptr,
			remaining_len: unsafe { self.ptr.offset(Part0::entry_count).read8() } as usize & 0x3F,
		}
	}
}

/// Mutably iterates over enhanced allocation [entries](EntryRef).
#[derive(Clone)]
pub struct EntriesIter<P: Ptr> {
	current: P,
	remaining_len: usize,
}

impl<P: Ptr> Iterator for EntriesIter<P> {
	type Item = EntryRef<P>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.remaining_len == 0 {
			return None;
		}
		self.remaining_len -= 1;
		let offset = 1 + (unsafe { self.current.offset(Entry::header).read32() } & 7) as i32;
		let next_ptr = unsafe { self.current.offset(offset << 2) };
		Some(EntryRef(replace(&mut self.current, next_ptr)))
	}
}

impl<P: Ptr> FusedIterator for EntriesIter<P> {}

impl<P: Ptr> Debug for EntriesIter<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

struct_offsets! {
	struct Entry {
		header: EntryHeader,
		start_lo: u32,
		end_lo: u32,
		hi0: u32,
		hi1: u32,
	}
}

/// Entry in an [enhanced allocation capability structure](EnhancedAllocRef).
#[derive(Clone, Copy, Debug)]
pub struct EntryRef<P: Ptr>(P);

impl<P: Ptr> EntryRef<P> {
	accessors! {
		use Entry;
		header: EntryHeader { get; set set_header; }
	}

	pub fn start_addr(&self) -> u64 {
		unsafe {
			let mut ret = self.0.offset(Entry::start_lo).read32_le() as u64;
			if ret & 2 != 0 {
				ret |= (self.0.offset(Entry::hi0).read32_le() as u64) << 0x20;
			}
			ret & 0xFFFF_FFFF_FFFF_FFFC
		}
	}

	pub fn set_start_addr(&self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid start_addr");
		unsafe {
			let use_hi = self.0.offset(Entry::start_lo).read32_le() & 2 != 0;
			self.0.offset(Entry::start_lo).write32_le(val as u32);
			if use_hi {
				self.0.offset(Entry::hi0).write32_le((val >> 0x20) as u32);
			} else {
				debug_assert!(u32::try_from(val).is_ok(), "invalid start_addr");
			}
		}
	}
	/// The actual end address is `4` higher than this.
	pub fn end_addr(&self) -> u64 {
		unsafe {
			let mut ret = self.0.offset(Entry::end_lo).read32_le() as u64;
			if ret & 2 != 0 {
				ret |= (self.end_hi_ptr().read32_le() as u64) << 0x20;
			}
			ret & 0xFFFF_FFFF_FFFF_FFFC
		}
	}

	/// The input should be the actual end address minus `4`.
	pub fn set_end_addr(&self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid end_addr");
		unsafe {
			let use_hi = self.0.offset(Entry::end_lo).read32_le() & 2 != 0;
			self.0.offset(Entry::end_lo).write32_le(val as u32);
			if use_hi {
				self.end_hi_ptr().write32_le((val >> 0x20) as u32);
			} else {
				debug_assert!(u32::try_from(val).is_ok(), "invalid end_addr");
			}
		}
	}

	fn end_hi_ptr(&self) -> P {
		unsafe {
			let start_lo = self.0.offset(Entry::start_lo).read32_le();
			if start_lo & 2 != 0 {
				self.0.offset(Entry::hi1)
			} else {
				self.0.offset(Entry::hi0)
			}
		}
	}
}

/// First value of an [entry](EntryRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct EntryHeader(u32);

impl EntryHeader {
	bit_accessors! {
		equivalent_bar: EquivalentBar, 4..8 {
			get => |val| EquivalentBar::try_from(val as u8).unwrap_or(EquivalentBar::NotIndicated);
		}
		primary_properties: Option<EntryProperties>, 8..0x10 {
			get => |val| EntryProperties::try_from(val as u8).ok();
		}
		secondary_properties: Option<EntryProperties>, 0x10..0x18 {
			get => |val| EntryProperties::try_from(val as u8).ok();
		}
		writable: 0x1E { get; }
		enabled: 0x1F { get; set enable; }
	}
}

unsafe impl ReprPrimitive for EntryHeader {
	type Repr = u32;
}

/// Value of [`EntryHeader::equivalent_bar`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum EquivalentBar {
	B0,
	B1,
	B2,
	B3,
	B4,
	B5,
	BehindFunc,
	NotIndicated,
	ExpansionRom,
	VirtualFunc0,
	VirtualFunc1,
	VirtualFunc2,
	VirtualFunc3,
	VirtualFunc4,
	VirtualFunc5,
}

impl EquivalentBar {
	pub fn bar_idx(self) -> Option<u8> {
		((self as u8) < 6).then_some(self as u8)
	}

	pub fn virtual_func_bar_idx(self) -> Option<u8> {
		u8::checked_sub(self as u8, Self::VirtualFunc0 as u8).filter(|&v| v < 6)
	}
}

/// Value of [`EntryHeader::primary_properties`] and
/// [`EntryHeader::secondary_properties`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum EntryProperties {
	MemNonprefetchable,
	MemPrefetchable,
	Io,
	VirtualFuncMemNonprefetchable,
	VirtualFuncMemPrefetchable,
	BehindFuncMemNonprefetchable,
	BehindFuncMemPrefetchable,
	BehindFuncIo,
	MemUnavailable = 0xFD,
	IoUnavailable,
	Unavailable,
}
