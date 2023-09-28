//! Enhanced allocation capability structure.

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
};

use num_enum::TryFromPrimitive;

use crate::{
	cast,
	config::{accessors, bit_accessors, BitField},
	map, VolatilePtr,
};

#[derive(Debug)] // FIXME: remove
#[derive(Clone, Copy)]
#[repr(C, align(4))]
pub(super) struct Part0 {
	_common: [u8; 2],
	entry_count: u8,
	_reserved: u8,
}

#[derive(Clone, Copy)]
#[repr(C, align(4))]
struct Part1 {
	secondary_bus_num: u8,
	subordinate_bus_num: u8,
	_reserved: [u8; 2],
}

#[derive(Clone, Copy)]
#[repr(C)]
struct EnhancedAllocT0 {
	part0: Part0,
	array: [Entry; 0],
}

#[derive(Clone, Copy)]
#[repr(C)]
struct EnhancedAllocT1 {
	part0: Part0,
	part1: Part1,
	array: [Entry; 0],
}

/// Reference to an enhanced allocation capability structure.
#[derive(Clone, Copy, Debug)]
pub struct EnhancedAllocRef {
	pub(super) ptr: VolatilePtr<Part0>,
	pub(super) type1: bool,
}

impl EnhancedAllocRef {
	pub const ID: u8 = 0x14;

	#[inline]
	fn part1(self) -> Option<VolatilePtr<Part1>> {
		self.type1
			.then(|| map!((cast!(self.ptr => EnhancedAllocT1)).part1))
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn secondary_bus_num(self) -> Option<u8> {
		self.part1().map(|p| map!(p.secondary_bus_num).read())
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn subordinate_bus_num(self) -> Option<u8> {
		self.part1().map(|p| map!(p.subordinate_bus_num).read())
	}

	pub fn entries(self) -> EntriesIter {
		let ptr = if self.type1 {
			map!((cast!(self.ptr => EnhancedAllocT1)).array)
		} else {
			map!((cast!(self.ptr => EnhancedAllocT0)).array)
		};
		EntriesIter {
			current: cast!(ptr),
			remaining_len: map!((self.ptr).entry_count).read() as usize & 0x3F,
		}
	}
}

/// Mutably iterates over enhanced allocation [entries](EntryRef).
#[derive(Clone)]
pub struct EntriesIter {
	current: VolatilePtr<Entry>,
	remaining_len: usize,
}

impl Iterator for EntriesIter {
	type Item = EntryRef;

	fn next(&mut self) -> Option<Self::Item> {
		if self.remaining_len == 0 {
			return None;
		}
		self.remaining_len -= 1;
		let ptr = self.current;
		let offset = 1 + (map!((self.current).header).read().0 & 7) as isize;
		self.current = map!((self.current)[offset]);
		Some(EntryRef(ptr))
	}
}

impl FusedIterator for EntriesIter {}

impl Debug for EntriesIter {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

#[derive(Debug)] // FIXME: remove
#[derive(Clone, Copy)]
#[repr(C)]
struct Entry {
	header: EntryHeader,
	start_lo: u32,
	end_lo: u32,
	hi0: u32,
	hi1: u32,
}

/// Entry in an [enhanced allocation capability structure](EnhancedAllocRef).
#[derive(Clone, Copy, Debug)]
pub struct EntryRef(VolatilePtr<Entry>);

impl EntryRef {
	accessors! {
		header: EntryHeader { get; set set_header; }
	}

	pub fn start_addr(self) -> u64 {
		let mut ret = u32::from_le(map!(self->start_lo).read()) as u64;
		if ret & 2 != 0 {
			ret |= (u32::from_le(map!(self->hi0).read()) as u64) << 0x20;
		}
		ret & 0xFFFF_FFFF_FFFF_FFFC
	}

	pub fn set_start_addr(self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid start_addr");
		let use_hi = u32::from_le(map!(self->start_lo).read()) & 2 != 0;
		map!(self->start_lo).write((val as u32).to_le());
		if use_hi {
			map!(self->hi0).write(((val >> 0x20) as u32).to_le());
		} else {
			debug_assert!(u32::try_from(val).is_ok(), "invalid start_addr");
		}
	}
	/// The actual end address is `4` higher than this.
	pub fn end_addr(self) -> u64 {
		let mut ret = u32::from_le(map!(self->end_lo).read()) as u64;
		if ret & 2 != 0 {
			ret |= (u32::from_le(self.end_hi_ptr().read()) as u64) << 0x20;
		}
		ret & 0xFFFF_FFFF_FFFF_FFFC
	}

	/// The input should be the actual end address minus `4`.
	pub fn set_end_addr(self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid end_addr");
		let use_hi = u32::from_le(map!(self->end_lo).read()) & 2 != 0;
		map!(self->end_lo).write((val as u32).to_le());
		if use_hi {
			self.end_hi_ptr().write(((val >> 0x20) as u32).to_le());
		} else {
			debug_assert!(u32::try_from(val).is_ok(), "invalid end_addr");
		}
	}

	fn end_hi_ptr(self) -> VolatilePtr<u32> {
		let start_lo = u32::from_le(map!(self->start_lo).read()) as u64;
		if start_lo & 2 != 0 {
			map!(self->hi1)
		} else {
			map!(self->hi0)
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

impl BitField for EntryHeader {
	type Inner = u32;
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
