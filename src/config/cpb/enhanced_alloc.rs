//! Enhanced allocation capability structure.

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
};

use num_enum::TryFromPrimitive;

use crate::{accessors, bit_accessors, struct_offsets, Ptr, ReprPrimitive, TPtr};

pub const ID: u8 = 0x14;

struct_offsets! {
	pub(super) struct Part0 {
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
		_part0: Part0,
		array: [Entry; 0],
	}
}

struct_offsets! {
	struct EnhancedAllocT1 {
		_part0: Part0,
		part1: Part1,
		array: [Entry; 0],
	}
}

/// Reference to an enhanced allocation capability structure.
#[derive(Clone, Copy, Debug)]
pub struct EnhancedAllocRef<P: Ptr> {
	pub(super) ptr: TPtr<P, Part0>,
	pub(super) type1: bool,
}

impl<P: Ptr> EnhancedAllocRef<P> {
	#[inline]
	fn part1(&self) -> Option<TPtr<P, Part1>> {
		self.type1
			.then(|| unsafe { self.ptr.cast() }.offset(EnhancedAllocT1::part1))
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn secondary_bus_num(&self) -> Option<u8> {
		self.part1()
			.map(|p| p.offset(Part1::secondary_bus_num).read())
	}

	/// Returns `None` if the configuration space header is of type 0.
	#[inline]
	pub fn subordinate_bus_num(&self) -> Option<u8> {
		self.part1()
			.map(|p| p.offset(Part1::subordinate_bus_num).read())
	}

	pub fn entries(&self) -> EntriesIter<P> {
		let ptr = if self.type1 {
			unsafe { self.ptr.cast() }.offset(EnhancedAllocT1::array)
		} else {
			unsafe { self.ptr.cast() }.offset(EnhancedAllocT0::array)
		};
		EntriesIter {
			current: ptr,
			remaining_len: self.ptr.offset(Part0::entry_count).read() & 0x3F,
		}
	}
}

/// Mutably iterates over enhanced allocation [entries](EntryRef).
#[derive(Clone)]
pub struct EntriesIter<P: Ptr> {
	current: TPtr<P, [Entry; 0]>,
	remaining_len: u8,
}

impl<P: Ptr> Iterator for EntriesIter<P> {
	type Item = EntryRef<P>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.remaining_len == 0 {
			return None;
		}
		self.remaining_len -= 1;
		let current = unsafe { self.current.cast::<Entry>() };
		let offset = 1 + (current.offset(Entry::header).read() & 7) as i32;
		self.current = unsafe { self.current.raw_offset(offset << 2) };
		Some(EntryRef(current))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		(
			self.remaining_len as usize,
			Some(self.remaining_len as usize),
		)
	}
}

impl<P: Ptr> ExactSizeIterator for EntriesIter<P> {}
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
pub struct EntryRef<P: Ptr>(TPtr<P, Entry>);

impl<P: Ptr> EntryRef<P> {
	accessors! {
		use Entry;
		header: EntryHeader { get; set set_header; }
	}

	pub fn start_addr(&self) -> u64 {
		let mut ret = self.0.offset(Entry::start_lo).read32_le() as u64;
		if ret & 2 != 0 {
			ret |= (self.0.offset(Entry::hi0).read32_le() as u64) << 0x20;
		}
		ret & 0xFFFF_FFFF_FFFF_FFFC
	}

	pub fn set_start_addr(&self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid start_addr");
		let use_hi = self.0.offset(Entry::start_lo).read32_le() & 2 != 0;
		self.0.offset(Entry::start_lo).write32_le(val as u32);
		if use_hi {
			self.0.offset(Entry::hi0).write32_le((val >> 0x20) as u32);
		} else {
			debug_assert!(u32::try_from(val).is_ok(), "invalid start_addr");
		}
	}
	/// The actual end address is `4` higher than this.
	pub fn end_addr(&self) -> u64 {
		let mut ret = self.0.offset(Entry::end_lo).read32_le() as u64;
		if ret & 2 != 0 {
			ret |= (self.end_hi_ptr().read32_le() as u64) << 0x20;
		}
		ret & 0xFFFF_FFFF_FFFF_FFFC
	}

	/// The input should be the actual end address minus `4`.
	pub fn set_end_addr(&self, val: u64) {
		debug_assert_eq!(val % 4, 0, "invalid end_addr");
		let use_hi = self.0.offset(Entry::end_lo).read32_le() & 2 != 0;
		self.0.offset(Entry::end_lo).write32_le(val as u32);
		if use_hi {
			self.end_hi_ptr().write32_le((val >> 0x20) as u32);
		} else {
			debug_assert!(u32::try_from(val).is_ok(), "invalid end_addr");
		}
	}

	fn end_hi_ptr(&self) -> TPtr<P, u32> {
		let start_lo = self.0.offset(Entry::start_lo).read32_le();
		if start_lo & 2 != 0 {
			unsafe { self.0.cast() }.offset(Entry::hi1)
		} else {
			unsafe { self.0.cast() }.offset(Entry::hi0)
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
