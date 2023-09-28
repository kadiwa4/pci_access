//! PCI Express extended capability structures.

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
	ptr::NonNull,
};

use crate::{cast, config::ConfigSpace, map, VolatilePtr};

/// A PCI Express configuration space. A pointer to this is used to construct an
/// [`ExtCpbIter`].
///
/// Size: 4 KiB, alignment: 4 bytes
#[repr(C)]
pub struct ExtConfigSpace {
	/// Offset: 0 bytes.
	pub conventional: ConfigSpace,
	ext_cpbs: [u8; 0x0F00],
}

/// Iterates over PCI Express extended capabilities. Skips null capabilities.
#[derive(Clone)]
pub struct ExtCpbIter {
	base_ptr: VolatilePtr<u8>,
	current: Option<ExtCpb>,
}

impl ExtCpbIter {
	/// # Safety
	/// - The input has to point to a valid PCI Express configuration space.
	/// - Only one thread can access the configuration space at a time.
	pub unsafe fn new(ptr: NonNull<ExtConfigSpace>) -> Self {
		let ptr = VolatilePtr::new(ptr);
		let current = Some(ExtCpb::new(cast!(map!(ptr.ext_cpbs))));
		current.filter(|&c| c.id != 0xFFFF || c.next_offset() == 0);
		Self {
			base_ptr: cast!(ptr),
			current,
		}
	}
}

impl Iterator for ExtCpbIter {
	type Item = ExtCpb;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let current = self.current?;
			let next_offset = current.next_offset();
			self.current = (next_offset != 0)
				.then(|| unsafe { ExtCpb::new(cast!(map!((self.base_ptr)[next_offset]))) });
			if current.id != 0 {
				return Some(current);
			}
		}
	}
}

impl FusedIterator for ExtCpbIter {}

impl Debug for ExtCpbIter {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

/// PCI Express extended capability structure of any type.
/// Use the methods to get a specific one.
#[derive(Clone, Copy)]
pub struct ExtCpb {
	header: VolatilePtr<u32>,
	id: u16,
}

impl ExtCpb {
	/// # Safety
	/// The input has to point to a extended capability.
	unsafe fn new(ptr: VolatilePtr<u32>) -> Self {
		let id = u16::from_le(cast!(ptr => u16).read());
		Self { header: ptr, id }
	}

	pub fn id(self) -> u16 {
		self.id
	}

	pub fn version(self) -> u8 {
		(u32::from_le(self.header.read()) >> 0x10) as u8 & 0x0F
	}

	fn next_offset(self) -> u16 {
		(u32::from_le(self.header.read()) >> 0x14) as u16 & 0x0FFC
	}
}

impl Debug for ExtCpb {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let mut d = f.debug_struct("ExtCpb");
		d.field("id", &self.id()).field("version", &self.version());
		// if let Some(specific) = todo!() {
		// 	d.field("power_management", &specific);
		// } else {
		d.finish_non_exhaustive()
		// }
		// d.finish()
	}
}
