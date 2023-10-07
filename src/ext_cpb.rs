//! PCI Express extended capability structures.

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
};

use crate::{struct_offsets, Ptr, PtrExt};

struct_offsets! {
	struct ExtConfigSpace {
		_header: [u8; 0x0100],
		ext_cpbs: [u8; 0x0F00],
	}
}

/// Iterates over PCI Express extended capabilities. Skips null capabilities.
#[derive(Clone)]
pub struct ExtCpbIter<P: Ptr> {
	base_ptr: P,
	current: Option<ExtCpb<P>>,
}

impl<P: Ptr> ExtCpbIter<P> {
	/// # Safety
	/// - The input has to point to a valid PCI Express configuration space.
	/// - Only one thread can access the configuration space at a time.
	pub unsafe fn new(ptr: P) -> Self {
		let current = Some(ExtCpb::new(ptr.offset(ExtConfigSpace::ext_cpbs)));
		Self {
			base_ptr: ptr,
			current: current.filter(|c| c.id != 0xFFFF || c.next_offset() == 0),
		}
	}
}

impl<P: Ptr> Iterator for ExtCpbIter<P> {
	type Item = ExtCpb<P>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let current = self.current.clone()?;
			let next_offset = current.next_offset() as i32;
			self.current = (next_offset != 0)
				.then(|| unsafe { ExtCpb::new(self.base_ptr.offset(next_offset)) });
			if current.id != 0 {
				return Some(current);
			}
		}
	}
}

impl<P: Ptr> FusedIterator for ExtCpbIter<P> {}

impl<P: Ptr> Debug for ExtCpbIter<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

/// PCI Express extended capability structure of any type.
/// Use the methods to get a specific one.
#[derive(Clone, Copy)]
pub struct ExtCpb<P: Ptr> {
	header: P,
	id: u16,
}

impl<P: Ptr> ExtCpb<P> {
	/// # Safety
	/// The input has to point to a extended capability.
	unsafe fn new(ptr: P) -> Self {
		let id = ptr.read16_le();
		Self { header: ptr, id }
	}

	pub fn id(&self) -> u16 {
		self.id
	}

	pub fn version(&self) -> u8 {
		(unsafe { self.header.read32_le() } >> 0x10) as u8 & 0x0F
	}

	fn next_offset(&self) -> u16 {
		(unsafe { self.header.read32_le() } >> 0x14) as u16 & 0x0FFC
	}
}

impl<P: Ptr> Debug for ExtCpb<P> {
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
