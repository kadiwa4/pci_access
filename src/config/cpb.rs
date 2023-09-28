//! PCI capability structures.

pub mod enhanced_alloc;
pub mod fpb;
pub mod msi;
pub mod pcie;
pub mod power_management;

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
};

use super::HeaderRef;
use crate::{cast, map, VolatilePtr};

#[derive(Clone, Copy)]
#[repr(C, align(4))]
struct CpbHeader {
	id: u8,
	next_ptr: u8,
}

/// Iterates over PCI capabilities. Skips null capabilities.
#[derive(Clone)]
pub struct CpbIter {
	header: VolatilePtr<u8>,
	current_offset: u8,
	type1: bool,
}

impl CpbIter {
	pub(super) fn new(header: HeaderRef, ptr: u8) -> Self {
		Self {
			header: cast!(header.0),
			current_offset: ptr & 0xFC,
			type1: header.specific().get_type() == 1,
		}
	}
}

impl Iterator for CpbIter {
	type Item = Cpb;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if self.current_offset == 0 {
				return None;
			}
			let ptr: VolatilePtr<CpbHeader> = cast!(map!((self.header)[self.current_offset]));
			let cpb_header = ptr.read();
			self.current_offset = cpb_header.next_ptr & 0xFC;
			if cpb_header.id != 0 {
				return Some(Cpb {
					ptr,
					type1: self.type1,
				});
			}
		}
	}
}

impl FusedIterator for CpbIter {}

impl Debug for CpbIter {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

/// PCI capability structure of any type. Use the methods to get a specific one.
#[derive(Clone, Copy)]
pub struct Cpb {
	ptr: VolatilePtr<CpbHeader>,
	type1: bool,
}

impl Cpb {
	pub fn id(self) -> u8 {
		map!((self.ptr).id).read()
	}

	pub fn power_management(self) -> Option<power_management::PowerManagementRef> {
		(self.id() == power_management::PowerManagementRef::ID)
			.then(|| power_management::PowerManagementRef(cast!(self.ptr)))
	}

	pub fn vpd(self) -> Option<vpd::VpdRef> {
		(self.id() == vpd::VpdRef::ID).then(|| vpd::VpdRef(cast!(self.ptr)))
	}

	pub fn msi(self) -> Option<msi::MsiRef> {
		(self.id() == msi::MsiRef::ID).then(|| msi::MsiRef::new(cast!(self.ptr)))
	}

	pub fn vendor_specific(self) -> Option<vendor_specific::VendorSpecificRef> {
		(self.id() == vendor_specific::VendorSpecificRef::ID)
			.then(|| vendor_specific::VendorSpecificRef(cast!(self.ptr)))
	}

	pub fn bridge_subsys_id(self) -> Option<bridge_subsys_id::BridgeSubsysIdRef> {
		(self.id() == bridge_subsys_id::BridgeSubsysIdRef::ID)
			.then(|| bridge_subsys_id::BridgeSubsysIdRef(cast!(self.ptr)))
	}

	pub fn pcie(self) -> Option<pcie::PcieRef> {
		(self.id() == pcie::PcieRef::ID).then(|| pcie::PcieRef(cast!(self.ptr)))
	}

	pub fn msix(self) -> Option<msix::MsixRef> {
		(self.id() == msix::MsixRef::ID).then(|| msix::MsixRef(cast!(self.ptr)))
	}

	pub fn advanced_features(self) -> Option<advanced_features::AdvancedFeaturesRef> {
		(self.id() == advanced_features::AdvancedFeaturesRef::ID)
			.then(|| advanced_features::AdvancedFeaturesRef(cast!(self.ptr)))
	}

	pub fn enhanced_alloc(self) -> Option<enhanced_alloc::EnhancedAllocRef> {
		(self.id() == enhanced_alloc::EnhancedAllocRef::ID).then(|| {
			enhanced_alloc::EnhancedAllocRef {
				ptr: cast!(self.ptr),
				type1: self.type1,
			}
		})
	}

	pub fn fpb(self) -> Option<fpb::FpbRef> {
		(self.id() == fpb::FpbRef::ID).then(|| fpb::FpbRef(cast!(self.ptr)))
	}
}

impl Debug for Cpb {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let mut d = f.debug_struct("Cpb");
		d.field("id", &self.id());
		if let Some(specific) = self.power_management() {
			d.field("power_management", &specific);
		} else if let Some(specific) = self.vpd() {
			d.field("vpd", &specific);
		} else if let Some(specific) = self.msi() {
			d.field("msi", &specific);
		} else if let Some(specific) = self.vendor_specific() {
			d.field("vendor_specific", &specific);
		} else if let Some(specific) = self.bridge_subsys_id() {
			d.field("bridge_subsys_id", &specific);
		} else if let Some(specific) = self.pcie() {
			d.field("pcie", &specific);
		} else if let Some(specific) = self.msix() {
			d.field("msix", &specific);
		} else if let Some(specific) = self.advanced_features() {
			d.field("advanced_features", &specific);
		} else if let Some(specific) = self.enhanced_alloc() {
			d.field("enhanced_alloc", &specific);
		} else if let Some(specific) = self.fpb() {
			d.field("fpb", &specific);
		} else {
			return d.finish_non_exhaustive();
		}
		d.finish()
	}
}

/// Vital product data capability structure.
pub mod vpd {
	use core::{
		sync::atomic::{
			compiler_fence,
			Ordering::{Acquire, Release},
		},
		task::Poll,
	};

	use crate::{map, VolatilePtr};

	#[derive(Debug)] // FIXME: remove
	#[derive(Clone, Copy)]
	#[repr(C)]
	pub(super) struct Vpd {
		_common: [u8; 2],
		address: u16,
		data: u32,
	}

	/// Reference to a vital product data capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct VpdRef(pub(super) VolatilePtr<Vpd>);

	// no idea if the compiler fences are worth it; my idea was that it should try to do as much
	// work as possible in between the start_* and the poll_*
	impl VpdRef {
		pub const ID: u8 = 3;

		pub fn start_read(self, address: u16) {
			debug_assert!(address % 4 == 0 && address < 0x8000, "invalid VPD address");
			map!(self->address).write((address & 0x7FFF).to_le());
			compiler_fence(Acquire);
		}

		pub fn poll_read(self) -> Poll<u32> {
			compiler_fence(Release);
			if u16::from_le(map!(self->address).read()) & 0x8000 == 0 {
				Poll::Pending
			} else {
				Poll::Ready(u32::from_le(map!(self->data).read()))
			}
		}

		/// Convencience method that calls [`Self::start_read`] and then
		/// repeatedly [`Self::poll_read`].
		pub fn read(self, address: u16) -> u32 {
			self.start_read(address);
			loop {
				if let Poll::Ready(val) = self.poll_read() {
					return val;
				}
			}
		}

		pub fn start_write(self, address: u16, val: u32) {
			debug_assert!(address % 4 == 0 && address < 0x8000, "invalid VPD address");
			map!(self->data).write(val.to_le());
			map!(self->address).write((address | 0x8000).to_le());
			compiler_fence(Acquire);
		}

		pub fn poll_write(self) -> Poll<()> {
			compiler_fence(Release);
			if map!(self->address).read() & 0x8000 == 0 {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		}

		/// Convencience method that calls [`Self::start_write`] and then
		/// repeatedly [`Self::poll_write`].
		pub fn write(self, address: u16, val: u32) {
			self.start_write(address, val);
			while self.poll_write().is_pending() {}
		}
	}
}

/// Vendor-specific capability structure.
pub mod vendor_specific {
	use crate::{cast, config::accessors, map, VolatilePtr};

	#[derive(Debug)] // FIXME: remove
	#[derive(Clone, Copy)]
	#[repr(C, align(4))]
	pub(super) struct VendorSpecific {
		_common: [u8; 2],
		len: u8,
	}

	/// Reference to a vendor-specific capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct VendorSpecificRef(pub(super) VolatilePtr<VendorSpecific>);

	impl VendorSpecificRef {
		pub const ID: u8 = 9;

		accessors! {
			len: u8 { get; }
		}

		pub fn is_empty(self) -> bool {
			self.len() == 0
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure.
		pub fn get(self, offset: u8) -> Option<u8> {
			(offset < self.len()).then(|| map!((cast!(self.0 => u8))[offset]).read())
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure.
		///
		/// # Panics
		/// Panics on an out-of-bounds write attempt.
		pub fn set(self, offset: u8, val: u8) {
			assert!(offset < self.len(), "index out of bounds");
			map!((cast!(self.0 => u8))[offset]).write(val);
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure divided by 4.
		pub fn get_u32(self, offset: u8) -> Option<u32> {
			(offset < self.len() >> 2).then(|| map!((cast!(self.0 => u32))[offset]).read())
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure divided by 4.
		///
		/// # Panics
		/// Panics on an out-of-bounds write attempt.
		pub fn set_u32(self, offset: u8, val: u32) {
			assert!(offset < self.len() >> 2, "index out of bounds");
			map!((cast!(self.0 => u32))[offset]).write(val);
		}
	}
}

/// PCI bridge subsystem ID and subsystem vendor ID capability structure.
pub mod bridge_subsys_id {
	use crate::{config::accessors, VolatilePtr};

	#[derive(Debug)] // FIXME: remove
	#[derive(Clone, Copy)]
	#[repr(C, align(4))]
	pub(super) struct BridgeSubsysId {
		_common: [u8; 2],
		_reserved: [u8; 2],
		vendor_id: u16,
		id: u16,
	}

	/// Reference to a subsystem ID and subsystem vendor ID capability
	/// structure.
	#[derive(Clone, Copy, Debug)]
	pub struct BridgeSubsysIdRef(pub(super) VolatilePtr<BridgeSubsysId>);

	impl BridgeSubsysIdRef {
		pub const ID: u8 = 0x0D;

		accessors! {
			vendor_id: u16 { get => u16::from_le; }
			id: u16 { get => u16::from_le; }
		}
	}
}

/// MSI-X capability structure.
pub mod msix {
	use crate::{
		config::{accessors, bit_accessors, BitField},
		map, VolatilePtr,
	};

	#[derive(Debug)] // FIXME: remove
	#[derive(Clone, Copy)]
	#[repr(C)]
	pub(super) struct Msix {
		_common: [u8; 2],
		message_control: MessageControl,
		table_offset: u32,
		pending_bit_array_offset: u32,
	}

	/// Reference to an MSI-X capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct MsixRef(pub(super) VolatilePtr<Msix>);

	impl MsixRef {
		pub const ID: u8 = 0x11;

		accessors! {
			message_control: MessageControl { get; set set_message_control; }
		}

		pub fn table_bar_idx(self) -> u8 {
			map!(self->table_offset).read() as u8 & 7
		}

		pub fn table_offset(self) -> u32 {
			map!(self->table_offset).read() & 0xFFFF_FFF8
		}

		pub fn pending_bit_array_bar_idx(self) -> u8 {
			map!(self->pending_bit_array_offset).read() as u8 & 7
		}

		pub fn pending_bit_array_offset(self) -> u32 {
			map!(self->pending_bit_array_offset).read() & 0xFFFF_FFF8
		}
	}

	/// Message control value of an [MSI-X capability structure](MsixRef).
	#[derive(Clone, Copy, Debug)]
	#[repr(transparent)]
	pub struct MessageControl(u16);

	impl MessageControl {
		bit_accessors! {
			table_last_idx: u16, 0..0x0B { get; }
			function_mask: 0x0E { get; set with_function_mask; }
			enabled: 0x0F { get; set enable; }
		}
	}

	impl BitField for MessageControl {
		type Inner = u16;
	}
}

/// PCI advanced features capability structure.
pub mod advanced_features {
	use crate::config::{accessors, bit_accessors, BitField, VolatilePtr};

	#[derive(Debug)] // FIXME: remove
	#[derive(Clone, Copy)]
	#[repr(C, align(4))]
	pub(super) struct AdvancedFeatures {
		_common: [u8; 2],
		_len: u8,
		cpbs: AdvancedFeaturesCpbs,
		control: Control,
		status: Status,
	}

	/// Reference to a PCI advanced features capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct AdvancedFeaturesRef(pub(super) VolatilePtr<AdvancedFeatures>);

	impl AdvancedFeaturesRef {
		pub const ID: u8 = 0x13;

		accessors! {
			cpbs: AdvancedFeaturesCpbs { get; }
			control: Control { get; set set_control; }
			status: Status { get; }
		}
	}

	/// [PCI advanced features](AdvancedFeaturesRef) capabilities value.
	#[derive(Clone, Copy, Debug)]
	#[repr(transparent)]
	pub struct AdvancedFeaturesCpbs(u8);

	impl AdvancedFeaturesCpbs {
		bit_accessors! {
			transactions_pending_support: 0 { get; }
			func_level_resetting: 1 { get; }
		}
	}

	impl BitField for AdvancedFeaturesCpbs {
		type Inner = u8;
	}

	/// Control value of a
	/// [PCI advanced features capability structure](AdvancedFeaturesRef).
	#[derive(Clone, Copy, Debug)]
	#[repr(transparent)]
	pub struct Control(u8);

	impl Control {
		#[must_use]
		pub fn init_func_level_reset(self) -> Self {
			Self(self.0 | 1)
		}
	}

	/// Status value of a
	/// [PCI advanced features capability structure](AdvancedFeaturesRef).
	#[derive(Clone, Copy, Debug)]
	#[repr(transparent)]
	pub struct Status(u8);

	impl Status {
		bit_accessors! {
			transactions_pending: 0 { get; }
		}
	}

	impl BitField for Status {
		type Inner = u8;
	}
}
