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
use crate::{Ptr, TPtr};

#[repr(C, align(2))]
struct CpbHeader {
	id: u8,
	next_ptr: u8,
}

/// Iterates over PCI capabilities. Skips null capabilities.
#[derive(Clone)]
pub struct CpbIter<P: Ptr> {
	header_ptr: P,
	current_offset: u8,
	type1: bool,
}

impl<P: Ptr> CpbIter<P> {
	pub(super) fn new(header: HeaderRef<P>, offset: u8) -> Self {
		Self {
			type1: header.header_type().get() == 1,
			header_ptr: header.0 .0,
			current_offset: offset & 0xFC,
		}
	}
}

impl<P: Ptr> Iterator for CpbIter<P> {
	type Item = Cpb<P>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			if self.current_offset == 0 {
				return None;
			}
			let ptr = unsafe { self.header_ptr.offset(self.current_offset as i32) };
			let cpb_header: CpbHeader = unsafe { core::mem::transmute(ptr.read16()) };
			self.current_offset = cpb_header.next_ptr & 0xFC;
			if cpb_header.id != 0 {
				return Some(Cpb {
					ptr: unsafe { TPtr::new(ptr) },
					type1: self.type1,
				});
			}
		}
	}
}

impl<P: Ptr> FusedIterator for CpbIter<P> {}

impl<P: Ptr> Debug for CpbIter<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

/// PCI capability structure of any type. Use the methods to get a specific one.
#[derive(Clone, Copy)]
pub struct Cpb<P: Ptr> {
	ptr: TPtr<P, CpbHeader>,
	type1: bool,
}

impl<P: Ptr> Cpb<P> {
	pub fn id(&self) -> u8 {
		unsafe { self.ptr.cast::<u8>() }.read()
	}

	pub fn power_management(&self) -> Option<power_management::PowerManagementRef<P>> {
		(self.id() == power_management::ID)
			.then(|| power_management::PowerManagementRef(unsafe { self.ptr.cast() }))
	}

	pub fn vpd(&self) -> Option<vpd::VpdRef<P>> {
		(self.id() == vpd::ID).then(|| vpd::VpdRef(unsafe { self.ptr.cast() }))
	}

	pub fn msi(&self) -> Option<msi::MsiRef<P>> {
		(self.id() == msi::ID).then(|| msi::MsiRef::new(unsafe { self.ptr.cast() }))
	}

	pub fn vendor_specific(&self) -> Option<vendor_specific::VendorSpecificRef<P>> {
		(self.id() == vendor_specific::ID)
			.then(|| vendor_specific::VendorSpecificRef(unsafe { self.ptr.cast() }))
	}

	pub fn bridge_subsys_id(&self) -> Option<bridge_subsys_id::BridgeSubsysIdRef<P>> {
		(self.id() == bridge_subsys_id::ID)
			.then(|| bridge_subsys_id::BridgeSubsysIdRef(unsafe { self.ptr.cast() }))
	}

	pub fn pcie(&self) -> Option<pcie::PcieRef<P>> {
		(self.id() == pcie::ID).then(|| pcie::PcieRef(unsafe { self.ptr.cast() }))
	}

	pub fn msix(&self) -> Option<msix::MsixRef<P>> {
		(self.id() == msix::ID).then(|| msix::MsixRef(unsafe { self.ptr.cast() }))
	}

	pub fn advanced_features(&self) -> Option<advanced_features::AdvancedFeaturesRef<P>> {
		(self.id() == advanced_features::ID)
			.then(|| advanced_features::AdvancedFeaturesRef(unsafe { self.ptr.cast() }))
	}

	pub fn enhanced_alloc(&self) -> Option<enhanced_alloc::EnhancedAllocRef<P>> {
		(self.id() == enhanced_alloc::ID).then(|| enhanced_alloc::EnhancedAllocRef {
			ptr: unsafe { self.ptr.cast() },
			type1: self.type1,
		})
	}

	pub fn fpb(&self) -> Option<fpb::FpbRef<P>> {
		(self.id() == fpb::ID).then(|| fpb::FpbRef(unsafe { self.ptr.cast() }))
	}
}

impl<P: Ptr> Debug for Cpb<P> {
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

	use crate::{struct_offsets, Ptr, TPtr};

	pub const ID: u8 = 3;

	struct_offsets! {
		pub(super) struct Vpd {
			_common: [u8; 2],
			address: u16,
			data: u32,
		}
	}

	/// Reference to a vital product data capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct VpdRef<P: Ptr>(pub(super) TPtr<P, Vpd>);

	// no idea if the compiler fences are worth it; my idea was that it should try to do as much
	// work as possible in between the start_* and the poll_*
	impl<P: Ptr> VpdRef<P> {
		pub fn start_read(&self, address: u16) {
			debug_assert!(address % 4 == 0 && address < 0x8000, "invalid VPD address");
			self.0.offset(Vpd::address).write16_le(address & 0x7FFF);
			compiler_fence(Acquire);
		}

		pub fn poll_read(&self) -> Poll<u32> {
			compiler_fence(Release);
			if self.0.offset(Vpd::address).read16_le() & 0x8000 == 0 {
				Poll::Pending
			} else {
				Poll::Ready(self.0.offset(Vpd::data).read32_le())
			}
		}

		/// Convencience method that calls [`Self::start_read`] and then
		/// repeatedly [`Self::poll_read`].
		pub fn read(&self, address: u16) -> u32 {
			self.start_read(address);
			loop {
				if let Poll::Ready(val) = self.poll_read() {
					return val;
				}
			}
		}

		pub fn start_write(&self, address: u16, val: u32) {
			debug_assert!(address % 4 == 0 && address < 0x8000, "invalid VPD address");
			self.0.offset(Vpd::data).write32_le(val);
			self.0.offset(Vpd::address).write16_le(address | 0x8000);
			compiler_fence(Acquire);
		}

		pub fn poll_write(&self) -> Poll<()> {
			compiler_fence(Release);
			if self.0.offset(Vpd::address).read16_le() & 0x8000 == 0 {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		}

		/// Convencience method that calls [`Self::start_write`] and then
		/// repeatedly [`Self::poll_write`].
		pub fn write(&self, address: u16, val: u32) {
			self.start_write(address, val);
			while self.poll_write().is_pending() {}
		}
	}
}

/// Vendor-specific capability structure.
pub mod vendor_specific {
	use crate::{accessors, struct_offsets, Ptr, TPtr};

	pub const ID: u8 = 9;

	struct_offsets! {
		pub(super) struct VendorSpecific {
			_common: [u8; 2],
			len: u8,
		}
	}

	/// Reference to a vendor-specific capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct VendorSpecificRef<P: Ptr>(pub(super) TPtr<P, VendorSpecific>);

	impl<P: Ptr> VendorSpecificRef<P> {
		accessors! {
			use VendorSpecific;
			len: u8 { get; }
		}

		pub fn is_empty(&self) -> bool {
			self.len() == 0
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure.
		pub fn get(&self, offset: u8) -> Option<u8> {
			(offset < self.len()).then(|| unsafe { self.0 .0.offset(offset as i32).read8() })
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure.
		///
		/// # Panics
		/// Panics on an out-of-bounds write attempt.
		pub fn set(&self, offset: u8, val: u8) {
			assert!(offset < self.len(), "index out of bounds");
			unsafe {
				self.0 .0.offset(offset as i32).write8(val);
			}
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure divided by 4. Returned value is little-endian.
		pub fn get_u32(&self, offset: u8) -> Option<u32> {
			(offset < self.len() >> 2)
				.then(|| unsafe { self.0 .0.offset((offset as i32) << 2).read32() })
		}

		/// `offset` is the byte offset from the start of the capability
		/// structure divided by 4. Returned value is little-endian.
		///
		/// # Panics
		/// Panics on an out-of-bounds write attempt.
		pub fn set_u32(&self, offset: u8, val: u32) {
			assert!(offset < self.len() >> 2, "index out of bounds");
			unsafe {
				self.0 .0.offset((offset as i32) << 2).write32(val);
			}
		}
	}
}

/// PCI bridge subsystem ID and subsystem vendor ID capability structure.
pub mod bridge_subsys_id {
	use crate::{accessors, struct_offsets, Ptr, TPtr};

	pub const ID: u8 = 0x0D;

	struct_offsets! {
		pub(super) struct BridgeSubsysId {
			_common: [u8; 2],
			_reserved: [u8; 2],
			vendor_id: u16,
			id: u16,
		}
	}

	/// Reference to a subsystem ID and subsystem vendor ID capability
	/// structure.
	#[derive(Clone, Copy, Debug)]
	pub struct BridgeSubsysIdRef<P: Ptr>(pub(super) TPtr<P, BridgeSubsysId>);

	impl<P: Ptr> BridgeSubsysIdRef<P> {
		accessors! {
			use BridgeSubsysId;
			vendor_id: u16 { get => u16::from_le; }
			id: u16 { get => u16::from_le; }
		}
	}
}

/// MSI-X capability structure.
pub mod msix {
	use crate::{accessors, bit_accessors, struct_offsets, Ptr, ReprPrimitive, TPtr};

	pub const ID: u8 = 0x11;

	struct_offsets! {
		pub(super) struct Msix {
			_common: [u8; 2],
			message_control: MessageControl,
			table_offset: u32,
			pending_bit_array_offset: u32,
		}
	}

	/// Reference to an MSI-X capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct MsixRef<P: Ptr>(pub(super) TPtr<P, Msix>);

	impl<P: Ptr> MsixRef<P> {
		accessors! {
			use Msix;
			message_control: MessageControl { get; set set_message_control; }
		}

		pub fn table_bar_idx(&self) -> u8 {
			self.0.offset(Msix::table_offset).read32_le() as u8 & 7
		}

		pub fn table_offset(&self) -> u32 {
			self.0.offset(Msix::table_offset).read32_le() & 0xFFFF_FFF8
		}

		pub fn pending_bit_array_bar_idx(&self) -> u8 {
			self.0.offset(Msix::pending_bit_array_offset).read32_le() as u8 & 7
		}

		pub fn pending_bit_array_offset(&self) -> u32 {
			self.0.offset(Msix::pending_bit_array_offset).read32_le() & 0xFFFF_FFF8
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

	unsafe impl ReprPrimitive for MessageControl {
		type Repr = u16;
	}
}

/// PCI advanced features capability structure.
pub mod advanced_features {
	use crate::{accessors, bit_accessors, struct_offsets, Ptr, ReprPrimitive, TPtr};

	pub const ID: u8 = 0x13;

	struct_offsets! {
		pub(super) struct AdvancedFeatures {
			_common: [u8; 2],
			_len: u8,
			cpbs: AdvancedFeaturesCpbs,
			control: Control,
			status: Status,
		}
	}

	/// Reference to a PCI advanced features capability structure.
	#[derive(Clone, Copy, Debug)]
	pub struct AdvancedFeaturesRef<P: Ptr>(pub(super) TPtr<P, AdvancedFeatures>);

	impl<P: Ptr> AdvancedFeaturesRef<P> {
		accessors! {
			use AdvancedFeatures;
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

	unsafe impl ReprPrimitive for AdvancedFeaturesCpbs {
		type Repr = u8;
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

	unsafe impl ReprPrimitive for Control {
		type Repr = u8;
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

	unsafe impl ReprPrimitive for Status {
		type Repr = u8;
	}
}
