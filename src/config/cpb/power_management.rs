//! PCI power management capability structure.

use crate::{accessors, bit_accessors, struct_offsets, Ptr, ReprPrimitive, TPtr};

pub const ID: u8 = 1;

struct_offsets! {
	pub(super) struct PowerManagement {
		_common: [u8; 2],
		cpbs: PowerManagementCpbs,
		control_status: ControlStatus,
		_reserved: u8,
		data: u8,
	}
}

/// Reference to a PCI power management capability structure.
#[derive(Clone, Copy, Debug)]
pub struct PowerManagementRef<P: Ptr>(pub(super) TPtr<P, PowerManagement>);

impl<P: Ptr> PowerManagementRef<P> {
	accessors! {
		use PowerManagement;
		cpbs: PowerManagementCpbs { get; }
		/// Call [`ControlStatus::mask_preserved`] before setting this register.
		control_status: ControlStatus { get; set set_control_status; }
	}

	/// Power consumed in milliwatts.
	pub fn power_consumed(&self, state: PowerState) -> Option<u16> {
		self.get_data(state as u8)
	}

	/// Power dissipated in milliwatts.
	pub fn power_dissipated(&self, state: PowerState) -> Option<u16> {
		self.get_data(state as u8 | 4)
	}

	/// Common logic power consumed in milliwatts.
	///
	/// Only available on Function 0.
	pub fn common_logic_power_consumed(&self) -> Option<u16> {
		self.get_data(8)
	}

	fn get_data(&self, data_select: u8) -> Option<u16> {
		self.set_control_status(
			self.control_status()
				.mask_preserved()
				.with_data_select(data_select),
		);
		self.control_status()
			.data_scale()
			.map(|s| s as u16 * self.0.offset(PowerManagement::data).read() as u16)
	}
}

/// [PCI power management](PowerManagementRef) capabilities value.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct PowerManagementCpbs(u16);

impl PowerManagementCpbs {
	bit_accessors! {
		version: u8, 0..3 { get; }
		pme_clock: 3 { get; }
		immediate_readiness_on_return_to_d0: 4 { get; }
		device_specific_init: 5 { get; }
		/// Auxiliary current in milliamperes.
		aux_current: u16, 6..9 {
			get => |val| match val {
				0 => 0,
				1 => 55,
				2 => 100,
				3 => 160,
				4 => 220,
				5 => 270,
				6 => 320,
				7 => 375,
				_ => unreachable!(),
			};
		}
		d1: 9 { get; }
		d2: 0x0A { get; }
		pme_from_d0: 0x0B { get; }
		pme_from_d1: 0x0C { get; }
		pme_from_d2: 0x0D { get; }
		pme_from_d3_hot: 0x0E { get; }
		pme_from_d3_cold: 0x0F { get; }
	}
}

unsafe impl ReprPrimitive for PowerManagementCpbs {
	type Repr = u16;
}

/// Control/status value of a
/// [PCI power management capability structure](PowerManagementRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct ControlStatus(u16);

impl ControlStatus {
	/// Clear all bits that should not be preserved.
	#[must_use]
	pub fn mask_preserved(self) -> Self {
		Self(self.0 & 0x7FFF_u16.to_le())
	}

	bit_accessors! {
		power_state: PowerState, 0..2 {
			get => |val| unsafe { core::mem::transmute(val as u8) };
			set with_power_state;
		}
		no_soft_reset: 3 { get; }
		pme_enabled: 8 { get; set enable_pme; }
		pme_status: 0x0F { get; set with_pme_status; }
	}

	#[inline]
	fn with_data_select(self, val: u8) -> Self {
		debug_assert!(val < 0x10, "invalid data_select input");
		Self((self.0 & 0xE1FF_u16.to_le()) | ((val as u16 & 0x0F) << 9).to_le())
	}

	/// Result is in milliwatts.
	fn data_scale(self) -> Option<u8> {
		match (u16::from_le(self.0) >> 13) & 3 {
			0 => None,
			1 => Some(100),
			2 => Some(10),
			3 => Some(1),
			_ => unreachable!(),
		}
	}
}

unsafe impl ReprPrimitive for ControlStatus {
	type Repr = u16;
}

/// Device power management state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum PowerState {
	#[default]
	D0,
	D1,
	D2,
	D3,
}
