//! PCI Express capability structure (residing in conventional PCI configuration
//! space).

use core::ops::{BitAnd, Bound};

use bitflags::bitflags;
use num_enum::TryFromPrimitive;

use crate::{
	config::{accessors, bit_accessors, ReprPrimitive},
	struct_offsets, Ptr,
};

pub const ID: u8 = 0x10;

struct_offsets! {
	struct Pcie {
		_common: [u8; 2],
		cpbs: PcieCpbs,
		device_cpbs: DeviceCpbs,
		device_control: DeviceControl,
		device_status: DeviceStatus,
		link_cpbs: LinkCpbs,
		link_control: LinkControl,
		link_status: LinkStatus,
		slot_cpbs: SlotCpbs,
		slot_control: SlotControl,
		slot_status: SlotStatus,
		root_control: RootControl,
		root_cpbs: RootCpbs,
		root_status: RootStatus,
		device_cpbs2: DeviceCpbs2,
		device_control2: DeviceControl2,
		_device_status2: u16,
		link_cpbs2: LinkCpbs2,
		link_control2: LinkControl2,
		link_status2: LinkStatus2,
		slot_cpbs2: SlotCpbs2,
		_slot_control2: u16,
		_slot_status2: u16,
	}
}

/// Reference to a PCI Express capability structure (residing in conventional
/// PCI configuration space).
#[derive(Clone, Copy, Debug)]
pub struct PcieRef<P: Ptr>(pub(super) P);

impl<P: Ptr> PcieRef<P> {
	accessors! {
		use Pcie;
		cpbs: PcieCpbs { get; }
		device_cpbs: DeviceCpbs { get; }
		device_control: DeviceControl { get; set set_device_control; }
		device_status: DeviceStatus { get; set set_device_status; }
		link_cpbs: LinkCpbs { get; }
		link_control: LinkControl { get; set set_link_control; }
		link_status: LinkStatus { get; set set_link_status; }
		slot_cpbs: SlotCpbs { get; }
		slot_control: SlotControl { get; set set_slot_control; }
		slot_status: SlotStatus { get; set set_slot_status; }
		root_cpbs: RootCpbs { get; }
		root_control: RootControl { get; set set_root_control; }
		root_status: RootStatus { get; set set_root_status; }
		device_cpbs2: DeviceCpbs2 { get; }
		device_control2: DeviceControl2 { get; set set_device_control2; }
		link_cpbs2: LinkCpbs2 { get; }
		link_control2: LinkControl2 { get; set set_link_control2; }
		link_status2: LinkStatus2 { get; set set_link_status2; }
		slot_cpbs2: SlotCpbs2 { get; }
	}
}

/// [PCI Express](PcieRef) capabilities value.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct PcieCpbs(u16);

impl PcieCpbs {
	bit_accessors! {
		version: u8, 0..4 { get; }
		device_port_type: DevicePortType, 4..8 {
			get => |v| DevicePortType::try_from(v as u8).expect("reserved value");
		}
		slot_implemented: 8 { get; }
		interrupt_message_num: u8, 9..0x0E { get; }
	}
}

unsafe impl ReprPrimitive for PcieCpbs {
	type Repr = u16;
}

/// Value of [`PcieCpbs::device_port_type`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum DevicePortType {
	T0PcieEndpoint,
	T0LegacyPcieEndpoint,
	T1PcieRcRootPort = 4,
	T1PcieSwitchUpstreamPort,
	T1PcieSwitchDownstreamPort,
	T1PcieToPciBridge,
	T1PciToPcieBridge,
	T0RcIntegratedEndpoint,
	T0RcEventCollector,
}

/// Device capabilities value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct DeviceCpbs(u32);

impl DeviceCpbs {
	bit_accessors! {
		max_payload_size: MaxSize, 0..3 {
			get => |val| MaxSize::try_from(val as u8).expect("reserved value");
		}
		phantom_func_bits: u8, 3..5 { get; }
		tag_field_8bit: 5 { get; }
		/// Endpoint L0s latency limit in nanoseconds.
		endpoint_l0s_latency_limit: Option<u16>, 6..9 {
			get => |exponent| {
				let latency = match exponent {
					0..=3 => 0x40 << exponent,
					4 => 1000,
					5 => 2000,
					6 => 4000,
					7 => return None,
					_ => unreachable!(),
				};
				Some(latency)
			};
		}
		/// Endpoint L0s latency limit in nanoseconds.
		endpoint_l1_latency_limit: Option<u16>, 9..0x0C {
			get => |exponent| (exponent != 7).then_some(1000_u16 << exponent);
		}
		role_based_error_reporting: 0x0F { get; }
		correctable_error_subclass: 0x10 { get; }
		func_level_resetting: 0x1C { get; }
	}

	/// Captured slot power limit in milliwatts.
	#[inline]
	pub fn captured_slot_power_limit(self) -> u32 {
		let bits = u32::from_le(self.0);
		decode_power_limit((bits >> 0x12) as u8, (bits >> 0x1A) as u8)
	}
}

unsafe impl ReprPrimitive for DeviceCpbs {
	type Repr = u32;
}

/// Device control value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct DeviceControl(u16);

impl DeviceControl {
	bit_accessors! {
		correctable_error_reporting: 0 { get; set with_correctable_error_reporting; }
		nonfatal_error_reporting: 1 { get; set with_nonfatal_error_reporting; }
		fatal_error_reporting: 2 { get; set with_fatal_error_reporting; }
		unsupported_request_reporting: 3 { get; set with_unsupported_request_reporting; }
		relaxed_ordering: 4 { get; set with_relaxed_ordering; }
		max_payload_size: MaxSize, 5..8 {
			get => |val| MaxSize::try_from(val as u8).expect("reserved value");
			set with_max_payload_size;
		}
		extended_tag_field: 8 { get; set with_extended_tag_field; }
		phantom_funcs: 9 { get; set with_phantom_funcs; }
		aux_power_pm: 0x0A { get; set with_aux_power_pm; }
		no_snoop_bit: 0x0B { get; set with_no_snoop_bit; }
		max_read_request_size: MaxSize, 0x0C..0x0F {
			get => |val| MaxSize::try_from(val as u8).expect("reserved value");
			set with_max_read_request_size;
		}
		bridge_config_retry_enabled: 0x0F { get; set enable_bridge_config_retry; }
	}

	#[inline]
	#[must_use]
	pub fn init_func_level_reset(self) -> Self {
		Self(self.0 | 0x8000_u16.to_le())
	}
}

unsafe impl ReprPrimitive for DeviceControl {
	type Repr = u16;
}

/// Value of [`DeviceCpbs::max_payload_size`],
/// [`DeviceControl::max_payload_size`] and
/// [`DeviceControl::max_read_request_size`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum MaxSize {
	S128B,
	S256B,
	S512B,
	S1Kib,
	S2Kib,
	S4Kib,
}

impl MaxSize {
	pub fn from_size(val: u16) -> Option<Self> {
		if val.count_ones() != 1 {
			return None;
		}
		let exponent = val.ilog2() as u8;
		Self::try_from(u8::checked_sub(exponent, 7)?).ok()
	}

	pub fn size(self) -> u16 {
		0x80 << (self as u8)
	}
}

/// Device status value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct DeviceStatus(u16);

impl DeviceStatus {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		correctable_error: 0 { get; set1 clear_correctable_error; }
		nonfatal_error: 1 { get; set1 clear_nonfatal_error; }
		fatal_error: 2 { get; set1 clear_fatal_error; }
		unsupported_request: 3 { get; set1 clear_unsupported_request; }
		aux_power: 4 { get; }
		transactions_pending: 5 { get; }
		emergency_power_reduction: 6 { get; set1 clear_emergency_power_reduction; }
	}
}

unsafe impl ReprPrimitive for DeviceStatus {
	type Repr = u16;
}

impl BitAnd for DeviceStatus {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Link capabilities value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct LinkCpbs(u32);

impl LinkCpbs {
	bit_accessors! {
		max_link_speed_bit: u8, 0..4 {
			get => |val| u8::checked_sub(val as u8, 1).filter(|&v| v < 7).expect("reserved value");
		}
		max_link_width: u8, 4..0x0A {
			get => |val| {
				let val = val as u8;
				assert!(
					val == 0x0C || (val.count_ones() == 1 && val < 0x40),
					"reserved value"
				);
				val
			};
		}
		aspm_l0s_support: 0x0A { get; }
		aspm_l1_support: 0x0B { get; }
		/// L0s exit latency as a range of nanoseconds.
		l0s_exit_latency: (Bound<u16>, Bound<u16>), 0x0C..0x0F {
			get => |val| match val {
				0 => (Bound::Unbounded, Bound::Excluded(64)),
				1 => (Bound::Included(64), Bound::Excluded(128)),
				2 => (Bound::Included(128), Bound::Excluded(256)),
				3 => (Bound::Included(256), Bound::Excluded(512)),
				4 => (Bound::Included(512), Bound::Excluded(1000)),
				5 => (Bound::Included(1000), Bound::Excluded(2000)),
				6 => (Bound::Included(2000), Bound::Included(4000)),
				7 => (Bound::Excluded(4000), Bound::Unbounded),
				_ => unreachable!(),
			};
		}
		/// L1 exit latency as a range of nanoseconds.
		l1_exit_latency: (Bound<u16>, Bound<u16>), 0x0F..0x12 {
			get => |val| match val {
				0 => (Bound::Unbounded, Bound::Excluded(1000)),
				1 => (Bound::Included(1000), Bound::Excluded(2000)),
				2 => (Bound::Included(2000), Bound::Excluded(4000)),
				3 => (Bound::Included(4000), Bound::Excluded(8000)),
				4 => (Bound::Included(8000), Bound::Excluded(16000)),
				5 => (Bound::Included(16000), Bound::Excluded(32000)),
				6 => (Bound::Included(32000), Bound::Included(64000)),
				7 => (Bound::Excluded(64000), Bound::Unbounded),
				_ => unreachable!(),
			};
		}
		clock_pm: 0x12 { get; }
		surprise_down_error_reporting: 0x13 { get; }
		dll_link_active_reporting: 0x14 { get; }
		link_bandwidth_notification: 0x15 { get; }
		aspm_optionality: 0x16 { get; }
		port_num: u8, 0x18..0x20 { get; }
	}
}

unsafe impl ReprPrimitive for LinkCpbs {
	type Repr = u32;
}

/// Link control value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct LinkControl(u16);

impl LinkControl {
	bit_accessors! {
		aspm_l0s_entry_enabled: 0 { get; set enable_aspm_l0s_entry; }
		aspm_l1_entry_enabled: 1 { get; set enable_aspm_l1_entry; }
		rcb_128bytes: 3 { get; set with_rcb_128bytes; }
		link_disabled: 4 { get; set disable_link; }
		common_clock_config: 6 { get; set with_common_clock_config; }
		extended_synching: 7 { get; set with_extended_synching; }
		clock_pm: 8 { get; set with_clock_pm; }
		hw_autonomous_width_disabled: 9 { get; set disable_hw_autonomous_width; }
		link_bandwidth_management_interrupt: 0x0A { get; set with_link_bandwidth_management_interrupt; }
		link_autonomous_bandwidth_interrupt: 0x0B { get; set with_link_autonomous_bandwidth_interrupt; }
		drs_signaling: DrsSignaling, 0x0E..0x10 {
			get => |val| DrsSignaling::try_from(val as u8).expect("reserved value");
			set with_drs_signaling;
		}
	}

	#[inline]
	#[must_use]
	pub fn retrain_link(self) -> Self {
		Self(self.0 | 0x20_u16.to_le())
	}
}

unsafe impl ReprPrimitive for LinkControl {
	type Repr = u16;
}

/// Value of [`LinkControl::drs_signaling`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum DrsSignaling {
	NotReported,
	Interrupt,
	FrsSignaling,
}

/// Link status value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct LinkStatus(u16);

impl LinkStatus {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		current_link_speed_bit: u8, 0..4 {
			get => |val| u8::checked_sub(val as u8, 1).filter(|&v| v < 7).expect("reserved value");
		}
		negotiated_link_width: u8, 4..0x0A {
			get => |val| {
				let val = val as u8;
				assert!(
					val == 0x0C || (val.count_ones() == 1 && val < 0x40),
					"reserved value"
				);
				val
			};
		}
		link_training: 0x0B { get; }
		slot_clock_config: 0x0C { get; }
		dll_link_active: 0x0D { get; }
		link_bandwidth_management_status: 0x0E { get; set1 clear_link_bandwidth_management_status; }
		link_autonomous_bandwidth_status: 0x0F { get; set1 clear_link_autonomous_bandwidth_status; }
	}
}

unsafe impl ReprPrimitive for LinkStatus {
	type Repr = u16;
}

impl BitAnd for LinkStatus {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Slot capabilities value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct SlotCpbs(u32);

impl SlotCpbs {
	bit_accessors! {
		attention_button: 0 { get; }
		power_controller: 1 { get; }
		mrl_sensor: 2 { get; }
		attention_indicator: 3 { get; }
		power_indicator: 4 { get; }
		hot_plug_surprise: 5 { get; }
		hot_plug: 6 { get; }
		electromechanical_interlock: 0x11 { get; }
		no_command_completed_support: 0x12 { get; }
		physical_slot_num: u16, 0x13..0x20 { get; }
	}

	/// Slot power limit in milliwatts.
	pub fn slot_power_limit(self) -> u32 {
		let bits = u32::from_le(self.0);
		decode_power_limit((bits >> 7) as u8, (bits >> 0x0F) as u8)
	}
}

unsafe impl ReprPrimitive for SlotCpbs {
	type Repr = u32;
}

/// Slot control value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct SlotControl(u16);

impl SlotControl {
	bit_accessors! {
		attention_button_pressed_reporting: 0 { get; set with_attention_button_pressed_reporting; }
		power_fault_detected_reporting: 1 { get; set with_power_fault_detect_reporting; }
		mrl_sensor_changed_reporting: 2 { get; set with_mrl_sensor_changed_reporting; }
		presence_detect_changed_reporting: 3 { get; set with_presence_detect_changed_reporting; }
		command_completed_interrupt: 4 { get; set with_command_completed_interrupt; }
		hot_plug_interrupt: 5 { get; set with_hot_plug_interrupt; }
		attention_indicator: Indicator, 6..8 {
			get => |val| Indicator::try_from(val as u8).expect("reserved value");
			set with_attention_indicator;
		}
		power_indicator: Indicator, 8..0x0A {
			get => |val| Indicator::try_from(val as u8).expect("reserved value");
			set with_power_indicator;
		}
		power_disabled: 0x0A { get; set disable_power; }
		dll_state_changed_reporting: 0x0C { get; set with_dll_state_changed_reporting; }
		auto_slot_power_limit_disabled: 0x0D { get; set disable_auto_slot_power_limit; }
		inband_pb_disabled: 0x0E { get; set disable_inband_pb; }
	}

	pub fn toggle_electromechanical_interlock(self) -> Self {
		Self(self.0 | 0x0F00_u16.to_le())
	}
}

unsafe impl ReprPrimitive for SlotControl {
	type Repr = u16;
}

/// Value of [`SlotControl::attention_indicator`] and
/// [`SlotControl::power_indicator`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum Indicator {
	On = 1,
	Blink,
	Off,
}

/// Slot status value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct SlotStatus(u16);

impl SlotStatus {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		attention_button_pressed: 0 { get; set1 clear_attention_button_pressed; }
		power_fault_detected: 1 { get; set1 clear_power_fault_detected; }
		mrl_sensor_changed: 2 { get; set1 clear_mrl_sensor_changed; }
		presence_detect_changed: 3 { get; set1 clear_presence_detect_changed; }
		command_completed: 4 { get; set1 clear_command_completed; }
		mrl_open: 5 { get; }
		adapter_present: 6 { get; }
		electromechanical_interlock_engaged: 7 { get; }
		dll_state_changed: 8 { get; set1 clear_dll_state_changed; }
	}
}

unsafe impl ReprPrimitive for SlotStatus {
	type Repr = u16;
}

impl BitAnd for SlotStatus {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Root control value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct RootControl(u16);

impl RootControl {
	bit_accessors! {
		sys_error_on_correctable_error: 0 { get; set with_sys_error_on_correctable_error; }
		sys_error_on_nonfatal_error: 1 { get; set with_sys_error_on_nonfatal_error; }
		sys_error_on_fatal_error: 2 { get; set with_sys_error_on_fatal_error; }
		pme_interrupt: 3 { get; set with_pme_interrupt; }
		crs_sw_visible: 4 { get; set with_crs_sw_visible; }
	}
}

unsafe impl ReprPrimitive for RootControl {
	type Repr = u16;
}

/// Root capabilities value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct RootCpbs(u16);

impl RootCpbs {
	bit_accessors! {
		crs_sw_visibility: 0 { get; }
	}
}

unsafe impl ReprPrimitive for RootCpbs {
	type Repr = u16;
}

/// Root status value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct RootStatus(u32);

impl RootStatus {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		pme_requester_id: u16, 0..0x10 { get; }
		pme: 0x10 { get; set1 clear_pme; }
		pme_pending: 0x11 { get; }
	}
}

unsafe impl ReprPrimitive for RootStatus {
	type Repr = u32;
}

impl BitAnd for RootStatus {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Device capabilities 2 value of a
/// [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct DeviceCpbs2(u32);

impl DeviceCpbs2 {
	bit_accessors! {
		completion_timeout_ranges: CompletionTimeoutRanges, 0..4 {
			get => |val| {
				assert!(matches!(val & 0x0E, 0 | 2 | 6 | 0x0E), "reserved value");
				CompletionTimeoutRanges::from_bits_retain(val as u8)
			};
		}
		completion_timeout_disabling: 4 { get; }
		ari_forwarding: 5 { get; }
		atomic_op_routing: 6 { get; }
		atomic_op_32bit_completer: 7 { get; }
		atomic_op_64bit_completer: 8 { get; }
		cas_128bit_completer: 9 { get; }
		no_relaxed_enabled_pr_pr_passing: 0x0A { get; }
		latency_tolerance_reporting: 0x0B { get; }
		tlp_processing_hints_completer: TlpProcessingHintsCompleterSupport, 0x0C..0x0E {
			get => |val| TlpProcessingHintsCompleterSupport::try_from(val as u8).expect("reserved value");
		}
		ln_sys_cache_line_size: LnSysCacheLineSize, 0x0E..0x10 {
			get => |val| LnSysCacheLineSize::try_from(val as u8).expect("reserved value");
		}
		tag_10bit_completer: 0x10 { get; }
		tag_10bit_requester: 0x11 { get; }
		obff_message_signaling: 0x12 { get; }
		obff_wake_signaling: 0x13 { get; }
		extended_fmt_field: 0x14 { get; }
		end_end_tlp_prefix: 0x15 { get; }
		max_end_end_tlp_prefixes: u8, 0x16..0x18 {
			get => |val| (u8::wrapping_sub(val as u8, 1) & 3) + 1;
		}
		emergency_power_reduction_trigger: EmergencyPowerReductionTrigger, 0x18..0x1A {
			get => |val| EmergencyPowerReductionTrigger::try_from(val as u8).expect("reserved value");
		}
		emergency_power_reduction_init_required: 0x1A { get; }
		func_readiness: 0x1F { get; }
	}
}

unsafe impl ReprPrimitive for DeviceCpbs2 {
	type Repr = u32;
}

bitflags! {
	/// Value of [`DeviceCpbs2::completion_timeout_ranges`].
	#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
	pub struct CompletionTimeoutRanges: u8 {
		const A = 1;
		const B = 2;
		const C = 4;
		const D = 8;
	}
}

/// Value of [`DeviceCpbs2::tlp_processing_hints_completer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum TlpProcessingHintsCompleterSupport {
	None,
	TlpProcessingHintsOnly,
	Both = 3,
}

/// Value of [`DeviceCpbs2::ln_sys_cache_line_size`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum LnSysCacheLineSize {
	None,
	S64,
	S128,
}

/// Value of [`DeviceCpbs2::emergency_power_reduction_trigger`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum EmergencyPowerReductionTrigger {
	None,
	DeviceSpecific,
	FormFactorSpecOrDeviceSpecific,
}

/// Device control 2 value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct DeviceControl2(u16);

impl DeviceControl2 {
	bit_accessors! {
		completion_timeout_range: CompletionTimeoutRange, 0..4 {
			get => |val| CompletionTimeoutRange::try_from(val as u8).expect("reserved value");
			set with_completion_timeout_range;
		}
		completion_timeout_disabled: 4 { get; set disable_completion_timeout; }
		forward_ari: 5 { get; set with_forward_ari; }
		atomic_op_requester: 6 { get; set with_atomic_op_requester; }
		atomic_op_block_egress: 7 { get; set with_atomic_op_block_egress; }
		ido_requests: 8 { get; set with_ido_requests; }
		ido_completion: 9 { get; set with_ido_completion; }
		latency_tolerance_reporting: 0x0A { get; set with_latency_tolerance_reporting; }
		emergency_power_reduction: 0x0B { get; set with_emergency_power_reduction; }
		tag_10bit_requester: 0x0C { get; set with_tag_10bit_requester; }
		obff_signaling: ObffSignaling, 0x0D..0x0F {
			get => |val| unsafe { core::mem::transmute(val as u8) };
			set with_obff_signaling;
		}
		block_end_end_tlp_prefixes: 0x0F { get; set with_block_end_end_tlp_prefixes; }
	}
}

unsafe impl ReprPrimitive for DeviceControl2 {
	type Repr = u16;
}

/// Value of [`DeviceControl2::completion_timeout_range`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum CompletionTimeoutRange {
	#[default]
	Default,
	A50To100Micros,
	A1To10Millis,
	B16To55Millis = 5,
	B65To210Millis,
	C260To900Millis = 9,
	C1To3_5Secs,
	D4To13Secs = 0x0D,
	D17To64Secs,
}

/// Value of [`DeviceControl2::obff_signaling`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ObffSignaling {
	#[default]
	None,
	MessageA,
	MessageB,
	Wake,
}

/// Link capabilities 2 value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct LinkCpbs2(u32);

impl LinkCpbs2 {
	bit_accessors! {
		link_2_5gt_s: 1 { get; }
		link_5gt_s: 2 { get; }
		link_8gt_s: 3 { get; }
		link_16gt_s: 4 { get; }
		link_32gt_s: 5 { get; }
		crosslink: 8 { get; }
		lower_skp_os_generation_2_5gt_s: 9 { get; }
		lower_skp_os_generation_5gt_s: 0x0A { get; }
		lower_skp_os_generation_8gt_s: 0x0B { get; }
		lower_skp_os_generation_16gt_s: 0x0C { get; }
		lower_skp_os_generation_32gt_s: 0x0D { get; }
		lower_skp_os_reception_2_5gt_s: 0x10 { get; }
		lower_skp_os_reception_5gt_s: 0x11 { get; }
		lower_skp_os_reception_8gt_s: 0x12 { get; }
		lower_skp_os_reception_16gt_s: 0x13 { get; }
		lower_skp_os_reception_32gt_s: 0x14 { get; }
		retimer_detection: 0x17 { get; }
		two_retimers_detection: 0x18 { get; }
		device_readiness: 0x1F { get; }
	}
}

unsafe impl ReprPrimitive for LinkCpbs2 {
	type Repr = u32;
}

/// Link control 2 value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct LinkControl2(u16);

impl LinkControl2 {
	bit_accessors! {
		target_link_speed_bit: u8, 0..4 {
			get => |val| u8::checked_sub(val as u8, 1).filter(|&v| v < 7).expect("reserved value");
			set with_target_link_speed_bit => |val| {
				assert!(val < 7, "invalid target_link_speed_bit");
				val as u16 + 1
			};
		}
		compliance_mode: 4 { get; set with_compliance_mode; }
		hw_autonomous_speed_disabled: 5 { get; set disable_hw_autonomous_speed; }
		selectable_deemphasis_3_5db: 6 { get; }
		transmit_margin: u8, 7..0x0A { get; set with_transmit_margin; }
		modified_compliance_mode: 0x0A { get; set with_modified_compliance_mode; }
		compliance_skp_ordered_sets: 0x0B { get; set with_compliance_skp_ordered_sets; }
		/// Only applies for data rates 8 GT/s and higher.
		compliance_preset: u8, 0x0C..0x10 { get; set with_compliance_preset; }
		/// Only applies for data rate 5 GT/s.
		deemphasis_3_5db: 0x0C { get; set with_deemphasis_3_5db; }
	}
}

unsafe impl ReprPrimitive for LinkControl2 {
	type Repr = u16;
}

/// Link status 2 value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct LinkStatus2(u16);

impl LinkStatus2 {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		current_deemphasis_3_5db: 0 { get; }
		equalization_8gt_s_complete: 1 { get; }
		equalization_8gt_s_phase1_success: 2 { get; }
		equalization_8gt_s_phase2_success: 3 { get; }
		equalization_8gt_s_phase3_success: 4 { get; }
		link_equalization_request_8gt_s: 5 { get; set1 clear_link_equalization_request_8gt_s; }
		retimer_detected: 6 { get; }
		two_retimers_detected: 7 { get; }
		crosslink_resolution: CrosslinkResolution, 8..0x0A {
			get => |val| unsafe { core::mem::transmute(val as u8) };
		}
		downstream_component: DownstreamComponentPresence, 0x0C..0x0F {
			get => |val| DownstreamComponentPresence::try_from(val as u8).expect("reserved value");
		}
		device_readiness_message_received: 0x0F { get; set1 clear_device_readiness_message_received; }
	}
}

unsafe impl ReprPrimitive for LinkStatus2 {
	type Repr = u16;
}

impl BitAnd for LinkStatus2 {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Value of [`LinkStatus2::crosslink_resolution`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum CrosslinkResolution {
	None,
	UpstreamPort,
	DownstreamPort,
	NotCompleted,
}

/// Value of [`LinkStatus2::downstream_component`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TryFromPrimitive)]
#[repr(u8)]
#[non_exhaustive]
pub enum DownstreamComponentPresence {
	LinkDownNotDetermined,
	LinkDownNotPresent,
	LinkDownPresent,
	LinkUpPresent = 4,
	LinkUpPresentAndDrsReceived,
}

impl DownstreamComponentPresence {
	pub fn link_up(self) -> bool {
		self as u8 & 0x40 != 0
	}
}

/// Slot capabilities 2 value of a [PCI Express capability structure](PcieRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct SlotCpbs2(u32);

impl SlotCpbs2 {
	bit_accessors! {
		inband_pb_disabling: 0 { get; }
	}
}

unsafe impl ReprPrimitive for SlotCpbs2 {
	type Repr = u32;
}

fn decode_power_limit(mantissa: u8, scale_discr: u8) -> u32 {
	let scale = match scale_discr & 3 {
		0 => match mantissa {
			..=0xEF => 1000,
			0xF0 => return 250_000,
			0xF1 => return 275_000,
			0xF2 => return 300_000,
			_ => panic!("reserved value"),
		},
		1 => 100,
		2 => 10,
		3 => 1,
		_ => unreachable!(),
	};
	mantissa as u32 * scale
}
