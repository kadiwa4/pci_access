//! PCI configuration space.

pub mod cpb;

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
	mem::replace,
	ops::BitAnd,
};

use crate::{struct_offsets, Ptr, PtrExt, ReprPrimitive};
use cpb::CpbIter;

macro_rules! accessors {
	{
		use $strct:ident;
		$($(#[$attr:meta])* $name:ident: $ty:ty { get $(=> $map_get:expr)?; $(set $set_name:ident $(=> $map_set:expr)?;)? })+
	} => {
		$(accessors!(@single $(#[$attr])* $strct::$name: $ty, { get $(=> $map_get)?; $(set $set_name $(=> $map_set)?;)? });)+
	};
	(@single $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, { get $(=> $map_get:expr)?; $(set $set_name:ident $(=> $map_set:expr)?;)? }) => {
		accessors!(@get $(#[$attr])* $strct::$name: $ty, $($map_get)?);
		accessors!(@set $(#[$attr])* $strct::$name: $ty, $($set_name, $($map_set)?)?);
	};
	(@get $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(&self) -> $ty {
			unsafe { core::mem::transmute(<<$ty as ReprPrimitive>::Repr as crate::Primitive>::read_from(self.0.offset($strct::$name))) }
		}
	};
	(@get $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(&self) -> $ty {
			$map_get(unsafe { core::mem::transmute(<<$ty as ReprPrimitive>::Repr as crate::Primitive>::read_from(self.0.offset($strct::$name))) })
		}
	};
	(@set $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty,) => {};
	(@set $(#[$attr:meta])* $strct:ident::$name:ident: $ty:ty, $set_name:ident, $($map_set:expr)?) => {
		$(#[$attr])*
		#[inline]
		pub fn $set_name(&self, val: $ty) {
			$(let val = $map_set(val);)?
			unsafe {
				crate::Primitive::write_to(core::mem::transmute::<$ty, <$ty as ReprPrimitive>::Repr>(val), self.0.offset($strct::$name));
			}
		}
	};
}

macro_rules! bit_accessors {
	($($(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal $($mask:ident)?)? { get $(=> $map_get:expr)?; $($set_kw:ident $set_name:ident $(=> $map_set:expr)?;)? })+) => {
		$(bit_accessors!(@single $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)? { get $(=> $map_get)?; $($set_kw $set_name $(=> $map_set)?;)? });)+
	};
	(@single $(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal $($mask:ident)?)? { get $(=> $map_get:expr)?; $($set_kw:ident $set_name:ident $(=> $map_set:expr)?;)? }) => {
		bit_accessors!(@get $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)?, $($map_get)?);
		bit_accessors!(@set $(#[$attr])* $name: $($ty,)? $start $(..$end $($mask)?)?, $($set_kw $set_name, $($map_set)?)?);
	};
	(@get $(#[$attr:meta])* $name:ident: $pos:literal,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> bool {
			<Self as ReprPrimitive>::Repr::from_le(self.0) & (1 << $pos) != 0
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			crate::BitManip::bit_range(<Self as ReprPrimitive>::Repr::from_le(self.0), $start..$end) as _
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			$map_get(crate::BitManip::bit_range(<Self as ReprPrimitive>::Repr::from_le(self.0), $start..$end))
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			(<Self as ReprPrimitive>::Repr::from_le(self.0) & mask) as _
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal)?,) => {};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: bool) -> Self {
			Self(
				(self.0 & !((1 as <Self as ReprPrimitive>::Repr) << $pos).to_le())
					| ((val as <Self as ReprPrimitive>::Repr) << $pos).to_le()
			)
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			debug_assert!((val as u128) < (1_u128 << ($end - $start)), "invalid {}", stringify!($name));
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ((val as <Self as ReprPrimitive>::Repr) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ($map_get(val) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as ReprPrimitive>::Repr = crate::BitManip::new_bit_mask($start..$end);
			debug_assert_eq!(val & mask, val, "invalid {}", stringify!($name));
			Self((self.0 & !mask.to_le()) | (val & mask).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set1 $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self) -> Self {
			Self(self.0 | ((1 as <Self as ReprPrimitive>::Repr) << $pos).to_le())
		}
	};
}

pub(crate) use {accessors, bit_accessors};

struct_offsets! {
	struct Header {
		vendor_id: u16,
		device_id: u16,
		command: Command,
		status: Status,
		class_code: ClassCode,
		cache_line_size: u8,
		latency_timer: u8,
		header_type: HeaderType,
		builtin_self_test: BuiltinSelfTest,
		_rest: [u8; 0xF0],
	}
}

/// Reference to a PCI configuration space.
#[derive(Clone, Copy)]
pub struct HeaderRef<P: Ptr>(P);

impl<P: Ptr> HeaderRef<P> {
	pub unsafe fn new(ptr: P) -> Self {
		Self(ptr)
	}

	accessors! {
		use Header;
		vendor_id: u16 { get => u16::from_le; }
		device_id: u16 { get => u16::from_le; }
		command: Command { get; set set_command; }
		status: Status { get; set set_status; }
		class_code: ClassCode { get; }
		cache_line_size: u8 { get; set set_cache_line_size; }
		latency_timer: u8 { get; set set_latency_timer; }
		header_type: HeaderType { get; }
		builtin_self_test: BuiltinSelfTest { get; set set_builtin_self_test; }
	}

	#[inline]
	pub fn specific(&self) -> SpecificHeaderRef<P> {
		match self.header_type().get() {
			0 => SpecificHeaderRef::Type0(T0HeaderRef(self.0.clone())),
			1 => SpecificHeaderRef::Type1(T1HeaderRef(self.0.clone())),
			_ => panic!("reserved value"),
		}
	}
}

impl<P: Ptr> Debug for HeaderRef<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("HeaderRef")
			.field("vendor_id", &self.vendor_id())
			.field("device_id", &self.device_id())
			.field("command", &self.command())
			.field("status", &self.status())
			.field("class_code", &self.class_code())
			.field("cache_line_size", &self.cache_line_size())
			.field("latency_timer", &self.latency_timer())
			.field("specific", &self.specific())
			.field("multi_func", &self.header_type().multi_func())
			.field("builtin_self_test", &self.builtin_self_test())
			.finish()
	}
}

/// Command value of a PCI configuration space.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Command(u16);

impl Command {
	bit_accessors! {
		io_space_enabled: 0 { get; set enable_io_space; }
		mem_space_enabled: 1 { get; set enable_mem_space; }
		bus_master_enabled: 2 { get; set enable_bus_master; }
		special_cycle: 3 { get; }
		mem_write_and_invalidate: 4 { get; }
		vga_palette_snoop: 5 { get; }
		parity_error_response: 6 { get; set with_parity_error_response; }
		idsel_stepping: 7 { get; }
		serr_enabled: 8 { get; set enable_serr; }
		fast_back_to_back_transactions: 9 { get; }
		interrupt_disabled: 0x0A { get; set disable_interrupt; }
	}
}

unsafe impl ReprPrimitive for Command {
	type Repr = u16;
}

/// Status value of a PCI configuration space.
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct Status(u16);

impl Status {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		immediate_readiness: 0 { get; }
		interrupt_pending: 3 { get; }
		pcie_cpb: 4 { get; }
		frequency_66mhz_support: 5 { get; }
		fast_back_to_back_transactions: 7 { get; }
		master_data_parity_error: 8 { get; set1 clear_master_data_parity_error; }
		devsel_timing: u8, 9..0x0B { get; }
		signaled_target_abort: 0x0B { get; set1 clear_signaled_target_abort; }
		received_target_abort: 0x0C { get; set1 clear_received_target_abort; }
		received_master_abort: 0x0D { get; set1 clear_received_master_abort; }
		signaled_system_error: 0x0E { get; set1 clear_signaled_system_error; }
		detected_parity_error: 0x0F { get; set1 clear_detected_parity_error; }
	}
}

unsafe impl ReprPrimitive for Status {
	type Repr = u16;
}

impl BitAnd for Status {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Class code value of a PCI configuration space.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct ClassCode {
	pub revision_id: u8,
	pub programming_interface: u8,
	pub sub_class: u8,
	pub base_class: u8,
}

unsafe impl ReprPrimitive for ClassCode {
	type Repr = u32;
}

/// Header type value of a PCI configuration space.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct HeaderType(u8);

impl HeaderType {
	pub const INVALID: Self = Self(u8::MAX);

	bit_accessors! {
		get: u8, 0..7 { get; }
		multi_func: 7 { get; }
	}
}

unsafe impl ReprPrimitive for HeaderType {
	type Repr = u8;
}

/// Built-in self test value of a PCI configuration space.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BuiltinSelfTest(u8);

impl BuiltinSelfTest {
	bit_accessors! {
		completion_code: u8, 0..4 { get; }
		start: 6 { get; set with_start; }
		support: 7 { get; }
	}
}

unsafe impl ReprPrimitive for BuiltinSelfTest {
	type Repr = u8;
}

/// Value of [`ExpansionRom::validation_status`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ExpansionRomValidationStatus {
	NotSupported,
	InProgress,
	PassValidNotTrustTested,
	PassValidTrusted,
	FailInvalid,
	FailValidNotTrusted,
	PassValidNotTrustTestedWithWarning,
	PassValidTrustedWithWarning,
}

/// Reference to a PCI configuration space with a specific header type.
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[non_exhaustive]
pub enum SpecificHeaderRef<P: Ptr> {
	Type0(T0HeaderRef<P>),
	Type1(T1HeaderRef<P>),
}

impl<P: Ptr> SpecificHeaderRef<P> {
	pub fn header_type(&self) -> u8 {
		unsafe { *(&self as *const _ as *const u8) }
	}
}

struct_offsets! {
	struct T0Header {
		_common0: [u8; 0x10],
		base_addrs: [u32; 6],
		cardbus_cis_ptr: u32,
		subsys_vendor_id: u16,
		subsys_id: u16,
		expansion_rom: ExpansionRom,
		cpbs_ptr: u8,
		_reserved: [u8; 7],
		interrupt_line: u8,
		interrupt_pin: u8,
		min_gnt: u8,
		max_lat: u8,
	}
}

/// Reference to a PCI configuration space with type 0 header.
#[derive(Clone, Copy)]
pub struct T0HeaderRef<P: Ptr>(P);

impl<P: Ptr> T0HeaderRef<P> {
	pub fn common(&self) -> HeaderRef<P> {
		HeaderRef(self.0.clone())
	}

	accessors! {
		use T0Header;
		cardbus_cis_ptr: u32 { get => u32::from_le; }
		subsys_vendor_id: u16 { get => u16::from_le; }
		subsys_id: u16 { get => u16::from_le; }
		expansion_rom: ExpansionRom { get; set set_expansion_rom; }
		interrupt_line: u8 { get; set set_interrupt_line; }
		interrupt_pin: u8 { get; }
		min_gnt: u8 { get; }
		max_lat: u8 { get; }
	}

	/// Mutably iterates over base address registers.
	///
	/// Do not call this while another `BarIter` or [`Bar`] still exists.
	pub fn bars(&self) -> BarIter<P> {
		unsafe { BarIter::new(self.0.offset(T0Header::base_addrs), 6) }
	}

	pub fn probe_expansion_rom_size(&self) -> u32 {
		self.set_expansion_rom(self.expansion_rom().with_base_addr(0xFFFF_F800));
		self.expansion_rom().base_addr().wrapping_neg()
	}

	pub fn cpbs(&self) -> CpbIter<P> {
		let offset = unsafe { self.0.offset(T0Header::cpbs_ptr).read8() };
		CpbIter::new(self.common(), offset)
	}
}

impl<P: Ptr> Debug for T0HeaderRef<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("T0HeaderRef")
			.field("bars", &self.bars())
			.field("cardbus_cis_ptr", &self.cardbus_cis_ptr())
			.field("subsys_vendor_id", &self.subsys_vendor_id())
			.field("subsys_id", &self.subsys_id())
			.field("expansion_rom", &self.expansion_rom())
			.field("cpbs", &self.cpbs())
			.field("interrupt_line", &self.interrupt_line())
			.field("interrupt_pin", &self.interrupt_pin())
			.field("min_gnt", &self.min_gnt())
			.field("max_lat", &self.max_lat())
			.finish_non_exhaustive()
	}
}

struct_offsets! {
	struct T1Header {
		_common0: [u8; 0x10],
		base_addrs: [u32; 2],
		primary_bus_num: u8,
		secondary_bus_num: u8,
		subordinate_bus_num: u8,
		secondary_latency_timer: u8,
		io_base_lo: u8,
		io_limit_lo: u8,
		secondary_status: SecondaryStatus,
		mem_base: u16,
		mem_limit: u16,
		prefetchable_mem_base_lo: u16,
		prefetchable_mem_limit_lo: u16,
		prefetchable_mem_base_hi: u32,
		prefetchable_mem_limit_hi: u32,
		io_base_hi: u16,
		io_limit_hi: u16,
		cpbs_ptr: u8,
		_reserved: [u8; 3],
		expansion_rom: ExpansionRom,
		interrupt_line: u8,
		interrupt_pin: u8,
		bridge_control: BridgeControl,
	}
}

/// Reference to a PCI configuration space with type 1 header.
#[derive(Clone, Copy)]
pub struct T1HeaderRef<P: Ptr>(P);

impl<P: Ptr> T1HeaderRef<P> {
	pub fn common(&self) -> HeaderRef<P> {
		HeaderRef(self.0.clone())
	}

	accessors! {
		use T1Header;
		primary_bus_num: u8 { get; set set_primary_bus_num; }
		secondary_bus_num: u8 { get; set set_secondary_bus_num; }
		subordinate_bus_num: u8 { get; set set_subordinate_bus_num; }
		secondary_latency_timer: u8 { get; }
		io_base_lo: u8 { get; set set_io_base_lo; }
		io_limit_lo: u8 { get; set set_io_limit_lo; }
		secondary_status: SecondaryStatus { get; set set_secondary_status; }
		prefetchable_mem_base_lo: u16 { get => u16::from_le; set set_prefetchable_mem_base_lo => u16::to_le; }
		prefetchable_mem_limit_lo: u16 { get => u16::from_le; set set_prefetchable_mem_limit_lo => u16::to_le; }
		prefetchable_mem_base_hi: u32 { get => u32::from_le; set set_prefetchable_mem_base_hi => u32::to_le; }
		prefetchable_mem_limit_hi: u32 { get => u32::from_le; set set_prefetchable_mem_limit_hi => u32::to_le; }
		io_base_hi: u16 { get => u16::from_le; set set_io_base_hi => u16::to_le; }
		io_limit_hi: u16 { get => u16::from_le; set set_io_limit_hi => u16::to_le; }
		expansion_rom: ExpansionRom { get; set set_expansion_rom; }
		interrupt_line: u8 { get; set set_interrupt_line; }
		interrupt_pin: u8 { get; }
		bridge_control: BridgeControl { get; }
	}

	/// Mutably iterates over base address registers.
	///
	/// Do not call this while another `BarIter` or [`Bar`] still exists.
	pub fn bars(&self) -> BarIter<P> {
		unsafe { BarIter::new(self.0.offset(T1Header::base_addrs), 2) }
	}

	pub fn mem_base(&self) -> u32 {
		(unsafe { self.0.offset(T1Header::mem_base).read16_le() } as u32 & 0xFFF0) << 0x10
	}

	pub fn set_mem_base(&self, val: u32) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid memory base");
		unsafe {
			self.0
				.offset(T1Header::mem_base)
				.write16_le((val >> 0x10) as u16);
		}
	}

	/// The actual limit is `0x10_0000` higher than this.
	pub fn mem_limit(&self) -> u32 {
		(unsafe { self.0.offset(T1Header::mem_limit).read16_le() } as u32 & 0xFFF0) << 0x10
	}

	/// The input should be the actual limit minus `0x10_0000`.
	pub fn set_mem_limit(&self, val: u32) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid memory limit");
		unsafe {
			self.0
				.offset(T1Header::mem_limit)
				.write16_le((val >> 0x10) as u16);
		}
	}

	/// Iterates over PCI capabilities.
	pub fn cpbs(&self) -> CpbIter<P> {
		let offset = unsafe { self.0.offset(T1Header::cpbs_ptr).read8() };
		CpbIter::new(self.common(), offset)
	}

	pub fn probe_expansion_rom_size(&self) -> u32 {
		self.set_expansion_rom(self.expansion_rom().with_base_addr(0xFFFF_F800));
		self.expansion_rom().base_addr().wrapping_neg()
	}
}

impl<P: Ptr> Debug for T1HeaderRef<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("T1HeaderRef")
			.field("bars", &self.bars())
			.field("primary_bus_num", &self.primary_bus_num())
			.field("secondary_bus_num", &self.secondary_bus_num())
			.field("subordinate_bus_num", &self.subordinate_bus_num())
			.field("secondary_latency_timer", &self.secondary_latency_timer())
			.field("io_base_lo", &self.io_base_lo())
			.field("io_limit_lo", &self.io_limit_lo())
			.field("secondary_status", &self.secondary_status())
			.field("mem_base", &self.mem_base())
			.field("mem_limit", &self.mem_limit())
			.field("prefetchable_mem_base_lo", &self.prefetchable_mem_base_lo())
			.field(
				"prefetchable_mem_limit_lo",
				&self.prefetchable_mem_limit_lo(),
			)
			.field("prefetchable_mem_base_hi", &self.prefetchable_mem_base_hi())
			.field(
				"prefetchable_mem_limit_hi",
				&self.prefetchable_mem_limit_hi(),
			)
			.field("io_base_hi", &self.io_base_hi())
			.field("io_limit_hi", &self.io_limit_hi())
			.field("cpbs", &self.cpbs())
			.field("expansion_rom", &self.expansion_rom())
			.field("interrupt_line", &self.interrupt_line())
			.field("interrupt_pin", &self.interrupt_pin())
			.field("bridge_control", &self.bridge_control())
			.finish_non_exhaustive()
	}
}

/// Secondary status value of a PCI configuration space with
/// [type 1 header](T1HeaderRef).
#[derive(Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct SecondaryStatus(u16);

impl SecondaryStatus {
	pub const DEFAULT: Self = Self(0);

	bit_accessors! {
		frequency_66mhz_support: 5 { get; }
		fast_back_to_back_transactions: 7 { get; }
		master_data_parity_error: 8 { get; set1 clear_master_data_parity_error; }
		devsel_timing: u8, 9..0x0B { get; }
		signaled_target_abort: 0x0B { get; set1 clear_signaled_target_abort; }
		received_target_abort: 0x0C { get; set1 clear_received_target_abort; }
		received_master_abort: 0x0D { get; set1 clear_received_master_abort; }
		received_system_error: 0x0E { get; set1 clear_received_system_error; }
		detected_parity_error: 0x0F { get; set1 clear_detected_parity_error; }
	}
}

unsafe impl ReprPrimitive for SecondaryStatus {
	type Repr = u16;
}

impl BitAnd for SecondaryStatus {
	type Output = Self;

	fn bitand(self, rhs: Self) -> Self::Output {
		Self(self.0 & rhs.0)
	}
}

/// Bridge control value of a PCI configuration space with
/// [type 1 header](T1HeaderRef).
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct BridgeControl(u16);

impl BridgeControl {
	bit_accessors! {
		parity_error_response_enabled: 0 { get; set enable_parity_error_response; }
		serr_enabled: 1 { get; set enable_serr; }
		isa_enabled: 2 { get; set enable_isa; }
		vga_enabled: 3 { get; set enable_vga; }
		vga_16bit_decode: 4 { get; set with_vga_16bit_decode; }
		master_abort_mode: 5 { get; }
		secondary_bus_reset: 6 { get; set with_secondary_bus_reset; }
		fast_back_to_back_transactions_enabled: 7 { get; }
		primary_discard_timer: 8 { get; }
		secondary_discard_timer: 9 { get; }
		discard_timer_status: 0x0A { get; }
		discard_timer_serr_enabled: 0x0B { get; }
	}
}

unsafe impl ReprPrimitive for BridgeControl {
	type Repr = u16;
}

/// Mutably iterates over base address registers.
#[derive(Clone)]
pub struct BarIter<P: Ptr> {
	start: P,
	end: P,
}

impl<P: Ptr> BarIter<P> {
	/// # Safety
	/// The input has to point to a valid array.
	unsafe fn new(ptr: P, len: i32) -> Self {
		Self {
			end: ptr.offset(len << 2),
			start: ptr,
		}
	}
}

impl<P: Ptr> Iterator for BarIter<P> {
	type Item = Bar<P>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.start == self.end {
			return None;
		}
		let next_ptr = unsafe { self.start.offset(4) };
		let ptr = replace(&mut self.start, next_ptr);
		let lo_le = unsafe { ptr.read32() };
		let lo = u32::from_le(lo_le);
		if lo & 1 != 0 {
			return Some(Bar::IoSpace(IoBarRef(ptr), lo));
		}
		let val = match lo & 6 {
			0 => Bar::MemSpace32(Mem32BarRef(ptr), Mem32BaseAddr(lo_le)),
			4 => {
				assert_ne!(self.start, self.end, "invalid 64-bit BAR");
				let hi = unsafe { self.start.read32() };
				self.start = unsafe { ptr.offset(4) };
				Bar::MemSpace64(Mem64BarRef(ptr), Mem64BaseAddr::new(lo_le, hi))
			}
			_ => panic!("reserved value"),
		};
		Some(val)
	}
}

impl<P: Ptr> FusedIterator for BarIter<P> {}

impl<P: Ptr> Debug for BarIter<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_list().entries(self.clone()).finish()
	}
}

/// Base address register.
#[non_exhaustive]
#[derive(Clone, Copy, Debug)]
pub enum Bar<P: Ptr> {
	MemSpace32(Mem32BarRef<P>, Mem32BaseAddr),
	MemSpace64(Mem64BarRef<P>, Mem64BaseAddr),
	IoSpace(IoBarRef<P>, u32),
}

/// Reference to base address register containing a 32-bit memory address.
#[derive(Clone, Copy, Debug)]
pub struct Mem32BarRef<P: Ptr>(P);

impl<P: Ptr> Mem32BarRef<P> {
	pub fn read(&self) -> Mem32BaseAddr {
		unsafe { Mem32BaseAddr(self.0.read32()) }
	}

	pub fn write(&self, val: Mem32BaseAddr) {
		unsafe {
			self.0.write32(val.0);
		}
	}

	pub fn probe_size(&self) -> u32 {
		self.write(self.read().with_addr(0xFFFF_FFF0));
		self.read().addr().wrapping_neg()
	}
}

/// Value of a base address register containing a 32-bit memory address.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Mem32BaseAddr(u32);

impl Mem32BaseAddr {
	bit_accessors! {
		prefetchable: 3 { get; }
		addr: u32, 4..0x20 mask { get; set with_addr; }
	}
}

unsafe impl ReprPrimitive for Mem32BaseAddr {
	type Repr = u32;
}

/// Reference to base address register containing a 64-bit memory address.
#[derive(Clone, Copy, Debug)]
pub struct Mem64BarRef<P: Ptr>(P);

impl<P: Ptr> Mem64BarRef<P> {
	#[inline]
	pub fn read(&self) -> Mem64BaseAddr {
		unsafe { Mem64BaseAddr::new(self.0.read32(), self.0.offset(4).read32()) }
	}

	#[inline]
	pub fn write(&self, val: Mem64BaseAddr) {
		let [a, b, c, d, e, f, g, h] = val.0.to_ne_bytes();
		unsafe {
			self.0.write32(u32::from_ne_bytes([a, b, c, d]));
			self.0.offset(4).write32(u32::from_ne_bytes([e, f, g, h]));
		}
	}

	pub fn probe_size(&self) -> u64 {
		self.write(self.read().with_addr(0xFFFF_FFFF_FFFF_FFF0));
		self.read().addr().wrapping_neg()
	}
}

/// Value of a base address register containing a 64-bit memory address.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Mem64BaseAddr(u64);

impl Mem64BaseAddr {
	#[inline]
	fn new(lo: u32, hi: u32) -> Self {
		let [a, b, c, d] = lo.to_ne_bytes();
		let [e, f, g, h] = hi.to_ne_bytes();
		Self(u64::from_ne_bytes([a, b, c, d, e, f, g, h]))
	}

	bit_accessors! {
		prefetchable: 3 { get; }
		addr: u64, 4..0x40 mask { get; set with_addr; }
	}
}

unsafe impl ReprPrimitive for Mem64BaseAddr {
	type Repr = u64;
}

/// Reference to a base address register containing a 32-bit I/O address.
#[derive(Clone, Copy, Debug)]
pub struct IoBarRef<P: Ptr>(P);

impl<P: Ptr> IoBarRef<P> {
	#[inline]
	pub fn read(&self) -> u32 {
		unsafe { self.0.read32_le() & 0xFFFF_FFFC }
	}

	#[inline]
	pub fn write(&self, val: u32) {
		debug_assert_eq!(val % 4, 0, "invalid addr");
		unsafe {
			self.0.write32_le((val & 0xFFFF_FFFC) | 1);
		}
	}

	#[inline]
	pub fn probe_size(&self) -> u32 {
		self.write(0xFFFF_FFFC_u32);
		self.read().wrapping_neg()
	}
}

/// Expansion ROM value of a PCI configuration space.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct ExpansionRom(u32);

impl ExpansionRom {
	bit_accessors! {
		enabled: 0 { get; set enable; }
		validation_status: ExpansionRomValidationStatus, 1..4 {
			get => |val| unsafe { core::mem::transmute(val as u8) };
		}
		validation_details: u8, 4..8 { get; }
		base_addr: u32, 0x0B..0x20 mask { get; set with_base_addr; }
	}
}

unsafe impl ReprPrimitive for ExpansionRom {
	type Repr = u32;
}
