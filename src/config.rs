//! PCI configuration space.

pub mod cpb;

use core::{
	fmt::{self, Debug, Formatter},
	iter::FusedIterator,
	ops::BitAnd,
	ptr::NonNull,
};

use crate::{cast, map, VolatilePtr};
use cpb::CpbIter;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncPos(u16);

impl FuncPos {
	pub const fn new(func: u8, device: u8, bus: u8) -> Self {
		Self((func & 7) as u16 | ((device as u16 & 0x1F) << 3) | ((bus as u16) << 8))
	}

	pub const fn func(self) -> u8 {
		self.0 as u8 & 7
	}

	pub const fn device(self) -> u8 {
		(self.0 >> 3) as u8 & 0x1F
	}

	pub const fn bus(self) -> u8 {
		(self.0 >> 8) as u8
	}

	pub const fn from_ecam_offset(val: isize) -> Self {
		Self((val >> 0x0C) as u16)
	}

	pub const fn to_ecam_offset(self) -> isize {
		(self.0 as isize) << 0x0C
	}

	pub const fn from_cam_offset(val: i32) -> Self {
		Self((val >> 8) as u16)
	}

	pub const fn to_cam_offset(self) -> i32 {
		(self.0 as i32) << 8
	}
}

macro_rules! accessors {
	($($(#[$attr:meta])* $name:ident: $ty:ty { get $(=> $map_get:expr)?; $(set $set_name:ident;)? })+) => {
		$(accessors!(@single $(#[$attr])* $name: $ty { get $(=> $map_get)?; $(set $set_name;)? });)+
	};
	(@single $(#[$attr:meta])* $name:ident: $ty:ty { get $(=> $map_get:expr)?; $(set $set_name:ident;)? }) => {
		accessors!(@get $(#[$attr])* $name: $ty, $($map_get)?);
		accessors!(@set $(#[$attr])* $name: $ty, $($set_name)?);
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			crate::map!(self->$name).read()
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			$map_get(crate::map!(self->$name).read())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty,) => {};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $set_name:ident) => {
		$(#[$attr])*
		#[inline]
		pub fn $set_name(self, val: $ty) {
			crate::map!(self->$name).write(val);
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
			<Self as BitField>::Inner::from_le(self.0) & (1 << $pos) != 0
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			crate::BitManip::bit_range(<Self as BitField>::Inner::from_le(self.0), $start..$end) as _
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			$map_get(crate::BitManip::bit_range(<Self as BitField>::Inner::from_le(self.0), $start..$end))
		}
	};
	(@get $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask,) => {
		$(#[$attr])*
		#[inline]
		pub fn $name(self) -> $ty {
			let mask: <Self as BitField>::Inner = crate::BitManip::new_bit_mask($start..$end);
			(<Self as BitField>::Inner::from_le(self.0) & mask) as _
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $($ty:ty,)? $start:literal $(..$end:literal)?,) => {};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: bool) -> Self {
			Self(
				(self.0 & !((1 as <Self as BitField>::Inner) << $pos).to_le())
					| ((val as <Self as BitField>::Inner) << $pos).to_le()
			)
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			debug_assert!((val as u128) < (1_u128 << ($end - $start)), "invalid {}", stringify!($name));
			let mask: <Self as BitField>::Inner = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ((val as <Self as BitField>::Inner) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal, set $set_name:ident, $map_get:expr) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as BitField>::Inner = crate::BitManip::new_bit_mask($start..$end);
			Self((self.0 & mask.to_le()) | ($map_get(val) << $start).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $ty:ty, $start:literal..$end:literal mask, set $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self, val: $ty) -> Self {
			let mask: <Self as BitField>::Inner = crate::BitManip::new_bit_mask($start..$end);
			debug_assert_eq!(val & mask, val, "invalid {}", stringify!($name));
			Self((self.0 & !mask.to_le()) | (val & mask).to_le())
		}
	};
	(@set $(#[$attr:meta])* $name:ident: $pos:literal, set1 $set_name:ident,) => {
		$(#[$attr])*
		#[inline]
		#[must_use]
		pub fn $set_name(self) -> Self {
			Self(self.0 | ((1 as <Self as BitField>::Inner) << $pos).to_le())
		}
	};
}

pub(crate) use {accessors, bit_accessors};

trait BitField {
	type Inner;
}

/// A PCI configuration space. A pointer to this is used to construct a
/// [`HeaderRef`].
///
/// Size: 256 bytes, alignment: 4 bytes
#[repr(C, align(4))]
pub struct ConfigSpace {
	vendor_id: u16,
	device_id: u16,
	command: Command,
	status: Status,
	revision_id: u8,
	class_code: ClassCode,
	cache_line_size: u8,
	latency_timer: u8,
	header_type: HeaderType,
	builtin_self_test: BuiltinSelfTest,
	_rest: [u8; 0xF0],
}

/// Reference to a PCI configuration space.
#[derive(Clone, Copy)]
pub struct HeaderRef(VolatilePtr<ConfigSpace>);

impl HeaderRef {
	/// # Safety
	/// - The input has to point to a valid PCI configuration space.
	/// - Only one thread can access the configuration space at a time.
	pub unsafe fn new(ptr: NonNull<ConfigSpace>) -> Self {
		Self(VolatilePtr::new(ptr))
	}

	/// # Safety
	/// - The input has to point to a valid PCI configuration space.
	/// - Only one thread can access the configuration space at a time.
	pub unsafe fn at_func_pos(ptr: NonNull<ConfigSpace>, pos: FuncPos) -> Self {
		let ptr = NonNull::new_unchecked(ptr.as_ptr().offset(pos.to_ecam_offset()));
		Self(VolatilePtr::new(ptr))
	}

	#[inline]
	pub fn specific(self) -> SpecificHeaderRef {
		match self.header_type().get() {
			0 => SpecificHeaderRef::Type0(T0HeaderRef(cast!(self.0))),
			1 => SpecificHeaderRef::Type1(T1HeaderRef(cast!(self.0))),
			_ => panic!("reserved value"),
		}
	}

	accessors! {
		vendor_id: u16 { get => u16::from_le; }
		device_id: u16 { get => u16::from_le; }
		command: Command { get; set set_command; }
		status: Status { get; set set_status; }
		revision_id: u8 { get; }
		class_code: ClassCode { get; }
		cache_line_size: u8 { get; set set_cache_line_size; }
		latency_timer: u8 { get; set set_latency_timer; }
		header_type: HeaderType { get; }
		builtin_self_test: BuiltinSelfTest { get; set set_builtin_self_test; }
	}
}

impl Debug for HeaderRef {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("HeaderRef")
			.field("vendor_id", &self.vendor_id())
			.field("device_id", &self.device_id())
			.field("command", &self.command())
			.field("status", &self.status())
			.field("revision_id", &self.revision_id())
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

impl BitField for Command {
	type Inner = u16;
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

impl BitField for Status {
	type Inner = u16;
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
	pub programming_interface: u8,
	pub sub_class: u8,
	pub base_class: u8,
}

/// Header type value of a PCI configuration space.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct HeaderType(u8);

impl HeaderType {
	pub const INVALID: Self = Self(u8::MAX);

	bit_accessors! {
		get: u8, 0..7 { get; }
		multi_func: 7 { get; }
	}
}

impl BitField for HeaderType {
	type Inner = u8;
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

impl BitField for BuiltinSelfTest {
	type Inner = u8;
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
pub enum SpecificHeaderRef {
	Type0(T0HeaderRef),
	Type1(T1HeaderRef),
}

impl SpecificHeaderRef {
	pub fn get_type(self) -> u8 {
		unsafe { *(&self as *const _ as *const u8) }
	}
}

#[repr(C)]
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

/// Reference to a PCI configuration space with type 0 header.
#[derive(Clone, Copy)]
pub struct T0HeaderRef(VolatilePtr<T0Header>);

impl T0HeaderRef {
	pub fn common(self) -> HeaderRef {
		HeaderRef(cast!(self.0))
	}

	accessors! {
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
	pub fn bars(self) -> BarIter {
		unsafe { BarIter::new(map!(self->base_addrs)) }
	}

	pub fn probe_expansion_rom_size(&mut self) -> u32 {
		self.set_expansion_rom(self.expansion_rom().with_base_addr(0xFFFF_F800));
		self.expansion_rom().base_addr().wrapping_neg()
	}

	pub fn cpbs(self) -> CpbIter {
		CpbIter::new(self.common(), map!(self->cpbs_ptr).read())
	}
}

impl Debug for T0HeaderRef {
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

#[repr(C)]
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

/// Reference to a PCI configuration space with type 1 header.
#[derive(Clone, Copy)]
pub struct T1HeaderRef(VolatilePtr<T1Header>);

impl T1HeaderRef {
	pub fn common(self) -> HeaderRef {
		HeaderRef(cast!(self.0))
	}

	accessors! {
		primary_bus_num: u8 { get; set set_primary_bus_num; }
		secondary_bus_num: u8 { get; set set_secondary_bus_num; }
		subordinate_bus_num: u8 { get; set set_subordinate_bus_num; }
		secondary_latency_timer: u8 { get; }
		secondary_status: SecondaryStatus { get; set set_secondary_status; }
		expansion_rom: ExpansionRom { get; set set_expansion_rom; }
		interrupt_line: u8 { get; set set_interrupt_line; }
		interrupt_pin: u8 { get; }
		bridge_control: BridgeControl { get; }
	}

	/// Mutably iterates over base address registers.
	///
	/// Do not call this while another `BarIter` or [`Bar`] still exists.
	pub fn bars(self) -> BarIter {
		unsafe { BarIter::new(map!(self->base_addrs)) }
	}

	pub fn io_base(self) -> u32 {
		let lo = map!(self->io_base_lo).read();
		let hi = u16::from_le(map!(self->io_base_hi).read());
		match lo & 0x0F {
			0 => assert_eq!(hi, 0, "inconsistent I/O base"),
			1 => (),
			_ => panic!("reserved value"),
		}

		(hi as u32) << 0x10 | (lo as u32 & 0xF0) << 8
	}

	pub fn set_io_base(self, val: u32) {
		debug_assert_eq!(val % 0x1000, 0, "invalid I/O base");
		let addressing_cpb = map!(self->io_base_lo).read() & 0x0F;
		let hi = match addressing_cpb {
			0 => {
				debug_assert!(u16::try_from(val).is_ok(), "invalid I/O base");
				0
			}
			1 => ((val >> 0x10) as u16).to_le(),
			_ => panic!("reserved value"),
		};
		map!(self->io_base_lo).write((val >> 8 & 0xF0) as u8 | addressing_cpb);
		map!(self->io_base_hi).write(hi);
	}

	/// The actual limit is `0x1000` higher than this.
	pub fn io_limit(self) -> u32 {
		let lo = map!(self->io_base_lo).read();
		let hi = u16::from_le(map!(self->io_base_hi).read());
		match lo & 0x0F {
			0 => assert_eq!(hi, 0, "inconsistent I/O limit"),
			1 => (),
			_ => panic!("reserved value"),
		}

		(hi as u32) << 0x10 | (lo as u32 & 0xF0) << 8
	}

	/// The input should be the actual limit minus `0x1000`.
	pub fn set_io_limit(self, val: u32) {
		debug_assert_eq!(val % 0x1000, 0, "invalid I/O limit");
		let addressing_cpb = map!(self->io_limit_lo).read() & 0x0F;
		let hi = match addressing_cpb {
			0 => {
				debug_assert!(u16::try_from(val).is_ok(), "invalid I/O limit");
				0
			}
			1 => ((val >> 0x10) as u16).to_le(),
			_ => panic!("reserved value"),
		};
		map!(self->io_limit_lo).write((val >> 8 & 0xF0) as u8 | addressing_cpb);
		map!(self->io_limit_hi).write(hi);
	}

	pub fn mem_base(self) -> u32 {
		(u16::from_le(map!(self->mem_base).read()) as u32 & 0xFFF0) << 0x10
	}

	pub fn set_mem_base(self, val: u32) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid memory base");
		map!(self->mem_base).write(((val >> 0x10) as u16).to_le());
	}

	/// The actual limit is `0x10_0000` higher than this.
	pub fn mem_limit(self) -> u32 {
		(u16::from_le(map!(self->mem_limit).read()) as u32 & 0xFFF0) << 0x10
	}

	/// The input should be the actual limit minus `0x10_0000`.
	pub fn set_mem_limit(self, val: u32) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid memory limit");
		map!(self->mem_limit).write(((val >> 0x10) as u16).to_le());
	}

	pub fn prefetchable_mem_base(self) -> u64 {
		let lo = u16::from_le(map!(self->prefetchable_mem_base_lo).read());
		let hi = u32::from_le(map!(self->prefetchable_mem_base_hi).read());
		match lo & 0x0F {
			0 => assert_eq!(hi, 0, "inconsistent I/O base"),
			1 => (),
			_ => panic!("reserved value"),
		}

		(hi as u64) << 0x20 | (lo as u64 & 0xFFF0) << 0x10
	}

	pub fn set_prefetchable_mem_base(self, val: u64) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid I/O base");
		let addressing_cpb = u16::from_le(map!(self->prefetchable_mem_base_lo).read()) & 0x0F;
		let hi = match addressing_cpb {
			0 => {
				debug_assert!(u32::try_from(val).is_ok(), "invalid I/O base");
				0
			}
			1 => ((val >> 0x20) as u32).to_le(),
			_ => panic!("reserved value"),
		};
		map!(self->prefetchable_mem_base_lo).write((val >> 0x10 & 0xFFF0) as u16 | addressing_cpb);
		map!(self->prefetchable_mem_base_hi).write(hi);
	}

	/// The actual limit is `0x10_0000` higher than this.
	pub fn prefetchable_mem_limit(self) -> u64 {
		let lo = u16::from_le(map!(self->prefetchable_mem_limit_lo).read());
		let hi = u32::from_le(map!(self->prefetchable_mem_limit_hi).read());
		match lo & 0x0F {
			0 => assert_eq!(hi, 0, "inconsistent I/O limit"),
			1 => (),
			_ => panic!("reserved value"),
		}

		(hi as u64) << 0x20 | (lo as u64 & 0xFFF0) << 0x10
	}

	/// The input should be the actual limit minus `0x10_0000`.
	pub fn set_prefetchable_mem_limit(self, val: u64) {
		debug_assert_eq!(val % 0x10_0000, 0, "invalid I/O limit");
		let addressing_cpb = u16::from_le(map!(self->prefetchable_mem_limit_lo).read()) & 0x0F;
		let hi = match addressing_cpb {
			0 => {
				debug_assert!(u32::try_from(val).is_ok(), "invalid I/O limit");
				0
			}
			1 => ((val >> 0x20) as u32).to_le(),
			_ => panic!("reserved value"),
		};
		map!(self->prefetchable_mem_limit_lo).write((val >> 0x10 & 0xFFF0) as u16 | addressing_cpb);
		map!(self->prefetchable_mem_limit_hi).write(hi);
	}

	/// Iterates over PCI capabilities.
	pub fn cpbs(self) -> CpbIter {
		CpbIter::new(self.common(), map!(self->cpbs_ptr).read())
	}

	pub fn probe_expansion_rom_size(&mut self) -> u32 {
		self.set_expansion_rom(self.expansion_rom().with_base_addr(0xFFFF_F800));
		self.expansion_rom().base_addr().wrapping_neg()
	}
}

impl Debug for T1HeaderRef {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("T1HeaderRef")
			.field("bars", &self.bars())
			.field("primary_bus_num", &self.primary_bus_num())
			.field("secondary_bus_num", &self.secondary_bus_num())
			.field("subordinate_bus_num", &self.subordinate_bus_num())
			.field("secondary_latency_timer", &self.secondary_latency_timer())
			.field("io_base", &self.io_base())
			.field("io_limit", &self.io_limit())
			.field("secondary_status", &self.secondary_status())
			.field("mem_base", &self.mem_base())
			.field("mem_limit", &self.mem_limit())
			.field("prefetchable_mem_base", &self.prefetchable_mem_base())
			.field("prefetchable_mem_limit", &self.prefetchable_mem_limit())
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

impl BitField for SecondaryStatus {
	type Inner = u16;
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

impl BitField for BridgeControl {
	type Inner = u16;
}

/// Mutably iterates over base address registers.
pub struct BarIter {
	start: VolatilePtr<u32>,
	end: VolatilePtr<u32>,
}

impl BarIter {
	/// # Safety
	/// The input has to point to a valid array.
	unsafe fn new<const N: usize>(ptr: VolatilePtr<[u32; N]>) -> Self {
		let start = cast!(ptr);
		Self {
			start,
			end: map!((start)[N]),
		}
	}
}

impl Iterator for BarIter {
	type Item = Bar;

	fn next(&mut self) -> Option<Self::Item> {
		if self.start.as_raw_ptr() == self.end.as_raw_ptr() {
			return None;
		}
		let ptr = self.start;
		self.start = map!((ptr)[1]);
		let lo_le = ptr.read();
		let lo = u32::from_le(lo_le);
		if lo & 1 != 0 {
			return Some(Bar::IoSpace(IoBarRef(ptr), lo));
		}
		let val = match lo & 6 {
			0 => Bar::MemSpace32(Mem32BarRef(cast!(ptr)), Mem32BaseAddr(lo_le)),
			4 => {
				assert_ne!(
					self.start.as_raw_ptr(),
					self.end.as_raw_ptr(),
					"invalid 64-bit BAR"
				);
				let hi = self.start.read();
				self.start = map!((self.start)[1]);
				Bar::MemSpace64(Mem64BarRef(ptr), Mem64BaseAddr::new(lo_le, hi))
			}
			_ => panic!("reserved value"),
		};
		Some(val)
	}
}

impl FusedIterator for BarIter {}

impl Debug for BarIter {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let clone = Self {
			start: self.start,
			end: self.end,
		};
		f.debug_list().entries(clone).finish()
	}
}

/// Base address register.
#[derive(Debug)]
#[non_exhaustive]
pub enum Bar {
	MemSpace32(Mem32BarRef, Mem32BaseAddr),
	MemSpace64(Mem64BarRef, Mem64BaseAddr),
	IoSpace(IoBarRef, u32),
}

/// Reference to base address register containing a 32-bit memory address.
#[derive(Debug)]
pub struct Mem32BarRef(VolatilePtr<Mem32BaseAddr>);

impl Mem32BarRef {
	pub fn read(&self) -> Mem32BaseAddr {
		self.0.read()
	}

	pub fn write(&mut self, val: Mem32BaseAddr) {
		self.0.write(val);
	}

	pub fn probe_size(&mut self) -> u32 {
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

impl BitField for Mem32BaseAddr {
	type Inner = u32;
}

/// Reference to base address register containing a 64-bit memory address.
#[derive(Debug)]
pub struct Mem64BarRef(VolatilePtr<u32>);

impl Mem64BarRef {
	#[inline]
	pub fn read(&self) -> Mem64BaseAddr {
		Mem64BaseAddr::new(self.0.read(), map!((self.0)[1]).read())
	}

	#[inline]
	pub fn write(&mut self, val: Mem64BaseAddr) {
		let [a, b, c, d, e, f, g, h] = val.0.to_ne_bytes();
		map!((self.0)[0]).write(u32::from_ne_bytes([a, b, c, d]));
		map!((self.0)[1]).write(u32::from_ne_bytes([e, f, g, h]));
	}

	pub fn probe_size(&mut self) -> u64 {
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

impl BitField for Mem64BaseAddr {
	type Inner = u64;
}

/// Reference to a base address register containing a 32-bit I/O address.
#[derive(Debug)]
pub struct IoBarRef(VolatilePtr<u32>);

impl IoBarRef {
	#[inline]
	pub fn read(&self) -> u32 {
		u32::from_le(self.0.read()) & 0xFFFF_FFFC
	}

	#[inline]
	pub fn write(&mut self, val: u32) {
		debug_assert_eq!(val % 4, 0, "invalid addr");
		self.0.write(((val & 0xFFFF_FFFC) | 1).to_le());
	}

	#[inline]
	pub fn probe_size(&mut self) -> u32 {
		self.0.write(0xFFFF_FFFD_u32.to_le());
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

impl BitField for ExpansionRom {
	type Inner = u32;
}
