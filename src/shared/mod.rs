#![allow(non_upper_case_globals)]

pub mod control_regs;
pub mod descriptor;
pub mod dtables;
pub mod io;
pub mod irq;
pub mod paging;
pub mod segmentation;

use self::segmentation::SegmentSelector;

bitflags! {
    pub flags Flags: usize {
        const CarryFlag = 1 << 0,
        const ParityFlag = 1 << 2,
        const AdjustFlag = 1 << 4,
        const ZeroFlag = 1 << 6,
        const SignFlag = 1 << 7,
        const TrapFlag = 1 << 8,
        const InterruptFlag = 1 << 9,
        const DirectionFlag = 1 << 10,
        const OverflowFlag = 1 << 11,
        const Iopl1 = 1 << 12,
        const Iopl2 = 1 << 13,
        const NestedTaskFlag = 1 << 14,
        const ResumeFlag = 1 << 16,
        const Virtual8086Flag = 1 << 17,
        const AlignmentFlag = 1 << 18,
        const VirtualInterruptFlag = 1 << 19,
        const VirtualInterruptPending = 1 << 20,
        const CpuIdFlag = 1 << 21
    }
}

bitflags!(
    pub flags Features: u64 {
        const Fpu = 1 << 0,
        const Virtual8086 = 1 << 1,
        const DebugExtension = 1 << 2,
        const PageSizeExtension = 1 << 3,
        const TimeStampCounter = 1 << 4,
        const ModelSpecificRegister = 1 << 5,
        const PhysicalAddressExtension = 1 << 6,
        const MachineCheckException = 1 << 7,
        const Cx8 = 1 << 8, // CMPXCHG8
        const Apic = 1 << 9,
        const SysEnter = 1 << 11,
        const MemoryTypeRange = 1 << 12,
        const PageGlobal = 1 << 13,
        const MachineCheckArchitecture = 1 << 14,
        const CMov = 1 << 15,
        const PageAttributeTable = 1 << 16,
        const PageSizeExtension36 = 1 << 17,
        const ProcessorSerial = 1 << 18,
        const CacheFlush = 1 << 19,
        const DebugStore = 1 << 21,
        const Acpi = 1 << 22,
        const Mmx = 1 << 23,
        const FxSave = 1 << 24,
        const Sse = 1 << 25,
        const Sse2 = 1 << 26,
        const SelfSnoop = 1 << 27,
        const HyperThreading = 1 << 28,
        const ThermalMonitor = 1 << 29,
        const Ia64 = 1 << 30,
        const PendingBreak = 1 << 31,

        const Sse3 = 1 << (32 + 0),
        const PclMulQdq = 1 << (32 + 1), // what
        const DebugStore64 = 1 << (32 + 2),
        const Monitor = 1 << (32 + 3),
        const CplDebugStore = 1 << (32 + 4),
        const Vmx = 1 << (32 + 5),
        const SaferMode = 1 << (32 + 6),
        const EnhancedSpeedStep = 1 << (32 + 7),
        const ThermalMonitor2 = 1 << (32 + 8),
        const Ssse3 = 1 << (32 + 9),
        const L1ContextId = 1 << (32 + 10),
        const Fma = 1 << (32 + 12),
        const Cx16 = 1 << (32 + 13), // CMPXCHG16B
        const Xtpr = 1 << (32 + 14), // I have no idea what this is
        const PerformanceMonitor = 1 << (32 + 15),
        const ProcessContextId = 1 << (32 + 17),
        const DirectCache = 1 << (32 + 18),
        const Sse41 = 1 << (32 + 19),
        const Sse42 = 1 << (32 + 20),
        const X2Apic = 1 << (32 + 21),
        const MovBe = 1 << (32 + 22),
        const PopulationCount = 1 << (32 + 23),
        const TscDeadline = 1 << (32 + 24),
        const AesNi = 1 << (32 + 25),
        const XSave = 1 << (32 + 26),
        const OsXSave = 1 << (32 + 27),
        const Avx = 1 << (32 + 28),
        const HalfPrecision = 1 << (32 + 29),
        const HwRandom = 1 << (32 + 30)
    }
);

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Msr {
    ApicBase = 0x1B
}

#[inline(always)]
pub fn cpuid(function: u32) -> (u32, u32, u32, u32) {
    unsafe {
        let (eax, ebx, ecx, edx): (u32, u32, u32, u32);
        asm!("cpuid" : "={eax}"(eax), "={ebx}"(ebx), "={ecx}"(ecx), "={edx}"(edx) : "{eax}"(function));
        (eax, ebx, ecx, edx)
    }
}

#[inline(always)]
pub fn supports() -> Features {
    let (_, _, feature_ecx, feature_edx) = cpuid(1);
    Features {
        bits: ((feature_ecx as u64) << 32) | (feature_edx as u64)
    }
}

#[inline(always)]
pub unsafe fn read_msr(msr: Msr) -> u64 {
    let (r1, r2): (u32, u32);
    asm!("rdmsr" : "={eax}"(r1), "={edx}"(r2) : "{ecx}"(msr as u32) :: "intel");
    r1 as u64 | ((r2 as u64) << 32)
}

#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum PrivilegeLevel {
    Ring0 = 0,
    Ring1 = 1,
    Ring2 = 2,
    Ring3 = 3,
}

#[inline(always)]
pub unsafe fn set_tr(selector: SegmentSelector) {
    asm!("ltr $0" :: "r"(selector.bits()) :: "volatile", "intel");
}

#[inline(always)]
pub unsafe fn halt() {
    asm!("hlt" :::: "volatile", "intel");
}
