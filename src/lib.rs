/// Universal crate for machine address types.

pub mod arch;

#[cfg(target_arch="x86_64")]
pub use crate::arch::x86_64::{VirtAddr, PhysAddr};

#[cfg(not(any(target_arch = "x86_64")))]
pub use crate::arch::fallback::{VirtAddr, PhysAddr};
