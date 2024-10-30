//! Universal crate for machine address types.

#![no_std]

pub mod arch;

cfg_if::cfg_if! {
    if #[cfg(all(target_arch = "x86_64", feature = "x86_64"))] {
        pub use crate::arch::x86_64::{PhysAddr, VirtAddr};
    } else if #[cfg(all(target_arch = "aarch64", feature = "aarch64"))] {
        pub use crate::arch::aarch64::{PhysAddr, VirtAddr};
    } else {
        pub use crate::arch::fallback::{PhysAddr, VirtAddr};
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn virtaddr_new_truncate() {
        assert_eq!(VirtAddr::new_truncate(0), VirtAddr(0));
        assert_eq!(VirtAddr::new_truncate(123), VirtAddr(123));
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }
}
