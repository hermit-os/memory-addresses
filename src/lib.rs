//! Universal crate for machine address types.

#![no_std]

use core::fmt;
use core::fmt::Debug;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub,
    SubAssign,
};

pub mod arch;
#[macro_use]
pub(crate) mod macros;
pub(crate) use macros::impl_address;

cfg_if::cfg_if! {
    if #[cfg(all(target_arch = "x86_64", feature = "x86_64"))] {
        pub use crate::arch::x86_64::{PhysAddr, VirtAddr};
    } else if #[cfg(all(target_arch = "aarch64", feature = "aarch64"))] {
        pub use crate::arch::aarch64::{PhysAddr, VirtAddr};
    } else {
        pub use crate::arch::fallback::{PhysAddr, VirtAddr};
    }
}

/// Trait that marks memory addresses.
///
/// An address must be a wrapper around a numeric value and thus behave like a number.
pub trait MemoryAddress:
    PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Copy
    + Clone
    + Sized
    + BitAnd<<Self>::RAW, Output = Self::RAW>
    + BitAndAssign<<Self>::RAW>
    + BitOr<<Self>::RAW, Output = Self::RAW>
    + BitOrAssign<<Self>::RAW>
    + BitXor<<Self>::RAW, Output = Self::RAW>
    + BitXorAssign<<Self>::RAW>
    + Add<<Self>::RAW>
    + AddAssign<<Self>::RAW>
    + Sub<Self, Output = Self::RAW>
    + Sub<<Self>::RAW, Output = Self>
    + SubAssign<<Self>::RAW>
    + fmt::Binary
    + fmt::LowerHex
    + fmt::UpperHex
    + fmt::Octal
    + fmt::Pointer
{
    /// Inner address type
    type RAW: Copy
        + PartialEq
        + Eq
        + PartialOrd
        + Ord
        + Not<Output = Self::RAW>
        + Add<Output = Self::RAW>
        + Sub<Output = Self::RAW>
        + BitAnd<Output = Self::RAW>
        + BitOr<Output = Self::RAW>
        + BitXor<Output = Self::RAW>
        + Debug
        + From<u8>;

    /// Get the raw underlying address value.
    fn raw(self) -> Self::RAW;
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
