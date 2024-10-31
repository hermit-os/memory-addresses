//! Universal crate for machine address types.

#![no_std]

use core::fmt;
use core::fmt::Debug;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl,
    ShlAssign, Shr, ShrAssign, Sub, SubAssign,
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
    } else if #[cfg(all(target_arch = "riscv64", feature = "riscv64"))] {
        pub use crate::arch::riscv64::{PhysAddr, VirtAddr};
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
    + Shr<usize, Output = Self>
    + ShrAssign<usize>
    + Shl<usize, Output = Self>
    + ShlAssign<usize>
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

/// Error type for [`AddrRange`]
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AddrRangeError {
    /// The range was constructed with the end before the start
    EndBeforeStart,
}

impl fmt::Display for AddrRangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EndBeforeStart => {
                f.write_str("Range end address can't be smaller than range start address")
            }
        }
    }
}

/// A memory range.
pub struct AddrRange<T: MemoryAddress> {
    start: T,
    end: T,
}
impl<T: MemoryAddress> AddrRange<T> {
    /// Construct a new memory range from `start` (inclusive) to `end` (exclusive).
    pub fn new(start: T, end: T) -> Result<Self, AddrRangeError> {
        if end < start {
            return Err(AddrRangeError::EndBeforeStart);
        }
        Ok(Self { start, end })
    }

    /// Produces an [`AddrIter`] to iterate over this memory range.
    pub fn iter(&self) -> AddrIter<T> {
        AddrIter {
            current: self.start,
            end: self.end,
        }
    }

    /// Check, wether `element` is part of the address range.
    pub fn contains(&self, element: &T) -> bool {
        element.raw() >= self.start.raw() && element.raw() < self.end.raw()
    }
}

/// An iterator over a memory range
pub struct AddrIter<T: MemoryAddress> {
    current: T,
    end: T,
}
impl<T: MemoryAddress> Iterator for AddrIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.end {
            None
        } else {
            let ret = Some(self.current);
            self.current += 1.into();
            ret
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn virtaddr_new_truncate() {
        assert_eq!(VirtAddr::new_truncate(0), VirtAddr::new(0));
        assert_eq!(VirtAddr::new_truncate(123), VirtAddr::new(123));
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }

    #[test]
    fn test_addr_range() {
        let r = AddrRange::new(VirtAddr::new(0x0), VirtAddr::new(0x3)).unwrap();
        assert!(r.contains(&VirtAddr::new(0x0)));
        assert!(r.contains(&VirtAddr::new(0x1)));
        assert!(!r.contains(&VirtAddr::new(0x3)));
        let mut i = r.iter();
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x0));
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x1));
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x2));
        assert!(i.next().is_none());

        for (i, a) in r.iter().enumerate() {
            assert_eq!(a.raw() as usize, i);
        }

        let r = AddrRange::new(PhysAddr::new(0x2), PhysAddr::new(0x4)).unwrap();
        let mut i = r.iter();
        assert_eq!(i.next().unwrap(), PhysAddr::new(0x2));
        assert_eq!(i.next().unwrap(), PhysAddr::new(0x3));
        assert!(i.next().is_none());

        assert_eq!(r.iter().map(|a| a.raw() as usize).sum::<usize>(), 0x5);
    }
}
