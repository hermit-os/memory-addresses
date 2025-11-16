//! Universal crate for machine address types.

#![no_std]

use core::fmt;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::marker::PhantomData;
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
        + From<u8>
        + TryInto<usize, Error: Debug>
        + TryFrom<usize, Error: Debug>;

    /// Get the raw underlying address value.
    fn raw(self) -> Self::RAW;

    /// Performs an add operation with `rhs`
    /// returning `None` if the operation overflowed or resulted in an invalid address.
    fn checked_add(self, rhs: Self::RAW) -> Option<Self>;

    /// Performs a sub operation with `rhs`
    /// returning `None` if the operation overflowed or resulted in an invalid address.
    fn checked_sub(self, rhs: Self::RAW) -> Option<Self>;
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
    /// Starting address
    pub start: T,
    /// End address (exclusive)
    pub end: T,
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
            end: Some(self.end),
            _phantom: PhantomData,
        }
    }

    /// Check, wether `element` is part of the address range.
    pub fn contains(&self, element: &T) -> bool {
        element.raw() >= self.start.raw() && element.raw() < self.end.raw()
    }

    /// Amount of addresses in the range.
    ///
    /// `AddrRange`s are half open, so the range from `0x0` to `0x1` has length 1.
    pub fn length(&self) -> usize {
        (self.end.raw() - self.start.raw())
            .try_into()
            .expect("address range is larger than the architecture's usize")
    }
}

/// An iterator over a memory range
#[allow(private_bounds)]
pub struct AddrIter<T: MemoryAddress, I: IterInclusivity = NonInclusive> {
    current: T,
    end: Option<T>, // None here indicates that this is exhausted
    _phantom: PhantomData<I>,
}

// Note this is deliberately private.
// Users may need to know about its existence but do not need to implement or use it.
trait IterInclusivity: 'static {
    fn exhausted<T: Ord>(start: &T, end: &T) -> bool;
}

/// This marks [AddrIter] as as acting as non-inclusive.
///
/// This is the behaviour when using [AddrRange::iter], it can also be constructed using [From].
///
///```
/// # use memory_addresses::AddrIter;
/// let start = memory_addresses::PhysAddr::new(0);
/// let end = memory_addresses::PhysAddr::new(0x1000);
///
/// for i in AddrIter::from(start..end) {
///    // ...
/// }
/// assert_eq!(AddrIter::from(start..end).last(), Some(memory_addresses::PhysAddr::new(0xfff)))
/// ```
pub enum NonInclusive {}

impl IterInclusivity for NonInclusive {
    fn exhausted<T: Ord>(start: &T, end: &T) -> bool {
        start >= end
    }
}

/// This marks [AddrIter] as as acting as inclusive.
///
/// The inclusive variant of [AddrIter] can be constructed using [From].
///
///```
/// # use memory_addresses::AddrIter;
/// let start = memory_addresses::PhysAddr::new(0);
/// let end = memory_addresses::PhysAddr::new(0x1000);
///
/// for i in AddrIter::from(start..=end) {
///    // ...
/// }
/// assert_eq!(AddrIter::from(start..end).last(), Some(memory_addresses::PhysAddr::new(0x1000)))
/// ```
pub enum Inclusive {}

impl IterInclusivity for Inclusive {
    fn exhausted<T: Ord>(start: &T, end: &T) -> bool {
        start > end
    }
}

impl<T: MemoryAddress, I: IterInclusivity> Iterator for AddrIter<T, I> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if I::exhausted(&self.current, &self.end?) {
            None
        } else {
            let ret = Some(self.current);
            self.current += 1.into();
            ret
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(end) = self.end else {
            return (0, Some(0));
        };
        let ni_count = (end - self.current)
            .try_into()
            .expect("address range is larger than the architecture's usize");

        // I whis there was a nicer way to do this.
        // This will determine whether I is `Inclusive` or `NonInclusive` and take the correct branch.
        // The compiler can determine which branch will be taken at compile time so this doesnt get checked at runtime.
        if core::any::TypeId::of::<I>() == core::any::TypeId::of::<NonInclusive>() {
            (ni_count, Some(ni_count))
        } else if core::any::TypeId::of::<I>() == core::any::TypeId::of::<Inclusive>() {
            (ni_count + 1, Some(ni_count + 1))
        } else {
            // Explicitly panic when I is not expected.
            // This should never be possible but it doesnt do any harm.
            unreachable!()
        }
    }

    fn last(self) -> Option<Self::Item> {
        self.max()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let Ok(n): Result<T::RAW, _> = n.try_into() else {
            // Fail to cast indicates that n > T::RAW::MAX, so we explicitly exhaust self.
            self.end.take();
            return None;
        };
        match self.current.checked_add(n) {
            Some(n) => self.current = n,
            None if self.current.raw() < n => {
                self.end.take();
                return None;
            }
            None => panic!("Attempted to iterate over invalid address"),
        }
        if I::exhausted(&self.current, &self.end?) {
            return None;
        }
        Some(self.current)
    }

    fn max(self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        Some(self.end.unwrap_or(self.current))
    }

    fn min(self) -> Option<Self::Item> {
        Some(self.current)
    }

    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<T: MemoryAddress> DoubleEndedIterator for AddrIter<T, NonInclusive> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if NonInclusive::exhausted(&self.current, &self.end?) {
            None
        } else {
            let one: T::RAW = 1u8.into();
            self.end = Some(self.end? - one);
            self.end
        }
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next_back(); // Avoids sub-with-overflow below
        }
        let Ok(n): Result<T::RAW, _> = n.try_into() else {
            // Fail to cast indicates that n > T::RAW::MAX, so we explicitly exhaust self.
            self.end.take();
            return None;
        };
        let Some(ret) = self.end?.checked_sub(n) else {
            if self.end?.raw() < n {
                panic!("Attempted to iterate over invalid address")
            }
            self.end.take();
            return None;
        };
        self.end = Some(ret);
        self.next_back()
    }
}

impl<T: MemoryAddress> DoubleEndedIterator for AddrIter<T, Inclusive> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if Inclusive::exhausted(&self.current, &self.end?) {
            None
        } else {
            let ret = self.end?;

            // We need to be able to step back to `0`.
            // We return `0` when self.end is currently `0`.
            // But then we subtract `0` by `1` triggering a sub-with-overflow
            // When we trigger a sub-with-overflow we return early and dont decrement `self.end`
            // The next call to self.next() will return as exhausted and the
            let Some(step) = self.end?.checked_sub(1.into()) else {
                // Check if this was an underflow or a non-canonical address
                // Panic on non-canonical
                // We can eat the overhead here because this branch is rare
                if self.end?.raw() != 0u8.into() {
                    panic!("Attempted to iterate over invalid address")
                }
                self.end = None;
                return Some(ret);
            };
            self.end = Some(step);
            Some(ret)
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next_back();
        }
        let Ok(n): Result<T::RAW, _> = n.try_into() else {
            // Fail to cast indicates that n > T::RAW::MAX, so we explicitly exhaust self.
            self.end.take();
            return None;
        };

        let Some(ret) = self.end?.checked_sub(n) else {
            if self.end?.raw() < n {
                panic!("Attempted to iterate over invalid address")
            }
            self.end.take();
            return None;
        };
        self.end = Some(ret);
        self.end
    }
}

impl<T: MemoryAddress> ExactSizeIterator for AddrIter<T, Inclusive> {
    fn len(&self) -> usize {
        let Some(end) = self.end else { return 0 };
        (end - self.current)
            .try_into()
            .expect("address range is larger than the architecture's usize")
            + 1
    }
}

impl<T: MemoryAddress> ExactSizeIterator for AddrIter<T, NonInclusive> {
    fn len(&self) -> usize {
        let Some(end) = self.end else { return 0 };
        (end - self.current)
            .try_into()
            .expect("address range is larger than the architecture's usize")
    }
}

impl<T: MemoryAddress> FusedIterator for AddrIter<T> {}

impl<T: MemoryAddress> From<core::ops::Range<T>> for AddrIter<T, NonInclusive> {
    fn from(range: core::ops::Range<T>) -> Self {
        Self {
            current: range.start,
            end: Some(range.end),
            _phantom: PhantomData,
        }
    }
}

impl<T: MemoryAddress> From<core::ops::RangeInclusive<T>> for AddrIter<T, Inclusive> {
    fn from(range: core::ops::RangeInclusive<T>) -> Self {
        Self {
            current: *range.start(),
            end: Some(*range.end()),
            _phantom: PhantomData,
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

        assert_eq!(r.iter().nth(0), Some(VirtAddr::new(0x0)));
        assert_eq!(r.iter().nth(1), Some(VirtAddr::new(0x1)));
        assert_eq!(r.iter().nth(2), Some(VirtAddr::new(0x2)));
        assert_eq!(r.iter().nth(3), None);

        {
            let mut range = r.iter();
            assert_eq!(range.next_back(), Some(VirtAddr::new(0x2)));
            assert_eq!(range.next_back(), Some(VirtAddr::new(0x1)));
            assert_eq!(range.next_back(), Some(VirtAddr::new(0x0)));
            assert_eq!(range.next_back(), None);
            assert_eq!(range.next(), None);

            let mut range = r.iter();
            assert_eq!(range.next(), Some(VirtAddr::new(0x0)));
            assert_eq!(range.next_back(), Some(VirtAddr::new(0x2)));
            assert_eq!(range.next(), Some(VirtAddr::new(0x1)));
            assert_eq!(range.next_back(), None);

            assert_eq!(r.iter().nth_back(0), Some(VirtAddr::new(0x2)));
            assert_eq!(r.iter().nth_back(1), Some(VirtAddr::new(0x1)));
            assert_eq!(r.iter().nth_back(2), Some(VirtAddr::new(0x0)));
            assert_eq!(r.iter().nth_back(3), None);
        }

        let r = AddrRange::new(PhysAddr::new(0x2), PhysAddr::new(0x4)).unwrap();
        let mut i = r.iter();
        assert_eq!(i.next().unwrap(), PhysAddr::new(0x2));
        assert_eq!(i.next().unwrap(), PhysAddr::new(0x3));
        assert!(i.next().is_none());

        assert_eq!(r.iter().map(|a| a.raw() as usize).sum::<usize>(), 0x5);
    }

    #[test]
    fn test_iter_incl() {
        let range = VirtAddr::new(0x0)..=VirtAddr::new(0x3);
        let mut i = AddrIter::from(range.clone());
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x0));
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x1));
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x2));
        assert_eq!(i.next().unwrap(), VirtAddr::new(0x3));

        let mut i = AddrIter::from(range.clone());
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x3)));
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x2)));
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x1)));
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x0)));
        assert_eq!(i.next_back(), None);

        let mut i = AddrIter::from(range.clone());
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x3)));
        assert_eq!(i.next(), Some(VirtAddr::new(0x0)));
        assert_eq!(i.next_back(), Some(VirtAddr::new(0x2)));
        assert_eq!(i.next(), Some(VirtAddr::new(0x1)));
        assert_eq!(i.next_back(), None);

        assert_eq!(
            AddrIter::from(range.clone()).nth(0),
            Some(VirtAddr::new(0x0))
        );
        assert_eq!(
            AddrIter::from(range.clone()).nth(1),
            Some(VirtAddr::new(0x1))
        );
        assert_eq!(
            AddrIter::from(range.clone()).nth(2),
            Some(VirtAddr::new(0x2))
        );
        assert_eq!(
            AddrIter::from(range.clone()).nth(3),
            Some(VirtAddr::new(0x3))
        );
        assert_eq!(AddrIter::from(range.clone()).nth(4), None);
    }

    #[test]
    fn iterator_assert_sizes() {
        let range_incl = VirtAddr::new(0x0)..=VirtAddr::new(0x3);
        assert_eq!(
            AddrIter::from(range_incl.clone()).count(),
            AddrIter::from(range_incl.clone()).len()
        );
        assert_eq!(
            AddrIter::from(range_incl.clone()).count(),
            AddrIter::from(range_incl.clone()).size_hint().0
        );
        assert_eq!(
            AddrIter::from(range_incl.clone()).count(),
            AddrIter::from(range_incl.clone()).size_hint().1.unwrap()
        );
    }
}
