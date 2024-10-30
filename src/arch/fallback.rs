//! Physical and virtual addresses manipulation

use crate::impl_address;
use core::fmt;

use align_address::Align;

/// A virtual memory address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VirtAddr(pub usize);

impl_address!(VirtAddr, usize);

/// A physical memory address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PhysAddr(pub usize);

impl_address!(PhysAddr, usize);

/// An invalid virtual address
pub struct VirtAddrNotValid(pub usize);

impl core::fmt::Debug for VirtAddrNotValid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VirtAddrNotValid")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl VirtAddr {
    /// Creates a new canonical virtual address.
    #[inline]
    pub const fn new(addr: usize) -> VirtAddr {
        Self(addr)
    }

    /// Tries to create a new canonical virtual address.
    #[inline]
    pub const fn try_new(addr: usize) -> Result<VirtAddr, VirtAddrNotValid> {
        Ok(Self(addr))
    }

    /// Creates a new virtual address truncating non-address parts.
    #[inline]
    pub const fn new_truncate(addr: usize) -> VirtAddr {
        Self(addr)
    }

    /// Creates a virtual address from the given pointer
    #[inline]
    pub fn from_ptr<T: ?Sized>(ptr: *const T) -> Self {
        Self::new(ptr as *const () as usize)
    }

    /// Converts the address to a raw pointer.
    #[inline]
    pub const fn as_ptr<T>(self) -> *const T {
        self.0 as *const T
    }

    /// Converts the address to a mutable raw pointer.
    #[inline]
    pub const fn as_mut_ptr<T>(self) -> *mut T {
        self.as_ptr::<T>() as *mut T
    }
}

impl Align<usize> for VirtAddr {
    #[inline]
    fn align_down(self, align: usize) -> Self {
        Self::new_truncate(self.0.align_down(align))
    }

    #[inline]
    fn align_up(self, align: usize) -> Self {
        Self::new_truncate(self.0.align_up(align))
    }
}

/// A passed `usize` was not a valid physical address.
///
/// This means that bits 52 to 64 were not all null.
///
/// Contains the invalid address.
pub struct PhysAddrNotValid(pub usize);

impl core::fmt::Debug for PhysAddrNotValid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PhysAddrNotValid")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl PhysAddr {
    /// Creates a new physical address.
    #[inline]
    pub const fn new(addr: usize) -> Self {
        Self(addr)
    }

    /// Creates a new physical address truncating non-address parts.
    #[inline]
    pub const fn new_truncate(addr: usize) -> PhysAddr {
        PhysAddr(addr)
    }

    /// Tries to create a new physical address.
    ///
    /// Fails if any bits in the range 52 to 64 are set.
    #[inline]
    pub const fn try_new(addr: usize) -> Result<Self, PhysAddrNotValid> {
        Ok(Self(addr))
    }
}

impl Align<usize> for PhysAddr {
    #[inline]
    fn align_down(self, align: usize) -> Self {
        Self::new(self.0.align_down(align))
    }

    #[inline]
    fn align_up(self, align: usize) -> Self {
        Self::new(self.0.align_up(align))
    }
}
