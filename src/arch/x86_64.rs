//! Physical and virtual addresses manipulation

use align_address::Align;
use core::fmt;
#[cfg(feature = "conv-x86")]
use x86::bits64::paging::{PAddr as x86_PAddr, VAddr as x86_VAddr};

use crate::impl_address;

use x86_64::structures::paging::page_table::PageTableLevel;
use x86_64::structures::paging::{PageOffset, PageTableIndex};

/// A canonical 64-bit virtual memory address.
///
/// This is a wrapper type around an `u64`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `u64` and `usize`.
///
/// On `x86_64`, only the 48 lower bits of a virtual address can be used. The top 16 bits need
/// to be copies of bit 47, i.e. the most significant bit. Addresses that fulfil this criterion
/// are called “canonical”. This type guarantees that it always represents a canonical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VirtAddr(u64);

impl_address!(VirtAddr, u64, as_u64);

impl crate::VirtualMemoryAddress for VirtAddr {}

/// A 64-bit physical memory address.
///
/// This is a wrapper type around an `u64`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `u64` and `usize`.
///
/// On `x86_64`, only the 52 lower bits of a physical address can be used. The top 12 bits need
/// to be zero. This type guarantees that it always represents a valid physical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PhysAddr(u64);

impl_address!(PhysAddr, u64, as_u64);

impl crate::PhysicalMemoryAddress for PhysAddr {}

/// A passed `u64` was not a valid virtual address.
///
/// This means that bits 48 to 64 are not
/// a valid sign extension and are not null either. So automatic sign extension would have
/// overwritten possibly meaningful bits. This likely indicates a bug, for example an invalid
/// address calculation.
///
/// Contains the invalid address.
pub struct VirtAddrNotValid(pub u64);

impl core::fmt::Debug for VirtAddrNotValid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VirtAddrNotValid")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl VirtAddr {
    /// Creates a new canonical virtual address.
    ///
    /// The provided address should already be canonical. If you want to check
    /// whether an address is canonical, use [`try_new`](Self::try_new).
    ///
    /// ## Panics
    ///
    /// This function panics if the bits in the range 48 to 64 are invalid
    /// (i.e. are not a proper sign extension of bit 47).
    #[inline]
    pub const fn new(addr: u64) -> VirtAddr {
        // TODO: Replace with .ok().expect(msg) when that works on stable.
        match Self::try_new(addr) {
            Ok(v) => v,
            Err(_) => panic!("virtual address must be sign extended in bits 48 to 64"),
        }
    }

    /// Tries to create a new canonical virtual address.
    ///
    /// This function checks wether the given address is canonical
    /// and returns an error otherwise. An address is canonical
    /// if bits 48 to 64 are a correct sign
    /// extension (i.e. copies of bit 47).
    #[inline]
    pub const fn try_new(addr: u64) -> Result<VirtAddr, VirtAddrNotValid> {
        let v = Self::new_truncate(addr);
        if v.0 == addr {
            Ok(v)
        } else {
            Err(VirtAddrNotValid(addr))
        }
    }

    /// Creates a new canonical virtual address, throwing out bits 48..64.
    ///
    /// This function performs sign extension of bit 47 to make the address
    /// canonical, overwriting bits 48 to 64. If you want to check whether an
    /// address is canonical, use [`new`](Self::new) or [`try_new`](Self::try_new).
    #[inline]
    pub const fn new_truncate(addr: u64) -> VirtAddr {
        // By doing the right shift as a signed operation (on a i64), it will
        // sign extend the value, repeating the leftmost bit.
        VirtAddr(((addr << 16) as i64 >> 16) as u64)
    }

    /// Creates a virtual address from the given pointer
    #[cfg(target_pointer_width = "64")]
    #[inline]
    pub fn from_ptr<T: ?Sized>(ptr: *const T) -> Self {
        Self::new(ptr as *const () as u64)
    }

    /// Converts the address to a raw pointer.
    #[cfg(target_pointer_width = "64")]
    #[inline]
    pub const fn as_ptr<T>(self) -> *const T {
        self.as_u64() as *const T
    }

    /// Converts the address to a mutable raw pointer.
    #[cfg(target_pointer_width = "64")]
    #[inline]
    pub const fn as_mut_ptr<T>(self) -> *mut T {
        self.as_ptr::<T>() as *mut T
    }

    #[cfg(target_pointer_width = "64")]
    // if the target_pointer_width is 64, usize = u64 so we can safely transform.
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }

    /// Checks whether the virtual address has the demanded alignment.
    #[inline]
    pub fn is_aligned(self, align: u64) -> bool {
        self.align_down(align).as_u64() == self.as_u64()
    }

    /// Returns the 12-bit page offset of this virtual address.
    #[inline]
    pub const fn page_offset(self) -> PageOffset {
        PageOffset::new_truncate(self.0 as u16)
    }

    /// Returns the 9-bit level 1 page table index.
    #[inline]
    pub const fn p1_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12) as u16)
    }

    /// Returns the 9-bit level 2 page table index.
    #[inline]
    pub const fn p2_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9) as u16)
    }

    /// Returns the 9-bit level 3 page table index.
    #[inline]
    pub const fn p3_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9 >> 9) as u16)
    }

    /// Returns the 9-bit level 4 page table index.
    #[inline]
    pub const fn p4_index(self) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> 9 >> 9 >> 9) as u16)
    }

    /// Returns the 9-bit level page table index.
    #[inline]
    pub const fn page_table_index(self, level: PageTableLevel) -> PageTableIndex {
        PageTableIndex::new_truncate((self.0 >> 12 >> ((level as u8 - 1) * 9)) as u16)
    }
}

impl Align<u64> for VirtAddr {
    #[inline]
    fn align_down(self, align: u64) -> Self {
        Self::new_truncate(self.0.align_down(align))
    }

    #[inline]
    fn align_up(self, align: u64) -> Self {
        Self::new_truncate(self.0.align_up(align))
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely transform.
impl From<usize> for VirtAddr {
    fn from(addr: usize) -> VirtAddr {
        Self::new_truncate(addr as u64)
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely add
impl core::ops::Add<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0 + rhs as u64)
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely add
impl core::ops::AddAssign<usize> for VirtAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely sub
impl core::ops::Sub<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0.checked_sub(rhs as u64).unwrap())
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely sub
impl core::ops::SubAssign<usize> for VirtAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<x86_64::VirtAddr> for VirtAddr {
    fn from(addr: x86_64::VirtAddr) -> Self {
        Self(addr.as_u64())
    }
}
#[cfg(feature = "conv-x86_64")]
impl From<&x86_64::VirtAddr> for VirtAddr {
    fn from(addr: &x86_64::VirtAddr) -> Self {
        Self(addr.as_u64())
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<VirtAddr> for x86_64::VirtAddr {
    fn from(addr: VirtAddr) -> x86_64::VirtAddr {
        x86_64::VirtAddr::new(addr.0)
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<&VirtAddr> for x86_64::VirtAddr {
    fn from(addr: &VirtAddr) -> x86_64::VirtAddr {
        x86_64::VirtAddr::new(addr.0)
    }
}

#[cfg(feature = "conv-x86")]
impl From<x86_VAddr> for VirtAddr {
    fn from(addr: x86_VAddr) -> Self {
        Self(addr.as_u64())
    }
}
#[cfg(feature = "conv-x86")]
impl From<&x86_VAddr> for VirtAddr {
    fn from(addr: &x86_VAddr) -> Self {
        Self(addr.as_u64())
    }
}

#[cfg(feature = "conv-x86")]
impl From<VirtAddr> for x86_VAddr {
    fn from(addr: VirtAddr) -> x86_VAddr {
        x86_VAddr(addr.0)
    }
}

#[cfg(feature = "conv-x86")]
impl From<&VirtAddr> for x86_VAddr {
    fn from(addr: &VirtAddr) -> x86_VAddr {
        x86_VAddr(addr.0)
    }
}

/// A passed `u64` was not a valid physical address.
///
/// This means that bits 52 to 64 were not all null.
///
/// Contains the invalid address.
pub struct PhysAddrNotValid(pub u64);

impl core::fmt::Debug for PhysAddrNotValid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PhysAddrNotValid")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl PhysAddr {
    /// Creates a new physical address.
    ///
    /// ## Panics
    ///
    /// This function panics if a bit in the range 52 to 64 is set.
    #[inline]
    pub const fn new(addr: u64) -> Self {
        // TODO: Replace with .ok().expect(msg) when that works on stable.
        match Self::try_new(addr) {
            Ok(p) => p,
            Err(_) => panic!("physical addresses must not have any bits in the range 52 to 64 set"),
        }
    }

    /// Creates a new physical address, throwing bits 52..64 away.
    #[inline]
    pub const fn new_truncate(addr: u64) -> PhysAddr {
        PhysAddr(addr % (1 << 52))
    }

    /// Tries to create a new physical address.
    ///
    /// Fails if any bits in the range 52 to 64 are set.
    #[inline]
    pub const fn try_new(addr: u64) -> Result<Self, PhysAddrNotValid> {
        let p = Self::new_truncate(addr);
        if p.0 == addr {
            Ok(p)
        } else {
            Err(PhysAddrNotValid(addr))
        }
    }

    #[cfg(target_pointer_width = "64")]
    // if the target_pointer_width is 64, usize = u64 so we can safely transform.
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl Align<u64> for PhysAddr {
    #[inline]
    fn align_down(self, align: u64) -> Self {
        Self::new(self.as_u64().align_down(align))
    }

    #[inline]
    fn align_up(self, align: u64) -> Self {
        Self::new(self.as_u64().align_up(align))
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely transform.
impl From<usize> for PhysAddr {
    fn from(addr: usize) -> PhysAddr {
        Self::new_truncate(addr as u64)
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely add
impl core::ops::Add<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0 + rhs as u64)
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely add
impl core::ops::AddAssign<usize> for PhysAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely sub
impl core::ops::Sub<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0.checked_sub(rhs as u64).unwrap())
    }
}

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely sub
impl core::ops::SubAssign<usize> for PhysAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<x86_64::PhysAddr> for PhysAddr {
    fn from(addr: x86_64::PhysAddr) -> Self {
        Self(addr.as_u64())
    }
}
#[cfg(feature = "conv-x86_64")]
impl From<&x86_64::PhysAddr> for PhysAddr {
    fn from(addr: &x86_64::PhysAddr) -> Self {
        Self(addr.as_u64())
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<PhysAddr> for x86_64::PhysAddr {
    fn from(addr: PhysAddr) -> x86_64::PhysAddr {
        x86_64::PhysAddr::new(addr.0)
    }
}

#[cfg(feature = "conv-x86_64")]
impl From<&PhysAddr> for x86_64::PhysAddr {
    fn from(addr: &PhysAddr) -> x86_64::PhysAddr {
        x86_64::PhysAddr::new(addr.0)
    }
}

#[cfg(feature = "conv-x86")]
impl From<x86_PAddr> for PhysAddr {
    fn from(addr: x86_PAddr) -> Self {
        Self(addr.as_u64())
    }
}
#[cfg(feature = "conv-x86")]
impl From<&x86_PAddr> for PhysAddr {
    fn from(addr: &x86_PAddr) -> Self {
        Self(addr.as_u64())
    }
}

#[cfg(feature = "conv-x86")]
impl From<PhysAddr> for x86_PAddr {
    fn from(addr: PhysAddr) -> x86_PAddr {
        x86_PAddr(addr.0)
    }
}

#[cfg(feature = "conv-x86")]
impl From<&PhysAddr> for x86_PAddr {
    fn from(addr: &PhysAddr) -> x86_PAddr {
        x86_PAddr(addr.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn virtaddr_new_truncate() {
        assert_eq!(VirtAddr::new_truncate(0), VirtAddr(0));
        assert_eq!(VirtAddr::new_truncate(1 << 47), VirtAddr(0xfffff << 47));
        assert_eq!(VirtAddr::new_truncate(123), VirtAddr(123));
        assert_eq!(VirtAddr::new_truncate(123 << 47), VirtAddr(0xfffff << 47));
    }

    #[test]
    fn test_virt_addr_align_up() {
        // Make sure the 47th bit is extended.
        assert_eq!(
            VirtAddr::new(0x7fff_ffff_ffff).align_up(2u64),
            VirtAddr::new(0xffff_8000_0000_0000)
        );
    }

    #[test]
    fn test_virt_addr_align_down() {
        // Make sure the 47th bit is extended.
        assert_eq!(
            VirtAddr::new(0xffff_8000_0000_0000).align_down(1u64 << 48),
            VirtAddr::new(0)
        );
    }

    #[test]
    #[should_panic]
    fn test_virt_addr_align_up_overflow() {
        VirtAddr::new(0xffff_ffff_ffff_ffff).align_up(2u64);
    }

    #[test]
    #[should_panic]
    fn test_phys_addr_align_up_overflow() {
        PhysAddr::new(0x000f_ffff_ffff_ffff).align_up(2u64);
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }
}
