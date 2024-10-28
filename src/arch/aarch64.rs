//! Physical and virtual addresses manipulation

use crate::{align_down, align_up};
use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/// A virtual memory address on `aarch64`.
///
/// In exception level (EL) 0  and EL1 the virtual address space ranges from `0` till
/// `0x000f_ffff_ffff_ffff`, as well as from `0xfff0_0000_0000_0000` to `0xffff_ffff_ffff_ffff`.
/// This type enforces this limit.
/// However, there are more restrictions (e.g., execption level 3 has only one address space)
/// that are not encoded in this type.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VirtAddr(pub u64);

/// An invalid virtual address.
///
/// Virutal addresses on aarch64 are invalid, if the topmost 12 bits are not the same.
/// However, there are more restrictions (e.g., execption level 3 has only one address space)
/// that are not encoded in this type.
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
    #[inline]
    pub const fn new(addr: u64) -> VirtAddr {
        // TODO: Replace with .ok().expect(msg) when that works on stable.
        match Self::try_new(addr) {
            Ok(v) => v,
            Err(_) => panic!("virtual address must be sign extended in bits 52 to 64"),
        }
    }

    /// Tries to create a new canonical virtual address.
    #[inline]
    pub const fn try_new(addr: u64) -> Result<VirtAddr, VirtAddrNotValid> {
        match addr {
            0..=0x000f_ffff_ffff_ffff | 0xfff0_0000_0000_0000..=0xffff_ffff_ffff_ffff => {
                Ok(Self(addr))
            }
            _ => Err(VirtAddrNotValid(addr)),
        }
    }

    /// Creates a new canonical virtual address, throwing out bits 52..63.
    ///
    /// Addresses on aarch64 are invalid, if the topmost 12 bits are not the same.
    /// This function performs sign extension of bit 56 to make the address
    /// canonical, overwriting bits 56 to 63.
    #[inline]
    pub const fn new_truncate(addr: u64) -> VirtAddr {
        // By doing the right shift as a signed operation (on a i64), it will
        // sign extend the value, repeating the leftmost bit.
        VirtAddr(((addr << 11) as i64 >> 11) as u64)
    }

    /// Creates a new virtual address, without any checks.
    #[inline]
    pub const unsafe fn new_unsafe(addr: u64) -> VirtAddr {
        VirtAddr(addr)
    }

    /// Creates a virtual address that points to `0`.
    #[inline]
    pub const fn zero() -> VirtAddr {
        VirtAddr(0)
    }

    /// Creates a virtual address from the given pointer
    #[inline]
    pub fn from_ptr<T: ?Sized>(ptr: *const T) -> Self {
        Self::new(ptr as *const () as u64)
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

    /// Convenience method for checking if a virtual address is null.
    #[inline]
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }

    /// Aligns the virtual address upwards to the given alignment.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<u64>,
    {
        VirtAddr::new_truncate(align_up(self.0, align.into()))
    }

    /// Aligns the virtual address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<u64>,
    {
        VirtAddr::new_truncate(align_down(self.0, align.into()))
    }

    /// Checks whether the virtual address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<u64>,
    {
        self.align_down(align).0 == self.0
    }
}

impl fmt::Debug for VirtAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("VirtAddr")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl fmt::Binary for VirtAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl fmt::LowerHex for VirtAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl fmt::Octal for VirtAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Octal::fmt(&self.0, f)
    }
}

impl fmt::UpperHex for VirtAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::UpperHex::fmt(&self.0, f)
    }
}

impl fmt::Pointer for VirtAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&(self.0 as *const ()), f)
    }
}

impl Add<u64> for VirtAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: u64) -> Self::Output {
        VirtAddr::new(self.0 + rhs)
    }
}

impl AddAssign<u64> for VirtAddr {
    #[inline]
    fn add_assign(&mut self, rhs: u64) {
        *self = *self + rhs;
    }
}

impl Sub<u64> for VirtAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: u64) -> Self::Output {
        VirtAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<u64> for VirtAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: u64) {
        *self = *self - rhs;
    }
}

impl Sub<VirtAddr> for VirtAddr {
    type Output = u64;
    #[inline]
    fn sub(self, rhs: VirtAddr) -> Self::Output {
        self.0.checked_sub(rhs.0).unwrap()
    }
}

/// A physical memory address.
///
/// The size of a valid physical address on aarch64 is implementation defined, but since Armv9.3
/// not larger than 56 bits. This type enforces this limit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PhysAddr(pub u64);

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
    #[inline]
    pub const fn new(addr: u64) -> Self {
        // TODO: Replace with .ok().expect(msg) when that works on stable.
        match Self::try_new(addr) {
            Ok(p) => p,
            Err(_) => panic!("physical addresses must not have any bits in the range 57 to 64 set"),
        }
    }

    /// Creates a new physical address truncating non-address parts.
    #[inline]
    pub const fn new_truncate(addr: u64) -> PhysAddr {
        PhysAddr(addr % (1 << 56))
    }

    /// Creates a new physical address, without any checks.
    ///
    /// ## Safety
    ///
    /// You must make sure bits 56..63 are zero. This is not checked.
    #[inline]
    pub const unsafe fn new_unsafe(addr: u64) -> PhysAddr {
        PhysAddr(addr)
    }

    /// Tries to create a new physical address.
    ///
    /// Fails if any bits in the range 56 to 64 are set.
    #[inline]
    pub const fn try_new(addr: u64) -> Result<Self, PhysAddrNotValid> {
        let p = Self::new_truncate(addr);
        if p.0 == addr {
            Ok(p)
        } else {
            Err(PhysAddrNotValid(addr))
        }
    }

    /// Creates a physical address that points to `0`.
    #[inline]
    pub const fn zero() -> PhysAddr {
        PhysAddr(0)
    }

    /// Convenience method for checking if a physical address is null.
    #[inline]
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }

    /// Aligns the physical address upwards to the given alignment.
    ///
    /// See the `align_up` function for more information.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<u64>,
    {
        PhysAddr::new(align_up(self.0, align.into()))
    }

    /// Aligns the physical address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<u64>,
    {
        Self(align_down(self.0, align.into()))
    }

    /// Checks whether the physical address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<u64>,
    {
        self.align_down(align).0 == self.0
    }
}

impl fmt::Debug for PhysAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("PhysAddr")
            .field(&format_args!("{:#x}", self.0))
            .finish()
    }
}

impl fmt::Binary for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Binary::fmt(&self.0, f)
    }
}

impl fmt::LowerHex for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl fmt::Octal for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Octal::fmt(&self.0, f)
    }
}

impl fmt::UpperHex for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::UpperHex::fmt(&self.0, f)
    }
}

impl fmt::Pointer for PhysAddr {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&(self.0 as *const ()), f)
    }
}

impl Add<u64> for PhysAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: u64) -> Self::Output {
        PhysAddr::new(self.0 + rhs)
    }
}

impl AddAssign<u64> for PhysAddr {
    #[inline]
    fn add_assign(&mut self, rhs: u64) {
        *self = *self + rhs;
    }
}

impl Sub<u64> for PhysAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: u64) -> Self::Output {
        PhysAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<u64> for PhysAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: u64) {
        *self = *self - rhs;
    }
}

impl Sub<PhysAddr> for PhysAddr {
    type Output = u64;
    #[inline]
    fn sub(self, rhs: PhysAddr) -> Self::Output {
        self.0.checked_sub(rhs.0).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_virt_addr() {
        let _ = VirtAddr::new(0x0);
        let _ = VirtAddr::new(0x1);
        let _ = VirtAddr::new(0x000f_ffff_ffff_ffff);
        let _ = VirtAddr::new(0xffff_0000_0000_0000);
        let _ = VirtAddr::new(0xffff_ffff_ffff_ffff);
    }

    #[test]
    #[should_panic]
    fn test_invalid_virt_addr() {
        let _ = VirtAddr::new(0x0ff0_0000_0000_0000);
        let _ = VirtAddr::new(0xffe0_0000_0000_0000);
        let _ = VirtAddr::new(0x0010_0000_0000_0000);
    }

    #[test]
    fn test_phys_addr() {
        let _ = PhysAddr::new(0x0);
        let _ = PhysAddr::new(0x1);
        let _ = PhysAddr::new(0x00ff_ffff_ffff_ffff);
    }

    #[test]
    #[should_panic]
    fn test_invalid_phys_addr() {
        let _ = PhysAddr::new(0x0100_0000_0000_0000);
        let _ = PhysAddr::new(0xffff_ffff_ffff_ffff);
    }

    #[test]
    pub fn virtaddr_new_truncate() {
        assert_eq!(VirtAddr::new_truncate(0), VirtAddr(0));
        assert_eq!(VirtAddr::new_truncate(1 << 51), VirtAddr(1 << 51));
        assert_eq!(VirtAddr::new_truncate(1 << 52), VirtAddr(0xfffff << 52));
        assert_eq!(VirtAddr::new_truncate(123), VirtAddr(123));
        assert_eq!(VirtAddr::new_truncate(123 << 51), VirtAddr(0xfffff << 51));
        assert_eq!(
            VirtAddr::new_truncate(0xfff0_0000_0000_0000),
            VirtAddr::new_truncate(0xfff0_0000_0000_0000)
        );
        assert_eq!(
            VirtAddr::new_truncate(0xfff0_0000_0000_1000),
            VirtAddr::new_truncate(0xfff0_0000_0000_1000)
        );
        assert_eq!(
            VirtAddr::new_truncate(0xffff_ffff_ffff_ffff),
            VirtAddr::new_truncate(0xffff_ffff_ffff_ffff)
        );
    }

    #[test]
    fn test_virt_addr_align_up() {
        assert_eq!(
            VirtAddr::new(0x0000_0000_0000_1234).align_up(0x1000_u64),
            VirtAddr::new(0x0000_0000_0000_2000)
        );
        assert_eq!(
            VirtAddr::new(0x000f_ffff_ffff_ffff).align_up(2u64),
            VirtAddr::new(0xfff0_0000_0000_0000)
        );
    }

    #[test]
    fn test_virt_addr_align_down() {
        assert_eq!(
            VirtAddr::new(0x0000_0000_0000_1005).align_down(0x1000_u64),
            VirtAddr::new(0x0000_0000_0000_1000)
        );
        assert_eq!(
            VirtAddr::new(0x0000_0000_0000_1000).align_down(0x1_0000_u64),
            VirtAddr::new(0x0000_0000_0000_0000)
        );
        assert_eq!(
            VirtAddr::new(0xfff0_0000_0000_0000).align_down(1u64 << 10),
            VirtAddr::new(0xfff0_0000_0000_0000)
        );
    }

    #[test]
    #[should_panic]
    fn test_virt_addr_align_up_overflow() {
        let v = VirtAddr::new(0xffff_ffff_ffff_ffff).align_up(2u64);
    }

    #[test]
    #[should_panic]
    fn test_phys_addr_align_up_overflow() {
        PhysAddr::new(0x00ff_ffff_ffff_ffff).align_up(2u64);
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }
}
