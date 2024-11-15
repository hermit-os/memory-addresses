//! Physical and virtual addresses manipulation

use crate::impl_address;
use core::fmt;

use align_address::Align;

/// A virtual memory address on `aarch64`.
///
/// In exception level (EL) 0  and EL1 the virtual address space ranges from `0` till
/// `0x000f_ffff_ffff_ffff`, as well as from `0xfff0_0000_0000_0000` to `0xffff_ffff_ffff_ffff`.
/// This type enforces this limit.
/// However, there are more restrictions (e.g., execption level 3 has only one address space)
/// that are not encoded in this type.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VirtAddr(u64);

impl_address!(VirtAddr, u64);

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

    #[cfg(target_pointer_width = "64")]
    // if the target_pointer_width is 64, usize = u64 so we can safely transform.
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
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

#[cfg(target_pointer_width = "64")]
// if the target_pointer_width is 64, usize = u64 so we can safely transform.
impl From<usize> for PhysAddr {
    fn from(addr: usize) -> PhysAddr {
        Self::new_truncate(addr as u64)
    }
}

/// A physical memory address.
///
/// The size of a valid physical address on aarch64 is implementation defined, but since Armv9.3
/// not larger than 56 bits. This type enforces this limit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PhysAddr(u64);

impl_address!(PhysAddr, u64);

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

    #[cfg(target_pointer_width = "64")]
    // if the target_pointer_width is 64, usize = u64 so we can safely transform.
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
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

impl Align<u64> for PhysAddr {
    #[inline]
    fn align_down(self, align: u64) -> Self {
        Self::new(self.0.align_down(align))
    }

    #[inline]
    fn align_up(self, align: u64) -> Self {
        Self::new(self.0.align_up(align))
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
        let _ = VirtAddr::new(0xffff_ffff_ffff_ffff).align_up(2u64);
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
