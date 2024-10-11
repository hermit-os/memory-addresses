//! Physical and virtual addresses manipulation

use core::fmt;
#[cfg(feature = "step_trait")]
use core::iter::Step;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/// A canonical 64-bit virtual memory address.
///
/// This is a wrapper type around an `usize`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `usize` and `usize`.
///
/// On `x86_64`, only the 48 lower bits of a virtual address can be used. The top 16 bits need
/// to be copies of bit 47, i.e. the most significant bit. Addresses that fulfil this criterion
/// are called “canonical”. This type guarantees that it always represents a canonical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VirtAddr(usize);

/// A 64-bit physical memory address.
///
/// This is a wrapper type around an `usize`, so it is always 8 bytes, even when compiled
/// on non 64-bit systems. The
/// [`TryFrom`](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) trait can be used for performing conversions
/// between `usize` and `usize`.
///
/// On `x86_64`, only the 52 lower bits of a physical address can be used. The top 12 bits need
/// to be zero. This type guarantees that it always represents a valid physical address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PhysAddr(usize);

/// A passed `usize` was not a valid virtual address.
///
/// This means that bits 48 to 64 are not
/// a valid sign extension and are not null either. So automatic sign extension would have
/// overwritten possibly meaningful bits. This likely indicates a bug, for example an invalid
/// address calculation.
///
/// Contains the invalid address.
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

    /// Creates a new virtual address, without any checks.
    #[inline]
    pub const unsafe fn new_unsafe(addr: usize) -> VirtAddr {
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

    /// Convenience method for checking if a virtual address is null.
    #[inline]
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }

    /// Aligns the virtual address upwards to the given alignment.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        VirtAddr::new(align_up(self.0, align.into()))
    }

    /// Aligns the virtual address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        VirtAddr::new_truncate(align_down(self.0, align.into()))
    }

    /// Checks whether the virtual address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<usize>,
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

impl Add<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0 + rhs)
    }
}

impl AddAssign<usize> for VirtAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl Sub<usize> for VirtAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        VirtAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<usize> for VirtAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Sub<VirtAddr> for VirtAddr {
    type Output = usize;
    #[inline]
    fn sub(self, rhs: VirtAddr) -> Self::Output {
        self.0.checked_sub(rhs.0).unwrap()
    }
}

#[cfg(feature = "step_trait")]
impl Step for VirtAddr {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        end.0.checked_sub(start.0)
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        start.checked_add(count)
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        start.checked_sub(count)
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
        PhysAddr(addr % (1 << 52))
    }

    /// Creates a new physical address, without any checks.
    ///
    /// ## Safety
    ///
    /// You must make sure bits 52..64 are zero. This is not checked.
    #[inline]
    pub const unsafe fn new_unsafe(addr: usize) -> PhysAddr {
        PhysAddr(addr)
    }

    /// Tries to create a new physical address.
    ///
    /// Fails if any bits in the range 52 to 64 are set.
    #[inline]
    pub const fn try_new(addr: usize) -> Result<Self, PhysAddrNotValid> {
        Ok(Self(addr))
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
    ///
    /// # Panics
    ///
    /// This function panics if the resulting address has a bit in the range 52
    /// to 64 set.
    #[inline]
    pub fn align_up<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        PhysAddr::new(align_up(self.0, align.into()))
    }

    /// Aligns the physical address downwards to the given alignment.
    ///
    /// See the `align_down` function for more information.
    #[inline]
    pub fn align_down<U>(self, align: U) -> Self
    where
        U: Into<usize>,
    {
        Self(align_down(self.0, align.into()))
    }

    /// Checks whether the physical address has the demanded alignment.
    #[inline]
    pub fn is_aligned<U>(self, align: U) -> bool
    where
        U: Into<usize>,
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

impl Add<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0 + rhs)
    }
}

impl AddAssign<usize> for PhysAddr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

impl Sub<usize> for PhysAddr {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        PhysAddr::new(self.0.checked_sub(rhs).unwrap())
    }
}

impl SubAssign<usize> for PhysAddr {
    #[inline]
    fn sub_assign(&mut self, rhs: usize) {
        *self = *self - rhs;
    }
}

impl Sub<PhysAddr> for PhysAddr {
    type Output = usize;
    #[inline]
    fn sub(self, rhs: PhysAddr) -> Self::Output {
        self.0.checked_sub(rhs.0).unwrap()
    }
}

/// Align address downwards.
///
/// Returns the greatest `x` with alignment `align` so that `x <= addr`.
///
/// Panics if the alignment is not a power of two.
#[inline]
pub const fn align_down(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two(), "`align` must be a power of two");
    addr & !(align - 1)
}

/// Align address upwards.
///
/// Returns the smallest `x` with alignment `align` so that `x >= addr`.
///
/// Panics if the alignment is not a power of two or if an overflow occurs.
#[inline]
pub const fn align_up(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two(), "`align` must be a power of two");
    let align_mask = align - 1;
    if addr & align_mask == 0 {
        addr // already aligned
    } else {
        // FIXME: Replace with .expect, once `Option::expect` is const.
        if let Some(aligned) = (addr | align_mask).checked_add(1) {
            aligned
        } else {
            panic!("attempt to add with overflow")
        }
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
    #[cfg(feature = "step_trait")]
    fn virtaddr_step_forward() {
        assert_eq!(Step::forward(VirtAddr(0), 0), VirtAddr(0));
        assert_eq!(Step::forward(VirtAddr(0), 1), VirtAddr(1));
        assert_eq!(
            Step::forward(VirtAddr(0x7fff_ffff_ffff), 1),
            VirtAddr(0xffff_8000_0000_0000)
        );
        assert_eq!(
            Step::forward(VirtAddr(0xffff_8000_0000_0000), 1),
            VirtAddr(0xffff_8000_0000_0001)
        );
        assert_eq!(
            Step::forward_checked(VirtAddr(0xffff_ffff_ffff_ffff), 1),
            None
        );
        assert_eq!(
            Step::forward(VirtAddr(0x7fff_ffff_ffff), 0x1234_5678_9abd),
            VirtAddr(0xffff_9234_5678_9abc)
        );
        assert_eq!(
            Step::forward(VirtAddr(0x7fff_ffff_ffff), 0x8000_0000_0000),
            VirtAddr(0xffff_ffff_ffff_ffff)
        );
        assert_eq!(
            Step::forward(VirtAddr(0x7fff_ffff_ff00), 0x8000_0000_00ff),
            VirtAddr(0xffff_ffff_ffff_ffff)
        );
        assert_eq!(
            Step::forward_checked(VirtAddr(0x7fff_ffff_ff00), 0x8000_0000_0100),
            None
        );
        assert_eq!(
            Step::forward_checked(VirtAddr(0x7fff_ffff_ffff), 0x8000_0000_0001),
            None
        );
    }

    #[test]
    #[cfg(feature = "step_trait")]
    fn virtaddr_step_backward() {
        assert_eq!(Step::backward(VirtAddr(0), 0), VirtAddr(0));
        assert_eq!(Step::backward_checked(VirtAddr(0), 1), None);
        assert_eq!(Step::backward(VirtAddr(1), 1), VirtAddr(0));
        assert_eq!(
            Step::backward(VirtAddr(0xffff_8000_0000_0000), 1),
            VirtAddr(0x7fff_ffff_ffff)
        );
        assert_eq!(
            Step::backward(VirtAddr(0xffff_8000_0000_0001), 1),
            VirtAddr(0xffff_8000_0000_0000)
        );
        assert_eq!(
            Step::backward(VirtAddr(0xffff_9234_5678_9abc), 0x1234_5678_9abd),
            VirtAddr(0x7fff_ffff_ffff)
        );
        assert_eq!(
            Step::backward(VirtAddr(0xffff_8000_0000_0000), 0x8000_0000_0000),
            VirtAddr(0)
        );
        assert_eq!(
            Step::backward(VirtAddr(0xffff_8000_0000_0000), 0x7fff_ffff_ff01),
            VirtAddr(0xff)
        );
        assert_eq!(
            Step::backward_checked(VirtAddr(0xffff_8000_0000_0000), 0x8000_0000_0001),
            None
        );
    }

    #[test]
    #[cfg(feature = "step_trait")]
    fn virtaddr_steps_between() {
        assert_eq!(Step::steps_between(&VirtAddr(0), &VirtAddr(0)), Some(0));
        assert_eq!(Step::steps_between(&VirtAddr(0), &VirtAddr(1)), Some(1));
        assert_eq!(Step::steps_between(&VirtAddr(1), &VirtAddr(0)), None);
        assert_eq!(
            Step::steps_between(
                &VirtAddr(0x7fff_ffff_ffff),
                &VirtAddr(0xffff_8000_0000_0000)
            ),
            Some(1)
        );
        assert_eq!(
            Step::steps_between(
                &VirtAddr(0xffff_8000_0000_0000),
                &VirtAddr(0x7fff_ffff_ffff)
            ),
            None
        );
        assert_eq!(
            Step::steps_between(
                &VirtAddr(0xffff_8000_0000_0000),
                &VirtAddr(0xffff_8000_0000_0000)
            ),
            Some(0)
        );
        assert_eq!(
            Step::steps_between(
                &VirtAddr(0xffff_8000_0000_0000),
                &VirtAddr(0xffff_8000_0000_0001)
            ),
            Some(1)
        );
        assert_eq!(
            Step::steps_between(
                &VirtAddr(0xffff_8000_0000_0001),
                &VirtAddr(0xffff_8000_0000_0000)
            ),
            None
        );
    }

    #[test]
    pub fn test_align_up() {
        // align 1
        assert_eq!(align_up(0, 1), 0);
        assert_eq!(align_up(1234, 1), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_ffff, 1), 0xffff_ffff_ffff_ffff);
        // align 2
        assert_eq!(align_up(0, 2), 0);
        assert_eq!(align_up(1233, 2), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_fffe, 2), 0xffff_ffff_ffff_fffe);
        // address 0
        assert_eq!(align_up(0, 128), 0);
        assert_eq!(align_up(0, 1), 0);
        assert_eq!(align_up(0, 2), 0);
        assert_eq!(align_up(0, 0x8000_0000_0000_0000), 0);
    }

    #[test]
    fn test_virt_addr_align_up() {
        // Make sure the 47th bit is extended.
        assert_eq!(
            VirtAddr::new(0x7fff_ffff_ffff).align_up(2usize),
            VirtAddr::new(0x0000_8000_0000_0000)
        );
    }

    #[test]
    fn test_virt_addr_align_down() {
        // Make sure the 47th bit is extended.
        assert_eq!(
            VirtAddr::new(0xffff_8000_0000_0000).align_down(1usize << 48),
            VirtAddr::new(0)
        );
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }
}
