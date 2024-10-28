/// Universal crate for machine address types.
use num::traits::{int::PrimInt, ToBytes};
use std::ops::{BitAnd, BitOr};

pub mod arch;

#[cfg(target_arch = "x86_64")]
pub use crate::arch::x86_64::{PhysAddr, VirtAddr};

#[cfg(not(any(target_arch = "x86_64")))]
pub use crate::arch::fallback::{PhysAddr, VirtAddr};

/// Align number upwards.
///
/// Returns the smallest `x` with alignment `align` so that `x >= addr`.
///
/// Panics if the alignment is not a power of two or if an overflow occurs.
// TODO: Make const one day
#[inline]
pub fn align_up<T: PrimInt + ToBytes + BitAnd + BitOr>(addr: T, align: T) -> T
{
    assert_eq!(align.count_ones(), 1, "`align` must be a power of two");
    let align_mask = align.checked_sub(&T::one()).unwrap();
    if addr & align_mask == T::zero() {
        addr // already aligned
    } else {
        if let Some(aligned) = (addr | align_mask).checked_add(&T::one()) {
            aligned
        } else {
            panic!("attempt to add with overflow")
        }
    }
}

/// Align number downwards.
///
/// Returns the greatest `x` with alignment `align` so that `x <= addr`.
///
/// Panics if the alignment is not a power of two.
#[inline]
pub fn align_down<T: PrimInt>(addr: T, align: T) -> T {
    assert_eq!(align.count_ones(), 1, "`align` must be a power of two");
    addr & !(align - T::one())
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
    pub fn test_align_up() {
        // align 1
        assert_eq!(align_up(1, 1), 1);
        assert_eq!(align_up(1234, 1), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_ffff_u64, 1), 0xffff_ffff_ffff_ffff);
        // align 2
        assert_eq!(align_up(1, 2), 2);
        assert_eq!(align_up(1233, 2), 1234);
        assert_eq!(align_up(0xffff_ffff_ffff_fffe_u64, 2), 0xffff_ffff_ffff_fffe);
        // align 4096
        assert_eq!(align_up(0x1234_1234, 0x1000), 0x1234_2000);
        // address 0
        assert_eq!(align_up(0, 128), 0);
        assert_eq!(align_up(0, 1), 0);
        assert_eq!(align_up(0, 2), 0);
        assert_eq!(align_up(0, 0x8000_0000_0000_0000_u64), 0);
    }

    #[test]
    pub fn test_align_down() {
        // align 1
        assert_eq!(align_down(0, 1), 0);
        assert_eq!(align_down(1234, 1), 1234);
        assert_eq!(align_down(0xffff_ffff_ffff_ffff_u64, 1), 0xffff_ffff_ffff_ffff);
        // align 2
        assert_eq!(align_down(0, 2), 0);
        assert_eq!(align_down(1233, 2), 1232);
        assert_eq!(align_down(0xffff_ffff_ffff_fffe_u64, 2), 0xffff_ffff_ffff_fffe);
        assert_eq!(align_down(0xffff_ffff_ffff_ffff_u64, 2), 0xffff_ffff_ffff_fffe);
        // align 4096
        assert_eq!(align_down(0x1234_1234, 0x1000), 0x1234_1000);
        // address 0
        assert_eq!(align_down(0, 128), 0);
        assert_eq!(align_down(0, 1), 0);
        assert_eq!(align_down(0, 2), 0);
        assert_eq!(align_down(0, 0x8000_0000_0000_0000_u64), 0);
    }

    #[test]
    fn test_from_ptr_array() {
        let slice = &[1, 2, 3, 4, 5];
        // Make sure that from_ptr(slice) is the address of the first element
        assert_eq!(VirtAddr::from_ptr(slice), VirtAddr::from_ptr(&slice[0]));
    }
}
