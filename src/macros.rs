//! Helper macros

/// Macro that implements the functionalities that every address type has.
/// Inspired/adopted from https://github.com/rust-vmm/vm-memory
macro_rules! impl_address {
    ($T:ident, $V:ty, $as_V:ident) => {
        impl $crate::MemoryAddress for $T {
            type RAW = $V;

            fn raw(self) -> Self::RAW {
                self.0
            }

            fn checked_add(self, rhs: Self::RAW) -> Option<Self> {
                Self::try_new(self.0.checked_add(rhs)?).ok()
            }

            fn checked_sub(self, rhs: Self::RAW) -> Option<Self> {
                Self::try_new(self.0.checked_sub(rhs)?).ok()
            }
        }

        impl $T {
            /// Creates a new address, without any checks.
            ///
            /// # Safety
            ///
            /// If `addr` does not comply with the platforms requirements for
            /// this address type, this can lead to UB in functions relying on
            /// the compliance or when using the requirements.
            #[inline]
            pub const unsafe fn new_unsafe(addr: $V) -> $T {
                $T(addr)
            }

            #[inline]
            /// Convenience method for checking if an address is null.
            pub const fn is_null(self) -> bool {
                self.0 == 0
            }

            /// Creates an address that points to `0`.
            #[inline]
            pub const fn zero() -> $T {
                $T::new(0)
            }

            #[doc = concat!("Converts the address to an `", stringify!($V), "`.")]
            #[inline]
            pub const fn $as_V(self) -> $V {
                self.0
            }
        }

        impl core::ops::Add<$V> for $T {
            type Output = Self;
            #[inline]
            fn add(self, rhs: $V) -> Self::Output {
                $T::new(self.0 + rhs)
            }
        }

        impl core::ops::AddAssign<$V> for $T {
            #[inline]
            fn add_assign(&mut self, rhs: $V) {
                *self = *self + rhs;
            }
        }

        impl core::ops::Sub<$V> for $T {
            type Output = Self;
            #[inline]
            fn sub(self, rhs: $V) -> Self::Output {
                $T::new(self.0.checked_sub(rhs).unwrap())
            }
        }

        impl core::ops::SubAssign<$V> for $T {
            #[inline]
            fn sub_assign(&mut self, rhs: $V) {
                *self = *self - rhs;
            }
        }

        impl core::ops::Sub<$T> for $T {
            type Output = $V;
            #[inline]
            fn sub(self, rhs: $T) -> Self::Output {
                self.$as_V().checked_sub(rhs.$as_V()).unwrap()
            }
        }

        impl core::ops::BitOr<$V> for $T {
            type Output = $V;
            #[inline]
            fn bitor(self, rhs: $V) -> Self::Output {
                self.0 | rhs
            }
        }

        impl core::ops::BitOrAssign<$V> for $T {
            #[inline]
            fn bitor_assign(&mut self, rhs: $V) {
                *self = Self::new_truncate(self.0 | rhs);
            }
        }

        impl core::ops::BitAnd<$V> for $T {
            type Output = $V;
            #[inline]
            fn bitand(self, rhs: $V) -> Self::Output {
                self.0 & rhs
            }
        }

        impl core::ops::BitAndAssign<$V> for $T {
            #[inline]
            fn bitand_assign(&mut self, rhs: $V) {
                *self = Self::new_truncate(self.0 & rhs);
            }
        }

        impl core::ops::BitXor<$V> for $T {
            type Output = $V;
            #[inline]
            fn bitxor(self, rhs: $V) -> Self::Output {
                self.0 ^ rhs
            }
        }

        impl core::ops::BitXorAssign<$V> for $T {
            #[inline]
            fn bitxor_assign(&mut self, rhs: $V) {
                *self = Self::new_truncate(self.0 ^ rhs);
            }
        }

        impl core::ops::Shl<usize> for $T {
            type Output = $T;
            #[inline]
            fn shl(self, rhs: usize) -> Self::Output {
                Self::new_truncate(self.0 << rhs)
            }
        }

        impl core::ops::Shr<usize> for $T {
            type Output = $T;
            #[inline]
            fn shr(self, rhs: usize) -> Self::Output {
                Self::new_truncate(self.0 >> rhs)
            }
        }

        impl core::ops::ShlAssign<usize> for $T {
            #[inline]
            fn shl_assign(&mut self, rhs: usize) {
                *self = Self::new_truncate(self.0 << rhs);
            }
        }

        impl core::ops::ShrAssign<usize> for $T {
            #[inline]
            fn shr_assign(&mut self, rhs: usize) {
                *self = Self::new_truncate(self.0 >> rhs);
            }
        }

        impl From<$V> for $T {
            #[inline]
            fn from(addr: $V) -> $T {
                Self::new_truncate(addr)
            }
        }

        impl core::fmt::Debug for $T {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.debug_tuple(stringify!($T))
                    .field(&format_args!("{:#x}", self.0))
                    .finish()
            }
        }

        impl core::fmt::Binary for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Binary::fmt(&self.0, f)
            }
        }

        impl core::fmt::LowerHex for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::LowerHex::fmt(&self.0, f)
            }
        }

        impl core::fmt::Octal for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Octal::fmt(&self.0, f)
            }
        }

        impl core::fmt::UpperHex for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::UpperHex::fmt(&self.0, f)
            }
        }

        impl core::fmt::Pointer for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Pointer::fmt(&(self.0 as *const ()), f)
            }
        }
    };
}

pub(crate) use impl_address;
