//! # Overview
//!
//! generic_once_cell is a generic `no_std` version of [once_cell].
//! Internal synchronization for initialization is provided as type parameter via custom mutexes based on [lock_api].
//! This makes it suitable for use in complex `no_std` scenarios where [once_cell's `critical-section` support] and [`once_cell::race`] are not sufficient.
//!
//! The core API looks *roughly* like this:
//! ```rust,ignore
//! impl<R: lock_api::RawMutex, T> OnceCell<R, T> {
//!     const fn new() -> Self { ... }
//!     fn set(&self, value: T) -> Result<(), T> { ... }
//!     fn get(&self) -> Option<&T> { ... }
//! }
//! ```
//!
//! # API
//!
//! Apart from the generic type parameter, this crate has exactly [once_cell]'s API.
//!
//! # Mutex implementations
//!
//! You can plug in any implementation of [`lock_api::RawMutex`].
//!
//! Different usable mutex implementations are available in crates:
//! * [spinning-top] from Rust OSDev.
//! * [spin], though you might prefer [`spin::once::Once`] and [`spin::lazy::Lazy`].
//! * [parking_lot], though you might prefer the original [once_cell].
//!
//! This crate shows its real strength when using custom, specialized mutex implementations though.
//!
//! # Performance
//!
//! The mutex is only used for initialization.
//! Once initialized, the overhead for each access is to check an `AtomicBool`.
//!
//! [once_cell]: https://crates.io/crates/once_cell
//! [lock_api]: https://crates.io/crates/lock_api
//! [once_cell's `critical-section` support]: https://github.com/matklad/once_cell/blob/master/CHANGELOG.md#1160
//! [`once_cell::race`]: https://docs.rs/once_cell/1.16.0/once_cell/race/index.html
//! [spinning-top]: https://crates.io/crates/spinning_top
//! [spin]: https://crates.io/crates/spin
//! [`spin::once::Once`]: https://docs.rs/spin/0.9.4/spin/once/struct.Once.html
//! [`spin::lazy::Lazy`]: https://docs.rs/spin/0.9.4/spin/lazy/struct.Lazy.html
//! [parking_lot]: https://crates.io/crates/parking_lot

#![no_std]
#![warn(unsafe_op_in_unsafe_fn)]

mod imp;

use core::{
    cell::Cell,
    fmt, mem,
    ops::{Deref, DerefMut},
    panic::RefUnwindSafe,
};

use imp::OnceCell as Imp;
use lock_api::RawMutex;

/// A thread-safe cell which can be written to only once.
///
/// `OnceCell` provides `&` references to the contents without RAII guards.
///
/// Reading a non-`None` value out of `OnceCell` establishes a
/// happens-before relationship with a corresponding write. For example, if
/// thread A initializes the cell with `get_or_init(f)`, and thread B
/// subsequently reads the result of this call, B also observes all the side
/// effects of `f`.
///
/// # Example
/// ```
/// # use parking_lot::RawMutex;
/// use generic_once_cell::OnceCell;
///
/// static CELL: OnceCell<RawMutex, String> = OnceCell::new();
/// assert!(CELL.get().is_none());
///
/// std::thread::spawn(|| {
///     let value: &String = CELL.get_or_init(|| {
///         "Hello, World!".to_string()
///     });
///     assert_eq!(value, "Hello, World!");
/// }).join().unwrap();
///
/// let value: Option<&String> = CELL.get();
/// assert!(value.is_some());
/// assert_eq!(value.unwrap().as_str(), "Hello, World!");
/// ```
pub struct OnceCell<R, T>(Imp<R, T>);

impl<R: RawMutex, T> Default for OnceCell<R, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<R: RawMutex, T: fmt::Debug> fmt::Debug for OnceCell<R, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get() {
            Some(v) => f.debug_tuple("OnceCell").field(v).finish(),
            None => f.write_str("OnceCell(Uninit)"),
        }
    }
}

impl<R: RawMutex, T: Clone> Clone for OnceCell<R, T> {
    fn clone(&self) -> Self {
        match self.get() {
            Some(value) => Self::with_value(value.clone()),
            None => Self::new(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        match (self.get_mut(), source.get()) {
            (Some(this), Some(source)) => this.clone_from(source),
            _ => *self = source.clone(),
        }
    }
}

impl<R: RawMutex, T> From<T> for OnceCell<R, T> {
    fn from(value: T) -> Self {
        Self::with_value(value)
    }
}

impl<R: RawMutex, T: PartialEq> PartialEq for OnceCell<R, T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<R: RawMutex, T: Eq> Eq for OnceCell<R, T> {}

impl<R: RawMutex, T> OnceCell<R, T> {
    /// Creates a new empty cell.
    pub const fn new() -> Self {
        Self(Imp::new())
    }

    /// Creates a new initialized cell.
    pub const fn with_value(value: T) -> Self {
        Self(Imp::with_value(value))
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty, or being initialized. This
    /// method never blocks.
    pub fn get(&self) -> Option<&T> {
        if self.0.is_initialized() {
            // Safe b/c value is initialized.
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    ///
    /// This method is allowed to violate the invariant of writing to a `OnceCell`
    /// at most once because it requires `&mut` access to `self`. As with all
    /// interior mutability, `&mut` access permits arbitrary modification:
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let mut cell: OnceCell<RawMutex, u32> = OnceCell::new();
    /// cell.set(92).unwrap();
    /// cell = OnceCell::new();
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.0.get_mut()
    }

    /// Get the reference to the underlying value, without checking if the
    /// cell is initialized.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the cell is in initialized state, and that
    /// the contents are acquired by (synchronized to) this thread.
    #[inline]
    pub unsafe fn get_unchecked(&self) -> &T {
        // SAFETY: The caller ensures that the value is initialized and access synchronized.
        unsafe { self.0.get_unchecked() }
    }

    /// Sets the contents of this cell to `value`.
    ///
    /// Returns `Ok(())` if the cell was empty and `Err(value)` if it was
    /// full.
    ///
    /// # Example
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// static CELL: OnceCell<RawMutex, i32> = OnceCell::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.set(92), Ok(()));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.set(62), Err(62));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    pub fn set(&self, value: T) -> Result<(), T> {
        match self.try_insert(value) {
            Ok(_) => Ok(()),
            Err((_, value)) => Err(value),
        }
    }

    /// Like [`set`](Self::set), but also returns a reference to the final cell value.
    ///
    /// # Example
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let cell = OnceCell::<RawMutex, _>::new();
    /// assert!(cell.get().is_none());
    ///
    /// assert_eq!(cell.try_insert(92), Ok(&92));
    /// assert_eq!(cell.try_insert(62), Err((&92, 62)));
    ///
    /// assert!(cell.get().is_some());
    /// ```
    pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
        let mut value = Some(value);
        let res = self.get_or_init(|| unsafe { value.take().unwrap_unchecked() });
        match value {
            None => Ok(res),
            Some(value) => Err((res, value)),
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if the cell
    /// was empty.
    ///
    /// Many threads may call `get_or_init` concurrently with different
    /// initializing functions, but it is guaranteed that only one function
    /// will be executed.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. The
    /// exact outcome is unspecified. Current implementation deadlocks, but
    /// this may be changed to a panic in the future.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let cell = OnceCell::<RawMutex, _>::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        enum Void {}
        match self.get_or_try_init(|| Ok::<T, Void>(f())) {
            Ok(val) => val,
            Err(void) => match void {},
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and
    /// the cell remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`.
    /// The exact outcome is unspecified. Current implementation
    /// deadlocks, but this may be changed to a panic in the future.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let cell = OnceCell::<RawMutex, _>::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // Fast path check
        if let Some(value) = self.get() {
            return Ok(value);
        }

        self.0.initialize(f)?;

        // Safe b/c value is initialized.
        debug_assert!(self.0.is_initialized());
        Ok(unsafe { self.get_unchecked() })
    }

    /// Takes the value out of this `OnceCell`, moving it back to an uninitialized state.
    ///
    /// Has no effect and returns `None` if the `OnceCell` hasn't been initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let mut cell: OnceCell<RawMutex, String> = OnceCell::new();
    /// assert_eq!(cell.take(), None);
    ///
    /// let mut cell = OnceCell::<RawMutex, _>::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.take(), Some("hello".to_string()));
    /// assert_eq!(cell.get(), None);
    /// ```
    ///
    /// This method is allowed to violate the invariant of writing to a `OnceCell`
    /// at most once because it requires `&mut` access to `self`. As with all
    /// interior mutability, `&mut` access permits arbitrary modification:
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let mut cell: OnceCell<RawMutex, u32> = OnceCell::new();
    /// cell.set(92).unwrap();
    /// cell = OnceCell::new();
    /// ```
    pub fn take(&mut self) -> Option<T> {
        mem::take(self).into_inner()
    }

    /// Consumes the `OnceCell`, returning the wrapped value. Returns
    /// `None` if the cell was empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::OnceCell;
    ///
    /// let cell: OnceCell<RawMutex, String> = OnceCell::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = OnceCell::<RawMutex, _>::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    #[inline]
    pub fn into_inner(self) -> Option<T> {
        self.0.into_inner()
    }
}

/// A value which is initialized on the first access.
///
/// This type is thread-safe and can be used in statics.
///
/// # Example
///
/// ```
/// # use parking_lot::RawMutex;
/// use std::collections::HashMap;
///
/// use generic_once_cell::Lazy;
///
/// static HASHMAP: Lazy<RawMutex, HashMap<i32, String>> = Lazy::new(|| {
///     println!("initializing");
///     let mut m = HashMap::new();
///     m.insert(13, "Spica".to_string());
///     m.insert(74, "Hoyten".to_string());
///     m
/// });
///
/// fn main() {
///     println!("ready");
///     std::thread::spawn(|| {
///         println!("{:?}", HASHMAP.get(&13));
///     }).join().unwrap();
///     println!("{:?}", HASHMAP.get(&74));
///
///     // Prints:
///     //   ready
///     //   initializing
///     //   Some("Spica")
///     //   Some("Hoyten")
/// }
/// ```
pub struct Lazy<R, T, F = fn() -> T> {
    cell: OnceCell<R, T>,
    init: Cell<Option<F>>,
}

impl<R: RawMutex, T: fmt::Debug, F> fmt::Debug for Lazy<R, T, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Lazy")
            .field("cell", &self.cell)
            .field("init", &"..")
            .finish()
    }
}

// We never create a `&F` from a `&Lazy<T, F>` so it is fine to not impl
// `Sync` for `F`. We do create a `&mut Option<F>` in `force`, but this is
// properly synchronized, so it only happens once so it also does not
// contribute to this impl.
unsafe impl<R, T, F: Send> Sync for Lazy<R, T, F> where OnceCell<R, T>: Sync {}
// auto-derived `Send` impl is OK.

impl<R, T, F: RefUnwindSafe> RefUnwindSafe for Lazy<R, T, F> where OnceCell<R, T>: RefUnwindSafe {}

impl<R: RawMutex, T, F> Lazy<R, T, F> {
    /// Creates a new lazy value with the given initializing
    /// function.
    pub const fn new(f: F) -> Self {
        Self {
            cell: OnceCell::new(),
            init: Cell::new(Some(f)),
        }
    }

    /// Consumes this `Lazy` returning the stored value.
    ///
    /// Returns `Ok(value)` if `Lazy` is initialized and `Err(f)` otherwise.
    pub fn into_value(this: Lazy<R, T, F>) -> Result<T, F> {
        let cell = this.cell;
        let init = this.init;
        cell.into_inner().ok_or_else(|| {
            init.take()
                .unwrap_or_else(|| panic!("Lazy instance has previously been poisoned"))
        })
    }
}

impl<R: RawMutex, T, F: FnOnce() -> T> Lazy<R, T, F> {
    /// Forces the evaluation of this lazy value and
    /// returns a reference to the result. This is equivalent
    /// to the `Deref` impl, but is explicit.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::Lazy;
    ///
    /// let lazy = Lazy::<RawMutex, _>::new(|| 92);
    ///
    /// assert_eq!(Lazy::force(&lazy), &92);
    /// assert_eq!(&*lazy, &92);
    /// ```
    pub fn force(this: &Self) -> &T {
        this.cell.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }

    /// Forces the evaluation of this lazy value and
    /// returns a mutable reference to the result. This is equivalent
    /// to the `Deref` impl, but is explicit.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::Lazy;
    ///
    /// let mut lazy = Lazy::<RawMutex, _>::new(|| 92);
    ///
    /// assert_eq!(Lazy::force_mut(&mut lazy), &mut 92);
    /// ```
    pub fn force_mut(this: &mut Self) -> &mut T {
        Self::force(this);
        Self::get_mut(this).unwrap_or_else(|| unreachable!())
    }

    /// Gets the reference to the result of this lazy value if
    /// it was initialized, otherwise returns `None`.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::Lazy;
    ///
    /// let lazy = Lazy::<RawMutex, _>::new(|| 92);
    ///
    /// assert_eq!(Lazy::get(&lazy), None);
    /// assert_eq!(&*lazy, &92);
    /// assert_eq!(Lazy::get(&lazy), Some(&92));
    /// ```
    pub fn get(this: &Self) -> Option<&T> {
        this.cell.get()
    }

    /// Gets the reference to the result of this lazy value if
    /// it was initialized, otherwise returns `None`.
    ///
    /// # Example
    /// ```
    /// # use parking_lot::RawMutex;
    /// use generic_once_cell::Lazy;
    ///
    /// let mut lazy = Lazy::<RawMutex, _>::new(|| 92);
    ///
    /// assert_eq!(Lazy::get_mut(&mut lazy), None);
    /// assert_eq!(&*lazy, &92);
    /// assert_eq!(Lazy::get_mut(&mut lazy), Some(&mut 92));
    /// ```
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        this.cell.get_mut()
    }
}

impl<R: RawMutex, T, F: FnOnce() -> T> Deref for Lazy<R, T, F> {
    type Target = T;
    fn deref(&self) -> &T {
        Self::force(self)
    }
}

impl<R: RawMutex, T, F: FnOnce() -> T> DerefMut for Lazy<R, T, F> {
    fn deref_mut(&mut self) -> &mut T {
        Self::force(self);
        self.cell.get_mut().unwrap_or_else(|| unreachable!())
    }
}

impl<R: RawMutex, T: Default> Default for Lazy<R, T> {
    /// Creates a new lazy value using `Default` as the initializing function.
    fn default() -> Self {
        Self::new(T::default)
    }
}

/// ```compile_fail
/// struct S(*mut ());
/// unsafe impl Sync for S {}
///
/// fn share<T: Sync>(_: &T) {}
/// share(&generic_once_cell::OnceCell::<parking_lot::RawMutex, S>::new());
/// ```
///
/// ```compile_fail
/// struct S(*mut ());
/// unsafe impl Sync for S {}
///
/// fn share<T: Sync>(_: &T) {}
/// share(&generic_once_cell::Lazy::<parking_lot::RawMutex, S>::new(|| unimplemented!()));
/// ```
///
/// ```compile_fail
/// struct M(core::marker::PhantomData<*mut ()>);
///
/// unsafe impl lock_api::RawMutex for M {
///     const INIT: Self = M(core::marker::PhantomData);
///     type GuardMarker = lock_api::GuardNoSend;
///     fn lock(&self) {}
///     fn try_lock(&self) -> bool { unimplemented!() }
///     unsafe fn unlock(&self) {}
/// }
///
/// fn share<T: Sync>(_: &T) {}
/// share(&generic_once_cell::OnceCell::<M, ()>::new());
/// ```
///
/// ```compile_fail
/// struct M(core::marker::PhantomData<*mut ()>);
///
/// unsafe impl lock_api::RawMutex for M {
///     const INIT: Self = M(core::marker::PhantomData);
///     type GuardMarker = lock_api::GuardNoSend;
///     fn lock(&self) {}
///     fn try_lock(&self) -> bool { unimplemented!() }
///     unsafe fn unlock(&self) {}
/// }
///
/// fn share<T: Sync>(_: &T) {}
/// share(&generic_once_cell::Lazy::<M, ()>::new(|| unimplemented!()));
/// ```
fn _dummy() {}
