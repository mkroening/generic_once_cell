use core::{
    panic::{RefUnwindSafe, UnwindSafe},
    sync::atomic::{AtomicBool, Ordering},
};

use lock_api::{Mutex, RawMutex};

pub(crate) struct OnceCell<R, T> {
    initialized: AtomicBool,
    value: Mutex<R, Option<T>>,
}

impl<R, T> RefUnwindSafe for OnceCell<R, T>
where
    R: RefUnwindSafe + UnwindSafe,
    T: RefUnwindSafe + UnwindSafe,
{
}
impl<R, T> UnwindSafe for OnceCell<R, T>
where
    R: UnwindSafe,
    T: UnwindSafe,
{
}

impl<R: RawMutex, T> OnceCell<R, T> {
    pub(crate) const fn new() -> Self {
        Self {
            initialized: AtomicBool::new(false),
            value: Mutex::new(None),
        }
    }

    pub(crate) const fn with_value(value: T) -> Self {
        Self {
            initialized: AtomicBool::new(true),
            value: Mutex::new(Some(value)),
        }
    }

    #[inline]
    pub(crate) fn is_initialized(&self) -> bool {
        self.initialized.load(Ordering::Acquire)
    }

    #[cold]
    pub(crate) fn initialize<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let mut guard = self.value.lock();
        if guard.is_none() {
            *guard = Some(f()?);
            self.initialized.store(true, Ordering::Release);
        }
        Ok(())
    }

    /// Get the reference to the underlying value, without checking if the cell
    /// is initialized.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the cell is in initialized state, and that
    /// the contents are acquired by (synchronized to) this thread.
    pub(crate) unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.is_initialized());
        // SAFETY: The caller ensures that the value is initialized and access synchronized.
        unsafe { (*self.value.data_ptr()).as_ref().unwrap_unchecked() }
    }

    #[inline]
    pub(crate) fn get_mut(&mut self) -> Option<&mut T> {
        self.value.get_mut().as_mut()
    }

    #[inline]
    pub(crate) fn into_inner(self) -> Option<T> {
        self.value.into_inner()
    }
}
