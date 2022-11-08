use std::sync::{
    atomic::{AtomicUsize, Ordering::SeqCst},
    Barrier,
};

use crossbeam_utils::thread::scope;
use parking_lot::RawMutex;

use generic_once_cell::{Lazy, OnceCell};

#[test]
fn once_cell() {
    let c = OnceCell::<RawMutex, _>::new();
    assert!(c.get().is_none());
    scope(|s| {
        s.spawn(|_| {
            c.get_or_init(|| 92);
            assert_eq!(c.get(), Some(&92));
        });
    })
    .unwrap();
    c.get_or_init(|| panic!("Kabom!"));
    assert_eq!(c.get(), Some(&92));
}

#[test]
fn once_cell_with_value() {
    static CELL: OnceCell<RawMutex, i32> = OnceCell::with_value(12);
    assert_eq!(CELL.get(), Some(&12));
}

#[test]
fn once_cell_get_mut() {
    let mut c = OnceCell::<RawMutex, _>::new();
    assert!(c.get_mut().is_none());
    c.set(90).unwrap();
    *c.get_mut().unwrap() += 2;
    assert_eq!(c.get_mut(), Some(&mut 92));
}

#[test]
fn once_cell_get_unchecked() {
    let c = OnceCell::<RawMutex, _>::new();
    c.set(92).unwrap();
    unsafe {
        assert_eq!(c.get_unchecked(), &92);
    }
}

#[test]
fn once_cell_drop() {
    static DROP_CNT: AtomicUsize = AtomicUsize::new(0);
    struct Dropper;
    impl Drop for Dropper {
        fn drop(&mut self) {
            DROP_CNT.fetch_add(1, SeqCst);
        }
    }

    let x = OnceCell::<RawMutex, _>::new();
    scope(|s| {
        s.spawn(|_| {
            x.get_or_init(|| Dropper);
            assert_eq!(DROP_CNT.load(SeqCst), 0);
            drop(x);
        });
    })
    .unwrap();
    assert_eq!(DROP_CNT.load(SeqCst), 1);
}

#[test]
fn once_cell_drop_empty() {
    let x = OnceCell::<RawMutex, String>::new();
    drop(x);
}

#[test]
fn clone() {
    let s = OnceCell::<RawMutex, _>::new();
    let c = s.clone();
    assert!(c.get().is_none());

    s.set("hello".to_string()).unwrap();
    let c = s.clone();
    assert_eq!(c.get().map(String::as_str), Some("hello"));
}

#[test]
fn get_or_try_init() {
    let cell: OnceCell<RawMutex, String> = OnceCell::new();
    assert!(cell.get().is_none());

    let res = std::panic::catch_unwind(|| cell.get_or_try_init(|| -> Result<_, ()> { panic!() }));
    assert!(res.is_err());
    assert!(cell.get().is_none());

    assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));

    assert_eq!(
        cell.get_or_try_init(|| Ok::<_, ()>("hello".to_string())),
        Ok(&"hello".to_string())
    );
    assert_eq!(cell.get(), Some(&"hello".to_string()));
}

#[test]
fn from_impl() {
    assert_eq!(OnceCell::<RawMutex, _>::from("value").get(), Some(&"value"));
    assert_ne!(OnceCell::<RawMutex, _>::from("foo").get(), Some(&"bar"));
}

#[test]
fn partialeq_impl() {
    assert!(OnceCell::<RawMutex, _>::from("value") == OnceCell::from("value"));
    assert!(OnceCell::<RawMutex, _>::from("foo") != OnceCell::from("bar"));

    assert!(OnceCell::<RawMutex, String>::new() == OnceCell::new());
    assert!(OnceCell::<RawMutex, String>::new() != OnceCell::from("value".to_owned()));
}

#[test]
fn into_inner() {
    let cell: OnceCell<RawMutex, String> = OnceCell::new();
    assert_eq!(cell.into_inner(), None);
    let cell = OnceCell::<RawMutex, _>::new();
    cell.set("hello".to_string()).unwrap();
    assert_eq!(cell.into_inner(), Some("hello".to_string()));
}

#[test]
fn debug_impl() {
    let cell = OnceCell::<RawMutex, _>::new();
    assert_eq!(format!("{:#?}", cell), "OnceCell(Uninit)");
    cell.set(vec!["hello", "world"]).unwrap();
    assert_eq!(
        format!("{:#?}", cell),
        r#"OnceCell(
    [
        "hello",
        "world",
    ],
)"#
    );
}

#[test]
fn lazy_new() {
    let called = AtomicUsize::new(0);
    let x = Lazy::<RawMutex, _, _>::new(|| {
        called.fetch_add(1, SeqCst);
        92
    });

    assert_eq!(called.load(SeqCst), 0);

    scope(|s| {
        s.spawn(|_| {
            let y = *x - 30;
            assert_eq!(y, 62);
            assert_eq!(called.load(SeqCst), 1);
        });
    })
    .unwrap();

    let y = *x - 30;
    assert_eq!(y, 62);
    assert_eq!(called.load(SeqCst), 1);
}

#[test]
fn lazy_deref_mut() {
    let called = AtomicUsize::new(0);
    let mut x = Lazy::<RawMutex, _, _>::new(|| {
        called.fetch_add(1, SeqCst);
        92
    });

    assert_eq!(called.load(SeqCst), 0);

    let y = *x - 30;
    assert_eq!(y, 62);
    assert_eq!(called.load(SeqCst), 1);

    *x /= 2;
    assert_eq!(*x, 46);
    assert_eq!(called.load(SeqCst), 1);
}

#[test]
fn lazy_default() {
    static CALLED: AtomicUsize = AtomicUsize::new(0);

    struct Foo(u8);
    impl Default for Foo {
        fn default() -> Self {
            CALLED.fetch_add(1, SeqCst);
            Foo(42)
        }
    }

    let lazy: Lazy<RawMutex, std::sync::Mutex<Foo>> = <_>::default();

    assert_eq!(CALLED.load(SeqCst), 0);

    assert_eq!(lazy.lock().unwrap().0, 42);
    assert_eq!(CALLED.load(SeqCst), 1);

    lazy.lock().unwrap().0 = 21;

    assert_eq!(lazy.lock().unwrap().0, 21);
    assert_eq!(CALLED.load(SeqCst), 1);
}

#[test]
fn static_lazy() {
    static XS: Lazy<RawMutex, Vec<i32>> = Lazy::new(|| {
        let mut xs = Vec::new();
        xs.push(1);
        xs.push(2);
        xs.push(3);
        xs
    });
    scope(|s| {
        s.spawn(|_| {
            assert_eq!(&*XS, &vec![1, 2, 3]);
        });
    })
    .unwrap();
    assert_eq!(&*XS, &vec![1, 2, 3]);
}

#[test]
fn static_lazy_via_fn() {
    fn xs() -> &'static Vec<i32> {
        static XS: OnceCell<RawMutex, Vec<i32>> = OnceCell::new();
        XS.get_or_init(|| {
            let mut xs = Vec::new();
            xs.push(1);
            xs.push(2);
            xs.push(3);
            xs
        })
    }
    assert_eq!(xs(), &vec![1, 2, 3]);
}

#[test]
fn lazy_into_value() {
    let l: Lazy<RawMutex, i32, _> = Lazy::new(|| panic!());
    assert!(matches!(Lazy::into_value(l), Err(_)));
    let l = Lazy::<RawMutex, _>::new(|| -> i32 { 92 });
    Lazy::force(&l);
    assert!(matches!(Lazy::into_value(l), Ok(92)));
}

#[test]
fn lazy_poisoning() {
    let x: Lazy<RawMutex, String> = Lazy::new(|| panic!("kaboom"));
    for _ in 0..2 {
        let res = std::panic::catch_unwind(|| x.len());
        assert!(res.is_err());
    }
}

#[test]
fn once_cell_is_sync_send() {
    fn assert_traits<T: Send + Sync>() {}
    assert_traits::<OnceCell<RawMutex, String>>();
    assert_traits::<Lazy<RawMutex, String>>();
}

#[test]
fn eval_once_macro() {
    macro_rules! eval_once {
            (|| -> $ty:ty {
                $($body:tt)*
            }) => {{
                static ONCE_CELL: OnceCell<RawMutex, $ty> = OnceCell::new();
                fn init() -> $ty {
                    $($body)*
                }
                ONCE_CELL.get_or_init(init)
            }};
        }

    let fib: &'static Vec<i32> = eval_once! {
        || -> Vec<i32> {
            let mut res = vec![1, 1];
            for i in 0..10 {
                let next = res[i] + res[i + 1];
                res.push(next);
            }
            res
        }
    };
    assert_eq!(fib[5], 8)
}

#[test]
fn once_cell_does_not_leak_partially_constructed_boxes() {
    let n_tries = if cfg!(miri) { 10 } else { 100 };
    let n_readers = 10;
    let n_writers = 3;
    const MSG: &str = "Hello, World";

    for _ in 0..n_tries {
        let cell: OnceCell<RawMutex, String> = OnceCell::new();
        scope(|scope| {
            for _ in 0..n_readers {
                scope.spawn(|_| loop {
                    if let Some(msg) = cell.get() {
                        assert_eq!(msg, MSG);
                        break;
                    }
                });
            }
            for _ in 0..n_writers {
                let _ = scope.spawn(|_| cell.set(MSG.to_owned()));
            }
        })
        .unwrap()
    }
}

#[test]
fn get_does_not_block() {
    let cell = OnceCell::<RawMutex, _>::new();
    let barrier = Barrier::new(2);
    scope(|scope| {
        scope.spawn(|_| {
            cell.get_or_init(|| {
                barrier.wait();
                barrier.wait();
                "hello".to_string()
            });
        });
        barrier.wait();
        assert_eq!(cell.get(), None);
        barrier.wait();
    })
    .unwrap();
    assert_eq!(cell.get(), Some(&"hello".to_string()));
}

#[test]
// https://github.com/rust-lang/rust/issues/34761#issuecomment-256320669
fn arrrrrrrrrrrrrrrrrrrrrr() {
    let cell = OnceCell::<RawMutex, _>::new();
    {
        let s = String::new();
        cell.set(&s).unwrap();
    }
}
