# generic_once_cell

[![Crates.io](https://img.shields.io/crates/v/generic_once_cell)](https://crates.io/crates/generic_once_cell)
[![docs.rs](https://img.shields.io/docsrs/generic_once_cell)](https://docs.rs/generic_once_cell)
[![CI](https://github.com/mkroening/generic_once_cell/actions/workflows/ci.yml/badge.svg)](https://github.com/mkroening/generic_once_cell/actions/workflows/ci.yml)

generic_once_cell is a generic `no_std` version of [once_cell].
Internal synchronization for initialization is provided as type parameter via custom mutexes based on [lock_api].
This makes it suitable for use in complex `no_std` scenarios where [once_cell's `critical-section` support] and [`once_cell::race`] are not sufficient.

The core API looks *roughly* like this:
```rust
impl<R: lock_api::RawMutex, T> OnceCell<R, T> {
    const fn new() -> Self { ... }
    fn set(&self, value: T) -> Result<(), T> { ... }
    fn get(&self) -> Option<&T> { ... }
}
```

More patterns and use-cases are in the [docs]!

[once_cell]: https://crates.io/crates/once_cell
[lock_api]: https://crates.io/crates/lock_api
[once_cell's `critical-section` support]: https://github.com/matklad/once_cell/blob/master/CHANGELOG.md#1160
[`once_cell::race`]: https://docs.rs/once_cell/1.16.0/once_cell/race/index.html
[docs]: https://docs.rs/generic_once_cell

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
