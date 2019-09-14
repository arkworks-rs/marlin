<h1 align="center">Marlin: A Preprocessing zkSNARK with Universal and Updatabale Reference String</h1>

<p align="center">
    <a href="https://travis-ci.org/scipr-lab/marlin"><img src="https://travis-ci.org/scipr-lab/marlin.svg?branch=master"></a>
    <a href="https://github.com/scipr-lab/marlin/blob/master/AUTHORS"><img src="https://img.shields.io/badge/authors-SCIPR%20Lab-orange.svg"></a>
    <a href="https://github.com/scipr-lab/marlin/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
   <a href="https://github.com/scipr-lab/marlin/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
</p>


`marlin` is a Rust library that implements a *zkSNARK* with **universal** and **updatabale** structured reference strings. `marlin` uses polynomial commitment schemes implemented in [`poly-commit`][https://github.com/scipr-lab/poly-commit] to apply the transformation described in the [Marlin paper][marlin] to a novel *algebraic holographic proof*. The resulting zkSNARK achieves state-of-the-art proving time, verification time, proof and SRS size. See [the Marlin paper][marlin] for details. The `marlin` library is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.


## Build guide

The library compiles on the `stable` toolchain of the Rust compiler. To install the latest version of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install stable
```

After that, use `cargo` (the standard Rust build tool) to build the library:
```bash
git clone https://github.com/scipr-lab/marlin.git
cd marlin
cargo build --release
```

This library comes with some unit and integration tests. Run these tests with:
```bash
cargo test
```

Lastly, this library is instrumented with profiling infrastructure that prints detailed traces of execution time. To enables this, compile with `cargo build --features timer`.

## License

This library is licensed under either of the following licenses, at your discretion.

 * [Apache License Version 2.0](LICENSE-APACHE)
 * [MIT License](LICENSE-MIT)

Unless you explicitly state otherwise, any contribution that you submit to this library shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

[marlin]: https://ia.cr/2019/xxx

## Reference paper

[Marlin: Preprocessing zkSNARKs with Universal and Updatable SRS][marlin]     
Alessandro Chiesa, Yuncong Hu, Mary Maller, [Pratyush Mishra](https://www.github.com/pratyush), Noah Vesely, [Nicholas Ward](https://www.github.com/npwardberkeley)     
IACR ePrint Report 2019/XXX

## Acknowledgements

This work was supported by: an Engineering and Physical Sciences Research Council grant; a Google Faculty Award; the RISELab at UC Berkeley; and donations from the Ethereum Foundation and the Interchain Foundation.
