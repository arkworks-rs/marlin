<h1 align="center">Marlin</h1>

<p align="center">
    <a href="https://travis-ci.org/scipr-lab/marlin"><img src="https://travis-ci.org/scipr-lab/marlin.svg?branch=master"></a>
    <a href="https://github.com/scipr-lab/marlin/blob/master/AUTHORS"><img src="https://img.shields.io/badge/authors-SCIPR%20Lab-orange.svg"></a>
    <a href="https://github.com/scipr-lab/marlin/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
   <a href="https://github.com/scipr-lab/marlin/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
</p>


`marlin` is a Rust library that implements a
<p style="text-align: center;">
<b>preprocessing zkSNARK for R1CS</b><br>
with<br>
<b>universal and updatable SRS</b>
</p>

This library was initially developed as part of the [Marlin paper][marlin], and is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Overview

A zkSNARK with **preprocessing** achieves succinct verification for arbitrary computations, as opposed to only for structured computations. Informally, in an offline phase, one can preprocess the desired computation to produce a short summary of it; subsequently, in an online phase, this summary can be used to check any number of arguments relative to this computation.

The preprocessing zkSNARKs in this library rely on a structured reference string (SRS), which contains system parameters required by the argument system to produce/validate arguments. The SRS in this library is **universal**, which means that it supports (deterministically) preprocessing any computation up to a given size bound. The SRS is also **updatable**, which means that anyone can contribute a fresh share of randomness to it, which facilitates deployments in the real world.

The construction in this library follows the methodology introduced in the [Marlin paper][marlin], which obtains preprocessing zkSNARKs with universal and updatable SRS by combining two ingredients:

* an **algebraic holographic proof**
* a **polynomial commitment scheme**

The first ingredient is provided as part of this library, and is an efficient algebraic holographic proof for R1CS (a generalization of arithmetic circuit satisfiability supported by many argument systems). The second ingredient is imported from [`poly-commit`](https://github.com/scipr-lab/poly-commit). See [the Marlin paper][marlin] for evaluation details.

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

Lastly, this library is instrumented with profiling infrastructure that prints detailed traces of execution time. To enable this, compile with `cargo build --features timer`.

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
