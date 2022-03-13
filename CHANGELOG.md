# CHANGELOG

## Pending

### Breaking changes

- [\#86](https://github.com/arkworks-rs/marlin/pull/86) Unify the interface for Fiat-Shamir transform.

### Features

### Improvements

- [\#71](https://github.com/arkworks-rs/marlin/pull/71) Remove an unnecessary clone of the full witness.

### Bug fixes

## v0.3.0

- Change dependency to version `0.3.0` of other arkworks-rs crates.

## v0.2.0

### Features

- [\#47](https://github.com/arkworks-rs/marlin/pull/47) Automatically pad input to be of length 2^k, so constraint writers can have a public input of any size
- [\#51](https://github.com/arkworks-rs/marlin/pull/51) Implement CanonicalSerialize for Marlin's proofs.
- [\#54](https://github.com/arkworks-rs/marlin/pull/54) Implement CanonicalSerialize for Marlin's Index and Index Verification Key.
