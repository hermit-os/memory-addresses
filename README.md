# Memory Addresses

This crate provides unified address types for the [Hermit ecosystem](https://github.com/hermit-os) and beyond.

## Features

| Name | Description |
|------|-------------|
| `x86_64` | Enables `x86_64` specific addresses (default) |
| `aarch64` | Enables `aarch64` specific addresses (default) |
| `step_trait` | Enables partial support for Rust's nightly [`step_trait`](https://doc.rust-lang.org/core/iter/trait.Step.html) |
| `conversions` | Enables all of the following conversion functionalities |
| `conv-x86_64` | Convert `x86_64::PhysAddr`/`x86_64::VirtAddr` to [`x86_64::PhysAddr`](https://docs.rs/x86_64/0.15.1/x86_64/addr/struct.PhysAddr.html)/[`x86_64::VirtAddr`](https://docs.rs/x86_64/0.15.1/x86_64/addr/struct.VirtAddr.html) using `into()` |
| `conv-x86` | Convert `x86_64::PhysAddr`/`x86_64::VirtAddr` to x86's 64-bit [`PAddr`](https://docs.rs/x86/0.52.0/x86/bits64/paging/struct.PAddr.html)/[`VAddr`](https://docs.rs/x86/0.52.0/x86/bits64/paging/struct.VAddr.html) using `into()` |

## Acknowledgement

This crate is based on work of the `x86_64` crate. An attempt was made to preserve the relevant commits with authorship and the apparently most active contributors of the original work are:

- Philipp Oppermann
- Gerd Zellweger
- Tom Dohrmann
- John Ericson
- Joe Richey
- Mara Bos
- Tobba
- Joseph Richey
- Dan Schatzberg
