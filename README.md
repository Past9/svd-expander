[![crates.io](https://img.shields.io/crates/d/svd-expander.svg)](https://crates.io/crates/svd-expander)
[![crates.io](https://img.shields.io/crates/v/svd-expander.svg)](https://crates.io/crates/svd-expander)
[![Documentation](https://docs.rs/svd-expander/badge.svg)](https://docs.rs/svd-expander)
![Rust CI](https://github.com/Past9/svd-expander/workflows/Rust/badge.svg?branch=master)

# `svd-expander`

Expands arrays and resolves inheritance chains in CMSIS-SVD specifications. 

## Example usage:

```rust
use std::fs::File;
use std::io::Read;
use svd_expander::DeviceSpec;

fn main() {
    let xml = &mut String::new();

    File::open("./stm32f303.svd")
        .unwrap()
        .read_to_string(xml)
        .unwrap();

    println!("{:#?}", DeviceSpec::from_xml(xml).unwrap());
}
```

This crate is intended for use in code generators. It is under active development and bug reports are welcome. 

Feature requests may be considered, but [svd-expander](https://crates.io/crates/svd-expander) depends on [svd-parser](https://crates.io/crates/svd-parser) (at least for now) to parse the SVD files, so it can only implement the features supported by the parser.
