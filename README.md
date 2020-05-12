# SVD Expander

This crate expands arrays and resolves inheritance chains in CMSIS-SVD specifications. 

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

This crate is immature but is intended for use in code generators. It is under active development and bug reports are welcome.