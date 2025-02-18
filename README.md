# pktbuilder

A safe builder for building network packets.

A simple way to build packets is to give a buffer to [Builder] and use it's
methods to populate buffer with values.

```rust
use std::net::Ipv4Addr;
use pktbuilder::Builder;

fn example1() -> Result<(), pktbuilder::Error> {
    let mut buffer = [0u8; 6];
    let mut builder = Builder::new(&mut buffer);

    let ip = Ipv4Addr::new(192, 0, 2, 42);

    builder
        .add_byte(0x01)?
        .add_ipv4_address_be(ip)?
        .add_byte(0x02)?;

    assert_eq!(buffer, [0x01_u8, 192, 0, 2, 42, 0x02]);
    Ok(())
}
```

But for most cases we already have e.g. a struct that should be encoded so we
can implement [Buildable] trait for the struct and use [Buildable::build] method
to write into [Builder]:

```rust
use std::net::Ipv4Addr;
use pktbuilder::{Builder, Buildable};

struct Foo {
    foo: u8,
    ip: Ipv4Addr,
    bar: u8,
}

impl Buildable for Foo {
    fn build(&self, builder: &mut Builder<'_>) -> Result<(), pktbuilder::Error> {
        builder
            .add_byte(self.foo)?
            .add_ipv4_address_be(self.ip)?
            .add_byte(self.bar)?;
        Ok(())
    }
}


fn example2() -> Result<(), pktbuilder::Error> {
    let mut buffer = [0u8; 6];
    let mut builder = Builder::new(&mut buffer);

    let foo = Foo {
        foo: 0x01,
        ip: Ipv4Addr::new(192, 0, 2, 42),
        bar: 0x02,
    };

    foo.build(&mut builder)?;

    assert_eq!(buffer, [0x01_u8, 192, 0, 2, 42, 0x02]);
    Ok(())
}
```
