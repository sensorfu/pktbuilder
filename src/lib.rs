#![no_std]
#![doc = include_str!("../README.md")]

use core::fmt::{self, Display};
use core::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use core::ops::{Add, AddAssign, Index, IndexMut};

/// Offset represents offset in a buffer.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Offset(usize);

impl Offset {
    /// Calculates the number of bytes on the from this offset to `other`.
    /// Offset to current position [Builder] can be retrieved with
    /// [Builder::offset()]
    ///
    /// `other` needs to be obtained further from the buffer than this offset,
    /// zero is returned of `other` is invalid.
    pub fn bytes_to(&self, other: Offset) -> usize {
        debug_assert!(*self <= other);
        if *self < other {
            other.0 - self.0
        } else {
            0
        }
    }
}

impl From<usize> for Offset {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Index<Offset> for [u8] {
    type Output = u8;

    fn index(&self, index: Offset) -> &Self::Output {
        &self[index.0]
    }
}

impl IndexMut<Offset> for [u8] {
    fn index_mut(&mut self, index: Offset) -> &mut Self::Output {
        &mut self[index.0]
    }
}

impl Add<usize> for Offset {
    type Output = Offset;

    fn add(self, rhs: usize) -> Self::Output {
        Offset(self.0 + rhs)
    }
}

impl AddAssign<usize> for Offset {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs
    }
}

impl Display for Offset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Builder can be used to build packet into given buffer.
/// Builder keeps internal index into the underlying buffer and all operations
/// will advance this index.
pub struct Builder<'a> {
    buf: &'a mut [u8],
    index: Offset,
}

/// Error type for builder operations
#[derive(Debug)]
pub enum Error {
    OutOfBounds(usize, Offset),
    OffsetError(Offset),
}

impl core::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::OutOfBounds(len, index) => {
                write!(
                    f,
                    "out-of-bounds write of {} bytes from index {}",
                    len, index
                )
            }
            Error::OffsetError(idx) => {
                write!(f, "Invalid index {}", idx)
            }
        }
    }
}

impl<'a> Builder<'a> {
    /// Creates new builder backed by given buffer.
    /// All operations will write to this buffer.
    pub fn new(buffer: &'a mut [u8]) -> Self {
        Builder {
            buf: buffer,
            index: Default::default(),
        }
    }

    /// Checks if buffer contains enough space to write `size` bytes from
    /// offset
    fn check(&self, size: usize) -> Result<(), Error> {
        if self.index + size > self.buf.len().into() {
            Err(Error::OutOfBounds(size, self.index))
        } else {
            Ok(())
        }
    }

    /// Checks if `idx` is within the buffer
    fn check_idx(&self, idx: Offset) -> Result<(), Error> {
        if idx >= self.buf.len().into() {
            Err(Error::OffsetError(idx))
        } else {
            Ok(())
        }
    }

    /// Checks if buffer contains space for `size` bytes starting from
    /// `idx`
    fn check_from_idx(&self, idx: Offset, size: usize) -> Result<(), Error> {
        if idx + size > self.buf.len().into() {
            Err(Error::OutOfBounds(size, idx))
        } else {
            Ok(())
        }
    }

    /// Adds a byte to buffer.
    pub fn add_byte(&mut self, data: u8) -> Result<&mut Self, Error> {
        self.put_byte(self.index, data)?;
        self.index += 1;
        Ok(self)
    }

    /// Puts `data` into position in buffer pointed by `offset`. Returns [Error]
    /// if `offset` is incorrect. Does not change the current position on
    /// buffer.
    pub fn put_byte(&mut self, offset: Offset, data: u8) -> Result<&mut Self, Error> {
        self.check_idx(offset)?;
        self.buf[offset.0] = data;
        Ok(self)
    }

    /// Adds `data` in big endian byte order into this buffer.
    pub fn add_u16_be(&mut self, data: u16) -> Result<&mut Self, Error> {
        self.put_u16_be(self.index, data)?;
        self.index += 2;
        Ok(self)
    }

    /// Puts `data` in big endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u16_be(&mut self, offset: Offset, data: u16) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, 2)?;
        let bytes = data.to_be_bytes();
        self.buf[offset] = bytes[0];
        self.buf[offset + 1] = bytes[1];
        Ok(self)
    }

    /// Adds `data` in little endian byte order into this buffer.
    pub fn add_u16_le(&mut self, data: u16) -> Result<&mut Self, Error> {
        self.put_u16_le(self.index, data)?;
        self.index += 2;
        Ok(self)
    }

    /// Puts `data` in little endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u16_le(&mut self, offset: Offset, data: u16) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, 2)?;
        let bytes = data.to_le_bytes();
        self.buf[offset] = bytes[0];
        self.buf[offset + 1] = bytes[1];
        Ok(self)
    }

    /// Puts `data` in big endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u24_be(&mut self, offset: Offset, data: u32) -> Result<&mut Self, Error> {
        debug_assert!(data >> 24 == 0, "expected 24bit data");
        self.check_from_idx(offset, 3)?;
        let bytes = data.to_be_bytes();
        self.buf[offset] = bytes[1];
        self.buf[offset + 1] = bytes[2];
        self.buf[offset + 2] = bytes[3];
        Ok(self)
    }

    /// Adds `data` in big endian byte order into this buffer.
    pub fn add_u24_be(&mut self, data: u32) -> Result<&mut Self, Error> {
        self.put_u24_be(self.index, data)?;
        self.index += 3;
        Ok(self)
    }

    /// Puts `data` in little endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u24_le(&mut self, offset: Offset, data: u32) -> Result<&mut Self, Error> {
        debug_assert!(data >> 24 == 0, "expected 24bit data");
        self.check_from_idx(offset, 3)?;
        let bytes = data.to_le_bytes();
        self.buf[offset] = bytes[0];
        self.buf[offset + 1] = bytes[1];
        self.buf[offset + 2] = bytes[2];
        Ok(self)
    }

    /// Adds `data` in little endian byte order into this buffer.
    pub fn add_u24_le(&mut self, data: u32) -> Result<&mut Self, Error> {
        self.put_u24_le(self.index, data)?;
        self.index += 3;
        Ok(self)
    }

    /// Adds u32 in big endian byte order into buffer
    pub fn add_u32_be(&mut self, data: u32) -> Result<&mut Self, Error> {
        self.put_u32_be(self.index, data)?;
        self.index += 4;
        Ok(self)
    }

    /// Puts `data` in big endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u32_be(&mut self, offset: Offset, data: u32) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, 4)?;
        let bytes = data.to_be_bytes();
        self.buf[offset] = bytes[0];
        self.buf[offset + 1] = bytes[1];
        self.buf[offset + 2] = bytes[2];
        self.buf[offset + 3] = bytes[3];
        Ok(self)
    }

    /// Adds u32 in big endian byte order into buffer
    pub fn add_u32_le(&mut self, data: u32) -> Result<&mut Self, Error> {
        self.put_u32_le(self.index, data)?;
        self.index += 4;
        Ok(self)
    }

    /// Puts `data` in big endian byte order into position pointed by `offset`.
    /// Returns [Error] if `offset` is incorrect. Does not change the current
    /// position on buffer.
    pub fn put_u32_le(&mut self, offset: Offset, data: u32) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, 4)?;
        let bytes = data.to_le_bytes();
        self.buf[offset] = bytes[0];
        self.buf[offset + 1] = bytes[1];
        self.buf[offset + 2] = bytes[2];
        self.buf[offset + 3] = bytes[3];
        Ok(self)
    }

    /// Adds contents of `data` into buffer.
    pub fn add(&mut self, data: &[u8]) -> Result<&mut Self, Error> {
        self.put(self.index, data)?;
        self.index += data.len();
        Ok(self)
    }

    /// Puts contents of `data` to buffer starting from position pointed by
    /// `offset`. Returns [Error] if `offset` is incorrect. Does not change
    /// the current position on buffer.
    pub fn put(&mut self, offset: Offset, data: &[u8]) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, data.len())?;
        self.buf[offset.0..offset.0 + data.len()].copy_from_slice(data);
        Ok(self)
    }

    /// Adds `addr` in big endian byte order into buffer.
    pub fn add_ipv6_address_be(&mut self, addr: Ipv6Addr) -> Result<&mut Self, Error> {
        let bytes = addr.octets();
        self.add(&bytes)
    }

    /// Adds `addr` in little endian byte order into buffer.
    pub fn add_ipv6_address_le(&mut self, addr: Ipv6Addr) -> Result<&mut Self, Error> {
        let mut bytes = addr.octets();
        bytes.reverse();
        self.add(&bytes)
    }

    /// Puts the `addr` into buffer in big endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipv6_address_be(
        &mut self,
        offset: Offset,
        addr: Ipv6Addr,
    ) -> Result<&mut Self, Error> {
        let data = addr.octets();
        self.put(offset, &data)
    }

    /// Puts the `addr` into buffer in little endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipv6_address_le(
        &mut self,
        offset: Offset,
        addr: Ipv6Addr,
    ) -> Result<&mut Self, Error> {
        let mut data = addr.octets();
        data.reverse();
        self.put(offset, &data)
    }

    /// Adds `addr` in big endian byte order into buffer.
    pub fn add_ipv4_address_be(&mut self, addr: Ipv4Addr) -> Result<&mut Self, Error> {
        let bytes = addr.octets();
        self.add(&bytes)
    }

    /// Adds `addr` in little endian byte order into buffer.
    pub fn add_ipv4_address_le(&mut self, addr: Ipv4Addr) -> Result<&mut Self, Error> {
        let mut bytes = addr.octets();
        bytes.reverse();
        self.add(&bytes)
    }

    /// Puts the `addr` into buffer in big endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipv4_address_be(
        &mut self,
        offset: Offset,
        addr: Ipv4Addr,
    ) -> Result<&mut Self, Error> {
        let bytes = addr.octets();
        self.put(offset, &bytes)
    }

    /// Puts the `addr` into buffer in little endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipv4_address_le(
        &mut self,
        offset: Offset,
        addr: Ipv4Addr,
    ) -> Result<&mut Self, Error> {
        let mut bytes = addr.octets();
        bytes.reverse();
        self.put(offset, &bytes)
    }

    /// Adds `addr` in big endian byte order into buffer
    pub fn add_ipaddr_be(&mut self, addr: IpAddr) -> Result<&mut Self, Error> {
        match addr {
            IpAddr::V4(addr) => self.add_ipv4_address_be(addr),
            IpAddr::V6(addr) => self.add_ipv6_address_be(addr),
        }
    }

    /// Adds `addr` in little endian byte order into buffer
    pub fn add_ipaddr_le(&mut self, addr: IpAddr) -> Result<&mut Self, Error> {
        match addr {
            IpAddr::V4(addr) => self.add_ipv4_address_le(addr),
            IpAddr::V6(addr) => self.add_ipv6_address_le(addr),
        }
    }

    /// Puts the `addr` into buffer in big endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipaddr_be(&mut self, offset: Offset, addr: IpAddr) -> Result<&mut Self, Error> {
        match addr {
            IpAddr::V4(addr) => self.put_ipv4_address_be(offset, addr),
            IpAddr::V6(addr) => self.put_ipv6_address_be(offset, addr),
        }
    }

    /// Puts the `addr` into buffer in little endian byte order starting from
    /// position pointed by `offset`. Returns [Error] if `offset` is incorrect.
    /// Does not change the current position on buffer.
    pub fn put_ipaddr_le(&mut self, offset: Offset, addr: IpAddr) -> Result<&mut Self, Error> {
        match addr {
            IpAddr::V4(addr) => self.put_ipv4_address_le(offset, addr),
            IpAddr::V6(addr) => self.put_ipv6_address_le(offset, addr),
        }
    }

    /// Skips (advance internal index by) `n` of bytes.
    pub fn skip(&mut self, n: usize) -> Result<&mut Self, Error> {
        self.check(n)?;
        self.index += n;
        Ok(self)
    }

    /// Adds `b` `n` times into buffer.
    pub fn fill(&mut self, n: usize, b: u8) -> Result<&mut Self, Error> {
        self.fill_from(self.index, n, b)?;
        self.index += n;
        Ok(self)
    }

    /// Adds `b` `n` times into buffer starting from `offset`.
    pub fn fill_from(&mut self, offset: Offset, n: usize, b: u8) -> Result<&mut Self, Error> {
        self.check_from_idx(offset, n)?;
        self.buf[offset.0..offset.0 + n].fill(b);
        Ok(self)
    }

    /// Returns [Offset] representing current position on buffer.
    pub fn offset(&self) -> Offset {
        self.index
    }

    /// Reset the builder back to the start of the buffer
    pub fn reset(&mut self) -> &mut Self {
        self.index = Offset(0);
        self
    }

    /// Returns length of data written to buffer.
    ///
    /// This is not the length of the underlying buffer but the length of
    /// data currently written into this buffer by this builder.
    pub fn len(&self) -> usize {
        self.index.0
    }

    ///  Returns `true` if no data has been written into the buffer.
    pub fn is_empty(&self) -> bool {
        self.index.0 == 0
    }

    /// Pads the buffer to 16 bit boundary with given byte. If buffer is already on
    /// boundary, no padding is added. Error is returned if there is
    /// no room for padding in buffer.
    pub fn pad_to_16(&mut self, pad: u8) -> Result<&mut Self, Error> {
        if self.len() % 2 != 0 {
            self.fill(1, pad)
        } else {
            Ok(self)
        }
    }

    /// Pads the buffer to 32 bit boundary with given byte. If buffer is already on
    /// boundary, no padding is added. Error is returned if there is
    /// no room for padding in buffer.
    pub fn pad_to_32(&mut self, pad: u8) -> Result<&mut Self, Error> {
        let pad_len = 4 - self.len() % 4;
        match pad_len {
            1..4 => self.fill(pad_len, pad),
            _ => Ok(self),
        }
    }

    /// Pads the buffer to 64 bit boundary with given byte. If buffer is already on
    /// boundary, no padding is added. Error is returned if there is
    /// no room for padding in buffer.
    pub fn pad_to_64(&mut self, pad: u8) -> Result<&mut Self, Error> {
        let pad_len = 8 - self.len() % 8;
        match pad_len {
            1..8 => self.fill(pad_len, pad),
            _ => Ok(self),
        }
    }

    /// Appends result of building `buildable` with self into the buffer.
    ///
    /// If error occurs while building `buildable` error is returned and the
    /// internal index is reset to position it was before building. However,
    /// the buffer might contain additional bytes written by `buildable`.
    pub fn append<B>(&mut self, buildable: &B) -> Result<&mut Self, Error>
    where
        B: Buildable,
    {
        let index = self.index;
        match buildable.build(self) {
            Ok(()) => Ok(self),
            Err(err) => {
                // reset index back to where we were before building
                self.index = index;
                Err(err)
            }
        }
    }

    /// Calculates a chekcsum of `len` bytes starting from `from`. The checksum
    /// is calculated using the function `checksum`. Resulting checksum value
    /// is stored to position starting from `sum_index`
    pub fn calculate_checksum_to<F>(
        &mut self,
        from: Offset,
        len: usize,
        sum_index: Offset,
        checksum: F,
    ) -> Result<&mut Self, Error>
    where
        F: FnOnce(&[u8]) -> u16,
    {
        self.check_from_idx(from, len)?;
        self.check_idx(sum_index)?;

        let sum = checksum(&self.buf[from.0..from.0 + len]);
        let current_index = self.index;
        // set the index to point to checksum
        self.index = sum_index;
        // we need to reset the index before returning
        if let Err(error) = self.add_u16_be(sum) {
            self.index = current_index;
            Err(error)
        } else {
            self.index = current_index;
            Ok(self)
        }
    }
}

/// A data structure which can be encoded into byte array using [Builder].
pub trait Buildable {
    /// Builds this to byte array using `builder`
    fn build(&self, builder: &mut Builder<'_>) -> Result<(), Error>;
}

#[cfg(test)]
mod test {
    use crate::Buildable;

    use super::Error;

    use super::Builder;
    use core::net::{Ipv4Addr, Ipv6Addr};
    use core::panic;

    type Result = core::result::Result<(), super::Error>;

    #[test]
    fn test_add_byte() -> Result {
        let mut data = [0u8; 2];
        let mut builder = Builder::new(&mut data);
        assert!(builder.is_empty());
        builder.add_byte(0x01)?.add_byte(0x02)?;
        assert_eq!(builder.len(), 2);
        assert_eq!(data, [0x01, 0x02]);
        Ok(())
    }

    #[test]
    fn test_add_byte_too_long() -> Result {
        let mut data = [0u8; 2];
        let mut builder = Builder::new(&mut data);
        assert!(builder
            .add_byte(0x01)?
            .add_byte(0x02)?
            .add_byte(0x03)
            .is_err());
        Ok(())
    }

    #[test]
    fn test_add_u16() -> Result {
        let mut data = [0u8; 4];

        let mut builder = Builder::new(&mut data);
        builder.add_byte(0x01)?.add_u16_be(0xaabb)?.add_byte(0x02)?;
        assert_eq!(builder.len(), 4);
        assert_eq!(data, [0x01, 0xaa, 0xbb, 0x02]);

        builder = Builder::new(&mut data);
        builder.add_byte(0x01)?.add_u16_le(0xaabb)?.add_byte(0x02)?;
        assert_eq!(builder.len(), 4);
        assert_eq!(data, [0x01, 0xbb, 0xaa, 0x02]);
        Ok(())
    }

    #[test]
    fn test_add_u16_too_long() -> Result {
        let mut data = [0u8; 2];
        let mut builder = Builder::new(&mut data);
        assert!(builder.add_byte(0x01)?.add_u16_be(0xaabb).is_err());
        Ok(())
    }

    #[test]
    fn test_add_u24() -> Result {
        let mut data = [0u8; 5];

        let mut builder = Builder::new(&mut data);
        builder
            .add_byte(0x01)?
            .add_u24_be(0xaabbcc)?
            .add_byte(0x02)?;
        assert_eq!(builder.len(), 5);
        assert_eq!(data, [0x01, 0xaa, 0xbb, 0xcc, 0x02]);

        builder = Builder::new(&mut data);
        builder
            .add_byte(0x01)?
            .add_u24_le(0xaabbcc)?
            .add_byte(0x02)?;
        assert_eq!(builder.len(), 5);
        assert_eq!(data, [0x01, 0xcc, 0xbb, 0xaa, 0x02]);
        Ok(())
    }

    #[test]
    fn test_add_u24_too_long() -> Result {
        let mut data = [0u8; 2];
        let mut builder = Builder::new(&mut data);
        assert!(builder.add_byte(0x01)?.add_u24_be(0xaabbcc).is_err());
        Ok(())
    }

    #[test]
    fn test_add_u32() -> Result {
        let mut data = [0u8; 6];
        let mut builder = Builder::new(&mut data);
        builder
            .add_byte(0x01)?
            .add_u32_be(0xaabbccdd)?
            .add_byte(0x02)?;
        assert_eq!(data, [0x01, 0xaa, 0xbb, 0xcc, 0xdd, 0x02]);

        builder = Builder::new(&mut data);
        builder
            .add_byte(0x01)?
            .add_u32_le(0xaabbccdd)?
            .add_byte(0x02)?;
        assert_eq!(data, [0x01, 0xdd, 0xcc, 0xbb, 0xaa, 0x02]);
        Ok(())
    }

    #[test]
    fn test_add_u32_too_long() -> Result {
        let mut data = [0u8; 4];
        let mut builder = Builder::new(&mut data);
        assert!(builder.add_byte(0x01)?.add_u32_be(0xaabbccdd).is_err());
        Ok(())
    }

    #[test]
    fn test_add_data() -> Result {
        let mut data = [0u8; 6];
        let input = [0x01, 0x02];
        let mut builder = Builder::new(&mut data);
        builder.skip(2)?;
        assert_eq!(builder.len(), 2);
        builder.add(&input)?.add_byte(0xff)?;
        assert_eq!(builder.len(), 5);
        assert_eq!(data, [0x00, 0x00, 0x01, 0x02, 0xff, 0x00]);
        Ok(())
    }

    #[test]
    fn test_add_data_too_long() -> Result {
        let mut data = [0u8; 3];
        let input = [0x01, 0x02];
        let mut builder = Builder::new(&mut data);
        assert!(builder.skip(2)?.add(&input).is_err());
        Ok(())
    }

    #[test]
    fn test_skip() -> Result {
        let mut data = [0u8; 4];
        let mut builder = Builder::new(&mut data);

        builder.skip(2)?.add_u16_be(0xaabb)?;
        assert_eq!(builder.len(), 4);
        assert_eq!(data, [0x00, 0x00, 0xaa, 0xbb]);
        Ok(())
    }

    #[test]
    fn test_skip_too_much() -> Result {
        let mut data = [0u8; 4];
        let mut builder = Builder::new(&mut data);

        assert!(builder.add_byte(0x01)?.skip(4).is_err());
        Ok(())
    }

    #[test]
    fn test_fill() -> Result {
        let mut data = [0u8; 6];
        let mut builder = Builder::new(&mut data);
        builder.skip(2)?.fill(2, 0xaa)?.add_byte(0xff)?;
        assert_eq!(builder.len(), 5);
        assert_eq!(data, [0x00, 0x00, 0xaa, 0xaa, 0xff, 0x00]);
        Ok(())
    }

    #[test]
    fn test_fill_too_much() -> Result {
        let mut data = [0u8; 4];
        let mut builder = Builder::new(&mut data);
        assert!(builder.add_u16_be(0xaabb)?.fill(4, 0x11).is_err());
        Ok(())
    }

    #[test]
    fn test_add_ipv4() -> Result {
        let addr: Ipv4Addr = "127.1.2.3".parse().unwrap();

        let mut data = [0; 6];
        let mut builder = Builder::new(&mut data);
        builder.skip(1)?.add_ipv4_address_be(addr)?.add_byte(0xff)?;

        assert_eq!(data, [0x00, 0x7f, 0x01, 0x02, 0x03, 0xff]);

        let mut data = [0; 6];
        builder = Builder::new(&mut data);
        builder.skip(1)?.add_ipv4_address_le(addr)?.add_byte(0xff)?;

        assert_eq!(data, [0x00, 0x03, 0x02, 0x01, 0x7f, 0xff]);
        Ok(())
    }

    #[test]
    fn test_put_ipv4() -> Result {
        let addr: Ipv4Addr = "127.1.2.3".parse().unwrap();

        let mut data = [0; 6];
        let mut builder = Builder::new(&mut data);
        builder
            .skip(5)?
            .put_ipv4_address_be(1.into(), addr)?
            .add_byte(0xff)?;

        assert_eq!(data, [0x00, 0x7f, 0x01, 0x02, 0x03, 0xff]);

        let mut data = [0; 6];
        builder = Builder::new(&mut data);
        builder
            .skip(5)?
            .put_ipv4_address_le(1.into(), addr)?
            .add_byte(0xff)?;

        assert_eq!(data, [0x00, 0x03, 0x02, 0x01, 0x7f, 0xff]);
        Ok(())
    }

    #[test]
    fn test_add_ipv4_short() -> Result {
        let addr: Ipv4Addr = "127.1.1.1".parse().unwrap();

        let mut data = [0; 6];
        let mut builder = Builder::new(&mut data);
        assert!(builder.skip(3)?.add_ipv4_address_be(addr).is_err());
        Ok(())
    }

    #[test]
    fn test_put_ipv4_short() {
        let addr: Ipv4Addr = "127.1.1.1".parse().unwrap();

        let mut data = [0; 6];
        let mut builder = Builder::new(&mut data);
        assert!(builder.put_ipv4_address_be(3.into(), addr).is_err());
    }

    #[test]
    fn test_add_ipv6() -> Result {
        let addr: Ipv6Addr = "7f01:0203:0405:0607:0809:0a0b:0c0d:0e0f".parse().unwrap();

        let mut data = [0; 18];
        let mut builder = Builder::new(&mut data);
        builder.skip(1)?.add_ipv6_address_be(addr)?.add_byte(0xff)?;

        assert_eq!(
            data,
            [
                0x00, 0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                0x0d, 0x0e, 0x0f, 0xff
            ]
        );

        let mut data = [0; 18];
        builder = Builder::new(&mut data);
        builder.skip(1)?.add_ipv6_address_le(addr)?.add_byte(0xff)?;

        assert_eq!(
            data,
            [
                0x00, 0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03,
                0x02, 0x01, 0x7f, 0xff
            ]
        );
        Ok(())
    }
    #[test]
    fn test_put_ipv6() -> Result {
        let addr: Ipv6Addr = "7f01:0203:0405:0607:0809:0a0b:0c0d:0e0f".parse().unwrap();

        let mut data = [0; 18];
        let mut builder = Builder::new(&mut data);
        builder
            .skip(17)?
            .put_ipv6_address_be(1.into(), addr)?
            .add_byte(0xff)?;

        assert_eq!(
            data,
            [
                0x00, 0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                0x0d, 0x0e, 0x0f, 0xff
            ]
        );

        data = [0; 18];
        builder = Builder::new(&mut data);
        builder
            .skip(17)?
            .put_ipv6_address_le(1.into(), addr)?
            .add_byte(0xff)?;

        assert_eq!(
            data,
            [
                0x00, 0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03,
                0x02, 0x01, 0x7f, 0xff
            ]
        );
        Ok(())
    }

    #[test]
    fn test_add_ipv6_short() -> Result {
        let addr: Ipv6Addr = "7f01:0203:0405:0607:0809:0a0b:0c0d:0e0f".parse().unwrap();

        let mut data = [0; 18];
        let mut builder = Builder::new(&mut data);
        assert!(builder.skip(3)?.add_ipv6_address_be(addr).is_err());
        Ok(())
    }

    #[test]
    fn test_put_ipv6_short() {
        let addr: Ipv6Addr = "7f01:0203:0405:0607:0809:0a0b:0c0d:0e0f".parse().unwrap();

        let mut data = [0; 18];
        let mut builder = Builder::new(&mut data);
        assert!(builder.put_ipv6_address_be(3.into(), addr).is_err());
    }

    #[test]
    fn test_reset() -> Result {
        let mut data = [0u8; 4];
        let mut builder = Builder::new(&mut data);

        let bld = builder.fill(2, 0x01)?;
        assert!(bld.offset() > 0.into());
        let bld = bld.reset();
        assert!(bld.offset() == 0.into());
        Ok(())
    }

    fn dummy_checksum(_data: &[u8]) -> u16 {
        0xf00f
    }

    #[test]
    fn test_checksum() -> Result {
        let mut data = [0u8; 8];
        let mut builder = Builder::new(&mut data);
        let idx = builder.offset();
        let pl = [0xaa, 0xbb, 0xcc, 0xdd];

        builder
            .add_byte(0x08)?
            .skip(3)?
            .add(&pl)?
            .calculate_checksum_to(idx, 8, idx + 2, dummy_checksum)?;

        assert_eq!(data, [0x08, 0x00, 0xf0, 0x0f, 0xaa, 0xbb, 0xcc, 0xdd]);
        Ok(())
    }

    #[test]
    fn test_checksum_invalid_len() -> Result {
        let mut data = [0u8; 5];
        let mut builder = Builder::new(&mut data);
        let idx = builder.add_byte(0x01)?.offset();
        let res = builder.calculate_checksum_to(idx, 6, idx, dummy_checksum);
        assert!(res.is_err());
        if let Err(Error::OutOfBounds(l, f)) = res {
            assert_eq!(f, idx);
            assert_eq!(l, 6);
        } else {
            panic!("unexpected error");
        }
        Ok(())
    }

    #[test]
    fn test_checksum_invalid_idx() -> Result {
        let mut data = [0u8; 5];
        let mut builder = Builder::new(&mut data);
        let idx = builder.add_byte(0x01)?.offset();
        let res = builder.calculate_checksum_to(6.into(), 3, idx, dummy_checksum);
        assert!(res.is_err());
        if let Err(Error::OutOfBounds(l, f)) = res {
            assert_eq!(f, 6.into());
            assert_eq!(l, 3);
        } else {
            panic!("unexpected error");
        }
        Ok(())
    }

    #[test]
    fn test_checksum_invalid_sum_index() -> Result {
        let mut data = [0u8; 5];
        let mut builder = Builder::new(&mut data);
        let idx = builder.add_byte(0x01)?.offset();
        let res = builder.calculate_checksum_to(idx, 3, 6.into(), dummy_checksum);
        assert!(res.is_err());
        if let Err(Error::OffsetError(o)) = res {
            assert_eq!(o, 6.into());
        } else {
            panic!("unexpected error");
        }
        Ok(())
    }

    #[test]
    fn test_checksum_no_room_for_sum() -> Result {
        let mut data = [0u8; 5];
        let mut builder = Builder::new(&mut data);
        let idx = builder.add_byte(0x01)?.offset();
        let res = builder.calculate_checksum_to(idx, 3, 4.into(), dummy_checksum);
        assert!(res.is_err());
        if let Err(Error::OutOfBounds(l, f)) = res {
            assert_eq!(f, 4.into());
            assert_eq!(l, 2);
        } else {
            panic!("unexpected error");
        }
        Ok(())
    }

    #[test]
    fn test_pad_to_16() -> Result {
        for n in 0..3 {
            let mut buf = [0; 4];
            let mut builder = Builder::new(&mut buf);
            builder.fill(n, 0x01)?;
            builder.pad_to_16(0x01)?;
            match n {
                0 => assert_eq!(buf, [0x00; 4]),
                _ => assert_eq!(buf, [0x01, 0x01, 0x00, 0x00]),
            }
        }
        Ok(())
    }

    #[test]
    fn test_pad_to_32() -> Result {
        for n in 0..5 {
            let mut buf = [0; 6];
            let mut builder = Builder::new(&mut buf);
            builder.fill(n, 0x01)?;
            builder.pad_to_32(0x01)?;
            match n {
                0 => assert_eq!(buf, [0x00; 6]),
                _ => assert_eq!(buf, [0x01, 0x01, 0x01, 0x01, 0x00, 0x00]),
            }
        }
        Ok(())
    }

    #[test]
    fn test_pad_to_64() -> Result {
        for n in 0..9 {
            let mut buf = [0; 10];
            let mut builder = Builder::new(&mut buf);
            builder.fill(n, 0x01)?;
            builder.pad_to_64(0x01)?;
            match n {
                0 => assert_eq!(buf, [0x00; 10]),
                _ => assert_eq!(
                    buf,
                    [0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00]
                ),
            }
        }
        Ok(())
    }

    #[test]
    fn test_pad_to_no_room() -> Result {
        let mut buf = [0; 3];
        let mut builder = Builder::new(&mut buf);
        builder.fill(3, 0x01)?;
        assert!(builder.pad_to_16(0x02).is_err());

        let mut buf = [0; 3];
        let mut builder = Builder::new(&mut buf);
        builder.fill(2, 0x01)?;
        assert!(builder.pad_to_32(0x02).is_err());
        assert!(builder.pad_to_64(0x03).is_err());
        assert_eq!(buf, [0x01, 0x01, 0x00]);
        Ok(())
    }

    #[test]
    fn test_append() -> Result {
        struct Element {
            data: u16,
        }

        impl Buildable for Element {
            fn build(&self, builder: &mut Builder<'_>) -> core::result::Result<(), Error> {
                builder.add_u16_be(self.data)?;
                Ok(())
            }
        }

        let elem = Element { data: 0x0203 };

        let mut buf = [0; 4];
        let mut builder = Builder::new(&mut buf);
        builder.add_byte(0x01)?.append(&elem)?.add_byte(0x04)?;

        assert_eq!(buf, [0x01, 0x02, 0x03, 0x04]);

        Ok(())
    }

    #[test]
    fn test_append_at_end() -> Result {
        struct Element {
            data: u16,
        }

        impl Buildable for Element {
            fn build(&self, builder: &mut Builder<'_>) -> core::result::Result<(), Error> {
                builder.add_u16_be(self.data)?;
                Ok(())
            }
        }

        let elem = Element { data: 0x0304 };

        let mut buf = [0; 4];
        let mut builder = Builder::new(&mut buf);
        builder.add_u16_be(0x0102)?.append(&elem)?;
        assert_eq!(buf, [0x01, 0x02, 0x03, 0x04]);
        Ok(())
    }

    #[test]
    fn test_append_no_space() -> Result {
        struct Element {
            data: u16,
        }

        impl Buildable for Element {
            fn build(&self, builder: &mut Builder<'_>) -> core::result::Result<(), Error> {
                builder.add_u16_be(self.data)?;
                Ok(())
            }
        }

        let elem = Element { data: 0x0304 };

        let mut buf = [0; 4];
        let mut builder = Builder::new(&mut buf);
        builder.fill(3, 0x01)?;
        assert!(builder.append(&elem).is_err());
        assert_eq!(buf, [0x01, 0x01, 0x01, 0x00]);
        Ok(())
    }

    #[test]
    fn test_append_partial() -> Result {
        struct Element {
            first: u8,
            second: u16,
            third: u8,
        }

        impl Buildable for Element {
            fn build(&self, builder: &mut Builder<'_>) -> core::result::Result<(), Error> {
                builder
                    .add_byte(self.first)?
                    .add_u16_be(self.second)?
                    .add_byte(self.third)?;
                Ok(())
            }
        }

        let elem = Element {
            first: 0x02,
            second: 0x0304,
            third: 0x04,
        };
        let mut buf = [0; 4];
        let mut builder = Builder::new(&mut buf);
        builder.add_byte(0x01)?;
        assert!(builder.append(&elem).is_err());
        assert_eq!(builder.index, 1.into());
        assert_eq!(buf, [0x01, 0x02, 0x03, 0x4]);

        Ok(())
    }
}
