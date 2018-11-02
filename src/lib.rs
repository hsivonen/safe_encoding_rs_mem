// Copyright 2015-2016 Mozilla Foundation. See the COPYRIGHT
// file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Reference implementation of `encoding_rs::mem` using the standard library
//! without `unsafe`, except for writing into `&mut str`.

extern crate encoding_rs;

use std::char::REPLACEMENT_CHARACTER;
use encoding_rs::mem::Latin1Bidi;

#[inline(always)]
fn write_iterator_to_slice<I: Iterator>(iter: I, slice: &mut [I::Item]) -> usize {
    iter.zip(slice.iter_mut())
        .map(|(from, to)| *to = from)
        .count()
}

#[inline(always)]
fn write_char_iterator_to_utf8<I: Iterator<Item = char>>(iter: I, slice: &mut [u8]) -> usize {
    let mut offset = 0;
    for c in iter {
        offset += c.encode_utf8(&mut slice[offset..]).len();
    }
    offset
}

/// Checks whether the buffer is all-ASCII.
///
/// May read the entire buffer even if it isn't all-ASCII. (I.e. the function
/// is not guaranteed to fail fast.)
#[inline]
pub fn is_ascii(buffer: &[u8]) -> bool {
    for b in buffer {
        if *b > 0x7F {
            return false;
        }
    }
    true
}

/// Checks whether the buffer is all-Basic Latin (i.e. UTF-16 representing
/// only ASCII characters).
///
/// May read the entire buffer even if it isn't all-ASCII. (I.e. the function
/// is not guaranteed to fail fast.)
#[inline]
pub fn is_basic_latin(buffer: &[u16]) -> bool {
    for u in buffer {
        if *u > 0x7F {
            return false;
        }
    }
    true
}

/// Checks whether the buffer is valid UTF-8 representing only code points
/// less than or equal to U+00FF.
///
/// Fails fast. (I.e. returns before having read the whole buffer if UTF-8
/// invalidity or code points above U+00FF are discovered.)
#[inline]
pub fn is_utf8_latin1(buffer: &[u8]) -> bool {
    match ::std::str::from_utf8(buffer) {
        Err(_) => false,
        Ok(s) => is_str_latin1(s),
    }
}

/// Checks whether the buffer represents only code point less than or equal
/// to U+00FF.
///
/// Fails fast. (I.e. returns before having read the whole buffer if code
/// points above U+00FF are discovered.)
#[inline]
pub fn is_str_latin1(buffer: &str) -> bool {
    for c in buffer.chars() {
        if c > '\u{FF}' {
            return false;
        }
    }
    true
}

/// Checks whether the buffer represents only code point less than or equal
/// to U+00FF.
///
/// May read the entire buffer even if it isn't all-Latin1. (I.e. the function
/// is not guaranteed to fail fast.)
#[inline]
pub fn is_utf16_latin1(buffer: &[u16]) -> bool {
    for u in buffer {
        if *u > 0xFF {
            return false;
        }
    }
    true
}

/// Checks whether a potentially-invalid UTF-8 buffer contains code points
/// that trigger right-to-left processing.
///
/// The check is done on a Unicode block basis without regard to assigned
/// vs. unassigned code points in the block. Additionally, the four
/// RIGHT-TO-LEFT FOO controls in General Punctuation are checked for.
/// Control characters that are technically bidi controls but do not cause
/// right-to-left behavior without the presence of right-to-left characters
/// or right-to-left controls are not checked for.
///
/// If the input is invalid UTF-8, may return `true` even if replacing the
/// errors with the REPLACEMENT CHARACTER and trying again would result in
/// `false`.
#[inline]
pub fn is_utf8_bidi(buffer: &[u8]) -> bool {
    match ::std::str::from_utf8(buffer) {
        Err(_) => true,
        Ok(s) => is_str_bidi(s),
    }
}

/// Checks whether a valid UTF-8 buffer contains code points that trigger
/// right-to-left processing.
///
/// The check is done on a Unicode block basis without regard to assigned
/// vs. unassigned code points in the block. Additionally, the four
/// RIGHT-TO-LEFT FOO controls in General Punctuation are checked for.
/// Control characters that are technically bidi controls but do not cause
/// right-to-left behavior without the presence of right-to-left characters
/// or right-to-left controls are not checked for.
#[inline]
pub fn is_str_bidi(buffer: &str) -> bool {
    for c in buffer.chars() {
        if is_char_bidi(c) {
            return true;
        }
    }
    false
}

/// Checks whether a UTF-16 buffer contains code points that trigger
/// right-to-left processing.
///
/// The check is done on a Unicode block basis without regard to assigned
/// vs. unassigned code points in the block. Additionally, the four
/// RIGHT-TO-LEFT FOO controls in General Punctuation are checked for.
/// Control characters that are technically bidi controls but do not cause
/// right-to-left behavior without the presence of right-to-left characters
/// or right-to-left controls are not checked for.
///
/// If the input is invalid UTF-16, may return `true` even if replacing the
/// errors with the REPLACEMENT CHARACTER and trying again would result in
/// `false`.
#[inline]
pub fn is_utf16_bidi(buffer: &[u16]) -> bool {
    for u in buffer {
        if is_utf16_code_unit_bidi(*u) {
            return true;
        }
    }
    false
}

/// Checks whether a code point triggers right-to-left processing.
///
/// The check is done on a Unicode block basis without regard to assigned
/// vs. unassigned code points in the block. Additionally, the four
/// RIGHT-TO-LEFT FOO controls in General Punctuation are checked for.
/// Control characters that are technically bidi controls but do not cause
/// right-to-left behavior without the presence of right-to-left characters
/// or right-to-left controls are not checked for.
#[inline(always)]
pub fn is_char_bidi(c: char) -> bool {
    // Controls:
    // Every control with RIGHT-TO-LEFT in its name in
    // https://www.unicode.org/charts/PDF/U2000.pdf
    // U+200F RLM
    // U+202B RLE
    // U+202E RLO
    // U+2067 RLI
    //
    // BMP RTL:
    // https://www.unicode.org/roadmaps/bmp/
    // U+0590...U+08FF
    // U+FB50...U+FDFF Arabic Presentation Forms A
    // U+FE70...U+FEFF Arabic Presentation Forms B
    //
    // Supplementary RTL:
    // https://www.unicode.org/roadmaps/smp/
    // U+10800...U+10FFF (Lead surrogate U+D802 or U+D803)
    // U+1E800...U+1EFFF (Lead surrogate U+D83A or U+D83B)
    match c {
        '\u{0590}'...'\u{08FF}' | '\u{FB50}'...'\u{FDFF}' |
        '\u{FE70}'...'\u{FEFF}' | '\u{10800}'...'\u{10FFF}' |
        '\u{1E800}'...'\u{1EFFF}' | '\u{200F}' | '\u{202B}' |
        '\u{202E}' | '\u{2067}' => true,
        _ => false,
    }
}

/// Checks whether a UTF-16 code unit triggers right-to-left processing.
///
/// The check is done on a Unicode block basis without regard to assigned
/// vs. unassigned code points in the block. Additionally, the four
/// RIGHT-TO-LEFT FOO controls in General Punctuation are checked for.
/// Control characters that are technically bidi controls but do not cause
/// right-to-left behavior without the presence of right-to-left characters
/// or right-to-left controls are not checked for.
///
/// Since supplementary-plane right-to-left blocks are identifiable from the
/// high surrogate without examining the low surrogate, this function returns
/// `true` for such high surrogates making the function suitable for handling
/// supplementary-plane text without decoding surrogate pairs to scalar
/// values. Obviously, such high surrogates are then reported as right-to-left
/// even if actually unpaired.
#[inline(always)]
pub fn is_utf16_code_unit_bidi(u: u16) -> bool {
    match u {
        0x0590...0x08FF | 0xFB50...0xFDFF |
        0xFE70...0xFEFF | 0xD802 | 0xD803 | 0xD83A | 0xD83B |
        0x200F | 0x202B | 0x202E | 0x2067 => true,
        _ => false,
    }
}

/// Checks whether a potentially invalid UTF-8 buffer contains code points
/// that trigger right-to-left processing or is all-Latin1.
///
/// Possibly more efficient than performing the checks separately.
///
/// Returns `Latin1Bidi::Latin1` if `is_utf8_latin1()` would return `true`.
/// Otherwise, returns `Latin1Bidi::Bidi` if `is_utf8_bidi()` would return
/// `true`. Otherwise, returns `Latin1Bidi::LeftToRight`.
#[inline]
pub fn check_utf8_for_latin1_and_bidi(buffer: &[u8]) -> Latin1Bidi {
    if is_utf8_latin1(buffer) {
        Latin1Bidi::Latin1
    } else {
        if is_utf8_bidi(buffer) {
            Latin1Bidi::Bidi
        } else {
            Latin1Bidi::LeftToRight
        }
    }
}

/// Checks whether a valid UTF-8 buffer contains code points
/// that trigger right-to-left processing or is all-Latin1.
///
/// Possibly more efficient than performing the checks separately.
///
/// Returns `Latin1Bidi::Latin1` if `is_str_latin1()` would return `true`.
/// Otherwise, returns `Latin1Bidi::Bidi` if `is_str_bidi()` would return
/// `true`. Otherwise, returns `Latin1Bidi::LeftToRight`.
#[inline]
pub fn check_str_for_latin1_and_bidi(buffer: &str) -> Latin1Bidi {
    if is_str_latin1(buffer) {
        Latin1Bidi::Latin1
    } else {
        if is_str_bidi(buffer) {
            Latin1Bidi::Bidi
        } else {
            Latin1Bidi::LeftToRight
        }
    }
}

/// Checks whether a potentially invalid UTF-16 buffer contains code points
/// that trigger right-to-left processing or is all-Latin1.
///
/// Possibly more efficient than performing the checks separately.
///
/// Returns `Latin1Bidi::Latin1` if `is_utf16_latin1()` would return `true`.
/// Otherwise, returns `Latin1Bidi::Bidi` if `is_utf16_bidi()` would return
/// `true`. Otherwise, returns `Latin1Bidi::LeftToRight`.
#[inline]
pub fn check_utf16_for_latin1_and_bidi(buffer: &[u16]) -> Latin1Bidi {
    if is_utf16_latin1(buffer) {
        Latin1Bidi::Latin1
    } else {
        if is_utf16_bidi(buffer) {
            Latin1Bidi::Bidi
        } else {
            Latin1Bidi::LeftToRight
        }
    }
}

/// Converts potentially-invalid UTF-8 to valid UTF-16 with errors replaced
/// with the REPLACEMENT CHARACTER.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer _plus one_.
///
/// Returns the number of `u16`s written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn convert_utf8_to_utf16(src: &[u8], dst: &mut [u16]) -> usize {
    assert!(dst.len() >= src.len() + 1);
    let s = String::from_utf8_lossy(src);
    write_iterator_to_slice(s.encode_utf16(), dst)
}

/// Converts valid UTF-8 to valid UTF-16.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// Returns the number of `u16`s written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn convert_str_to_utf16(src: &str, dst: &mut [u16]) -> usize {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    write_iterator_to_slice(src.encode_utf16(), dst)
}

/// Converts potentially-invalid UTF-16 to valid UTF-8 with errors replaced
/// with the REPLACEMENT CHARACTER.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer times three _plus one_.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
///
/// # Safety
///
/// Note that this function may write garbage beyond the number of bytes
/// indicated by the return value, so using a `&mut str` interpreted as
/// `&mut [u8]` as the destination is not safe. If you want to convert into
/// a `&mut str`, use `convert_utf16_to_str()` instead of this function.
#[inline]
pub fn convert_utf16_to_utf8(src: &[u16], dst: &mut [u8]) -> usize {
    assert!(dst.len() >= src.len() * 3 + 1);
    write_char_iterator_to_utf8(std::char::decode_utf16(src.iter().cloned())
                                    .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER)),
                                dst)
}

/// Converts potentially-invalid UTF-16 to valid UTF-8 with errors replaced
/// with the REPLACEMENT CHARACTER such that the validity of the output is
/// signaled using the Rust type system.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer times three _plus one_.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn convert_utf16_to_str(src: &[u16], dst: &mut str) -> usize {
    assert!(dst.len() >= src.len() * 3 + 1);
    let bytes = unsafe { dst.as_bytes_mut() };
    let n = convert_utf16_to_utf8(src, bytes);
    let mut trail = n;
    while trail < bytes.len() && ((bytes[trail] & 0xC0) == 0x80) {
        bytes[trail] = 0;
        trail += 1;
    }
    n
}

/// Converts bytes whose unsigned value is interpreted as Unicode code point
/// (i.e. U+0000 to U+00FF, inclusive) to UTF-16.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// The number of `u16`s written equals the length of the source buffer.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline(never)]
pub fn convert_latin1_to_utf16(src: &[u8], dst: &mut [u16]) {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    src.iter()
        .zip(dst.iter_mut())
        .for_each(|(from, to)| *to = *from as u16);
}

/// Converts bytes whose unsigned value is interpreted as Unicode code point
/// (i.e. U+0000 to U+00FF, inclusive) to UTF-8.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer times two.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
///
/// # Safety
///
/// Note that this function may write garbage beyond the number of bytes
/// indicated by the return value, so using a `&mut str` interpreted as
/// `&mut [u8]` as the destination is not safe. If you want to convert into
/// a `&mut str`, use `convert_utf16_to_str()` instead of this function.
#[inline]
pub fn convert_latin1_to_utf8(src: &[u8], dst: &mut [u8]) -> usize {
    assert!(dst.len() >= src.len() * 2,
            "Destination must not be shorter than the source times two.");
    write_char_iterator_to_utf8(src.iter().map(|b| *b as char), dst)
}

/// Converts bytes whose unsigned value is interpreted as Unicode code point
/// (i.e. U+0000 to U+00FF, inclusive) to UTF-8 such that the validity of the
/// output is signaled using the Rust type system.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer times two.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn convert_latin1_to_str(src: &[u8], dst: &mut str) -> usize {
    assert!(dst.len() >= src.len() * 2,
            "Destination must not be shorter than the source times two.");
    let bytes = unsafe { dst.as_bytes_mut() };
    let n = convert_latin1_to_utf8(src, bytes);
    let mut trail = n;
    while trail < bytes.len() && ((bytes[trail] & 0xC0) == 0x80) {
        bytes[trail] = 0;
        trail += 1;
    }
    n
}

/// If the input is valid UTF-8 representing only Unicode code points from
/// U+0000 to U+00FF, inclusive, converts the input into output that
/// represents the value of each code point as the unsigned byte value of
/// each output byte.
///
/// If the input does not fulfill the condition stated above, this function
/// does something that is memory-safe without any promises about any
/// properties of the output. In particular, callers shouldn't assume the
/// output to be the same across crate versions or CPU architectures and
/// should not assume that non-ASCII input can't map to ASCII output.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn convert_utf8_to_latin1_lossy(src: &[u8], dst: &mut [u8]) -> usize {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    let valid = String::from_utf8_lossy(src);
    write_iterator_to_slice(valid.chars().map(|r| r as u8),
                            dst)
}

/// If the input is valid UTF-16 representing only Unicode code points from
/// U+0000 to U+00FF, inclusive, converts the input into output that
/// represents the value of each code point as the unsigned byte value of
/// each output byte.
///
/// If the input does not fulfill the condition stated above, this function
/// does something that is memory-safe without any promises about any
/// properties of the output. In particular, callers shouldn't assume the
/// output to be the same across crate versions or CPU architectures and
/// should not assume that non-Basic Latin input can't map to ASCII output.
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// The number of bytes written equals the length of the source buffer.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline(never)]
pub fn convert_utf16_to_latin1_lossy(src: &[u16], dst: &mut [u8]) {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    src.iter()
        .zip(dst.iter_mut())
        .for_each(|(from, to)| *to = *from as u8);
}

/// Returns the index of the first unpaired surrogate or, if the input is
/// valid UTF-16 in its entirety, the length of the input.
#[inline]
pub fn utf16_valid_up_to(buffer: &[u16]) -> usize {
    let mut offset = 0;
    for r in std::char::decode_utf16(buffer.iter().cloned()) {
        match r {
            Ok(c) => {
                if c <= '\u{FFFF}' {
                    offset += 1;
                } else {
                    offset += 2;
                }
            }
            Err(_) => return offset,
        }
    }
    assert_eq!(offset, buffer.len());
    offset
}

/// Replaces unpaired surrogates in the input with the REPLACEMENT CHARACTER.
#[inline]
pub fn ensure_utf16_validity(buffer: &mut [u16]) {
    // This is the same implementation as in `encoding_rs::mem`.
    let mut offset = 0;
    loop {
        offset += utf16_valid_up_to(&buffer[offset..]);
        if offset == buffer.len() {
            return;
        }
        buffer[offset] = 0xFFFD;
        offset += 1;
    }
}

/// Copies ASCII from source to destination up to the first non-ASCII byte
/// (or the end of the input if it is ASCII in its entirety).
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn copy_ascii_to_ascii(src: &[u8], dst: &mut [u8]) -> usize {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    src.iter()
        .zip(dst.iter_mut())
        .take_while(|&(from, _)| *from < 0x80)
        .map(|(from, to)| *to = *from)
        .count()
}

/// Copies ASCII from source to destination zero-extending it to UTF-16 up to
/// the first non-ASCII byte (or the end of the input if it is ASCII in its
/// entirety).
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// Returns the number of `u16`s written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn copy_ascii_to_basic_latin(src: &[u8], dst: &mut [u16]) -> usize {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    src.iter()
        .zip(dst.iter_mut())
        .take_while(|&(from, _)| *from < 0x80)
        .map(|(from, to)| *to = *from as u16)
        .count()
}

/// Copies Basic Latin from source to destination narrowing it to ASCII up to
/// the first non-Basic Latin code unit (or the end of the input if it is
/// Basic Latin in its entirety).
///
/// The length of the destination buffer must be at least the length of the
/// source buffer.
///
/// Returns the number of bytes written.
///
/// # Panics
///
/// Panics if the destination buffer is shorter than stated above.
#[inline]
pub fn copy_basic_latin_to_ascii(src: &[u16], dst: &mut [u8]) -> usize {
    assert!(dst.len() >= src.len(),
            "Destination must not be shorter than the source.");
    src.iter()
        .zip(dst.iter_mut())
        .take_while(|&(from, _)| *from < 0x80)
        .map(|(from, to)| *to = *from as u8)
        .count()
}

// Any copyright to the test code below this comment is dedicated to the
// Public Domain. http://creativecommons.org/publicdomain/zero/1.0/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_ascii_success() {
        let mut src: Vec<u8> = Vec::with_capacity(128);
        src.resize(128, 0);
        for i in 0..src.len() {
            src[i] = i as u8;
        }
        for i in 0..src.len() {
            assert!(is_ascii(&src[i..]));
        }
    }

    #[test]
    fn test_is_ascii_fail() {
        let mut src: Vec<u8> = Vec::with_capacity(128);
        src.resize(128, 0);
        for i in 0..src.len() {
            src[i] = i as u8;
        }
        for i in 0..src.len() {
            let tail = &mut src[i..];
            for j in 0..tail.len() {
                tail[j] = 0xA0;
                assert!(!is_ascii(tail));
            }
        }
    }

    #[test]
    fn test_is_basic_latin_success() {
        let mut src: Vec<u16> = Vec::with_capacity(128);
        src.resize(128, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            assert!(is_basic_latin(&src[i..]));
        }
    }

    #[test]
    fn test_is_basic_latin_fail() {
        let mut src: Vec<u16> = Vec::with_capacity(128);
        src.resize(128, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let tail = &mut src[i..];
            for j in 0..tail.len() {
                tail[j] = 0xA0;
                assert!(!is_basic_latin(tail));
            }
        }
    }

    #[test]
    fn test_is_utf16_latin1_success() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            assert!(is_utf16_latin1(&src[i..]));
            assert_eq!(check_utf16_for_latin1_and_bidi(&src[i..]), Latin1Bidi::Latin1);
        }
    }

    #[test]
    fn test_is_utf16_latin1_fail() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let tail = &mut src[i..];
            for j in 0..tail.len() {
                tail[j] = 0x100 + j as u16;
                assert!(!is_utf16_latin1(tail));
                assert_ne!(check_utf16_for_latin1_and_bidi(tail), Latin1Bidi::Latin1);
            }
        }
    }

    #[test]
    fn test_is_str_latin1_success() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let s = String::from_utf16(&src[i..]).unwrap();
            assert!(is_str_latin1(&s[..]));
            assert_eq!(check_str_for_latin1_and_bidi(&s[..]), Latin1Bidi::Latin1);
        }
    }

    #[test]
    fn test_is_str_latin1_fail() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let tail = &mut src[i..];
            for j in 0..tail.len() {
                tail[j] = 0x100 + j as u16;
                let s = String::from_utf16(tail).unwrap();
                assert!(!is_str_latin1(&s[..]));
                assert_ne!(check_str_for_latin1_and_bidi(&s[..]), Latin1Bidi::Latin1);
            }
        }
    }

    #[test]
    fn test_is_utf8_latin1_success() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let s = String::from_utf16(&src[i..]).unwrap();
            assert!(is_utf8_latin1(s.as_bytes()));
            assert_eq!(check_utf8_for_latin1_and_bidi(s.as_bytes()), Latin1Bidi::Latin1);
        }
    }

    #[test]
    fn test_is_utf8_latin1_fail() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        for i in 0..src.len() {
            src[i] = i as u16;
        }
        for i in 0..src.len() {
            let tail = &mut src[i..];
            for j in 0..tail.len() {
                tail[j] = 0x100 + j as u16;
                let s = String::from_utf16(tail).unwrap();
                assert!(!is_utf8_latin1(s.as_bytes()));
                assert_ne!(check_utf8_for_latin1_and_bidi(s.as_bytes()), Latin1Bidi::Latin1);
            }
        }
    }

    #[test]
    fn test_is_utf8_latin1_invalid() {
        assert!(!is_utf8_latin1(b"\xC3"));
        assert!(!is_utf8_latin1(b"a\xC3"));
        assert!(!is_utf8_latin1(b"\xFF"));
        assert!(!is_utf8_latin1(b"a\xFF"));
        assert!(!is_utf8_latin1(b"\xC3\xFF"));
        assert!(!is_utf8_latin1(b"a\xC3\xFF"));
    }

    #[test]
    fn test_convert_utf8_to_utf16() {
        let src = "abcdefghijklmnopqrstu\u{1F4A9}v\u{2603}w\u{00B6}xyzz";
        let mut dst: Vec<u16> = Vec::with_capacity(src.len() + 1);
        dst.resize(src.len() + 1, 0);
        let len = convert_utf8_to_utf16(src.as_bytes(), &mut dst[..]);
        dst.truncate(len);
        let reference: Vec<u16> = src.encode_utf16().collect();
        assert_eq!(dst, reference);
    }

    #[test]
    fn test_convert_str_to_utf16() {
        let src = "abcdefghijklmnopqrstu\u{1F4A9}v\u{2603}w\u{00B6}xyzz";
        let mut dst: Vec<u16> = Vec::with_capacity(src.len());
        dst.resize(src.len(), 0);
        let len = convert_str_to_utf16(src, &mut dst[..]);
        dst.truncate(len);
        let reference: Vec<u16> = src.encode_utf16().collect();
        assert_eq!(dst, reference);
    }

    #[test]
    fn test_convert_utf16_to_utf8() {
        let reference = "abcdefghijklmnopqrstu\u{1F4A9}v\u{2603}w\u{00B6}xyzz";
        let src: Vec<u16> = reference.encode_utf16().collect();
        let mut dst: Vec<u8> = Vec::with_capacity(src.len() * 3 + 1);
        dst.resize(src.len() * 3 + 1, 0);
        let len = convert_utf16_to_utf8(&src[..], &mut dst[..]);
        dst.truncate(len);
        assert_eq!(dst, reference.as_bytes());
    }

    #[test]
    fn test_convert_latin1_to_utf16() {
        let mut src: Vec<u8> = Vec::with_capacity(256);
        src.resize(256, 0);
        let mut reference: Vec<u16> = Vec::with_capacity(256);
        reference.resize(256, 0);
        for i in 0..256 {
            src[i] = i as u8;
            reference[i] = i as u16;
        }
        let mut dst: Vec<u16> = Vec::with_capacity(src.len());
        dst.resize(src.len(), 0);
        convert_latin1_to_utf16(&src[..], &mut dst[..]);
        assert_eq!(dst, reference);
    }

    #[test]
    fn test_convert_latin1_to_utf8() {
        let mut src: Vec<u8> = Vec::with_capacity(256);
        src.resize(256, 0);
        let mut reference: Vec<u16> = Vec::with_capacity(256);
        reference.resize(256, 0);
        for i in 0..256 {
            src[i] = i as u8;
            reference[i] = i as u16;
        }
        let s = String::from_utf16(&reference[..]).unwrap();
        let mut dst: Vec<u8> = Vec::with_capacity(src.len() * 2);
        dst.resize(src.len() * 2, 0);
        let len = convert_latin1_to_utf8(&src[..], &mut dst[..]);
        dst.truncate(len);
        assert_eq!(&dst[..], s.as_bytes());
    }

    #[test]
    fn test_convert_utf8_to_latin1_lossy() {
        let mut reference: Vec<u8> = Vec::with_capacity(256);
        reference.resize(256, 0);
        let mut src16: Vec<u16> = Vec::with_capacity(256);
        src16.resize(256, 0);
        for i in 0..256 {
            src16[i] = i as u16;
            reference[i] = i as u8;
        }
        let src = String::from_utf16(&src16[..]).unwrap();
        let mut dst: Vec<u8> = Vec::with_capacity(src.len());
        dst.resize(src.len(), 0);
        let len = convert_utf8_to_latin1_lossy(src.as_bytes(), &mut dst[..]);
        dst.truncate(len);
        assert_eq!(dst, reference);
    }

    #[test]
    fn test_convert_utf16_to_latin1_lossy() {
        let mut src: Vec<u16> = Vec::with_capacity(256);
        src.resize(256, 0);
        let mut reference: Vec<u8> = Vec::with_capacity(256);
        reference.resize(256, 0);
        for i in 0..256 {
            src[i] = i as u16;
            reference[i] = i as u8;
        }
        let mut dst: Vec<u8> = Vec::with_capacity(src.len());
        dst.resize(src.len(), 0);
        convert_utf16_to_latin1_lossy(&src[..], &mut dst[..]);
        assert_eq!(dst, reference);
    }

    #[test]
    fn test_utf16_valid_up_to() {
        let valid = vec![0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                         0x2603u16, 0xD83Du16, 0xDCA9u16, 0x00B6u16];
        assert_eq!(utf16_valid_up_to(&valid[..]), 16);;
        let lone_high = vec![0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                             0u16, 0u16, 0x2603u16, 0xD83Du16, 0x00B6u16];
        assert_eq!(utf16_valid_up_to(&lone_high[..]), 14);;
        let lone_low = vec![0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                            0u16, 0u16, 0x2603u16, 0xDCA9u16, 0x00B6u16];
        assert_eq!(utf16_valid_up_to(&lone_low[..]), 14);;
        let lone_high_at_end = vec![0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                                    0u16, 0u16, 0u16, 0x2603u16, 0x00B6u16, 0xD83Du16];
        assert_eq!(utf16_valid_up_to(&lone_high_at_end[..]), 15);;
    }

    #[test]
    fn test_ensure_utf16_validity() {
        let mut src = vec![0u16, 0xD83Du16, 0u16, 0u16, 0u16, 0xD83Du16, 0xDCA9u16, 0u16, 0u16,
                           0u16, 0u16, 0u16, 0u16, 0xDCA9u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                           0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16];
        let reference = vec![0u16, 0xFFFDu16, 0u16, 0u16, 0u16, 0xD83Du16, 0xDCA9u16, 0u16, 0u16,
                             0u16, 0u16, 0u16, 0u16, 0xFFFDu16, 0u16, 0u16, 0u16, 0u16, 0u16,
                             0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16, 0u16,
                             0u16];
        ensure_utf16_validity(&mut src[..]);
        assert_eq!(src, reference);
    }

    #[test]
    fn test_is_char_bidi() {
        assert!(!is_char_bidi('a'));
        assert!(!is_char_bidi('\u{03B1}'));
        assert!(!is_char_bidi('\u{3041}'));
        assert!(!is_char_bidi('\u{1F4A9}'));
        assert!(!is_char_bidi('\u{FE00}'));
        assert!(!is_char_bidi('\u{202C}'));
        assert!(is_char_bidi('\u{0590}'));
        assert!(is_char_bidi('\u{08FF}'));
        assert!(is_char_bidi('\u{061C}'));
        assert!(is_char_bidi('\u{FB50}'));
        assert!(is_char_bidi('\u{FDFF}'));
        assert!(is_char_bidi('\u{FE70}'));
        assert!(is_char_bidi('\u{FEFF}'));
        assert!(is_char_bidi('\u{200F}'));
        assert!(is_char_bidi('\u{202B}'));
        assert!(is_char_bidi('\u{202E}'));
        assert!(is_char_bidi('\u{2067}'));
        assert!(is_char_bidi('\u{10800}'));
        assert!(is_char_bidi('\u{10FFF}'));
        assert!(is_char_bidi('\u{1E800}'));
        assert!(is_char_bidi('\u{1EFFF}'));
    }

    #[test]
    fn test_is_utf16_code_unit_bidi() {
        assert!(!is_utf16_code_unit_bidi(0x0062));
        assert!(!is_utf16_code_unit_bidi(0x03B1));
        assert!(!is_utf16_code_unit_bidi(0x3041));
        assert!(!is_utf16_code_unit_bidi(0xD801));
        assert!(!is_utf16_code_unit_bidi(0xFE00));
        assert!(!is_utf16_code_unit_bidi(0x202C));
        assert!(is_utf16_code_unit_bidi(0x0590));
        assert!(is_utf16_code_unit_bidi(0x08FF));
        assert!(is_utf16_code_unit_bidi(0x061C));
        assert!(is_utf16_code_unit_bidi(0xFB50));
        assert!(is_utf16_code_unit_bidi(0xFDFF));
        assert!(is_utf16_code_unit_bidi(0xFE70));
        assert!(is_utf16_code_unit_bidi(0xFEFF));
        assert!(is_utf16_code_unit_bidi(0x200F));
        assert!(is_utf16_code_unit_bidi(0x202B));
        assert!(is_utf16_code_unit_bidi(0x202E));
        assert!(is_utf16_code_unit_bidi(0x2067));
        assert!(is_utf16_code_unit_bidi(0xD802));
        assert!(is_utf16_code_unit_bidi(0xD803));
        assert!(is_utf16_code_unit_bidi(0xD83A));
        assert!(is_utf16_code_unit_bidi(0xD83B));
    }

    #[test]
    fn test_is_str_bidi() {
        assert!(!is_str_bidi("abcdefghijklmnopaabcdefghijklmnop"));
        assert!(!is_str_bidi("abcdefghijklmnop\u{03B1}abcdefghijklmnop"));
        assert!(!is_str_bidi("abcdefghijklmnop\u{3041}abcdefghijklmnop"));
        assert!(!is_str_bidi("abcdefghijklmnop\u{1F4A9}abcdefghijklmnop"));
        assert!(!is_str_bidi("abcdefghijklmnop\u{FE00}abcdefghijklmnop"));
        assert!(!is_str_bidi("abcdefghijklmnop\u{202C}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{0590}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{08FF}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{061C}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{FB50}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{FDFF}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{FE70}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{FEFF}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{200F}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{202B}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{202E}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{2067}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{10800}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{10FFF}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{1E800}abcdefghijklmnop"));
        assert!(is_str_bidi("abcdefghijklmnop\u{1EFFF}abcdefghijklmnop"));
    }

    #[test]
    fn test_is_utf8_bidi() {
        assert!(!is_utf8_bidi("abcdefghijklmnopaabcdefghijklmnop".as_bytes()));
        assert!(!is_utf8_bidi("abcdefghijklmnop\u{03B1}abcdefghijklmnop".as_bytes()));
        assert!(!is_utf8_bidi("abcdefghijklmnop\u{3041}abcdefghijklmnop".as_bytes()));
        assert!(!is_utf8_bidi("abcdefghijklmnop\u{1F4A9}abcdefghijklmnop".as_bytes()));
        assert!(!is_utf8_bidi("abcdefghijklmnop\u{FE00}abcdefghijklmnop".as_bytes()));
        assert!(!is_utf8_bidi("abcdefghijklmnop\u{202C}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{0590}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{08FF}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{061C}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{FB50}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{FDFF}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{FE70}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{FEFF}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{200F}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{202B}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{202E}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{2067}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{10800}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{10FFF}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{1E800}abcdefghijklmnop".as_bytes()));
        assert!(is_utf8_bidi("abcdefghijklmnop\u{1EFFF}abcdefghijklmnop".as_bytes()));
    }

    #[test]
    fn test_is_utf16_bidi() {
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x0062, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x03B1, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x3041, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD801, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFE00, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(!is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202C, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x0590, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x08FF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x061C, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFB50, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFDFF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFE70, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFEFF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x200F, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202B, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202E, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x2067, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD802, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD803, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD83A, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD83B, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));

        assert!(is_utf16_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x3041, 0x0590, 0x3041, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]));
    }

    #[test]
    fn test_check_str_for_latin1_and_bidi() {
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnopaabcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{03B1}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{3041}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{1F4A9}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{FE00}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_ne!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{202C}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{0590}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{08FF}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{061C}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{FB50}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{FDFF}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{FE70}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{FEFF}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{200F}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{202B}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{202E}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{2067}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{10800}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{10FFF}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{1E800}abcdefghijklmnop"), Latin1Bidi::Bidi);
        assert_eq!(check_str_for_latin1_and_bidi("abcdefghijklmnop\u{1EFFF}abcdefghijklmnop"), Latin1Bidi::Bidi);
    }

    #[test]
    fn test_check_utf8_for_latin1_and_bidi() {
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnopaabcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{03B1}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{3041}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{1F4A9}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{FE00}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_ne!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{202C}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{0590}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{08FF}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{061C}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{FB50}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{FDFF}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{FE70}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{FEFF}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{200F}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{202B}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{202E}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{2067}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{10800}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{10FFF}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{1E800}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
        assert_eq!(check_utf8_for_latin1_and_bidi("abcdefghijklmnop\u{1EFFF}abcdefghijklmnop".as_bytes()), Latin1Bidi::Bidi);
    }

    #[test]
    fn test_check_utf16_for_latin1_and_bidi() {
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x0062, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x03B1, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x3041, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD801, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFE00, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_ne!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202C, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x0590, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x08FF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x061C, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFB50, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFDFF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFE70, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xFEFF, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x200F, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202B, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x202E, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x2067, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD802, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD803, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD83A, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xD83B, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);

        assert_eq!(check_utf16_for_latin1_and_bidi(&[0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x3041, 0x0590, 0x3041, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69]), Latin1Bidi::Bidi);
    }
}
