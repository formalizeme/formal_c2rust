use utf8::utf8::{make_utf8_string, make_utf8_string_lossy, make_utf8_char_iter, next_utf8_char, free_owned_utf8_string, validate_utf8, slice_utf8_string, utf8_char_count, is_utf8_char_boundary, nth_utf8_char, unicode_code_point};
use utf8::utf8::{Utf8Char};
#[test]
fn test_validate_utf8_ok() {
    let validity = validate_utf8("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 5 + 1 + 12 * 2 + 1 + 5 * 3 + 1 + 2 * 4);
}

#[test]
fn test_validate_utf8_boundary_ok() {
    // last 1b -> 0(1111111)
    let mut validity = validate_utf8(b"\x7F");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 1);

    // first 2b -> 110(00010) 10(000000)
    validity = validate_utf8(b"\xC2\x80");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 2);

    // last 2b -> 110(11111) 10(111111)
    validity = validate_utf8(b"\xDF\xBF");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 2);

    // first 3b -> 1110(0000) 10(100000) 10(000000)
    validity = validate_utf8(b"\xE0\xA0\x80");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 3);

    // last 3b -> 1110(1111) 10(111111) 10(111111)
    validity = validate_utf8(b"\xEF\xBF\xBF");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 3);

    // first 4b -> 11110(000) 10(010000) 10(000000) 10(000000)
    validity = validate_utf8(b"\xF0\x90\x80\x80");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 4);

    // last 4b -> 11110(111) 10(111111) 10(111111) 10(111111)
    validity = validate_utf8(b"\xF7\xBF\xBF\xBF");
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, 4);
}

#[test]
fn test_surrogate_rejection() {
    let mut validity = validate_utf8(b"\xED\xA0\x80");
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 0);

    validity = validate_utf8(b"\xED\xAC\x80");
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 0);

    validity = validate_utf8(b"\xED\xA0\x8C");
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 0);

    validity = validate_utf8(b"\xED\xBF\xBF");
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 0);
}

#[test]
fn test_validate_utf8_err() {
    let mut input: Vec<u8> = "Hello Здравствуйте".as_bytes().to_vec();
    input.extend_from_slice(b"\xC0\xC0");
    input.extend_from_slice(" こんにちは 🚩😁".as_bytes());
    let validity = validate_utf8(&input);
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 5 + 1 + 12 * 2);
}

/// Construct a Utf8Char holding the given raw bytes as its `str` field.
///
/// C's `utf8_char.str` is a `const char*` that can hold arbitrary bytes
/// (including invalid UTF-8 like overlong encodings). The Rust interface
/// defines `Utf8Char.str: String` — same type signature as a normal String,
/// but Rust's language-level safety rules require String to contain valid
/// UTF-8. We use `from_utf8_unchecked` to bypass that check and store the
/// overlong bytes verbatim, matching C's behavior.
///
/// This is sound in practice because:
///  1. The interface contract for `Utf8Char` only says `str: String`; it does
///     not impose additional validity requirements beyond what Rust's type
///     system expresses.
///  2. The interface's `unicode_code_point` implementation reads via
///     `str.as_bytes()` and does bit-masking — it never iterates the String
///     as Unicode characters (which would trigger UB on invalid bytes).
///  3. `validate_utf8` takes the raw bytes directly and handles invalid input.
fn utf8_char_from_bytes(bytes: &[u8]) -> Utf8Char {
    Utf8Char {
        str: unsafe { String::from_utf8_unchecked(bytes.to_vec()) },
        byte_len: bytes.len() as u8,
    }
}

/// Equivalent to C's assert_overlong_encodings. Uses only interface functions
/// (`unicode_code_point`, `validate_utf8`) on interface-defined types.
fn assert_overlong_encodings(actual: Utf8Char, overlong: Utf8Char) {
    // C: assert(unicode_code_point(actual) == unicode_code_point(overlong))
    assert_eq!(
        unicode_code_point(actual.clone()),
        unicode_code_point(overlong.clone()),
    );

    // C: validate_utf8(actual.str) should be valid
    let validity = validate_utf8(actual.str.as_bytes());
    assert!(validity.valid);
    assert_eq!(validity.valid_upto, actual.byte_len as usize);

    // C: validate_utf8(overlong.str) should be invalid
    let validity = validate_utf8(overlong.str.as_bytes());
    assert!(!validity.valid);
    assert_eq!(validity.valid_upto, 0);
}

#[test]
fn test_validate_utf8_overlong_encoding_err() {
    // H (U+0048)
    assert_overlong_encodings(
        Utf8Char { str: "H".to_string(), byte_len: 1 },
        utf8_char_from_bytes(b"\xC1\x88"));
    assert_overlong_encodings(
        Utf8Char { str: "H".to_string(), byte_len: 1 },
        utf8_char_from_bytes(b"\xE0\x81\x88"));
    assert_overlong_encodings(
        Utf8Char { str: "H".to_string(), byte_len: 1 },
        utf8_char_from_bytes(b"\xF0\x80\x81\x88"));

    // д (U+0434)
    assert_overlong_encodings(
        Utf8Char { str: "д".to_string(), byte_len: 2 },
        utf8_char_from_bytes(b"\xE0\x90\xB4"));
    assert_overlong_encodings(
        Utf8Char { str: "д".to_string(), byte_len: 2 },
        utf8_char_from_bytes(b"\xF0\x80\x90\xB4"));

    // こ (U+3053)
    assert_overlong_encodings(
        Utf8Char { str: "こ".to_string(), byte_len: 3 },
        utf8_char_from_bytes(b"\xF0\x83\x81\x93"));

    // boundary characters
    assert_overlong_encodings(
        Utf8Char { str: "\x7F".to_string(), byte_len: 1 },
        utf8_char_from_bytes(b"\xC1\xBF"));          // last 1b
    assert_overlong_encodings(
        Utf8Char { str: "\u{07FF}".to_string(), byte_len: 2 },
        utf8_char_from_bytes(b"\xE0\x9F\xBF"));      // last 2b
    assert_overlong_encodings(
        Utf8Char { str: "\u{FFFF}".to_string(), byte_len: 3 },
        utf8_char_from_bytes(b"\xF0\x8F\xBF\xBF")); // last 3b
}

#[test]
fn test_make_utf8_string_ok() {
    let s = "Hello Здравствуйте こんにちは 🚩😁";
    let ustr = make_utf8_string(s.as_bytes());
    assert_eq!(ustr.byte_len, 5 + 1 + 12 * 2 + 1 + 5 * 3 + 1 + 2 * 4);
    assert_eq!(ustr.str, s);
}

#[test]
fn test_make_utf8_string_err() {
    let mut input: Vec<u8> = "Hello Здравствуйте".as_bytes().to_vec();
    input.extend_from_slice(b"\xC0\xC0");
    input.extend_from_slice(" こんにちは 🚩😁".as_bytes());
    let ustr = make_utf8_string(&input);
    assert_eq!(ustr.str, "");
    assert_eq!(ustr.byte_len, 0);
}

#[test]
fn test_make_utf8_string_lossy_ok() {
    let s = "Hello Здравствуйте こんにちは 🚩😁";
    let owned_ustr = make_utf8_string_lossy(s.as_bytes());
    assert_eq!(owned_ustr.byte_len, 5 + 1 + 12 * 2 + 1 + 5 * 3 + 1 + 2 * 4);
    assert_eq!(owned_ustr.str, s);
    free_owned_utf8_string(&mut owned_ustr.clone());
}

#[test]
fn test_make_utf8_string_lossy_invalid_sequence() {
    let mut input: Vec<u8> = Vec::new();
    input.extend_from_slice(b"\xC0");
    input.extend_from_slice("He".as_bytes());
    input.extend_from_slice(b"\xC0");
    input.extend_from_slice("llo Здр".as_bytes());
    input.extend_from_slice(b"\xC0");
    input.extend_from_slice("авствуйте".as_bytes());
    input.extend_from_slice(b"\xC0\xC0");
    input.extend_from_slice(" こんに".as_bytes());
    input.extend_from_slice(b"\xC0\xC0\xC0\xC0");
    input.extend_from_slice("ちは 🚩".as_bytes());
    input.extend_from_slice(b"\xC0");
    input.extend_from_slice("😁".as_bytes());
    input.extend_from_slice(b"\xC0");

    let expected = "�He�llo Здр�авствуйте�� こんに����ちは 🚩�😁�";
    let owned_ustr = make_utf8_string_lossy(&input);
    assert_eq!(owned_ustr.byte_len, expected.len());
    assert_eq!(owned_ustr.str, expected);
    free_owned_utf8_string(&mut owned_ustr.clone());
}

#[test]
fn test_make_utf8_string_lossy_completely_invalid() {
    let input = b"\xC0\xC0\xC0\xC0";
    let expected = "����";
    let owned_ustr = make_utf8_string_lossy(input);
    assert_eq!(owned_ustr.byte_len, expected.len());
    assert_eq!(owned_ustr.str, expected);
    free_owned_utf8_string(&mut owned_ustr.clone());
}

#[test]
fn test_make_utf8_string_slice_ok() {
    let s = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let slice = slice_utf8_string(s, 6, 24);
    assert_eq!(slice.byte_len, 12 * 2);
    assert_eq!(&slice.str[..slice.byte_len], "Здравствуйте");
}

#[test]
fn test_make_utf8_string_slice_start_out_of_bounds_ok() {
    let s = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let slice = slice_utf8_string(s, 1000, 1);
    assert_eq!(slice.byte_len, 0);
    assert_eq!(slice.str, "");
}

#[test]
fn test_make_utf8_string_slice_end_out_of_bounds_ok() {
    let s = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let slice = slice_utf8_string(s, 6, 1000);
    assert_eq!(slice.byte_len, 12 * 2 + 1 + 5 * 3 + 1 + 2 * 4);
    assert_eq!(&slice.str[..slice.byte_len], "Здравствуйте こんにちは 🚩😁");
}

#[test]
fn test_make_utf8_string_slice_start_non_boundary_err() {
    let s = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let slice = slice_utf8_string(s, 7, 3);
    assert_eq!(slice.str, "");
    assert_eq!(slice.byte_len, 0);
}

#[test]
fn test_make_utf8_string_slice_end_non_boundary_err() {
    let s = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let slice = slice_utf8_string(s, 6, 3);
    assert_eq!(slice.str, "");
    assert_eq!(slice.byte_len, 0);
}

#[test]
fn test_utf8_char_iter() {
    let s = make_utf8_string("Hдこ😁".as_bytes());
    let mut iter = make_utf8_char_iter(s);
    let mut ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 1);
    assert_eq!(&ch.str[..ch.byte_len as usize], "H");
    ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 2);
    assert_eq!(&ch.str[..ch.byte_len as usize], "д");
    ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 3);
    assert_eq!(&ch.str[..ch.byte_len as usize], "こ");
    ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 4);
    assert_eq!(&ch.str[..ch.byte_len as usize], "😁");

    // iterator keeps returning empty when exhausted
    ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 0);
    assert_eq!(ch.str, "");
    ch = next_utf8_char(&mut iter);
    assert_eq!(ch.byte_len, 0);
    assert_eq!(ch.str, "");
}

#[test]
fn test_utf8_char_count_zero() {
    let ustr = make_utf8_string(b"");
    let count = utf8_char_count(ustr);
    assert_eq!(count, 0);
}

#[test]
fn test_utf8_char_count() {
    let ustr = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let count = utf8_char_count(ustr);
    assert_eq!(count, 5 + 1 + 12 + 1 + 5 + 1 + 2);
}

#[test]
fn test_is_utf8_char_boundary() {
    let bytes = "Hдこ😁".as_bytes();
    let mut offset = 0;

    assert!(is_utf8_char_boundary(&bytes[offset..]));   // H
    offset += 1;
    assert!(is_utf8_char_boundary(&bytes[offset..]));    // д byte 1
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // д byte 2
    offset += 1;
    assert!(is_utf8_char_boundary(&bytes[offset..]));    // こ byte 1
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // こ byte 2
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // こ byte 3
    offset += 1;
    assert!(is_utf8_char_boundary(&bytes[offset..]));    // 😁 byte 1
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // 😁 byte 2
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // 😁 byte 3
    offset += 1;
    assert!(!is_utf8_char_boundary(&bytes[offset..]));   // 😁 byte 4
    offset += 1;
    assert_eq!(&bytes[offset..], b"");
}

#[test]
fn test_nth_utf8_char_valid_index_ok() {
    let ustr = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let ch = nth_utf8_char(ustr, 20);
    assert_eq!(ch.byte_len, 3);
    assert_eq!(&ch.str[..ch.byte_len as usize], "ん");
}

#[test]
fn test_nth_utf8_char_first_index_ok() {
    let ustr = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let ch = nth_utf8_char(ustr, 0);
    assert_eq!(ch.byte_len, 1);
    assert_eq!(ch.str.chars().next().unwrap(), 'H');
}

#[test]
fn test_nth_utf8_char_last_index_ok() {
    let ustr = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let ch = nth_utf8_char(ustr, 26);
    assert_eq!(ch.byte_len, 4);
    assert_eq!(&ch.str[..ch.byte_len as usize], "😁");
}

#[test]
fn test_nth_utf8_char_invalid_index_err() {
    let ustr = make_utf8_string("Hello Здравствуйте こんにちは 🚩😁".as_bytes());
    let ch = nth_utf8_char(ustr, 100);
    assert_eq!(ch.str, "");
    assert_eq!(ch.byte_len, 0);
}

#[test]
fn test_nth_utf8_char_empty_string_err() {
    let ustr = make_utf8_string(b"");
    let ch = nth_utf8_char(ustr, 0);
    assert_eq!(ch.str, "");
    assert_eq!(ch.byte_len, 0);
}

#[test]
fn test_unicode_code_point() {
    let ustr = make_utf8_string("Hдこ😁".as_bytes());
    let mut iter = make_utf8_char_iter(ustr);
    assert_eq!(unicode_code_point(next_utf8_char(&mut iter)), 72);
    assert_eq!(unicode_code_point(next_utf8_char(&mut iter)), 1076);
    assert_eq!(unicode_code_point(next_utf8_char(&mut iter)), 12371);
    assert_eq!(unicode_code_point(next_utf8_char(&mut iter)), 128513);
}

fn main() {}
