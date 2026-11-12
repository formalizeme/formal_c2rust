use fleur;
use fleur::fleur::BloomFilter;
use fleur::fleur::Header;
use rand::Rng;
use std::fs::File;
use std::io::Read;
use std::path::Path;

struct Tester {
    bf: BloomFilter,
    buf: Vec<Vec<u8>>,
}

fn generate_test_value(length: u64) -> Vec<u8> {
    let mut rng = rand::thread_rng();
    (0..length).map(|_| rng.gen::<u8>()).collect()
}

fn generate_example_filter(capacity: u64, p: f64, samples: u64) -> Tester {
    let mut bf = BloomFilter::initialize(capacity, p, b"foobar");

    let mut test_bufs = Vec::with_capacity(samples as usize);
    for _ in 0..samples {
        let buf = generate_test_value(100);
        bf.add(buf.as_slice());
        test_bufs.push(buf);
    }

    Tester { bf, buf: test_bufs }
}

#[test]
fn test_reading_header() {
    let mut file = File::open("src/bin/header.bin").expect("Failed to open header.bin");
    let mut header_bytes = Vec::new();
    file.read_to_end(&mut header_bytes)
        .expect("Failed to read header");

    let h = unsafe { std::ptr::read(header_bytes.as_ptr() as *const Header) };

    assert_eq!(h.version, 1);
    assert_eq!(h.n, 354253067);
    assert_eq!(h.p, 0.0001);
    assert_eq!(h.k, 14);
    assert_eq!(h.m, 6791072655);
    assert_eq!(h.n_value, 354249652);
    assert!(h.check());

    // hang0 p too small
    let mut file_hang0 = File::open("src/bin/hang0.bin").expect("Failed to open hang0.bin");
    let mut hang0_bytes = Vec::new();
    file_hang0.read_to_end(&mut hang0_bytes).expect("Failed to read hang0");
    let h0 = unsafe { std::ptr::read(hang0_bytes.as_ptr() as *const Header) };
    assert!(!h0.check());

    // hang1 bad header version
    let mut file_hang1 = File::open("src/bin/hang1.bin").expect("Failed to open hang1.bin");
    let mut hang1_bytes = Vec::new();
    file_hang1.read_to_end(&mut hang1_bytes).expect("Failed to read hang1");
    let h1 = unsafe { std::ptr::read(hang1_bytes.as_ptr() as *const Header) };
    assert!(!h1.check());
}

#[test]
fn test_reading_full() {
    let file = File::open("src/bin/datatest.bloom").expect("Failed to open datatest.bloom");
    let bf = BloomFilter::from_file(file);
    assert_eq!(bf.error, 0);
    assert_eq!(bf.m, 450);
    println!("{}", bf);

    // hang2 p above 1
    let file_hang2 = File::open("src/bin/hang2.bin").expect("Failed to open hang2.bin");
    let bf1 = BloomFilter::from_file(file_hang2);
    assert_eq!(bf1.error, 1);
}

#[test]
fn test_writing() {
    let path = Path::new("src/bin/writing-test.bloom");
    let file = File::create(path).expect("Failed to create file");

    let tester = generate_example_filter(1000, 0.001, 100);
    let ret = tester.bf.to_file(file);
    assert_eq!(ret, 1);
}

#[test]
fn test_initialize() {
    let bf = BloomFilter::initialize(10000, 0.001, b"");
    assert_eq!(bf.h.k, 10);
    assert_eq!(bf.h.m, 143775);
    let expected_m = ((bf.h.m as f64) / 64.0).ceil() as u64;
    assert_eq!(bf.m, expected_m);
    for i in 0..bf.m as usize {
        assert_eq!(bf.v[i], 0);
    }
}

#[test]
fn test_fingerprint() {
    let bf = BloomFilter::initialize(100000, 0.01, b"");

    let input = "bar";
    let fp = bf.fingerprint(input.as_bytes());
    let expected = vec![20311, 36825, 412501, 835777, 658914, 853361, 307361];
    assert_eq!(fp, expected);
}

#[test]
fn test_checking() {
    let capacity = 100000;
    let p = 0.001;
    let samples = 100000;

    let tester = generate_example_filter(capacity, p, samples);

    for buf in &tester.buf {
        assert_eq!(tester.bf.check(buf), 1);
    }

    let not_in_filter = b"this is not in the filter";
    assert_eq!(tester.bf.check(not_in_filter), 0);
}

#[test]
fn test_joining() {
    let file1 = File::open("src/bin/join1.bloom").expect("Failed to open join1.bloom");
    let file_full = File::open("src/bin/datatest.bloom").expect("Failed to open datatest.bloom");
    let file2 = File::open("src/bin/join2.bloom").expect("Failed to open join2.bloom");
    let file3 = File::open("src/bin/join3.bloom").expect("Failed to open join3.bloom");

    let j1 = BloomFilter::from_file(file1);
    let mut j0 = BloomFilter::from_file(file_full);
    let mut j2 = BloomFilter::from_file(file2);
    let mut j3 = BloomFilter::from_file(file3);

    assert_eq!(j2.join(&j1), -1);
    assert_eq!(j0.join(&j1), 0);
    assert_eq!(j3.join(&j1), 1);
}

fn main() {
}
