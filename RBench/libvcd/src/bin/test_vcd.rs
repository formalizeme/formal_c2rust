use std::{env, process};

use libvcd::vcd::*;

/// Extract a C-style null-terminated string from a fixed-size byte array.
/// Equivalent to C's `printf("%s", buf)` which stops at the first '\0'.
fn c_str(buf: &[u8]) -> &str {
    let len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    std::str::from_utf8(&buf[..len]).unwrap_or("")
}

pub fn print_vcd(vcd: &VCD) {
    println!(
        "{{\n\tdate=\"{}\",\n\tversion=\"{}\",\n\ttimescale= {{\n\t\tunit=\"{}\",\n\t\tscale=\"{}\"\n\t}},\n\tsignal= {{",
        String::from_utf8_lossy(&vcd.date),
        String::from_utf8_lossy(&vcd.version),
        String::from_utf8_lossy(&vcd.timescale.unit),
        vcd.timescale.scale
    );

    for signal in &vcd.signals {
        println!(
            "\t\t{}= {{\n\t\t\tsize={},\n\t\t\tchanges= {{",
            String::from_utf8_lossy(&signal.name),
            signal.size
        );

        for value_change in &signal.value_changes {
            println!(
                "\t\t\t\t{{\n\t\t\t\t\ttimestamp={},\n\t\t\t\t\tvalue={}\n\t\t\t\t}},",
                value_change.timestamp,
                String::from_utf8_lossy(&value_change.value)
            );
        }

        println!("\t\t\t}},\n\t\t}},");
    }
    println!("\t}}\n}}");
}

#[test]
fn test_ram_vcd() {
    // 1. Read the VCD (adjust path as needed).
    let vcd_file_path = "src/bin/assets/ram.vcd";
    let vcd = VCD::read_from_path(vcd_file_path)
        .expect("Failed to read the 'ram.vcd' file");

    // 2. Assert header fields (using c_str to strip null bytes from fixed-size arrays,
    //    matching C's printf("%s", vcd->date) which stops at the first '\0').
    assert_eq!(c_str(&vcd.date), "Fri Jul 15 15:17:36 2022");
    assert_eq!(c_str(&vcd.version), "Icarus Verilog");
    assert_eq!(c_str(&vcd.timescale.unit), "s");
    assert_eq!(vcd.timescale.scale, 1);

    // 3. Check signals by name. The VCD file declares:
    //    "$var wire 9 ! matched [8:0] $end" so the signal name is "matched [8:0]".
    let matched_signal = vcd
        .get_signal_by_name("matched [8:0]")
        .expect("Expected to find signal 'matched [8:0]'");
    assert_eq!(matched_signal.size, 9);

    // 4. Check a specific timestamp value. At #25 the VCD has `b10010 !`,
    //    which is a 5-bit binary value: 10010.
    let val_25 = matched_signal
        .get_value_at_timestamp(25)
        .expect("No value for 'matched [8:0]' at timestamp 25");
    assert_eq!(c_str(val_25), "10010");

    // 5. Check the clock signal.
    let clock_signal = vcd
        .get_signal_by_name("clock")
        .expect("Expected to find signal 'clock'");
    let clock_val_5 = clock_signal
        .get_value_at_timestamp(5)
        .expect("No 'clock' value at #5");
    assert_eq!(c_str(clock_val_5), "1");

    // 6. Print the VCD (matches C's print_vcd behavior).
    print_vcd(&vcd);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() % 2 == 1 {
        eprintln!("Usage: test <vcd-file> [signal-name timestamp] ...");
        process::exit(1);
    }

    let vcd_file_path = &args[1];
    let vcd = match VCD::read_from_path(vcd_file_path) {
        Ok(vcd) => vcd,
        Err(_) => {
            eprintln!("Could not read the VCD");
            process::exit(1);
        }
    };

    print_vcd(&vcd);
    println!();

    for i in (2..args.len()).step_by(2) {
        let signal_name = &args[i];
        let timestamp: Timestamp = match args[i + 1].parse() {
            Ok(ts) => ts,
            Err(_) => {
                eprintln!("Invalid timestamp: {}", args[i + 1]);
                process::exit(1);
            }
        };

        if let Some(signal) = vcd.get_signal_by_name(signal_name) {
            if let Some(value) = signal.get_value_at_timestamp(timestamp) {
                println!(
                    "{} at {} equals {}",
                    signal_name,
                    timestamp,
                    String::from_utf8_lossy(value)
                );
            } else {
                println!("{} at {} not found in VCD", signal_name, timestamp);
            }
        } else {
            println!("Signal '{}' not found in VCD", signal_name);
        }
    }
}
