use inversion_list::inversion_list::*;

#[test]
fn test() {
    let a = [1, 2, 3, 5, 7, 9];
    let b = [1, 2, 3, 5, 7, 9, 10];
    let c = [23, 12, 1];

    let set = InversionList::new(20, &a).unwrap();
    let set2 = InversionList::new(20, &b).unwrap();
    // In C, create(20, c) returns NULL (23 >= capacity), which acts as a
    // sentinel terminating the variadic intersection loop.  So the first
    // intersection effectively computes intersection(set, set2) only.
    assert!(InversionList::new(20, &c).is_err());

    let inter1 = set.intersection(&set2);
    assert_eq!(inter1.to_str(), "[1, 2, 3, 5, 7, 9]");

    // intersection(set, set2)
    let inter2 = set.intersection(&set2);
    assert_eq!(inter2.to_str(), "[1, 2, 3, 5, 7, 9]");

    println!("test_intersection passed.");
}
fn main(){}
