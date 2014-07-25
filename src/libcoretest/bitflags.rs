use core::option::{Some, None};
use core::ops::{BitOr, BitAnd, Sub, Not};

bitflags!(
    flags Flags: u32 {
        static FlagA       = 0x00000001,
        static FlagB       = 0x00000010,
        static FlagC       = 0x00000100,
        static FlagABC     = FlagA.bits
                           | FlagB.bits
                           | FlagC.bits
    }
)

#[test]
fn test_bits(){
    assert_eq!(Flags::empty().bits(), 0x00000000);
    assert_eq!(FlagA.bits(), 0x00000001);
    assert_eq!(FlagABC.bits(), 0x00000111);
}

#[test]
fn test_from_bits() {
    assert!(Flags::from_bits(0) == Some(Flags::empty()));
    assert!(Flags::from_bits(0x1) == Some(FlagA));
    assert!(Flags::from_bits(0x10) == Some(FlagB));
    assert!(Flags::from_bits(0x11) == Some(FlagA | FlagB));
    assert!(Flags::from_bits(0x1000) == None);
}

#[test]
fn test_from_bits_truncate() {
    assert!(Flags::from_bits_truncate(0) == Flags::empty());
    assert!(Flags::from_bits_truncate(0x1) == FlagA);
    assert!(Flags::from_bits_truncate(0x10) == FlagB);
    assert!(Flags::from_bits_truncate(0x11) == (FlagA | FlagB));
    assert!(Flags::from_bits_truncate(0x1000) == Flags::empty());
    assert!(Flags::from_bits_truncate(0x1001) == FlagA);
}

#[test]
fn test_is_empty(){
    assert!(Flags::empty().is_empty());
    assert!(!FlagA.is_empty());
    assert!(!FlagABC.is_empty());
}

#[test]
fn test_is_all() {
    assert!(Flags::all().is_all());
    assert!(!FlagA.is_all());
    assert!(FlagABC.is_all());
}

#[test]
fn test_two_empties_do_not_intersect() {
    let e1 = Flags::empty();
    let e2 = Flags::empty();
    assert!(!e1.intersects(e2));
}

#[test]
fn test_empty_does_not_intersect_with_full() {
    let e1 = Flags::empty();
    let e2 = FlagABC;
    assert!(!e1.intersects(e2));
}

#[test]
fn test_disjoint_intersects() {
    let e1 = FlagA;
    let e2 = FlagB;
    assert!(!e1.intersects(e2));
}

#[test]
fn test_overlapping_intersects() {
    let e1 = FlagA;
    let e2 = FlagA | FlagB;
    assert!(e1.intersects(e2));
}

#[test]
fn test_contains() {
    let e1 = FlagA;
    let e2 = FlagA | FlagB;
    assert!(!e1.contains(e2));
    assert!(e2.contains(e1));
    assert!(FlagABC.contains(e2));
}

#[test]
fn test_insert(){
    let mut e1 = FlagA;
    let e2 = FlagA | FlagB;
    e1.insert(e2);
    assert!(e1 == e2);
}

#[test]
fn test_remove(){
    let mut e1 = FlagA | FlagB;
    let e2 = FlagA | FlagC;
    e1.remove(e2);
    assert!(e1 == FlagB);
}

#[test]
fn test_operators() {
    let e1 = FlagA | FlagC;
    let e2 = FlagB | FlagC;
    assert!((e1 | e2) == FlagABC);         // union
    assert!((e1 & e2) == FlagC);           // intersection
    assert!((e1 ^ e2) == (FlagA | FlagB)); // symmetric difference
    assert!((e1 - e2) == FlagA);           // set difference
    assert!(!e2 == FlagA);                 // set complement
}
