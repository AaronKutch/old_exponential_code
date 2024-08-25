mod exp;
mod fpbits;
mod horner;

pub use horner::ExtAwiHorner;

#[test]
fn horner_test() {
    use awint::bw;
    use awint::{ExtAwi, FP};
    use std::str::FromStr;
    let mut horner = ExtAwiHorner::new(bw(128), 128 - 16, bw(128), bw(256), 192).unwrap();

    // e^1.0 = 2.7182818284590452353602874713526624..., only wrong in the last place
    let res = horner
        .exp(&FP::new(true, ExtAwi::from_str("1.0_i128f112").unwrap(), 128 - 16).unwrap())
        .unwrap();
    assert_eq!(
        FP::to_str_general(&res, 10, false, 1, 1, 4096).unwrap(),
        (
            "2".to_owned(),
            "7182818284590452353602874713526623".to_owned()
        )
    );

    // e^-1.23 = 0.2922925776808594009609443919071889..., perfect in last digit
    let res = horner
        .exp(&FP::new(true, ExtAwi::from_str("-1.23_i128f112").unwrap(), 128 - 16).unwrap())
        .unwrap();
    assert_eq!(
        FP::to_str_general(&res, 10, false, 1, 1, 4096).unwrap(),
        (
            "0".to_owned(),
            "2922925776808594009609443919071889".to_owned()
        )
    );
}
