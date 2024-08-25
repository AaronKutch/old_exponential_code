#![feature(test)]

extern crate test;
use awint::{bw, ExtAwi, FP};
use old_exponential_code::ExtAwiHorner;
use test::{black_box, Bencher};

#[bench]
fn exp256(bencher: &mut Bencher) {
    let w = bw(256);
    let fp = 128;
    let mut horner = ExtAwiHorner::new(w, fp, bw(256), bw(512), 256 + 64).unwrap();
    let mut input = FP::new(
        true,
        ExtAwi::from_str_general(Some(false), "12", "345", 0, 10, w, fp).unwrap(),
        fp,
    )
    .unwrap();
    bencher.iter(|| {
        input.inc_(true);
        black_box(
            horner
                .exp(black_box(&input))
                .unwrap()
                .const_as_ref()
                .to_usize(),
        )
    })
}
