use std::borrow::BorrowMut;

use awint::{Bits, FP};

// As of `awint` 0.17 I haven't gotten around to porting these functions to the modern `awint::FP`

/// Returns `None` if `pad.bw() < self.bw() + rhs.bw()`. Returns
/// `Some(true)` if overflow occurs.
pub fn fp_umul_<B0: BorrowMut<Bits>, B1: BorrowMut<Bits>>(
    lhs: &mut FP<B0>,
    rhs: &FP<B1>,
    pad: &mut Bits,
) -> Option<bool> {
    if pad.bw() < lhs.bw() + rhs.bw() {
        return None;
    }
    pad.zero_();
    pad.arb_umul_add_(&lhs.const_as_ref(), rhs.const_as_ref());
    let mut abs = rhs.fp().unsigned_abs();
    if abs >= pad.bw() {
        abs = pad.bw() - 1;
    }
    if rhs.fp() <= 0 {
        if pad.lz() < abs {
            return None;
        }
        pad.shl_(abs).unwrap();
    } else {
        pad.lshr_(abs).unwrap();
    }
    Some(lhs.const_as_mut().zero_resize_(pad))
}

pub fn fp_imul_<B0: BorrowMut<Bits>, B1: BorrowMut<Bits>>(
    lhs: &mut FP<B0>,
    rhs: &mut FP<B1>,
    pad: &mut Bits,
) -> Option<bool> {
    if pad.bw() < lhs.bw() + rhs.bw() {
        return None;
    }
    pad.zero_();
    pad.arb_imul_add_(lhs.const_as_mut(), rhs.const_as_mut());
    let mut abs = rhs.fp().unsigned_abs();
    if abs >= pad.bw() {
        abs = pad.bw() - 1;
    }
    if rhs.fp() <= 0 {
        if pad.lz() < abs {
            return None;
        }
        pad.shl_(abs).unwrap();
    } else {
        pad.ashr_(abs).unwrap();
    }
    Some(lhs.const_as_mut().sign_resize_(pad))
}

pub fn fp_uimul_<B0: BorrowMut<Bits>, B1: BorrowMut<Bits>>(
    lhs: &mut FP<B0>,
    rhs: &mut FP<B1>,
    signed: bool,
    pad: &mut Bits,
) -> Option<bool> {
    if signed {
        fp_imul_(lhs, rhs, pad)
    } else {
        fp_umul_(lhs, rhs, pad)
    }
}

/// Returns `None` if `quo` and `rem` do not have same fp types, or
/// the pads do not have the same bitwidth, or `pad0.bw() <= duo.fp() -
/// div.fp() + quo.fp()`. Returns a boolean indicating if overflow
/// happened.
///
/// This function works numerically by calculating `(duo * 2^duo.fp() *
/// 2^(-div.fp()) * 2^quo.fp()) / div`. `zero_resize_` is used to
/// temporarily change the bitwidth to that of the scratchpads, the division
/// is performed, and then resized back to the size of the outputs.
pub fn fp_udivide<
    B0: BorrowMut<Bits>,
    B1: BorrowMut<Bits>,
    B2: BorrowMut<Bits>,
    B3: BorrowMut<Bits>,
>(
    quo: &mut FP<B0>,
    rem: &mut FP<B1>,
    duo: &FP<B2>,
    div: &FP<B3>,
    pad0: &mut Bits,
    pad1: &mut Bits,
    pad2: &mut Bits,
    pad3: &mut Bits,
) -> Option<bool> {
    if (quo.bw() != rem.bw()) || (quo.fp() != rem.fp()) {
        return None;
    }
    let mut o = false;
    let num_fp = duo.fp().checked_sub(div.fp())?.checked_add(quo.fp())?;
    o |= pad0.zero_resize_(duo.const_as_ref());
    if num_fp < 0 {
        pad0.lshr_(num_fp.unsigned_abs())?;
    } else {
        o |= pad0.lz() < num_fp.unsigned_abs();
        pad0.shl_(num_fp.unsigned_abs())?;
    }
    o |= pad1.zero_resize_(div.const_as_ref());
    Bits::udivide(pad2, pad3, pad0, pad1)?;
    o |= quo.const_as_mut().zero_resize_(pad2);
    o |= rem.const_as_mut().zero_resize_(pad3);
    Some(o)
}
