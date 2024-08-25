use std::{borrow::BorrowMut, num::NonZeroUsize};

use awint::{Bits, ExtAwi, FP};

use crate::fpbits::{fp_imul_, fp_udivide, fp_umul_};

// Faster exponential calculations requires `2^x` and different kinds
// logarithms, so we have to bootstrap our way with these `_slow` functions that
// depend on nothing but basic arithmetic. `e^x` allows us to use bisection to
// calculate `ln(x)` which allows us to calculate `ln(2)`, then we can change
// base to calculate `2^x`, calculate `lb(x)`, and finally `lb(e)` which
// completes the bootstrapping constants we need.

/// Returns the lower and upper bounds for `e^self` using a series
/// approximation in `self`'s fp type. `self` is interpreted as
/// signed. Returns `None` if one of the bounds overflows or some
/// internal error condition occurs.
///
/// Note: `self` is assumed to be perfect numerically, if the user's `self`
/// is a truncated version of some numerical value, then the lower bound
/// of `x.expBounds` and upper bound of `x_incremented.expBounds` are
/// the real bounds.
pub fn exp_bounds<B0: BorrowMut<Bits>>(this: &FP<B0>) -> Option<(FP<ExtAwi>, FP<ExtAwi>)> {
    assert!(this.signed());
    let x = ExtAwi::zero(this.nzbw());
    let mut x = FP::new(true, x, this.fp()).unwrap();
    x.const_as_mut().copy_(this.const_as_ref()).unwrap();
    // find sign of `x`. The `short_udivide_` in the loop requires only
    // positive integers, so we record the sign here, make it positive, make the
    // addition alternate with subtraction in the loop if negative
    if x.const_as_ref().is_imin() {
        return None;
    }
    let sign = x.const_as_ref().msb();
    x.const_as_mut().neg_(sign);

    let mut tmp0 = ExtAwi::zero(x.nzbw());
    let tmp0 = tmp0.const_as_mut();
    let mut tmp1 = ExtAwi::zero(x.nzbw());
    let tmp1 = tmp1.const_as_mut();
    let mut lo_mul = FP::new(true, ExtAwi::zero(x.nzbw()), x.fp()).unwrap();
    let mut hi_mul = FP::new(true, ExtAwi::zero(x.nzbw()), x.fp()).unwrap();
    let mut lo_sum = FP::new(true, ExtAwi::zero(x.nzbw()), x.fp()).unwrap();
    let mut hi_sum = FP::new(true, ExtAwi::zero(x.nzbw()), x.fp()).unwrap();

    let mut pad = ExtAwi::zero(NonZeroUsize::new(this.bw().checked_mul(2)?)?);
    let pad = pad.const_as_mut();

    // the initial +1 in the taylor series
    FP::one_(&mut lo_mul).unwrap();
    FP::one_(&mut hi_mul).unwrap();
    for i in 1usize.. {
        if sign && ((i & 1) == 0) {
            // note what we do here: `hi_mul` is subtracted from `lo_sum` and `lo_mul` is
            // subtracted from `hi_sum` in order to capture the bounds properly.
            tmp0.copy_(hi_mul.const_as_ref()).unwrap();
            let mut o = tmp0.is_imin();
            tmp0.neg_(true);
            o |= tmp1.cin_sum_(false, lo_sum.const_as_ref(), tmp0).unwrap().1;
            lo_sum.const_as_mut().copy_(tmp1).unwrap();

            tmp0.copy_(lo_mul.const_as_ref()).unwrap();
            o |= tmp0.is_imin();
            tmp0.neg_(true);
            o |= tmp1.cin_sum_(false, hi_sum.const_as_ref(), tmp0).unwrap().1;
            hi_sum.const_as_mut().copy_(tmp1).unwrap();
            if o {
                return None;
            }
        } else {
            let mut o = tmp0
                .cin_sum_(false, lo_sum.const_as_ref(), lo_mul.const_as_ref())
                .unwrap()
                .1;
            lo_sum.const_as_mut().copy_(tmp0).unwrap();

            o |= tmp0
                .cin_sum_(false, hi_sum.const_as_ref(), hi_mul.const_as_ref())
                .unwrap()
                .1;
            hi_sum.const_as_mut().copy_(tmp0).unwrap();
            if o {
                return None;
            }
        }
        // increase the power of x
        let mut o = fp_umul_(&mut lo_mul, &x, pad).unwrap();
        o |= fp_umul_(&mut hi_mul, &x, pad).unwrap();
        // upper bound of what the truncation in the fixed point multiplication above
        // removed
        o |= hi_mul.const_as_mut().inc_(true);
        // increase the factorial in the divisor
        lo_mul.const_as_mut().digit_udivide_inplace_(i).unwrap();
        hi_mul.const_as_mut().digit_udivide_inplace_(i).unwrap();
        if o {
            return None;
        }
        if hi_mul.const_as_ref().is_zero() {
            break;
        }
        if hi_mul.const_as_mut().inc_(true) {
            // upper bound the inplace division
            return None;
        }
    }
    // if `sign` and the result should be in the range 0.0..1.0, the `hiMul` 1.0
    // value will be subtracted first from `lo_sum` before the `break`, so
    // there aren't any weird low fp cases where `lo_mul` would need to be
    // decremented

    // be really conservative and add 4 because of the last increment for `hi_mul`
    // after the `break`, plus 3 for low fp cases where the remaining
    // partials could add up to `e` and/or be enough to roll over the ULP.
    if hi_sum.inc_(true) || hi_sum.inc_(true) || hi_sum.inc_(true) || hi_sum.inc_(true) {
        return None;
    }
    Some((lo_sum, hi_sum))
}

/// Computes a bound on the natural logarithm of `self`. Returns `None` if
/// it cannot find both bounds
pub fn ln_bounds<B0: BorrowMut<Bits>>(this: &FP<B0>) -> Option<(FP<ExtAwi>, FP<ExtAwi>)> {
    assert!(this.signed());
    // Uses a two stage bisection separately for both bounds, starting with
    // increasing steps until overshoot happens, then decreasing steps to narrow
    // down the tightest bounds. We need two stages because if we start with large
    // steps, `exp_bounds` can produce valid but incredibly wide bounds that
    // act in a metastable way to confuse the decreasing stage.

    if this.msb() {
        return None;
    }
    let mut one = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    if this.bw() == 1 {
        // prevent panic on shifts
        return None;
    }
    // this handles bad fp
    FP::one_(&mut one).unwrap();
    let lt_one = this.ilt(&one).unwrap();

    // stage 1, separately for both bounds. Steps exponentially negative if
    // `lt_one`, else steps exponentially positive until passing `self`.
    let mut bisect_lo = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    let mut step_lo = ExtAwi::uone(this.nzbw());
    loop {
        let (_, hi) = exp_bounds(&bisect_lo)?;
        bisect_lo.neg_add_(lt_one, &step_lo).unwrap();
        if lt_one {
            if hi.ile(this).unwrap() {
                break;
            }
        } else if hi.igt(this).unwrap() {
            break;
        }
        step_lo.shl_(1).unwrap();
        if step_lo.is_zero() {
            // prevent infinite loops in case `step_lo` zeroes before `exp_bounds` returns
            // `None`
            return None;
        }
    }
    let mut bisect_hi = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    let mut step_hi = ExtAwi::uone(this.nzbw());
    loop {
        let (lo, _) = exp_bounds(&bisect_hi)?;
        bisect_hi.neg_add_(lt_one, &step_hi).unwrap();
        // note different equal cases
        if lt_one {
            if lo.ilt(this).unwrap() {
                break;
            }
        } else if lo.ige(this).unwrap() {
            break;
        }
        step_hi.shl_(1).unwrap();
        if step_hi.is_zero() {
            return None;
        }
    }

    // stage 2, hone in. Finds bounds such that `exp_bounds(bisect_lo).upper_bound
    // <= self < exp_bounds(bisect_hi).lower_bound`.
    loop {
        let (_, hi) = exp_bounds(&bisect_lo)?;
        bisect_lo
            .neg_add_(this.ile(&hi).unwrap(), &step_lo)
            .unwrap();
        step_lo.lshr_(1).unwrap();
        if step_lo.is_zero() {
            break;
        }
    }
    loop {
        let (lo, _) = exp_bounds(&bisect_hi)?;
        bisect_hi.neg_add_(lo.igt(this).unwrap(), &step_hi).unwrap();
        step_hi.lshr_(1).unwrap();
        if step_hi.is_zero() {
            break;
        }
    }

    // If bisection hits `self` perfectly in one step, the following steps will
    // bring it 1 ULP away. We do one extra increment to insure that the bisection
    // isn't one off.
    if !bisect_lo.dec_(false) || bisect_hi.inc_(true) {
        return None;
    }
    // final check
    let (_, hi) = exp_bounds(&bisect_lo)?;
    let (lo, _) = exp_bounds(&bisect_hi)?;
    if hi.const_as_ref().ile(this.const_as_ref()).unwrap()
        && this.const_as_ref().ilt(lo.const_as_ref()).unwrap()
    {
        Some((bisect_lo, bisect_hi))
    } else {
        None
    }
}

/// Returns the lower and upper bounds for `e^(self * rhs.0)` and `e^(self *
/// rhs.1)`. Returns `None` if `self` and `rhs` do not have the same fixed
/// point type. Useful for general exponentiation.
pub fn mul_exp_bounds<B0: BorrowMut<Bits>, B1: BorrowMut<Bits>, B2: BorrowMut<Bits>>(
    this: &FP<B0>,
    rhs: (&FP<B1>, &FP<B2>),
) -> Option<(FP<ExtAwi>, FP<ExtAwi>)> {
    if (this.fp_ty() != rhs.0.fp_ty()) || (this.fp_ty() != rhs.1.fp_ty()) {
        return None;
    }
    let mut pad = ExtAwi::zero(NonZeroUsize::new(this.bw().checked_mul(2)?)?);
    // so `self` does not need to be mutable
    let mut self_tmp = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    let mut tmp0 = self_tmp.clone();
    let mut tmp1 = self_tmp.clone();
    self_tmp.copy_(this).unwrap();
    tmp0.copy_(rhs.0).unwrap();
    tmp1.copy_(rhs.1).unwrap();
    fp_imul_(&mut tmp0, &mut self_tmp, &mut pad)?;
    fp_imul_(&mut tmp1, &mut self_tmp, &mut pad)?;
    // a negative `self_tmp` complicates things, just swap so `tmp0 < tmp1` and
    // widen both bounds
    if tmp1.ilt(&tmp0).unwrap() {
        core::mem::swap(&mut tmp0, &mut tmp1);
    }
    tmp0.dec_(false);
    tmp1.inc_(true);
    let (lo, _) = exp_bounds(&tmp0)?;
    let (_, hi) = exp_bounds(&tmp1)?;
    Some((lo, hi))
}

/// Returns the lower and upper bounds for `2^self`
pub fn exp2_bounds<B0: BorrowMut<Bits>>(this: &FP<B0>) -> Option<(FP<ExtAwi>, FP<ExtAwi>)> {
    if this.fp() + 3 > isize::try_from(this.bw()).ok()? {
        // can't calculate `ln_2`
        return None;
    }
    let mut two = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    FP::one_(&mut two).unwrap();
    two.shl_(1).unwrap();
    let ln_2 = ln_bounds(&two)?;
    // use `2^x = e^(x*ln(2))`
    mul_exp_bounds(&this, (&ln_2.0, &ln_2.1))
}

// Returns the lower and upper bounds for `lb(self)` (`lb` is the binary
// logarithm or base 2 logarithm)
pub fn lb_bounds<B0: BorrowMut<Bits>>(this: &FP<B0>) -> Option<(FP<ExtAwi>, FP<ExtAwi>)> {
    if this.fp() + 3 > isize::try_from(this.bw()).ok()? {
        // can't calculate `ln_2`
        return None;
    }
    let mut two = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    FP::one_(&mut two).unwrap();
    two.shl_(1).unwrap();
    let ln_2 = ln_bounds(&two)?;
    let ln_x = ln_bounds(&this)?;
    // use `lb(x) = ln(x)/ln(2)`
    let mut pad0 = ExtAwi::zero(NonZeroUsize::new(this.bw().checked_mul(2)?)?);
    let mut pad1 = ExtAwi::zero(pad0.nzbw());
    let mut pad2 = ExtAwi::zero(pad0.nzbw());
    let mut pad3 = ExtAwi::zero(pad0.nzbw());
    let mut rem = FP::new(true, ExtAwi::zero(this.nzbw()), this.fp()).unwrap();
    let mut quo_lo = rem.clone();
    let mut quo_hi = rem.clone();
    // smallest dividend and largest divisor
    fp_udivide(
        &mut quo_lo,
        &mut rem,
        &ln_x.0,
        &ln_2.1,
        &mut pad0,
        &mut pad1,
        &mut pad2,
        &mut pad3,
    )?;
    // largest dividend and smallest divisor
    fp_udivide(
        &mut quo_hi,
        &mut rem,
        &ln_x.1,
        &ln_2.0,
        &mut pad0,
        &mut pad1,
        &mut pad2,
        &mut pad3,
    )?;
    Some((quo_lo, quo_hi))
}

#[test]
fn transcendental_test() {
    macro_rules! fpbits {
        (- $int:expr, $frac:expr) => {
            FP::new(
                true,
                ExtAwi::from_str_general(Some(true), $int, $frac, 0, 10, awint::bw(128), 32)
                    .unwrap(),
                32,
            )
            .unwrap()
        };
        ($int:expr, $frac:expr) => {
            FP::new(
                true,
                ExtAwi::from_str_general(Some(false), $int, $frac, 0, 10, awint::bw(128), 32)
                    .unwrap(),
                32,
            )
            .unwrap()
        };
    }
    // exp_bounds
    let awi_in = fpbits!("1", "");
    let (lo, hi) = exp_bounds(&awi_in).unwrap();
    assert_eq!(lo.to_i64(), 11674931549); // 11674931549 * 2^(-32) = 2.71828...
    assert_eq!(hi.to_i64(), 11674931571);

    // ln_bounds
    let awi_in = fpbits!("3", "123");
    let (lo, hi) = ln_bounds(&awi_in).unwrap();
    assert_eq!(lo.to_i64(), 4891083317);
    assert_eq!(hi.to_i64(), 4891083327);
    let awi_in = fpbits!("", "5");
    let (lo, hi) = ln_bounds(&awi_in).unwrap();
    assert_eq!(lo.to_i64(), -2977044497);
    assert_eq!(hi.to_i64(), -2977044449);

    // mul_exp_bounds
    let mut awi_in = fpbits!("1", "234");
    // very large bounds
    let rhs = (fpbits!(-"4", "321"), fpbits!("1", "337"));
    let (lo, hi) = mul_exp_bounds(&awi_in, (&rhs.0, &rhs.1)).unwrap();
    assert_eq!(lo.to_i64(), 20761109);
    assert_eq!(hi.to_i64(), 22360632655);
    awi_in.neg_(true);
    let (lo, hi) = mul_exp_bounds(&awi_in, (&rhs.0, &rhs.1)).unwrap();
    assert_eq!(lo.to_i64(), 824965199);
    assert_eq!(hi.to_i64(), 888520696425);

    // exp2_bounds
    let awi_in = fpbits!(-"0", "42");
    let (lo, hi) = exp2_bounds(&awi_in).unwrap();
    assert_eq!(lo.to_i64(), 3210164309);
    // accurate truncated value is 3210164317
    assert_eq!(hi.to_i64(), 3210164328);

    // lb_bounds
    let awi_in = fpbits!("1234", "");
    let (lo, hi) = lb_bounds(&awi_in).unwrap();
    assert_eq!(lo.to_i64(), 44105563196);
    // accurate truncated value is 44105563245
    assert_eq!(hi.to_i64(), 44105563376);
}
