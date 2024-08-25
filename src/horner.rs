use std::{borrow::BorrowMut, num::NonZeroUsize};

use awint::{Bits, ExtAwi, FP};

use crate::{
    exp::{exp_bounds, lb_bounds, ln_bounds},
    fpbits::fp_umul_,
};

/// There is a problem when calculating transcendental functions like `e^x`. We
/// know that its Taylor series is `x^0/0! + x^1/1! + x^2/2! + x^3/3! + ...`.
/// Besides error incurred in calculating the individual terms, we must
/// eventually stop adding terms. If all are terms are positive (which can be
/// enforced with identities like `e^(-abs(x)) = 1 / e(abs(x))`), then cutting
/// off some terms will result in a lower bound on the function. If the
/// individual terms are also biased to have truncation errors (note: we choose
/// use truncation rounding and no other kind of rounding, because the horner
/// evaluation in exp2m1 must not result in a partial greater than 1.0, or
/// else we could get exponential growth problems) that lower bound the
/// function, then the whole thing will be a lower bound of the true value
/// of `e^x`. It would be great if we could always get a perfectly rounded
/// bitstring for a given fixed point numerical function, for the purposes of
/// determinisim. What I mean by "perfect" is that no larger intermediate fixed
/// point computations with more terms would change the truncated bitstring
/// further. Unfortunately, as far as I currently know, there is no property of
/// `e^x` that prevents one of the many inputs from forming an arbitrarily long
/// string of binary ones in the fraction that will roll over from a very low
/// term, and change the target truncation (thus messing up the perfect
/// determinism). I have decided to use an intermediate fixed point type double
/// the bitwidth and fixed point of the desired type we are operating on. Any
/// precomputed constants will be computed with a high enough precompute fixed
/// point such that they have perfect trunctions, and thus we can have a higher
/// level determinism. Note that if the intermediate fixed point type is
/// changed (say, we move from `exp2_fw = 128` to `exp2_fw = 256`), there is a
/// slim but nonzero chance that one of the inputs in the `exp2_fw = 128` domain
/// did not have a perfect truncated output, that would be incremented in the
/// new `exp2_fw = 256` output. The new functions _must_ be considered
/// deterministically incompatible with the old functions even if it appears
/// from extensive fuzzing that all the outputs are equal.
#[derive(Debug)]
pub struct ExtAwiHorner {
    // Note: we use a lot of redundant bitwidths here so that the runtime does not have to read the
    // bitwidths from the end of the Bits.
    /// Constants needed for horner evaluation, stored as only the fractional
    /// part numbers approximating `C_[constants.len() - n] = ln(2)^n / n!`.
    /// The integer part is always zero, but is kept for multiplication
    constants: Vec<ExtAwi>,
    /// has a bitwidth of `target_bw + exp2_fw + 1` to hold a fixed point
    /// product
    full_bw_tmp: ExtAwi,
    exp2_fw: NonZeroUsize,
    double_bw_tmp: ExtAwi,
    /// has a bitwidth of `exp2_fw + 1`, so that the ~1.4427 constant fits
    lb_e: ExtAwi,
    /// full_bw - y_fp, integer width of the full fixed point
    y_iw: NonZeroUsize,
    /// has a bitwidth of `y_iw`
    y_i: ExtAwi,
    exp2_sub1_arg: ExtAwi,
    exp2_sub1_res: ExtAwi,
    target_bw: NonZeroUsize,
    target_fp: isize,
    target_fp_unsigned: usize,
    /// used for handling target sized temporaries
    target_tmp: FP<ExtAwi>,
    /// Another intermediate with the exp2 result integer width and the target
    /// fraction width
    res_to_target_tmp: ExtAwi,
    /// number of extra fraction bits `exp2` intermediates have
    exp2_target_diff: usize,
}

impl ExtAwiHorner {
    /// Precomputes constants and preallocates temporaries needed for quick
    /// computation of the exponential function on fixed point inputs with a
    /// bitwidth of `iw.bw() + fw.bw()`, integer part width of `iw`, and
    /// fractional part width of `fw`. The output uses the same fixed point. The
    /// extra `bwe` and `fpe` arguments specify the intermediate sizes used in
    /// generating internal constants. If not enough precision (note: both a
    /// large integer and fractional part is needed even if the main
    /// fp type is fractional only) is supplied, this will return `None`.
    pub fn new(
        target_bw: NonZeroUsize,
        target_fp: isize,
        // The fraction width of the intermediates, equal to the bitwidth fed to `exp2_sub1_fast`
        exp2_fw: NonZeroUsize,
        precompute_bw: NonZeroUsize,
        precompute_fp: isize,
    ) -> Option<Self> {
        if precompute_fp + 3 > isize::try_from(precompute_bw.get()).ok()? {
            // can't calculate `ln_2`
            return None;
        }

        let mut int = FP::new(true, ExtAwi::zero(precompute_bw), precompute_fp).unwrap();
        FP::one_(&mut int)?;
        let e = exp_bounds(&int)?;
        let lb_e = (lb_bounds(&e.0)?.0, lb_bounds(&e.1)?.1);
        // used for checking ideal truncation of `lb_e` constant
        let mut lb_e_target0 = FP::new(
            true,
            ExtAwi::zero(NonZeroUsize::new(exp2_fw.get().checked_add(1)?)?),
            isize::try_from(exp2_fw.get()).ok()?,
        )
        .unwrap();
        let mut lb_e_target1 = lb_e_target0.clone();
        let mut o = FP::outruncate_(&mut lb_e_target0, &lb_e.0).1;
        o |= FP::outruncate_(&mut lb_e_target1, &lb_e.1).1;
        if o || (lb_e_target0.const_as_ref() != lb_e_target1.const_as_ref()) {
            return None;
        }
        let lb_e = lb_e_target0.clone().into_b();

        // set to 2
        int.const_as_mut().shl_(1).unwrap();
        let ln_2 = ln_bounds(&int)?;

        let mut product = (ln_2.0.clone(), ln_2.1.clone());
        let mut pad = ExtAwi::zero(NonZeroUsize::new(precompute_bw.get().checked_mul(2)?)?);
        let pad = pad.const_as_mut();
        // used for checking ideal truncation of horner constants
        let mut exp2_fw_target0 = FP::new(
            true,
            ExtAwi::zero(exp2_fw),
            isize::try_from(exp2_fw.get()).ok()?,
        )
        .unwrap();
        let mut exp2_fw_target1 = exp2_fw_target0.clone();

        // calculate the `C_n = ln(2)^n / n!` constants for `exp2_horner`
        let mut constants = vec![];
        for i in 2.. {
            // check that truncating both the lower and upper bounds results in the same
            // answer
            let mut o = FP::outruncate_(&mut exp2_fw_target0, &product.0).1;
            o |= FP::outruncate_(&mut exp2_fw_target1, &product.1).1;
            if exp2_fw_target0.const_as_ref() != exp2_fw_target1.const_as_ref() {
                return None;
            }
            let c = exp2_fw_target0.clone().into_b();
            if c.const_as_ref().is_zero() {
                break;
            }
            constants.push(c);
            // multiply by ln(2)
            fp_umul_(&mut product.0, &ln_2.0, pad).unwrap();
            fp_umul_(&mut product.1, &ln_2.1, pad).unwrap();
            o |= product.1.const_as_mut().inc_(true);

            // divide to increase the factorial
            product.0.const_as_mut().digit_udivide_inplace_(i).unwrap();
            product.1.const_as_mut().digit_udivide_inplace_(i).unwrap();
            o |= product.1.const_as_mut().inc_(true);
            if o {
                return None;
            }
        }
        constants.reverse();
        let full_bw = NonZeroUsize::new(target_bw.get().checked_add(lb_e.bw())?)?;
        let double_bw = NonZeroUsize::new(exp2_fw.get().checked_mul(2)?)?;
        let y_fp = usize::try_from(target_fp)
            .ok()?
            .checked_add(exp2_fw.get())?;
        let y_iw = NonZeroUsize::new(full_bw.get().checked_sub(y_fp)?)?;
        let target_tmp = FP::new(true, ExtAwi::zero(target_bw), target_fp).unwrap();
        let mut one = ExtAwi::uone(target_bw);
        one.const_as_mut()
            .shl_(usize::try_from(target_tmp.fp()).ok()?)?;
        let target_fp_unsigned = usize::try_from(target_tmp.fp()).ok()?;
        let target_iw = target_bw.get() - target_fp_unsigned;
        Some(Self {
            constants,
            full_bw_tmp: ExtAwi::zero(full_bw),
            exp2_fw,
            double_bw_tmp: ExtAwi::zero(double_bw),
            lb_e,
            y_iw,
            y_i: ExtAwi::zero(y_iw),
            exp2_sub1_arg: ExtAwi::zero(exp2_fw),
            exp2_sub1_res: ExtAwi::zero(exp2_fw),
            target_bw: target_tmp.nzbw(),
            target_fp: target_tmp.fp(),
            target_fp_unsigned,
            target_tmp,
            res_to_target_tmp: ExtAwi::zero(NonZeroUsize::new(
                exp2_fw.get().checked_add(target_iw)?,
            )?),
            exp2_target_diff: exp2_fw.get().checked_sub(target_fp_unsigned)?,
        })
    }

    /// Uses `self.exp2_sub1_arg` as the argument to a `2^x - 1` calculation and
    /// sets `self.exp2_sub1_res` to the result
    fn exp2_sub1_internal(&mut self) {
        // `2^x = 1 + (ln(2)/1!)*x + (ln(2)^2/2!)*x^2 + (ln(2)^3/3!)*x^3`
        // `2^x - 1 = x*(C_1 + x*(C_2 + x*(C_3 + ...)))` where `C_n = ln(2)^n / n!`

        let tmp = self.double_bw_tmp.const_as_mut();
        let h = self.exp2_sub1_res.const_as_mut();
        // zero out previous value
        h.zero_();
        // note: this is optimal, we can't calculate the series with
        // `arb_umul_add_` only because the fixed point shift must be done
        // inbetween the multiplication and the addition
        for i in 0..self.constants.len() {
            h.add_(self.constants[i].const_as_ref()).unwrap();
            // manual fixed point multiply
            tmp.zero_();
            tmp.arb_umul_add_(self.exp2_sub1_arg.const_as_ref(), h);
            tmp.lshr_(self.exp2_fw.get()).unwrap();
            h.resize_(tmp, false);
        }
    }

    /// Interprets `x` as an unsigned fracint (so the input is in the range
    /// 0.0..1.0) and returns `2.0^x - 1.0` (so the output is also
    /// in the range 0.0..1.0). This function avoids allocation.
    pub fn uexp2_sub1_fracint(&mut self, x: &Bits) -> Option<&Bits> {
        self.exp2_sub1_arg.const_as_mut().copy_(x)?;
        self.exp2_sub1_internal();
        Some(self.exp2_sub1_res.const_as_ref())
    }

    /// Calculates `e^x`, using the fixed point type defined at
    /// `Self::new`. Returns `None` if `x` does not have the correct type or
    /// overflow occurs. This function avoids allocation.
    pub fn exp<B: BorrowMut<Bits>>(&mut self, x: &FP<B>) -> Option<&FP<ExtAwi>> {
        if x.nzbw() != self.target_bw || x.fp() != self.target_fp {
            return None;
        }
        let t = self.target_tmp.const_as_mut();
        t.copy_(x.const_as_ref()).unwrap();
        let msb = t.msb();
        // reinterpret as unsigned here
        t.neg_(msb);

        // transform the problem so that we can use `exp2_horner`
        // `e^x = 2^(x*lb(e))`
        // `2^x = (2^floor(x)) * 2^(x - floor(x))`
        // let `y = x*lb(e)`
        // `e^x = (2^floor(y)) * 2^(y - floor(y))`

        // calculate `y = x*lb(e)`
        let full = self.full_bw_tmp.const_as_mut();
        // manual fixed point multiply, resultant fp == target_fp + exp2_fw
        full.zero_();
        full.arb_umul_add_(t, self.lb_e.const_as_mut());
        // separate fractional and integer parts
        // remove less significant `target_fp` bits not used
        full.lshr_(self.target_fp_unsigned).unwrap();
        self.exp2_sub1_arg.const_as_mut().resize_(full, false);
        // shift down integer part
        full.lshr_(self.exp2_fw.get()).unwrap();
        self.y_i.const_as_mut().resize_(full, false);
        // check if `y_i` does not fit in a `isize` accounting for sign bit
        let y_i = self.y_i.const_as_ref();
        if self.y_iw.get() - y_i.lz() >= (usize::BITS as usize) {
            // certain overflow
            None
        } else {
            // the right shift to multiply by `2*floor(y)` and shift back to the target
            // fixed point
            let mut shift = y_i.to_isize();
            if msb {
                shift = -shift - 1;
            }
            shift = shift.checked_sub(self.exp2_target_diff as isize)?;

            self.exp2_sub1_arg.const_as_mut().neg_(msb);
            // use `exp2_sub1_arg` to calculate `exp2_sub1_res`
            self.exp2_sub1_internal();

            // note: output is positive from here on

            // get more integer width to avoid losing information
            let res = self.res_to_target_tmp.const_as_mut();
            res.resize_(self.exp2_sub1_res.const_as_ref(), false);
            // add the remaining +1 to complete the series, this works because the output is
            // exclusively upper bounded by 1.0.
            res.digit_or_(1, self.exp2_fw.get());
            if shift < 0 {
                if shift.unsigned_abs() >= res.bw() {
                    res.zero_()
                } else {
                    res.lshr_(shift.unsigned_abs()).unwrap();
                }
                if self.target_tmp.const_as_mut().zero_resize_(res) {
                    None
                } else {
                    Some(&self.target_tmp)
                }
            } else if shift.unsigned_abs() <= res.lz() {
                res.shl_(shift.unsigned_abs()).unwrap();
                if self.target_tmp.const_as_mut().zero_resize_(res) {
                    None
                } else {
                    Some(&self.target_tmp)
                }
            } else {
                // overflow
                None
            }
        }
    }
}
