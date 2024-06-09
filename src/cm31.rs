use crate::m31_add;
use crate::treepp::*;

/// Push a zero CM31 element.
///
/// Output:
/// - cm31 representing 0: 0, 0
///
pub fn push_cm31_zero() -> Script {
    script! {
        { 0 } { 0 }
    }
}

/// Push a one CM31 element.
///
/// Output:
/// - cm31 representing 1: 0, 1
///
pub fn push_cm31_one() -> Script {
    script! {
        { 0 } { 1 }
    }
}

/// Add two CM31 elements.
///
/// Input:
/// - cm31
/// - cm31
///
/// Output:
/// - cm31
///
pub fn cm31_add() -> Script {
    script! {
        OP_ROT m31_add
        OP_TOALTSTACK m31_add OP_FROMALTSTACK
    }
}

/// Require two CM31 elements to be equal.
///
/// Input:
/// - cm31
/// - cm31
///
/// Fail if the two CM31 elements are not equal.
///
pub fn cm31_equalverify() -> Script {
    script! {
        OP_ROT OP_EQUALVERIFY
        OP_EQUALVERIFY
    }
}

#[cfg(test)]
mod test {
    use std::ops::Add;
    use crate::treepp::*;
    use p3_field::extension::Complex;
    use p3_field::PrimeField32;
    use p3_mersenne_31::Mersenne31;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use crate::{cm31_add, cm31_equalverify, m31_add};

    type F = Complex<Mersenne31>;

    #[test]
    fn test_cm31_add() {
        let mut prng = ChaCha20Rng::seed_from_u64(0u64);
        eprintln!("cm31 add: {}", m31_add().len());

        for _ in 0..100 {
            let a = prng.gen::<F>();
            let b = prng.gen::<F>();

            let c = a.add(b);

            let script = script! {
                { a.imag().as_canonical_u32() }
                { a.real().as_canonical_u32() }
                { b.imag().as_canonical_u32() }
                { b.real().as_canonical_u32() }
                cm31_add
                { c.imag().as_canonical_u32() }
                { c.real().as_canonical_u32() }
                cm31_equalverify
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }
}