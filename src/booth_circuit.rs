use anyhow::{ensure, Result};
use ark_r1cs_std::{
    prelude::{AllocVar, Boolean},
    R1CSVar, ToBitsGadget,
};
use simpleworks::gadgets::{traits::IsWitness, ConstraintF, UInt8Gadget};
use std::{iter::Peekable, slice::Chunks, vec::IntoIter};

const BITS: usize = 8;

fn to_bits_be(byte: &UInt8Gadget) -> Result<Vec<Boolean<ConstraintF>>> {
    let mut bits_be = byte.to_bits_le()?;
    bits_be.reverse();
    Ok(bits_be)
}

fn from_bits_be(bits: Vec<Boolean<ConstraintF>>) -> UInt8Gadget {
    let mut bits_le = bits;
    bits_le.reverse();
    UInt8Gadget::from_bits_le(&bits_le)
}

fn kary_xor(bits: &[Boolean<ConstraintF>]) -> Result<Boolean<ConstraintF>> {
    ensure!(!bits.is_empty());
    let mut cur: Option<Boolean<ConstraintF>> = None;
    for next in bits {
        cur = if let Some(b) = cur {
            Some(b.xor(next)?)
        } else {
            Some(next.clone())
        };
    }

    Ok(cur.expect("should not be 0"))
}

fn add(augend: &UInt8Gadget, addend: &UInt8Gadget) -> Result<UInt8Gadget> {
    // println!("ADDING {} + {}", augend.value()?, addend.value()?);
    let mut sum = [Boolean::<ConstraintF>::FALSE; 8];
    let mut carry = Boolean::<ConstraintF>::FALSE;
    for (i, (augend_bit, addend_bit)) in to_bits_be(augend)?
        .into_iter()
        .zip(to_bits_be(addend)?)
        .enumerate()
        .rev()
    {
        // Bit by bit sum is an xor for the augend, the addend and the carry bits.
        // carry in | addend | augend | carry out | augend + addend |
        //     0    |    0   |   0    |     0     |        0        |
        //     0    |    0   |   1    |     0     |        1        |
        //     0    |    1   |   0    |     0     |        1        |
        //     0    |    1   |   1    |     1     |        0        |
        //     1    |    0   |   0    |     0     |        1        |
        //     1    |    0   |   1    |     1     |        0        |
        //     1    |    1   |   0    |     1     |        0        |
        //     1    |    1   |   1    |     1     |        1        |
        // sum[i] = (!carry & (augend_bit ^ addend_bit)) | (carry & !(augend_bit ^ addend_bit))
        //        = augend_bit ^ addend_bit ^ carry
        sum[i] = carry.xor(&augend_bit)?.xor(&addend_bit)?;
        println!("{carry:?} XOR {augend_bit:?} XOR {addend_bit:?} = {:?}", sum[i]);
        // To simplify things, the variable carry acts for both the carry in and
        // the carry out.
        // The carry out is augend & addend when the carry in is 0, and it is
        // augend | addend when the carry in is 1.
        // carry = carry.not()
        carry = (carry.not().and(&(augend_bit.and(&addend_bit)?))?)
            .or(&(carry.and(&(augend_bit.or(&addend_bit)?))?))?;
    }
    // println!("RESULT {} + {} = {:?}", augend.value()?, addend.value()?, from_bits_be(sum.to_vec()).value()?);
    Ok(from_bits_be(sum.to_vec()))
}

fn shift_left(
    shifted: &mut UInt8Gadget,
    byte_to_shift: &UInt8Gadget,
    bits_to_shift: usize,
) -> Result<()> {
    for (shifted_bit, multiplicand_bit) in to_bits_be(shifted)?
        .iter_mut()
        .zip(to_bits_be(byte_to_shift)?.iter().skip(bits_to_shift))
    {
        *shifted_bit = multiplicand_bit.clone();
    }
    Ok(())
}

fn modified_mul(multiplicand: &UInt8Gadget, multiplier: &UInt8Gadget) -> Result<UInt8Gadget> {
    let mut product = UInt8Gadget::constant(0_u8);
    let encoded_multiplier = encode_bits_pairwise(multiplier)?;
    for (i, token) in encoded_multiplier.iter().rev().enumerate() {
        let partial_product = match token.as_str() {
            "0" => continue,
            "+1" => UInt8Gadget::constant(multiplicand.value()? << (2 * i)),
            "-1" => {
                let multiplicand_twos_complement = twos_complement(multiplicand)?;
                UInt8Gadget::constant(multiplicand_twos_complement.value()? << (2 * i))
            }
            "+2" => UInt8Gadget::constant(multiplicand.value()? << (2 * i + 1)),
            "-2" => {
                let multiplicand_twos_complement = twos_complement(multiplicand)?;
                UInt8Gadget::constant(multiplicand_twos_complement.value()? << (2 * i + 1))
            }
            _ => todo!(),
        };
        product = add(&product, &partial_product)?;
    }
    println!(
        "{} * {} = {}",
        multiplicand.value()?,
        multiplier.value()?,
        product.value()?
    );
    Ok(product)
}

fn mul(multiplicand: &UInt8Gadget, multiplier: &UInt8Gadget) -> Result<UInt8Gadget> {
    let mut product = UInt8Gadget::constant(0_u8);
    let encoded_multiplier = encode_bits(multiplier)?;
    for (i, token) in encoded_multiplier.iter().rev().enumerate() {
        let partial_product = match token.as_str() {
            "0" => continue,
            "+1" => UInt8Gadget::constant(multiplicand.value()? << i),
            "-1" => {
                let multiplicand_twos_complement = twos_complement(multiplicand)?;
                UInt8Gadget::constant(multiplicand_twos_complement.value()? << i)
            }
            _ => todo!(),
        };
        println!("{} + {} = {}", product.value()?, partial_product.value()?, add(&product, &partial_product)?.value()?);
        product = add(&product, &partial_product)?;
        println!("{}", product.value()?);
    }
    println!("3 * 3 = 253 + 12 = 00001001 = {}", add(&UInt8Gadget::constant(253), &UInt8Gadget::constant(12))?.value()?);
    Ok(product)
}

fn encode_next_pair(
    encoded_bit_pairs: &mut Vec<String>,
    encoded_bits: &mut Peekable<Chunks<String>>,
) -> Vec<String> {
    if let Some([a, b]) = encoded_bits.next() {
        match (a.as_str(), b.as_str()) {
            ("0", "0") => {
                encoded_bit_pairs.push("0".to_owned());
                encode_next_pair(encoded_bit_pairs, encoded_bits);
            }
            ("0", "+1") | ("+1", "-1") => {
                encoded_bit_pairs.push("+1".to_owned());
                encode_next_pair(encoded_bit_pairs, encoded_bits);
            }
            ("0", "-1") | ("-1", "+1") => {
                encoded_bit_pairs.push("-1".to_owned());
                encode_next_pair(encoded_bit_pairs, encoded_bits);
            }
            ("+1", "0") => {
                encoded_bit_pairs.push("+2".to_owned());
                encode_next_pair(encoded_bit_pairs, encoded_bits);
            }
            ("-1", "0") => {
                encoded_bit_pairs.push("-2".to_owned());
                encode_next_pair(encoded_bit_pairs, encoded_bits);
            }
            _ => unreachable!(),
        }
    }

    encoded_bit_pairs.clone()
}

fn encode_bits_pairwise(bits: &UInt8Gadget) -> Result<Vec<String>> {
    Ok(encode_next_pair(
        &mut Vec::new(),
        &mut encode_bits(bits)?.chunks(2).peekable(),
    ))
}

fn peek_bit(bits: &mut Peekable<IntoIter<Boolean<ConstraintF>>>) -> Option<&Boolean<ConstraintF>> {
    bits.peek()
}

fn peek_bit_is_one(bits: &mut Peekable<IntoIter<Boolean<ConstraintF>>>) -> bool {
    matches!(peek_bit(bits), Some(Boolean::Is(_)))
        || matches!(peek_bit(bits), Some(Boolean::Constant(true)))
}

fn encode_next_bit(
    encoded_bits: &mut Vec<String>,
    bits: &mut Peekable<IntoIter<Boolean<ConstraintF>>>,
) -> Vec<String> {
    match bits.next() {
        Some(Boolean::Is(_)) | Some(Boolean::Constant(true)) => {
            // It's another 1 in the 1's sequence.
            if peek_bit_is_one(bits) {
                encoded_bits.push("0".to_owned());
                encode_next_bit(encoded_bits, bits)
            // It's the start of the 1's sequence.
            } else {
                encoded_bits.push("-1".to_owned());
                encode_next_bit(encoded_bits, bits)
            }
        }
        Some(Boolean::Not(_)) | Some(Boolean::Constant(false)) => {
            // It's the end of the 1's sequence.
            if peek_bit_is_one(bits) {
                encoded_bits.push("+1".to_owned());
                encode_next_bit(encoded_bits, bits)
            // It's another 0 in the 0's sequence.
            } else {
                encoded_bits.push("0".to_owned());
                encode_next_bit(encoded_bits, bits)
            }
        }
        _ => encoded_bits.clone(),
    }
}

fn encode_bits(bits: &UInt8Gadget) -> Result<Vec<String>> {
    Ok(encode_next_bit(
        &mut Vec::new(),
        &mut to_bits_be(bits)?.into_iter().peekable(),
    ))
}

// C(n) = M - n where M = 2^b with b the amount of bits. Because may not have
// enough bits to represent M we subtract 1 to it and add 1 to maintain equality.
// Finally C(n) = (M-1) - n + 1 which in an 4-bit example we have:
// C(0010) = (10000 - 1) - 0010 + 0001
//         = 1111 - 0010 + 0001
//         = 1110.
// In binary the same result could be achieved by negating bit by bit and adding 1.
fn twos_complement(primitive_bits: &UInt8Gadget) -> Result<UInt8Gadget> {
    let mut twos_complement_bits = [Boolean::<ConstraintF>::FALSE; BITS];
    let mut carry = Boolean::TRUE;
    for (twos_complement_bit, primitive_bit) in twos_complement_bits
        .iter_mut()
        .zip(to_bits_be(primitive_bits)?)
        .rev()
    {
        *twos_complement_bit = primitive_bit.not().xor(&carry)?;
        carry = carry.and(&twos_complement_bit.not())?;
    }
    Ok(from_bits_be(twos_complement_bits.to_vec()))
}

fn main() {
    let multiplicand: UInt8Gadget = from_bits_be(vec![
        Boolean::TRUE,
        Boolean::FALSE,
        Boolean::FALSE,
        Boolean::FALSE,
        Boolean::FALSE,
        Boolean::FALSE,
        Boolean::FALSE,
        Boolean::FALSE,
    ]);
    let multiplier: UInt8Gadget = from_bits_be(vec![
        Boolean::TRUE,
        Boolean::FALSE,
        Boolean::TRUE,
        Boolean::FALSE,
        Boolean::TRUE,
        Boolean::FALSE,
        Boolean::TRUE,
        Boolean::FALSE,
    ]);

    println!("{:?}", mul(&multiplicand, &multiplier));
    println!("{:?}", modified_mul(&multiplicand, &multiplier));
}

/*
TODO:
- i8 addition & multiplication with both algorithms.
- Multiplication with overflow for both algorithms.
*/
#[cfg(test)]
mod tests {
    use crate::booth_circuit::{self, from_bits_be, BITS};
    use ark_r1cs_std::{prelude::Boolean, R1CSVar};
    use simpleworks::gadgets::{ConstraintF, UInt8Gadget};

    /* First Encoding */

    #[test]
    fn test_all_zeros() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "0", "0"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_all_ones() {
        let bits: UInt8Gadget = UInt8Gadget::constant(255);
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "0", "-1"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_only_one_one() {
        let bits: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "+1", "-1"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_consecutive_ones() {
        let bits: UInt8Gadget = UInt8Gadget::constant(7);
        let expected_encoded_bits = vec!["0", "0", "0", "0", "+1", "0", "0", "-1"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_one() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_encoded_bits = vec!["+1", "-1", "+1", "-1", "+1", "-1", "+1", "-1"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_zero() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_encoded_bits = vec!["-1", "+1", "-1", "+1", "-1", "+1", "-1", "0"];

        assert_eq!(
            booth_circuit::encode_bits(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    /* Second Encoding */

    #[test]
    fn test_all_zeros_pairwise_encoding() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_encoded_bits = vec!["0", "0", "0", "0"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_all_ones_pairwise_encoding() {
        let bits: UInt8Gadget = UInt8Gadget::constant(255);
        let expected_encoded_bits = vec!["0", "0", "0", "-1"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_only_one_one_pairwise_encoding() {
        let bits: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_encoded_bits = vec!["0", "0", "0", "+1"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_consecutive_ones_pairwise_encoding() {
        let bits: UInt8Gadget = UInt8Gadget::constant(7);
        let expected_encoded_bits = vec!["0", "0", "+2", "-1"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_one_pairwise_encoding() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_encoded_bits = vec!["+1", "+1", "+1", "+1"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_zero_pairwise_encoding() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_encoded_bits = vec!["-1", "-1", "-1", "-2"];

        assert_eq!(
            booth_circuit::encode_bits_pairwise(&bits).unwrap(),
            expected_encoded_bits
        );
    }

    /* Two's Complement */

    #[test]
    fn test_twos_complement_without_carry() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_twos_complement_bits = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
        ]);

        assert_eq!(
            booth_circuit::twos_complement(&bits)
                .unwrap()
                .value()
                .unwrap(),
            expected_twos_complement_bits.value().unwrap()
        );
    }

    #[test]
    fn test_twos_complement_with_one_carry() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_twos_complement_bits = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::twos_complement(&bits)
                .unwrap()
                .value()
                .unwrap(),
            expected_twos_complement_bits.value().unwrap()
        );
    }

    #[test]
    fn test_twos_complement_with_more_than_one_carry() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_twos_complement_bits = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::twos_complement(&bits)
                .unwrap()
                .value()
                .unwrap(),
            expected_twos_complement_bits.value().unwrap()
        );
    }

    #[test]
    fn test_twos_complement_with_overflow() {
        let bits: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_twos_complement_bits = bits.clone();

        assert_eq!(
            booth_circuit::twos_complement(&bits)
                .unwrap()
                .value()
                .unwrap(),
            expected_twos_complement_bits.value().unwrap()
        );
    }

    /* u8 addition */

    #[test]
    fn test_u8_add_without_carry() {
        let augend: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::FALSE; BITS]);
        let addend: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::TRUE; BITS]);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            addend.value().unwrap()
        );
    }

    #[test]
    fn test_u8_add_with_one_carry() {
        let augend: UInt8Gadget = UInt8Gadget::constant(1);
        let addend: UInt8Gadget = augend.clone();
        let expected_result: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            expected_result.value().unwrap()
        );
    }

    #[test]
    fn test_u8_add_with_more_than_one_carry() {
        let augend: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let addend: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_result: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            expected_result.value().unwrap()
        );
    }

    #[test]
    fn test_u8_add_with_overflow() {
        let augend: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::TRUE; BITS]);
        let addend: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_result: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            expected_result.value().unwrap()
        );
    }

    #[test]
    fn test_u8_add() {
        let augend: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let addend: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_result: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            expected_result.value().unwrap()
        );
    }

    #[test]
    fn test_addition_is_commutative() {
        let augend = UInt8Gadget::constant(3);
        let addend = UInt8Gadget::constant(4);

        assert_eq!(
            booth_circuit::add(&augend, &addend)
                .unwrap()
                .value()
                .unwrap(),
            booth_circuit::add(&addend, &augend)
                .unwrap()
                .value()
                .unwrap()
        );
    }

    /* u8 multiplication with Booth's algorithm */

    #[test]
    fn test_u8_mul_all_zeros_multiplier() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::TRUE; BITS]);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_all_ones_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(255);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_only_one_one_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_consecutive_ones_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(7);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_alternating_ones_and_zeros_starting_with_one_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_alternating_ones_and_zeros_starting_with_zero_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_with_booths_algorithm() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(3);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(3);
        let expected_product: UInt8Gadget = UInt8Gadget::constant(9);

        assert_eq!(
            booth_circuit::mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    /* u8 multiplication with modified Booth's algorithm */

    #[test]
    fn test_u8_modified_mul_with_all_zeros_multiplier() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::TRUE; BITS]);
        let multiplier: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::FALSE; BITS]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_modified_mul_with_all_ones_multiplier() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::FALSE; BITS]);
        let multiplier: UInt8Gadget = from_bits_be(vec![Boolean::<ConstraintF>::TRUE; BITS]);
        let expected_product: UInt8Gadget = multiplicand.clone();

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_modified_mul_with_only_one_one_multiplier() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(1);
        let expected_product: UInt8Gadget = multiplicand.clone();

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_modified_mul_with_consecutive_ones_multiplier() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let multiplier: UInt8Gadget = UInt8Gadget::constant(7);
        let expected_product: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
        ]);

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_modified_mul_alternating_ones_and_zeros_starting_with_one_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_modified_mul_alternating_ones_and_zeros_starting_with_zero_multiplier() {
        let multiplicand: UInt8Gadget = UInt8Gadget::constant(1);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::FALSE,
        ]);
        let expected_product: UInt8Gadget = multiplier.clone();

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }

    #[test]
    fn test_u8_mul_with_modified_booths_algorithm() {
        let multiplicand: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let multiplier: UInt8Gadget = from_bits_be(vec![
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::FALSE,
            Boolean::<ConstraintF>::TRUE,
            Boolean::<ConstraintF>::TRUE,
        ]);
        let expected_product: UInt8Gadget = UInt8Gadget::constant(9);

        assert_eq!(
            booth_circuit::modified_mul(&multiplicand, &multiplier)
                .unwrap()
                .value()
                .unwrap(),
            expected_product.value().unwrap()
        );
    }
}
