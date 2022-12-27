use std::{array::IntoIter, iter::Peekable, slice::Chunks};

const BITS: usize = 8;

type Byte = [bool; 8];

fn add(augend: Byte, addend: Byte) -> Byte {
    let mut sum = [false; BITS];
    let mut carry = false;
    for (i, (augend_bit, addend_bit)) in augend.iter().zip(addend).enumerate().rev() {
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
        sum[i] = carry ^ augend_bit ^ addend_bit;
        // To simplify things, the variable carry acts for both the carry in and
        // the carry out.
        // The carry out is augend & addend when the carry in is 0, and it is
        // augend | addend when the carry in is 1.
        carry = (!carry & augend_bit & addend_bit) | (carry & (augend_bit | addend_bit));
    }
    sum
}

fn shift_left(shifted: &mut Byte, byte_to_shift: Byte, bits_to_shift: usize) {
    for (shifted_bit, multiplicand_bit) in shifted
        .iter_mut()
        .zip(byte_to_shift.iter().skip(bits_to_shift))
    {
        *shifted_bit = *multiplicand_bit;
    }
}

fn modified_mul(multiplicand: Byte, multiplier: Byte) -> Byte {
    let mut product = [false; BITS];
    let encoded_multiplier = encode_bits_pairwise(multiplier);
    for (i, token) in encoded_multiplier.iter().rev().enumerate() {
        let mut shifted = [false; BITS];
        match token.as_str() {
            "0" => continue,
            "+1" => shift_left(&mut shifted, multiplicand, 2 * i),
            "-1" => shift_left(&mut shifted, twos_complement(multiplicand), 2 * i),
            "+2" => shift_left(&mut shifted, multiplicand, 2 * i + 1),
            "-2" => shift_left(&mut shifted, twos_complement(multiplicand), 2 * i + 1),
            _ => todo!(),
        };
        product = add(product, shifted);
    }
    product
}

fn mul(multiplicand: Byte, multiplier: Byte) -> Byte {
    let mut product = [false; BITS];
    let encoded_multiplier = encode_bits(multiplier);
    for (i, token) in encoded_multiplier.iter().rev().enumerate() {
        let mut shifted = [false; BITS];
        match token.as_str() {
            "0" => continue,
            "+1" => shift_left(&mut shifted, multiplicand, i),
            "-1" => shift_left(&mut shifted, twos_complement(multiplicand), i),
            _ => todo!(),
        };
        product = add(product, shifted);
    }
    product
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

fn encode_bits_pairwise(bits: Byte) -> Vec<String> {
    encode_next_pair(&mut Vec::new(), &mut encode_bits(bits).chunks(2).peekable())
}

fn peek_bit(bits: &mut Peekable<IntoIter<bool, BITS>>) -> Option<&bool> {
    bits.peek()
}

fn peek_bit_is(bits: &mut Peekable<IntoIter<bool, BITS>>, bit: bool) -> bool {
    peek_bit(bits) == Some(&bit)
}

fn encode_next_bit(
    encoded_bits: &mut Vec<String>,
    bits: &mut Peekable<IntoIter<bool, BITS>>,
) -> Vec<String> {
    match bits.next() {
        Some(true) => {
            // It's another 1 in the 1's sequence.
            if peek_bit_is(bits, true) {
                encoded_bits.push("0".to_owned());
                encode_next_bit(encoded_bits, bits)
            // It's the start of the 1's sequence.
            } else {
                encoded_bits.push("-1".to_owned());
                encode_next_bit(encoded_bits, bits)
            }
        }
        Some(false) => {
            // It's the end of the 1's sequence.
            if peek_bit_is(bits, true) {
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

fn encode_bits(bits: Byte) -> Vec<String> {
    encode_next_bit(&mut Vec::new(), &mut bits.into_iter().peekable())
}

// C(n) = M - n where M = 2^b with b the amount of bits. Because may not have
// enough bits to represent M we subtract 1 to it and add 1 to maintain equality.
// Finally C(n) = (M-1) - n + 1 which in an 4-bit example we have:
// C(0010) = (10000 - 1) - 0010 + 0001
//         = 1111 - 0010 + 0001
//         = 1110.
// In binary the same result could be achieved by negating bit by bit and adding 1.
fn twos_complement(primitive_bits: Byte) -> Byte {
    let mut twos_complement_bits = [false; BITS];
    let mut carry = true;
    for (twos_complement_bit, primitive_bit) in
        twos_complement_bits.iter_mut().zip(primitive_bits).rev()
    {
        *twos_complement_bit = !primitive_bit ^ carry;
        carry &= !*twos_complement_bit;
    }
    twos_complement_bits
}

fn main() {
    let multiplicand: Byte = [false, false, false, false, false, false, false, true];
    let multiplier: Byte = [false, true, false, true, false, true, false, true];

    println!("{:?}", mul(multiplicand, multiplier));
    println!("{:?}", modified_mul(multiplicand, multiplier));
}

/*
TODO:
- i8 addition & multiplication with both algorithms.
- Multiplication with overflow for both algorithms.
*/
#[cfg(test)]
mod tests {
    use crate::{
        add, encode_bits, encode_bits_pairwise, modified_mul, mul, twos_complement, Byte, BITS,
    };

    /* First Encoding */

    #[test]
    fn test_all_zeros() {
        let bits: Byte = [false, false, false, false, false, false, false, false];
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "0", "0"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    #[test]
    fn test_all_ones() {
        let bits: Byte = [true, true, true, true, true, true, true, true];
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "0", "-1"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    #[test]
    fn test_only_one_one() {
        let bits: Byte = [false, false, false, false, false, false, false, true];
        let expected_encoded_bits = vec!["0", "0", "0", "0", "0", "0", "+1", "-1"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    #[test]
    fn test_consecutive_ones() {
        let bits: Byte = [false, false, false, false, false, true, true, true];
        let expected_encoded_bits = vec!["0", "0", "0", "0", "+1", "0", "0", "-1"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_one() {
        let bits: Byte = [false, true, false, true, false, true, false, true];
        let expected_encoded_bits = vec!["+1", "-1", "+1", "-1", "+1", "-1", "+1", "-1"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_zero() {
        let bits: Byte = [true, false, true, false, true, false, true, false];
        let expected_encoded_bits = vec!["-1", "+1", "-1", "+1", "-1", "+1", "-1", "0"];

        assert_eq!(encode_bits(bits), expected_encoded_bits);
    }

    /* Second Encoding */

    #[test]
    fn test_all_zeros_pairwise_encoding() {
        let bits: Byte = [false, false, false, false, false, false, false, false];
        let expected_encoded_bits = vec!["0", "0", "0", "0"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    #[test]
    fn test_all_ones_pairwise_encoding() {
        let bits: Byte = [true, true, true, true, true, true, true, true];
        let expected_encoded_bits = vec!["0", "0", "0", "-1"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    #[test]
    fn test_only_one_one_pairwise_encoding() {
        let bits: Byte = [false, false, false, false, false, false, false, true];
        let expected_encoded_bits = vec!["0", "0", "0", "+1"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    #[test]
    fn test_consecutive_ones_pairwise_encoding() {
        let bits: Byte = [false, false, false, false, false, true, true, true];
        let expected_encoded_bits = vec!["0", "0", "+2", "-1"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_one_pairwise_encoding() {
        let bits: Byte = [false, true, false, true, false, true, false, true];
        let expected_encoded_bits = vec!["+1", "+1", "+1", "+1"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    #[test]
    fn test_alternating_ones_and_zeros_starting_with_zero_pairwise_encoding() {
        let bits: Byte = [true, false, true, false, true, false, true, false];
        let expected_encoded_bits = vec!["-1", "-1", "-1", "-2"];

        assert_eq!(encode_bits_pairwise(bits), expected_encoded_bits);
    }

    /* Two's Complement */

    #[test]
    fn test_twos_complement_without_carry() {
        let bits: Byte = [false, false, false, false, false, false, true, true];
        let expected_twos_complement_bits = [true, true, true, true, true, true, false, true];

        assert_eq!(twos_complement(bits), expected_twos_complement_bits);
    }

    #[test]
    fn test_twos_complement_with_one_carry() {
        let bits: Byte = [false, false, false, false, false, false, true, false];
        let expected_twos_complement_bits = [true, true, true, true, true, true, true, false];

        assert_eq!(twos_complement(bits), expected_twos_complement_bits);
    }

    #[test]
    fn test_twos_complement_with_more_than_one_carry() {
        let bits: Byte = [false, false, false, false, false, true, false, false];
        let expected_twos_complement_bits = [true, true, true, true, true, true, false, false];

        assert_eq!(twos_complement(bits), expected_twos_complement_bits);
    }

    #[test]
    fn test_twos_complement_with_overflow() {
        let bits: Byte = [false, false, false, false, false, false, false, false];
        let expected_twos_complement_bits = bits;

        assert_eq!(twos_complement(bits), expected_twos_complement_bits);
    }

    /* u8 addition */

    #[test]
    fn test_u8_add_without_carry() {
        let augend: Byte = [false; BITS];
        let addend: Byte = [true; BITS];

        assert_eq!(add(augend, addend), addend);
    }

    #[test]
    fn test_u8_add_with_one_carry() {
        let augend: Byte = [false, false, false, false, false, false, false, true];
        let addend: Byte = augend;
        let expected_result: Byte = [false, false, false, false, false, false, true, false];

        assert_eq!(add(augend, addend), expected_result);
    }

    #[test]
    fn test_u8_add_with_more_than_one_carry() {
        let augend: Byte = [false, false, false, false, false, false, true, true];
        let addend: Byte = [false, false, false, false, false, false, false, true];
        let expected_result: Byte = [false, false, false, false, false, true, false, false];

        assert_eq!(add(augend, addend), expected_result);
    }

    #[test]
    fn test_u8_add_with_overflow() {
        let augend: Byte = [true; BITS];
        let addend: Byte = [false, false, false, false, false, false, false, true];
        let expected_result: Byte = [false, false, false, false, false, false, false, false];

        assert_eq!(add(augend, addend), expected_result);
    }

    #[test]
    fn test_u8_add() {
        let augend: Byte = [false, false, false, false, false, false, true, true];
        let addend: Byte = [false, false, false, false, false, false, true, true];
        let expected_result: Byte = [false, false, false, false, false, true, true, false];

        assert_eq!(add(augend, addend), expected_result);
    }

    /* u8 multiplication with Booth's algorithm */

    #[test]
    fn test_u8_mul_all_zeros_multiplier() {
        let multiplicand: Byte = [true; BITS];
        let multiplier: Byte = [false, false, false, false, false, false, false, false];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_all_ones_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [true, true, true, true, true, true, true, true];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_only_one_one_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [false, false, false, false, false, false, false, true];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_consecutive_ones_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [false, false, false, false, false, true, true, true];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_alternating_ones_and_zeros_starting_with_one_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [false, true, false, true, false, true, false, true];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_alternating_ones_and_zeros_starting_with_zero_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [true, false, true, false, true, false, true, false];
        let expected_product: Byte = multiplier;

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_with_booths_algorithm() {
        let multiplicand: Byte = [false, false, false, false, false, false, true, true];
        let multiplier: Byte = [false, false, false, false, false, false, true, true];
        let expected_product: Byte = [false, false, false, false, true, false, false, true];

        assert_eq!(mul(multiplicand, multiplier), expected_product);
    }

    /* u8 multiplication with modified Booth's algorithm */

    #[test]
    fn test_u8_modified_mul_with_all_zeros_multiplier() {
        let multiplicand: Byte = [true; BITS];
        let multiplier: Byte = [false; BITS];
        let expected_product: Byte = multiplier;

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_modified_mul_with_all_ones_multiplier() {
        let multiplicand: Byte = [false; BITS];
        let multiplier: Byte = [true; BITS];
        let expected_product: Byte = multiplicand;

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_modified_mul_with_only_one_one_multiplier() {
        let multiplicand: Byte = [true, true, false, false, true, true, false, false];
        let multiplier: Byte = [false, false, false, false, false, false, false, true];
        let expected_product: Byte = multiplicand;

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_modified_mul_with_consecutive_ones_multiplier() {
        let multiplicand: Byte = [false, false, false, false, true, true, false, false];
        let multiplier: Byte = [false, false, false, false, false, true, true, true];
        let expected_product: Byte = [false, true, false, true, false, true, false, false];

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_modified_mul_alternating_ones_and_zeros_starting_with_one_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [false, true, false, true, false, true, false, true];
        let expected_product: Byte = multiplier;

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_modified_mul_alternating_ones_and_zeros_starting_with_zero_multiplier() {
        let multiplicand: Byte = [false, false, false, false, false, false, false, true];
        let multiplier: Byte = [true, false, true, false, true, false, true, false];
        let expected_product: Byte = multiplier;

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }

    #[test]
    fn test_u8_mul_with_modified_booths_algorithm() {
        let multiplicand: Byte = [false, false, false, false, false, false, true, true];
        let multiplier: Byte = [false, false, false, false, false, false, true, true];
        let expected_product: Byte = [false, false, false, false, true, false, false, true];

        assert_eq!(modified_mul(multiplicand, multiplier), expected_product);
    }
}
