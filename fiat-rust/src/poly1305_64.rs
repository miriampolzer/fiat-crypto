//! Autogenerated: 'src/ExtractionOCaml/unsaturated_solinas' --lang Rust --inline poly1305 64 3 '2^130 - 5' carry_mul carry_square carry add sub opp selectznz to_bytes from_bytes relax
//! curve description: poly1305
//! machine_wordsize = 64 (from "64")
//! requested operations: carry_mul, carry_square, carry, add, sub, opp, selectznz, to_bytes, from_bytes, relax
//! n = 3 (from "3")
//! s-c = 2^130 - [(1, 5)] (from "2^130 - 5")
//! tight_bounds_multiplier = 1 (from "")
//!
//! Computed values:
//!   carry_chain = [0, 1, 2, 0, 1]
//!   eval z = z[0] + (z[1] << 44) + (z[2] << 87)
//!   bytes_eval z = z[0] + (z[1] << 8) + (z[2] << 16) + (z[3] << 24) + (z[4] << 32) + (z[5] << 40) + (z[6] << 48) + (z[7] << 56) + (z[8] << 64) + (z[9] << 72) + (z[10] << 80) + (z[11] << 88) + (z[12] << 96) + (z[13] << 104) + (z[14] << 112) + (z[15] << 120) + (z[16] << 128)
//!   balance = [0x1ffffffffff6, 0xffffffffffe, 0xffffffffffe]

#![allow(unused_parens)]
#![allow(non_camel_case_types)]

pub type fiat_poly1305_u1 = u8;
pub type fiat_poly1305_i1 = i8;
pub type fiat_poly1305_u2 = u8;
pub type fiat_poly1305_i2 = i8;

/** The type fiat_poly1305_loose_field_element is a field element with loose bounds. */
/** Bounds: [[0x0 ~> 0x300000000000], [0x0 ~> 0x180000000000], [0x0 ~> 0x180000000000]] */
#[derive(Clone, Copy)]
pub struct fiat_poly1305_loose_field_element(pub [u64; 3]);

impl core::ops::Index<usize> for fiat_poly1305_loose_field_element {
    type Output = u64;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl core::ops::IndexMut<usize> for fiat_poly1305_loose_field_element {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

/** The type fiat_poly1305_tight_field_element is a field element with tight bounds. */
/** Bounds: [[0x0 ~> 0x100000000000], [0x0 ~> 0x80000000000], [0x0 ~> 0x80000000000]] */
#[derive(Clone, Copy)]
pub struct fiat_poly1305_tight_field_element(pub [u64; 3]);

impl core::ops::Index<usize> for fiat_poly1305_tight_field_element {
    type Output = u64;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl core::ops::IndexMut<usize> for fiat_poly1305_tight_field_element {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}


/// The function fiat_poly1305_addcarryx_u44 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^44
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^44⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xfffffffffff]
///   arg3: [0x0 ~> 0xfffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xfffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_poly1305_addcarryx_u44(out1: &mut u64, out2: &mut fiat_poly1305_u1, arg1: fiat_poly1305_u1, arg2: u64, arg3: u64) -> () {
  let x1: u64 = (((arg1 as u64) + arg2) + arg3);
  let x2: u64 = (x1 & 0xfffffffffff);
  let x3: fiat_poly1305_u1 = ((x1 >> 44) as fiat_poly1305_u1);
  *out1 = x2;
  *out2 = x3;
}

/// The function fiat_poly1305_subborrowx_u44 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^44
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^44⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xfffffffffff]
///   arg3: [0x0 ~> 0xfffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xfffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_poly1305_subborrowx_u44(out1: &mut u64, out2: &mut fiat_poly1305_u1, arg1: fiat_poly1305_u1, arg2: u64, arg3: u64) -> () {
  let x1: i64 = ((((((arg2 as i128) - (arg1 as i128)) as i64) as i128) - (arg3 as i128)) as i64);
  let x2: fiat_poly1305_i1 = ((x1 >> 44) as fiat_poly1305_i1);
  let x3: u64 = (((x1 as i128) & (0xfffffffffff as i128)) as u64);
  *out1 = x3;
  *out2 = (((0x0 as fiat_poly1305_i2) - (x2 as fiat_poly1305_i2)) as fiat_poly1305_u1);
}

/// The function fiat_poly1305_addcarryx_u43 is an addition with carry.
///
/// Postconditions:
///   out1 = (arg1 + arg2 + arg3) mod 2^43
///   out2 = ⌊(arg1 + arg2 + arg3) / 2^43⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_poly1305_addcarryx_u43(out1: &mut u64, out2: &mut fiat_poly1305_u1, arg1: fiat_poly1305_u1, arg2: u64, arg3: u64) -> () {
  let x1: u64 = (((arg1 as u64) + arg2) + arg3);
  let x2: u64 = (x1 & 0x7ffffffffff);
  let x3: fiat_poly1305_u1 = ((x1 >> 43) as fiat_poly1305_u1);
  *out1 = x2;
  *out2 = x3;
}

/// The function fiat_poly1305_subborrowx_u43 is a subtraction with borrow.
///
/// Postconditions:
///   out1 = (-arg1 + arg2 + -arg3) mod 2^43
///   out2 = -⌊(-arg1 + arg2 + -arg3) / 2^43⌋
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0x7ffffffffff]
///   arg3: [0x0 ~> 0x7ffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0x7ffffffffff]
///   out2: [0x0 ~> 0x1]
#[inline]
pub fn fiat_poly1305_subborrowx_u43(out1: &mut u64, out2: &mut fiat_poly1305_u1, arg1: fiat_poly1305_u1, arg2: u64, arg3: u64) -> () {
  let x1: i64 = ((((((arg2 as i128) - (arg1 as i128)) as i64) as i128) - (arg3 as i128)) as i64);
  let x2: fiat_poly1305_i1 = ((x1 >> 43) as fiat_poly1305_i1);
  let x3: u64 = (((x1 as i128) & (0x7ffffffffff as i128)) as u64);
  *out1 = x3;
  *out2 = (((0x0 as fiat_poly1305_i2) - (x2 as fiat_poly1305_i2)) as fiat_poly1305_u1);
}

/// The function fiat_poly1305_cmovznz_u64 is a single-word conditional move.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [0x0 ~> 0xffffffffffffffff]
///   arg3: [0x0 ~> 0xffffffffffffffff]
/// Output Bounds:
///   out1: [0x0 ~> 0xffffffffffffffff]
#[inline]
pub fn fiat_poly1305_cmovznz_u64(out1: &mut u64, arg1: fiat_poly1305_u1, arg2: u64, arg3: u64) -> () {
  let x1: fiat_poly1305_u1 = (!(!arg1));
  let x2: u64 = ((((((0x0 as fiat_poly1305_i2) - (x1 as fiat_poly1305_i2)) as fiat_poly1305_i1) as i128) & (0xffffffffffffffff as i128)) as u64);
  let x3: u64 = ((x2 & arg3) | ((!x2) & arg2));
  *out1 = x3;
}

/// The function fiat_poly1305_carry_mul multiplies two field elements and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg2) mod m
///
#[inline]
pub fn fiat_poly1305_carry_mul(out1: &mut fiat_poly1305_tight_field_element, arg1: &fiat_poly1305_loose_field_element, arg2: &fiat_poly1305_loose_field_element) -> () {
  let x1: u128 = (((arg1[2]) as u128) * (((arg2[2]) * 0x5) as u128));
  let x2: u128 = (((arg1[2]) as u128) * (((arg2[1]) * 0xa) as u128));
  let x3: u128 = (((arg1[1]) as u128) * (((arg2[2]) * 0xa) as u128));
  let x4: u128 = (((arg1[2]) as u128) * ((arg2[0]) as u128));
  let x5: u128 = (((arg1[1]) as u128) * (((arg2[1]) * 0x2) as u128));
  let x6: u128 = (((arg1[1]) as u128) * ((arg2[0]) as u128));
  let x7: u128 = (((arg1[0]) as u128) * ((arg2[2]) as u128));
  let x8: u128 = (((arg1[0]) as u128) * ((arg2[1]) as u128));
  let x9: u128 = (((arg1[0]) as u128) * ((arg2[0]) as u128));
  let x10: u128 = (x9 + (x3 + x2));
  let x11: u64 = ((x10 >> 44) as u64);
  let x12: u64 = ((x10 & (0xfffffffffff as u128)) as u64);
  let x13: u128 = (x7 + (x5 + x4));
  let x14: u128 = (x8 + (x6 + x1));
  let x15: u128 = ((x11 as u128) + x14);
  let x16: u64 = ((x15 >> 43) as u64);
  let x17: u64 = ((x15 & (0x7ffffffffff as u128)) as u64);
  let x18: u128 = ((x16 as u128) + x13);
  let x19: u64 = ((x18 >> 43) as u64);
  let x20: u64 = ((x18 & (0x7ffffffffff as u128)) as u64);
  let x21: u64 = (x19 * 0x5);
  let x22: u64 = (x12 + x21);
  let x23: u64 = (x22 >> 44);
  let x24: u64 = (x22 & 0xfffffffffff);
  let x25: u64 = (x23 + x17);
  let x26: fiat_poly1305_u1 = ((x25 >> 43) as fiat_poly1305_u1);
  let x27: u64 = (x25 & 0x7ffffffffff);
  let x28: u64 = ((x26 as u64) + x20);
  out1[0] = x24;
  out1[1] = x27;
  out1[2] = x28;
}

/// The function fiat_poly1305_carry_square squares a field element and reduces the result.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 * eval arg1) mod m
///
#[inline]
pub fn fiat_poly1305_carry_square(out1: &mut fiat_poly1305_tight_field_element, arg1: &fiat_poly1305_loose_field_element) -> () {
  let x1: u64 = ((arg1[2]) * 0x5);
  let x2: u64 = (x1 * 0x2);
  let x3: u64 = ((arg1[2]) * 0x2);
  let x4: u64 = ((arg1[1]) * 0x2);
  let x5: u128 = (((arg1[2]) as u128) * (x1 as u128));
  let x6: u128 = (((arg1[1]) as u128) * ((x2 * 0x2) as u128));
  let x7: u128 = (((arg1[1]) as u128) * (((arg1[1]) * 0x2) as u128));
  let x8: u128 = (((arg1[0]) as u128) * (x3 as u128));
  let x9: u128 = (((arg1[0]) as u128) * (x4 as u128));
  let x10: u128 = (((arg1[0]) as u128) * ((arg1[0]) as u128));
  let x11: u128 = (x10 + x6);
  let x12: u64 = ((x11 >> 44) as u64);
  let x13: u64 = ((x11 & (0xfffffffffff as u128)) as u64);
  let x14: u128 = (x8 + x7);
  let x15: u128 = (x9 + x5);
  let x16: u128 = ((x12 as u128) + x15);
  let x17: u64 = ((x16 >> 43) as u64);
  let x18: u64 = ((x16 & (0x7ffffffffff as u128)) as u64);
  let x19: u128 = ((x17 as u128) + x14);
  let x20: u64 = ((x19 >> 43) as u64);
  let x21: u64 = ((x19 & (0x7ffffffffff as u128)) as u64);
  let x22: u64 = (x20 * 0x5);
  let x23: u64 = (x13 + x22);
  let x24: u64 = (x23 >> 44);
  let x25: u64 = (x23 & 0xfffffffffff);
  let x26: u64 = (x24 + x18);
  let x27: fiat_poly1305_u1 = ((x26 >> 43) as fiat_poly1305_u1);
  let x28: u64 = (x26 & 0x7ffffffffff);
  let x29: u64 = ((x27 as u64) + x21);
  out1[0] = x25;
  out1[1] = x28;
  out1[2] = x29;
}

/// The function fiat_poly1305_carry reduces a field element.
///
/// Postconditions:
///   eval out1 mod m = eval arg1 mod m
///
#[inline]
pub fn fiat_poly1305_carry(out1: &mut fiat_poly1305_tight_field_element, arg1: &fiat_poly1305_loose_field_element) -> () {
  let x1: u64 = (arg1[0]);
  let x2: u64 = ((x1 >> 44) + (arg1[1]));
  let x3: u64 = ((x2 >> 43) + (arg1[2]));
  let x4: u64 = ((x1 & 0xfffffffffff) + ((x3 >> 43) * 0x5));
  let x5: u64 = ((((x4 >> 44) as fiat_poly1305_u1) as u64) + (x2 & 0x7ffffffffff));
  let x6: u64 = (x4 & 0xfffffffffff);
  let x7: u64 = (x5 & 0x7ffffffffff);
  let x8: u64 = ((((x5 >> 43) as fiat_poly1305_u1) as u64) + (x3 & 0x7ffffffffff));
  out1[0] = x6;
  out1[1] = x7;
  out1[2] = x8;
}

/// The function fiat_poly1305_add adds two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 + eval arg2) mod m
///
#[inline]
pub fn fiat_poly1305_add(out1: &mut fiat_poly1305_loose_field_element, arg1: &fiat_poly1305_tight_field_element, arg2: &fiat_poly1305_tight_field_element) -> () {
  let x1: u64 = ((arg1[0]) + (arg2[0]));
  let x2: u64 = ((arg1[1]) + (arg2[1]));
  let x3: u64 = ((arg1[2]) + (arg2[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/// The function fiat_poly1305_sub subtracts two field elements.
///
/// Postconditions:
///   eval out1 mod m = (eval arg1 - eval arg2) mod m
///
#[inline]
pub fn fiat_poly1305_sub(out1: &mut fiat_poly1305_loose_field_element, arg1: &fiat_poly1305_tight_field_element, arg2: &fiat_poly1305_tight_field_element) -> () {
  let x1: u64 = ((0x1ffffffffff6 + (arg1[0])) - (arg2[0]));
  let x2: u64 = ((0xffffffffffe + (arg1[1])) - (arg2[1]));
  let x3: u64 = ((0xffffffffffe + (arg1[2])) - (arg2[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/// The function fiat_poly1305_opp negates a field element.
///
/// Postconditions:
///   eval out1 mod m = -eval arg1 mod m
///
#[inline]
pub fn fiat_poly1305_opp(out1: &mut fiat_poly1305_loose_field_element, arg1: &fiat_poly1305_tight_field_element) -> () {
  let x1: u64 = (0x1ffffffffff6 - (arg1[0]));
  let x2: u64 = (0xffffffffffe - (arg1[1]));
  let x3: u64 = (0xffffffffffe - (arg1[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/// The function fiat_poly1305_selectznz is a multi-limb conditional select.
///
/// Postconditions:
///   out1 = (if arg1 = 0 then arg2 else arg3)
///
/// Input Bounds:
///   arg1: [0x0 ~> 0x1]
///   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
///   arg3: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
/// Output Bounds:
///   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
#[inline]
pub fn fiat_poly1305_selectznz(out1: &mut [u64; 3], arg1: fiat_poly1305_u1, arg2: &[u64; 3], arg3: &[u64; 3]) -> () {
  let mut x1: u64 = 0;
  fiat_poly1305_cmovznz_u64(&mut x1, arg1, (arg2[0]), (arg3[0]));
  let mut x2: u64 = 0;
  fiat_poly1305_cmovznz_u64(&mut x2, arg1, (arg2[1]), (arg3[1]));
  let mut x3: u64 = 0;
  fiat_poly1305_cmovznz_u64(&mut x3, arg1, (arg2[2]), (arg3[2]));
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}

/// The function fiat_poly1305_to_bytes serializes a field element to bytes in little-endian order.
///
/// Postconditions:
///   out1 = map (λ x, ⌊((eval arg1 mod m) mod 2^(8 * (x + 1))) / 2^(8 * x)⌋) [0..16]
///
/// Output Bounds:
///   out1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
#[inline]
pub fn fiat_poly1305_to_bytes(out1: &mut [u8; 17], arg1: &fiat_poly1305_tight_field_element) -> () {
  let mut x1: u64 = 0;
  let mut x2: fiat_poly1305_u1 = 0;
  fiat_poly1305_subborrowx_u44(&mut x1, &mut x2, 0x0, (arg1[0]), 0xffffffffffb);
  let mut x3: u64 = 0;
  let mut x4: fiat_poly1305_u1 = 0;
  fiat_poly1305_subborrowx_u43(&mut x3, &mut x4, x2, (arg1[1]), 0x7ffffffffff);
  let mut x5: u64 = 0;
  let mut x6: fiat_poly1305_u1 = 0;
  fiat_poly1305_subborrowx_u43(&mut x5, &mut x6, x4, (arg1[2]), 0x7ffffffffff);
  let mut x7: u64 = 0;
  fiat_poly1305_cmovznz_u64(&mut x7, x6, (0x0 as u64), 0xffffffffffffffff);
  let mut x8: u64 = 0;
  let mut x9: fiat_poly1305_u1 = 0;
  fiat_poly1305_addcarryx_u44(&mut x8, &mut x9, 0x0, x1, (x7 & 0xffffffffffb));
  let mut x10: u64 = 0;
  let mut x11: fiat_poly1305_u1 = 0;
  fiat_poly1305_addcarryx_u43(&mut x10, &mut x11, x9, x3, (x7 & 0x7ffffffffff));
  let mut x12: u64 = 0;
  let mut x13: fiat_poly1305_u1 = 0;
  fiat_poly1305_addcarryx_u43(&mut x12, &mut x13, x11, x5, (x7 & 0x7ffffffffff));
  let x14: u64 = (x12 << 7);
  let x15: u64 = (x10 << 4);
  let x16: u8 = ((x8 & (0xff as u64)) as u8);
  let x17: u64 = (x8 >> 8);
  let x18: u8 = ((x17 & (0xff as u64)) as u8);
  let x19: u64 = (x17 >> 8);
  let x20: u8 = ((x19 & (0xff as u64)) as u8);
  let x21: u64 = (x19 >> 8);
  let x22: u8 = ((x21 & (0xff as u64)) as u8);
  let x23: u64 = (x21 >> 8);
  let x24: u8 = ((x23 & (0xff as u64)) as u8);
  let x25: u8 = ((x23 >> 8) as u8);
  let x26: u64 = (x15 + (x25 as u64));
  let x27: u8 = ((x26 & (0xff as u64)) as u8);
  let x28: u64 = (x26 >> 8);
  let x29: u8 = ((x28 & (0xff as u64)) as u8);
  let x30: u64 = (x28 >> 8);
  let x31: u8 = ((x30 & (0xff as u64)) as u8);
  let x32: u64 = (x30 >> 8);
  let x33: u8 = ((x32 & (0xff as u64)) as u8);
  let x34: u64 = (x32 >> 8);
  let x35: u8 = ((x34 & (0xff as u64)) as u8);
  let x36: u8 = ((x34 >> 8) as u8);
  let x37: u64 = (x14 + (x36 as u64));
  let x38: u8 = ((x37 & (0xff as u64)) as u8);
  let x39: u64 = (x37 >> 8);
  let x40: u8 = ((x39 & (0xff as u64)) as u8);
  let x41: u64 = (x39 >> 8);
  let x42: u8 = ((x41 & (0xff as u64)) as u8);
  let x43: u64 = (x41 >> 8);
  let x44: u8 = ((x43 & (0xff as u64)) as u8);
  let x45: u64 = (x43 >> 8);
  let x46: u8 = ((x45 & (0xff as u64)) as u8);
  let x47: u64 = (x45 >> 8);
  let x48: u8 = ((x47 & (0xff as u64)) as u8);
  let x49: u8 = ((x47 >> 8) as u8);
  out1[0] = x16;
  out1[1] = x18;
  out1[2] = x20;
  out1[3] = x22;
  out1[4] = x24;
  out1[5] = x27;
  out1[6] = x29;
  out1[7] = x31;
  out1[8] = x33;
  out1[9] = x35;
  out1[10] = x38;
  out1[11] = x40;
  out1[12] = x42;
  out1[13] = x44;
  out1[14] = x46;
  out1[15] = x48;
  out1[16] = x49;
}

/// The function fiat_poly1305_from_bytes deserializes a field element from bytes in little-endian order.
///
/// Postconditions:
///   eval out1 mod m = bytes_eval arg1 mod m
///
/// Input Bounds:
///   arg1: [[0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0xff], [0x0 ~> 0x3]]
#[inline]
pub fn fiat_poly1305_from_bytes(out1: &mut fiat_poly1305_tight_field_element, arg1: &[u8; 17]) -> () {
  let x1: u64 = (((arg1[16]) as u64) << 41);
  let x2: u64 = (((arg1[15]) as u64) << 33);
  let x3: u64 = (((arg1[14]) as u64) << 25);
  let x4: u64 = (((arg1[13]) as u64) << 17);
  let x5: u64 = (((arg1[12]) as u64) << 9);
  let x6: u64 = (((arg1[11]) as u64) * (0x2 as u64));
  let x7: u64 = (((arg1[10]) as u64) << 36);
  let x8: u64 = (((arg1[9]) as u64) << 28);
  let x9: u64 = (((arg1[8]) as u64) << 20);
  let x10: u64 = (((arg1[7]) as u64) << 12);
  let x11: u64 = (((arg1[6]) as u64) << 4);
  let x12: u64 = (((arg1[5]) as u64) << 40);
  let x13: u64 = (((arg1[4]) as u64) << 32);
  let x14: u64 = (((arg1[3]) as u64) << 24);
  let x15: u64 = (((arg1[2]) as u64) << 16);
  let x16: u64 = (((arg1[1]) as u64) << 8);
  let x17: u8 = (arg1[0]);
  let x18: u64 = (x16 + (x17 as u64));
  let x19: u64 = (x15 + x18);
  let x20: u64 = (x14 + x19);
  let x21: u64 = (x13 + x20);
  let x22: u64 = (x12 + x21);
  let x23: u64 = (x22 & 0xfffffffffff);
  let x24: u8 = ((x22 >> 44) as u8);
  let x25: u64 = (x11 + (x24 as u64));
  let x26: u64 = (x10 + x25);
  let x27: u64 = (x9 + x26);
  let x28: u64 = (x8 + x27);
  let x29: u64 = (x7 + x28);
  let x30: u64 = (x29 & 0x7ffffffffff);
  let x31: fiat_poly1305_u1 = ((x29 >> 43) as fiat_poly1305_u1);
  let x32: u64 = (x6 + (x31 as u64));
  let x33: u64 = (x5 + x32);
  let x34: u64 = (x4 + x33);
  let x35: u64 = (x3 + x34);
  let x36: u64 = (x2 + x35);
  let x37: u64 = (x1 + x36);
  out1[0] = x23;
  out1[1] = x30;
  out1[2] = x37;
}

/// The function fiat_poly1305_relax is the identity function converting from tight field elements to loose field elements.
///
/// Postconditions:
///   out1 = arg1
///
#[inline]
pub fn fiat_poly1305_relax(out1: &mut fiat_poly1305_loose_field_element, arg1: &fiat_poly1305_tight_field_element) -> () {
  let x1: u64 = (arg1[0]);
  let x2: u64 = (arg1[1]);
  let x3: u64 = (arg1[2]);
  out1[0] = x1;
  out1[1] = x2;
  out1[2] = x3;
}
