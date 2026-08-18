Require Import ZArith BinInt Lia Arith PeanoNat.
Require Import Coq.Lists.List.
From Coq Require Import Setoid Classes.Morphisms.
Import ListNotations.

From coqutil Require Import
  letexists
  OfListWord
  Word.Properties
  Datatypes.List
  Tactics.Tactics.
Require Import (notations) coqutil.Map.Memory.

From bedrock2 Require Import
  Syntax
  bottom_up_simpl
  Array
  SepAutoArray
  ListIndexNotations
  wsize
  NotationsCustomEntry
  ProgramLogic
  WeakestPrecondition
  SeparationLogic
  AbsintWordToZ
  ZnWords.
Import ProgramLogic.Coercions.
Import symmetry.

From bedrock2Examples Require Import
  memcpy.

Require Import
  PrimeFieldTheorems
  Spec.WeierstrassCurve
  Curves.Weierstrass.Affine
  Curves.Weierstrass.AffineProofs
  Curves.Weierstrass.Jacobian.Jacobian
  Curves.Weierstrass.P256
  Bedrock.P256.Platform
  Bedrock.P256.Specs
  Bedrock.P256.Jacobian
  Bedrock.P256.JacobianAffine
  Bedrock.P256.PrecomputedMultiples.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Import LittleEndianList.

Require Import bedrock2.BasicC64Semantics.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.
#[local] Open Scope list_scope.

#[local] Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").
#[local] Notation sizeof_point := 96%nat.
#[local] Notation pointarray := (Array.array (fun (p : word.rep) (Q : point) =>
  ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat sizeof_point))).
#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).

#[local] Notation to_affine := Jacobian.to_affine.
#[local] Notation of_affine := Jacobian.of_affine.

(*** ========================================================================= ***)
(*** Section 1: Gallina Specification for Combed Base-Point Multiplication     ***)
(*** ========================================================================= ***)

Section Gallina.

  (* Comb structure parameters:
     - 32 rounds (i from 31 down to 0)
     - Comb spacing of 64 bits across 4 teeth
     - Interleaved second comb shifted by 32 bits
     - 15 non-zero precomputed multiples per subtable (indices 1 to 15) *)
  Definition comb_rounds : nat := 32%nat.
  Definition comb_spacing : Z := 64.
  Definition comb_shift : Z := 32.
  Definition comb_table_size : nat := 15%nat.

  (* Bit extraction: returns the bit at index idx of scalar s as a Z (0 or 1) *)
  Definition get_bit (s : Z) (idx : Z) : Z :=
    Z.b2z (Z.testbit s idx).

  (* Extracts 4 bits from scalar s at offsets [i + offset + 3*comb_spacing,
                                              i + offset + 2*comb_spacing,
                                              i + offset + 1*comb_spacing,
                                              i + offset]
     into an integer in [0, 15] *)
  Definition get_comb_bits_Z (s : Z) (i : Z) (offset : Z) : Z :=
    (get_bit s (i + offset + 3 * comb_spacing) * 8) +
    (get_bit s (i + offset + 2 * comb_spacing) * 4) +
    (get_bit s (i + offset + 1 * comb_spacing) * 2) +
    (get_bit s (i + offset)).

  (* Point in table 0 for index idx \in [0, 15]:
     idx = b3*8 + b2*4 + b1*2 + b0 corresponds to
     (b3 * 2^(3*comb_spacing) + b2 * 2^(2*comb_spacing) + b1 * 2^comb_spacing + b0) * G.
     Note: idx = 0 yields 0 * G = W.zero. *)
  Definition comb_point_0 (G : affine_point) (idx : Z) : affine_point :=
    let b0 := get_bit idx 0 in
    let b1 := get_bit idx 1 in
    let b2 := get_bit idx 2 in
    let b3 := get_bit idx 3 in
    let k := b0 + b1 * 2^comb_spacing + b2 * 2^(2 * comb_spacing) + b3 * 2^(3 * comb_spacing) in
    W.mul k G.

  (* Table 0: list of 15 non-zero points for indices 1 to 15 (0*G omitted) *)
  Definition comb_table_0 (G : affine_point) : list affine_point :=
    map (fun idx => comb_point_0 G (Z.of_nat idx)) (seq 1 comb_table_size).

  (* Point in table 1 for index idx \in [0, 15]:
     Each point of table 0 multiplied by 2^comb_shift, i.e., [2^comb_shift] * comb_point_0 G idx *)
  Definition comb_point_1 (G : affine_point) (idx : Z) : affine_point :=
    W.mul (2^comb_shift) (comb_point_0 G idx).

  (* Table 1: list of 15 non-zero points for indices 1 to 15 (0*G omitted) *)
  Definition comb_table_1 (G : affine_point) : list affine_point :=
    map (fun idx => comb_point_1 G (Z.of_nat idx)) (seq 1 comb_table_size).

  (* Combined precomputed table of 30 points: table 0 (15 pts) followed by table 1 (15 pts) *)
  Definition comb_table (G : affine_point) : list affine_point :=
    comb_table_0 G ++ comb_table_1 G.

  (* Tooth term: get_bit s (i + k*32) * 2^(k*32) *)
  Definition comb_tooth (s : Z) (i : Z) (k : Z) : Z :=
    get_bit s (i + k * comb_shift) * 2^(k * comb_shift).

  (* Full round scalar: sum of all 8 teeth for round i *)
  Definition comb_round_scalar (s : Z) (i : Z) : Z :=
    comb_tooth s i 0 + comb_tooth s i 1 +
    comb_tooth s i 2 + comb_tooth s i 3 +
    comb_tooth s i 4 + comb_tooth s i 5 +
    comb_tooth s i 6 + comb_tooth s i 7.

  (* Scalar accumulated by the loop for a given number of rounds *)
  Fixpoint comb_loop_scalar (s : Z) (round : nat) : Z :=
    match round with
    | O => 0
    | S r =>
      comb_loop_scalar s r + 2^(Z.of_nat r) * comb_round_scalar s (Z.of_nat r)
    end.

  (* High-level functional specification of the 32-round comb loop:
     Starting from acc = infinity (W.zero), in each round from i = 31 down to 0:
       acc <- 2 * acc + (T1[bits1] + T0[bits0]) *)
  Fixpoint comb_scalarmult_loop (G : affine_point) (s : Z) (round : nat) (acc : affine_point) : affine_point :=
    match round with
    | O => acc
    | S r =>
      let i := Z.of_nat r in
      let bits1 := get_comb_bits_Z s i comb_shift in
      let bits0 := get_comb_bits_Z s i 0 in
      let p1 := comb_point_1 G bits1 in
      let p0 := comb_point_0 G bits0 in
      let acc' := W.mul 2 acc in
      let acc'' := W.add acc' (W.add p1 p0) in
      comb_scalarmult_loop G s r acc''
    end.

  (* Top-level Gallina combed scalar multiplication *)
  Definition comb_scalarmult (G : affine_point) (s : Z) : affine_point :=
    comb_scalarmult_loop G s comb_rounds W.zero.

  Local Lemma comb_point_0_get_comb_bits_Z : forall (G : affine_point) (s : Z) (i : Z) (offset : Z),
    comb_point_0 G (get_comb_bits_Z s i offset) =
    W.mul (get_bit s (i + offset) +
           get_bit s (i + offset + 1 * comb_spacing) * 2^comb_spacing +
           get_bit s (i + offset + 2 * comb_spacing) * 2^(2 * comb_spacing) +
           get_bit s (i + offset + 3 * comb_spacing) * 2^(3 * comb_spacing)) G.
  Proof.
    intros G s i offset.
    cbv [comb_point_0 get_comb_bits_Z get_bit].
    destruct (Z.testbit s (i + offset)),
             (Z.testbit s (i + offset + 1 * comb_spacing)),
             (Z.testbit s (i + offset + 2 * comb_spacing)),
             (Z.testbit s (i + offset + 3 * comb_spacing));
      reflexivity.
  Qed.

  Local Lemma comb_round_step_eq : forall (G : affine_point) (s : Z) (i : Z),
    W.eq (W.add (comb_point_1 G (get_comb_bits_Z s i comb_shift))
                (comb_point_0 G (get_comb_bits_Z s i 0)))
         (W.mul (comb_round_scalar s i) G).
  Proof.
    intros G s i.
    cbv [comb_point_1].
    rewrite !comb_point_0_get_comb_bits_Z.
    rewrite ScalarMult.scalarmult_assoc, <- ScalarMult.scalarmult_add_l.
    f_equiv.
    cbv [comb_round_scalar comb_tooth comb_shift comb_spacing].
    rewrite <- !Z.add_assoc.
    cbn.
    lia.
  Qed.

  Local Lemma comb_scalarmult_loop_invariant : forall (G : affine_point) (s : Z) (round : nat) (acc : affine_point) (acc_val : Z),
    W.eq acc (W.mul acc_val G) ->
    W.eq (comb_scalarmult_loop G s round acc)
         (W.mul (2^(Z.of_nat round) * acc_val + comb_loop_scalar s round) G).
  Proof.
    intros G0 s0.
    induction round as [|r IHr]; intros acc acc_val Hacc.
    {
      simpl comb_scalarmult_loop.
      simpl comb_loop_scalar.
      rewrite Z.pow_0_r.
      replace (1 * acc_val + 0) with acc_val by lia.
      exact Hacc.
    }
    {
      simpl comb_scalarmult_loop.
      set (p1 := comb_point_1 G0 (get_comb_bits_Z s0 (Z.of_nat r) comb_shift)).
      set (p0 := comb_point_0 G0 (get_comb_bits_Z s0 (Z.of_nat r) 0)).
      assert (Hstep : W.eq (W.add (W.mul 2 acc) (W.add p1 p0))
                           (W.mul (2 * acc_val + comb_round_scalar s0 (Z.of_nat r)) G0)).
      {
        subst p1 p0.
        rewrite comb_round_step_eq.
        rewrite Hacc.
        rewrite ScalarMult.scalarmult_assoc, <- ScalarMult.scalarmult_add_l.
        f_equiv.
        lia.
      }
      apply (IHr (W.add (W.mul 2 acc) (W.add p1 p0)) (2 * acc_val + comb_round_scalar s0 (Z.of_nat r))) in Hstep.
      rewrite Hstep.
      f_equiv.
      simpl comb_loop_scalar.
      rewrite Znat.Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat r)) with (Z.of_nat r + 1) by lia.
      rewrite Z.pow_add_r by lia.
      change (2^1) with 2.
      lia.
    }
  Qed.

  Local Lemma get_bit_div_pow2 : forall (s : Z) (r k : Z),
    0 <= r -> 0 <= k ->
    get_bit s (r + k) = get_bit (s / 2^k) r.
  Proof.
    intros s r k Hr Hk.
    cbv [get_bit].
    rewrite Z.div_pow2_bits by lia.
    reflexivity.
  Qed.

  Local Lemma mod_pow2_step_bits : forall (s n : Z),
    0 <= n ->
    s mod 2^(n + 1) = s mod 2^n + 2^n * get_bit s n.
  Proof.
    intros s0 n Hn.
    rewrite Z.pow_add_r by lia.
    change (2^1) with 2.
    assert (Hs0 : s0 = 2^n * (s0 / 2^n) + s0 mod 2^n) by (apply Z.div_mod; lia).
    assert (Hdiv : (s0 / 2^n) = 2 * ((s0 / 2^n) / 2) + (s0 / 2^n) mod 2) by (apply Z.div_mod; lia).
    rewrite Hdiv in Hs0.
    assert (Hmod_range : 0 <= s0 mod 2^n < 2^n) by (apply Z.mod_pos_bound; lia).
    assert (Hdiv_mod_range : 0 <= (s0 / 2^n) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    rewrite Hs0 at 1.
    replace (2 ^ n * (2 * (s0 / 2 ^ n / 2) + (s0 / 2 ^ n) mod 2) + s0 mod 2 ^ n)
      with ((s0 mod 2 ^ n + 2 ^ n * ((s0 / 2 ^ n) mod 2)) + (s0 / 2 ^ n / 2) * (2 ^ n * 2)) by lia.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small by nia.
    cbv [get_bit].
    rewrite <- Z.testbit_spec' by exact Hn.
    lia.
  Qed.

  Local Lemma div_div_pow2 : forall (a n m : Z),
    0 <= n -> 0 <= m ->
    (a / 2^n) / 2^m = a / 2^(n + m).
  Proof.
    intros a n m Hn Hm.
    rewrite Z.div_div by lia.
    rewrite <- Z.pow_add_r by lia.
    reflexivity.
  Qed.

  Local Lemma comb_loop_scalar_correct : forall (s : Z),
    0 <= s < 2^(4 * comb_spacing) ->
    comb_loop_scalar s 32 = s.
  Proof.
    intros s Hs.
    assert (Hloop : forall round,
      comb_loop_scalar s round =
      let m := 2^(Z.of_nat round) in
      ((s / 2^0) mod m) * 2^0 +
      ((s / 2^32) mod m) * 2^32 +
      ((s / 2^64) mod m) * 2^64 +
      ((s / 2^96) mod m) * 2^96 +
      ((s / 2^128) mod m) * 2^128 +
      ((s / 2^160) mod m) * 2^160 +
      ((s / 2^192) mod m) * 2^192 +
      ((s / 2^224) mod m) * 2^224).
    {
      induction round as [|r IHr].
      {
        simpl comb_loop_scalar.
        cbn.
        rewrite !Z.mod_1_r.
        reflexivity.
      }
      {
        simpl comb_loop_scalar.
        rewrite IHr.
        cbv [comb_round_scalar comb_tooth comb_shift].
        rewrite Znat.Nat2Z.inj_succ.
        replace (Z.succ (Z.of_nat r)) with (Z.of_nat r + 1) by lia.
        rewrite !get_bit_div_pow2 by lia.
        rewrite !(mod_pow2_step_bits _ (Z.of_nat r)) by lia.
        cbn [Pos.mul Pos.add Z.mul].
        lia.
      }
    }
    rewrite (Hloop 32%nat).
    cbn [Z.of_nat].
    change (Z.pos (PosDef.Pos.of_succ_nat 31)) with 32.
    change (2^0) with 1.
    rewrite Z.div_1_r.
    assert (Hdecomp : forall k, 0 <= k ->
      s / 2^k = (s / 2^k) mod 2^32 + 2^32 * (s / 2^(k + 32))).
    {
      intros k Hk.
      rewrite (Z.div_mod (s / 2^k) (2^32)) at 1 by lia.
      rewrite div_div_pow2 by lia.
      lia.
    }
    assert (Hdiv256 : s / 2^256 = 0).
    {
      apply Z.div_small.
      cbv [comb_spacing] in Hs.
      exact Hs.
    }
    assert (Hs0 : s = 2^32 * (s / 2^32) + s mod 2^32) by (apply Z.div_mod; lia).
    pose proof (Hdecomp 32 ltac:(lia)) as Hs1.
    pose proof (Hdecomp 64 ltac:(lia)) as Hs2.
    pose proof (Hdecomp 96 ltac:(lia)) as Hs3.
    pose proof (Hdecomp 128 ltac:(lia)) as Hs4.
    pose proof (Hdecomp 160 ltac:(lia)) as Hs5.
    pose proof (Hdecomp 192 ltac:(lia)) as Hs6.
    pose proof (Hdecomp 224 ltac:(lia)) as Hs7.
    change (32 + 32) with 64 in Hs1.
    change (64 + 32) with 96 in Hs2.
    change (96 + 32) with 128 in Hs3.
    change (128 + 32) with 160 in Hs4.
    change (160 + 32) with 192 in Hs5.
    change (192 + 32) with 224 in Hs6.
    change (224 + 32) with 256 in Hs7.
    rewrite Hs7, Hdiv256 in Hs6.
    rewrite Hs6 in Hs5.
    rewrite Hs5 in Hs4.
    rewrite Hs4 in Hs3.
    rewrite Hs3 in Hs2.
    rewrite Hs2 in Hs1.
    rewrite Hs1 in Hs0.
    rewrite Hs0 at 9.
    lia.
  Qed.

  (* Mathematical correctness theorem of the comb multiplication algorithm *)
  Lemma comb_scalarmult_correct : forall (G : affine_point) (s : Z),
    0 <= s < 2^(4 * comb_spacing) ->
    W.eq (comb_scalarmult G s) (W.mul s G).
  Proof.
    intros G s Hs.
    cbv [comb_scalarmult comb_rounds].
    pose proof (comb_scalarmult_loop_invariant G s 32%nat W.zero 0) as Hinv.
    assert (H_zero : W.eq W.zero (W.mul 0 G)) by (symmetry; apply ScalarMult.scalarmult_0_l).
    apply Hinv in H_zero.
    rewrite H_zero.
    replace (2 ^ Z.of_nat 32 * 0 + comb_loop_scalar s 32) with (comb_loop_scalar s 32) by lia.
    apply (@ScalarMult.Proper_scalarmult_ref _ W.eq W.add W.zero W.opp (Hierarchy.commutative_group_group curve_commutative_group)); [|reflexivity].
    apply comb_loop_scalar_correct.
    exact Hs.
  Qed.

End Gallina.


(*** ========================================================================= ***)
(*** Section 2: Bedrock2 Function Definitions                                  ***)
(*** ========================================================================= ***)

(* Extracts 4 comb bits from scalar at offsets i + offset + {192, 128, 64, 0} *)
Definition p256_get_comb_bits :=
  func! (p_scalar, i, offset) ~> bits {
    w0 = load(p_scalar);
    w1 = load(p_scalar + $8);
    w2 = load(p_scalar + $16);
    w3 = load(p_scalar + $24);
    shift = i + offset;
    b0 = (w0 >> shift) & $1;
    b1 = (w1 >> shift) & $1;
    b2 = (w2 >> shift) & $1;
    b3 = (w3 >> shift) & $1;
    bits = (b3 << $3) | (b2 << $2) | (b1 << $1) | b0
  }.

(* Constant-time selection of an affine point from a 15-point table (each entry 96 bytes).
   idx = 0 produces point at infinity (zeroed coordinates).
   idx \in [1, 15] selects table[idx - 1]. *)
Definition p256_select_point_affine :=
  func! (p_out, p_table, idx) {
    p256_point_set_zero(p_out);
    i = $1;
    while ($16 - i) {
      unpack! ineq = br_broadcast_nonzero(i ^ idx);
      br_memcxor(p_out, p_table + ($sizeof_point * (i - $1)), $sizeof_point, ~ineq);
      i = i + $1;
      $(cmd.unset "ineq")
    }
  }.

(* Combed base-point multiplication on P-256 *)
Definition p256_point_mul_base :=
  func! (p_out, p_scalar, p_table) {
    stackalloc sizeof_point as p_nq;
    stackalloc sizeof_point as p_tmp;
    stackalloc sizeof_point as p_sum;

    p256_point_set_zero(p_nq);
    skip = $1;
    step = $0;
    while ($32 - step) {
      i = $31 - step;

      if !skip {
        p256_point_double(p_nq, p_nq)
      };

      (* First: look 32 bits upwards -> table 1 at offset 15 * sizeof_point *)
      unpack! bits1 = p256_get_comb_bits(p_scalar, i, $32);
      p256_select_point_affine(p_tmp, p_table + ($sizeof_point * $15), bits1);

      if !skip {
        p256_point_add_vartime_if_doubling(p_sum, p_nq, p_tmp);
        br_memcpy(p_nq, p_sum, $sizeof_point)
      } else {
        br_memcpy(p_nq, p_tmp, $sizeof_point);
        skip = $0
      };

      (* Second: look at current position -> table 0 at offset 0 *)
      unpack! bits0 = p256_get_comb_bits(p_scalar, i, $0);
      p256_select_point_affine(p_tmp, p_table, bits0);
      p256_point_add_vartime_if_doubling(p_sum, p_nq, p_tmp);
      br_memcpy(p_nq, p_sum, $sizeof_point);

      step = step + $1;
      $(cmd.unset "i");
      $(cmd.unset "bits1");
      $(cmd.unset "bits0")
    };

    br_memcpy(p_out, p_nq, $sizeof_point)
  }.


(*** ========================================================================= ***)
(*** Section 3: Bedrock2 Specifications                                        ***)
(*** ========================================================================= ***)

#[export] Instance spec_of_p256_get_comb_bits : spec_of "p256_get_comb_bits" :=
  fnspec! "p256_get_comb_bits" (p_scalar i offset : word) / scalar R ~> bits,
  { requires t m :=
      m =* bytearray p_scalar scalar * R /\
      length scalar = 32%nat /\
      0 <= word.unsigned i < Z.of_nat comb_rounds /\
      (word.unsigned offset = 0 \/ word.unsigned offset = comb_shift);
    ensures T M :=
      M = m /\ T = t /\
      word.unsigned bits = get_comb_bits_Z (LittleEndianList.le_combine scalar) (word.unsigned i) (word.unsigned offset) /\
      0 <= word.unsigned bits < 16
  }.

#[export] Instance spec_of_p256_select_point_affine : spec_of "p256_select_point_affine" :=
  fnspec! "p256_select_point_affine" p_out p_table idx / (out_old : list Byte.byte) (table : list point) R,
  { requires t m :=
      m =* out_old$@p_out * pointarray p_table table * R /\
      length out_old = sizeof_point /\
      length table = 15%nat /\
      0 <= word.unsigned idx < 16;
    ensures t' m := t' = t /\
      m =* (if (word.unsigned idx =? 0)%Z
            then of_affine W.zero
            else nth_default (of_affine W.zero) table (Z.to_nat (word.unsigned idx) - 1))$@p_out *
          pointarray p_table table * R
  }.

#[export] Instance spec_of_p256_point_mul_base : spec_of "p256_point_mul_base" :=
  fnspec! "p256_point_mul_base" (p_out p_scalar p_table : word) / out scalar (table : list point) (G : affine_point) R,
  { requires t m :=
      m =* out$@p_out * bytearray p_scalar scalar * pointarray p_table table * R /\
      length out = sizeof_point /\
      length scalar = 32%nat /\
      length table = 30%nat /\
      Forall2 W.eq (map to_affine table) (comb_table G) /\
      0 <= LittleEndianList.le_combine scalar < p256_group_order;
    ensures T M := exists (Q : point),
      M =* Q$@p_out * bytearray p_scalar scalar * pointarray p_table table * R /\
      W.eq (to_affine Q) (W.mul (LittleEndianList.le_combine scalar) G) /\
      T = t
  }.


(*** ========================================================================= ***)
(*** Section 4: Correctness Proofs (Admitted Skeletons)                        ***)
(*** ========================================================================= ***)

Lemma p256_get_comb_bits_ok : program_logic_goal_for_function! p256_get_comb_bits.
Proof.
  admit.
Admitted.

Lemma p256_select_point_affine_ok : program_logic_goal_for_function! p256_select_point_affine.
Proof.
  admit.
Admitted.

Lemma p256_point_mul_base_ok :
  let _ := spec_of_p256_point_add_constant_time in
  program_logic_goal_for_function! p256_point_mul_base.
Proof.
  admit.
Admitted.
