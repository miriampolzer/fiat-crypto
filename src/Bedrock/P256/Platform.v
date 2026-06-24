Require Import Bedrock.P256.Specs.
Require Import Coq.ZArith.ZArith.
From bedrock2 Require Import Loops.
Require Import Bedrock.Field.Common.Tactics.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.

Import bedrock2.Syntax bedrock2.NotationsCustomEntry
LittleEndianList
ZArith.BinInt
BinInt BinNat Init.Byte
PrimeFieldTheorems ModInv
micromega.Lia
coqutil.Byte
Lists.List micromega.Lia
Jacobian
Coq.Strings.String Coq.Lists.List
ProgramLogic WeakestPrecondition
ProgramLogic.Coercions
Word.Interface OfListWord Separation SeparationLogic
letexists
ListIndexNotations
SepAutoArray
symmetry
PeanoNat micromega.Lia
Tactics
UniquePose
micromega.Lia Word.Properties
ZnWords
bedrock2.BasicCSemantics.

Import ListIndexNotations.
Local Open Scope list_index_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Import (notations) coqutil.Map.Memory.
Require Import bedrock2.wsize.


Require coqutil.Word.Interface.
Require coqutil.Map.Interface.

(* Parameterize word size to ensure proofs are valid in 32 and 64 bit context.*)
Section WithParameters.
Context {width} {BW: Bitwidth.Bitwidth width}.
#[local] Hint Extern 0 (word width) => exact (Naive.word width) : typeclass_instances.
#[local] Notation word := (Naive.word width).

Import Specs. (* Now word is accessible with short name. *)

(* ZnWords with destructed word size equality after ZnWords_pre, to incorporate word size in hypothesis. *)
#[local] Ltac ZnWords ::=
  pose proof word_ok;
  destruct Bitwidth.width_cases as [W|W]; symmetry in W; ZnWords_pre; try destruct W; better_lia.

Definition br_value_barrier := func! (a) ~> a {
  /*skip*/ (* insert appropriate incantation for compilers that optimize values *)
}.

Definition br_declassify := func! (a) ~> a {
  /*skip*/ (* insert appropriate incantation for ctgrind *)
}.

Definition br_broadcast_odd := func! (x) ~> y {
  unpack! x = br_value_barrier(x&$1);
  y = -x
}.

Definition br_broadcast_negative := func! (x) ~> y {
  y = x.>>$wmask;
  unpack! y = br_value_barrier(y)
}.

Definition br_broadcast_nonzero := func! (x) ~> y {
  unpack! y = br_broadcast_negative(x | -x)
}.

Lemma value_barrier_ok : program_logic_goal_for_function! br_value_barrier.
Proof. cbv [spec_of_value_barrier]; repeat straightline. Qed.

Lemma br_declassify_ok : program_logic_goal_for_function! br_declassify.
Proof. cbv [spec_of_br_declassify]; repeat straightline. Qed.

Lemma br_broadcast_odd_ok : program_logic_goal_for_function! br_broadcast_odd.
Proof.
  cbv [spec_of_br_broadcast_odd].
  repeat straightline.
  straightline_call; repeat straightline.
  subst x0 y.
  try rewrite word.sub_0_l.
  cbv [word.broadcast]; apply f_equal.
  apply word.unsigned_inj, Z.bits_inj'; intros i Hi.
  rewrite word.unsigned_and, !word.unsigned_of_Z, !word.testbit_wrap.
  f_equal. f_equal. replace (word.wrap 1) with (Z.ones 1) by (cbv [Z.ones]; ZnWords). rewrite Z.land_ones by lia.
  rewrite <-Z.bit0_mod, Z.bit0_odd; trivial.
Qed.

Lemma br_broadcast_negative_ok : program_logic_goal_for_function! br_broadcast_negative.
Proof.
  cbv [spec_of_br_broadcast_negative].
  repeat straightline.
  straightline_call; repeat straightline.
  subst y.
  rewrite word.signed_lts.
  rewrite word.signed_of_Z_nowrap by ZnWords.
  rewrite <-word.testbit_msb.
  setoid_rewrite eval_wmask'.
  setoid_rewrite word.srs_msb; trivial.
Qed.

Lemma br_broadcast_nonzero_ok : program_logic_goal_for_function! br_broadcast_nonzero.
Proof.
  cbv [spec_of_br_broadcast_nonzero].
  repeat straightline.
  straightline_call; repeat straightline.
  apply f_equal, Bool.eq_true_iff_eq; rewrite Bool.negb_true_iff, Z.eqb_neq.
  rewrite word.signed_lts, word.signed_of_Z_nowrap by ZnWords.
  rewrite <-word.testbit_msb, word.unsigned_or_nowrap, Z.lor_spec, !word.testbit_msb.
  rewrite <- nz_signed.
  case Z.ltb_spec; intros; cbn [orb]; try lia.
  setoid_rewrite signed_opp_nowrap; intuition ZnWords.ZnWords.
Qed.

Definition br_cmov := func! (c, vnz, vz) ~> r {
  unpack! m = br_broadcast_nonzero(c);
  r = m & vnz | ~m & vz
}.

Lemma br_cmov_ok : program_logic_goal_for_function! br_cmov.
Proof.
  cbv [spec_of_br_cmov].
  repeat (straightline || straightline_call).
  subst r x; cbn [Semantics.interp_op1] in *.
  pose proof word.unsigned_range vz.
  pose proof word.unsigned_range vnz.
  case Z.eqb_spec; intros; unfold word.broadcast in *; cbn [Z.b2z negb].
  all : apply word.unsigned_inj;
    repeat rewrite ?word.unsigned_or, word.unsigned_and, ?word.unsigned_opp, ?word.unsigned_not, ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; cbv [word.wrap].
  all : apply Z.bits_inj'; intros i Hi;
    repeat rewrite <-?Z.land_ones, ?Z.land_spec, ?Z.lor_spec, ?Z.testbit_ones, ?Z.lnot_spec, ?Z.testbit_0_l by try ZnWords.ZnWords.
  2: rewrite word.unsigned_opp_nowrap, word.unsigned_of_Z_1 by ZnWords;
     change (2 ^ width - 1) with (Z.pred (2 ^ width)); rewrite <- Z.ones_equiv.
  all: repeat (((case Z.ltb_spec; [|]; intros)||(case Z.leb_spec; [|]; intros)); rewrite
      ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r,
      ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
      ?Z.testbit_0_l, ?prove_Zeq_bitwise.testbit_minus1, ?Z.testbit_neg_r, ?Z.testbit_high,
      ?Z.testbit_ones
    by intuition (idtac;
         match goal with
         | H : ?x < ?y^?a |- ?x < ?y^?b =>
             apply (Z.lt_le_trans _ (y^a)), Z.pow_le_mono_r; lia
         | _ => lia
         end);
    cbn [negb]; trivial; try lia).
Qed.

Definition br_abs := func! (k, sign_mask) ~> r {
  (* Alternatively we could have called br_cmov. *)
  r = (k ^ sign_mask) + (sign_mask & $1)
}.

#[local] Ltac div_mod_lia := rewrite ?word.signed_eq_swrap_unsigned, ?word.swrap_as_div_mod in *;
      PreOmega.Z.to_euclidean_division_equations; ZnWords.

Lemma opp_sub_opp_add n m : - n - m = - (n + m). Proof. lia. Qed.

Lemma br_abs_ok : program_logic_goal_for_function! br_abs.
Proof.
  cbv [spec_of_br_abs]. repeat straightline.
  subst r.
  pose proof word.unsigned_range k.
  destruct (Z.abs_spec (word.signed k)) as [[? ->] | [? ->]].
    { repeat (rewrite ?H, ?word.unsigned_add_nowrap, ?unsigned_xor_nowrap,
      ?word.unsigned_and_nowrap, ?word.unsigned_of_Z_nowrap,
      ?word.unsigned_xor_nowrap, ?Z.land_0_l, ?Z.lxor_0_r;
      try (lia || ZnWords.ZnWords); try (case Z.ltb_spec; intros)).
      div_mod_lia. }
    { repeat rewrite ?H, ?word.unsigned_add_nowrap, ?unsigned_xor_nowrap,
      ?word.unsigned_and_nowrap, ?word.unsigned_of_Z_nowrap,
      ?word.unsigned_xor_nowrap, ?Hsign, ?Z.land_ones; try (lia || ZnWords.ZnWords);
      try (case Z.ltb_spec; intros); try div_mod_lia.
      all: rewrite Z.land_comm, Z.land_ones_low; try ZnWords.
      2, 4: clear -BW; destruct Bitwidth.width_cases as [-> | ->]; cbv; trivial.
      all: rewrite Z.lxor_comm, <- word.unsigned_not_nowrap, word.unsigned_not;
        rewrite Zbitwise.Z.lnot_eq_pred_opp.
      all: cbv [word.wrap]; rewrite opp_sub_opp_add, Modulo.Z.mod_opp_small by ZnWords.
      all: try div_mod_lia. }
Qed.

Definition br_memset := func! (p_d, v, n) {
  while n {
    store1(p_d, v);
    p_d = p_d+$1;
    n = n-$1
  }
}.

Definition br_memcxor := func! (p_d, p_s, n, m) {
  while n {
    store1(p_d, load1(p_d) ^ (m & load1(p_s)));
    p_d = p_d+$1;
    n = n-$1
  }
}.


Lemma br_memset_ok : program_logic_goal_for_function! br_memset.
Admitted.

Lemma br_memcxor_ok : program_logic_goal_for_function! br_memcxor.
Proof.
  (* Proof implementation for br_memcxor would go here *)
Admitted.

End WithParameters.
