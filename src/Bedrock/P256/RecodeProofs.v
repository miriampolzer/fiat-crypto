Require Import ZArith.ZArith Lia Lists.List.
From coqutil Require Import
  Byte
  Word.LittleEndianList
  Word.Interface
  Word.Properties
  Tactics.Tactics
  Datatypes.List.

From bedrock2 Require Import
  NotationsCustomEntry
  WeakestPrecondition
  ProgramLogic
  Map.SeparationLogic
  Array
  Scalars
  Syntax
  ZnWords.

Require Import Bedrock.P256.Specs Bedrock.P256.RecodeSpecs.
From bedrock2Examples Require Import full_sub.

Import BinInt String ListNotations.
Import ProgramLogic.Coercions.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.

(* Parameterize word size to ensure proofs are valid in 32 and 64 bit context.*)
Require Import bedrock2.BasicCSemantics.
Section WithParameters.
Context {width} {BW: Bitwidth.Bitwidth width}.
#[local] Hint Extern 0 (word width) => exact (Naive.word width) : typeclass_instances.
#[local] Notation word := (Naive.word width).

Import Specs. (* Now word is accessible with short name. *)

Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Notation "$ n" := (match word.of_Z n return word (width:=width) with w => w end) (at level 9, format "$ n").

(* ZnWords with destructed word size equality after ZnWords_pre, to incorporate word size in hypothesis. *)
#[local] Ltac ZnWords ::=
  pose proof word_ok;  cbv [word] in *;
  destruct Bitwidth.width_cases as [W|W]; symmetry in W; ZnWords_pre; try destruct W; better_lia.

#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).

(* Limb size (nonzero). *)
#[local] Notation w := 5.

(* TODO these can go into bedrock examples, or as general file into p256, but word size agnostic. *)
Require Import coqutil.Macros.ident_to_string.

Local Notation "x += e" :=
  (cmd.set
     (ident_to_string! x)
     (expr.op bopname.add (ident_to_string! x) e))
    (in custom bedrock_cmd at
          level 0, x ident, e custom bedrock_expr, only parsing).

Local Notation "x -= e" :=
  (cmd.set
     (ident_to_string! x)
     (expr.op bopname.sub (ident_to_string! x) e))
    (in custom bedrock_cmd at
          level 0, x ident, e custom bedrock_expr, only parsing).

(* This definition is inspired by `bn_sub_with_borrow` in BoringSSL,
 * but has been rewritten in order to simplify its verification.  *)
Definition br_full_sub :=
  func! (x, y, borrow) ~> (diff, out_borrow) {
      out_borrow = x < y;
      diff = x - y;
      out_borrow += diff < borrow;
      diff -= borrow
    }.

#[export] Instance spec_of_full_sub : spec_of "br_full_sub" :=
  fnspec! "br_full_sub" x y borrow ~> diff out_borrow,
    { requires t m :=
        (* This pre-condition is not required in order to ensure the
         * post-condition, but formalizes on a condition on the
         * operation's expected usage. *)
        word.unsigned borrow < 2;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned diff - 2^width * word.unsigned out_borrow =
            word.unsigned x - word.unsigned y - word.unsigned borrow
    }.

    Lemma ltu_as_borrow :
  forall a b : (Specs.word (width:=width)),
    word.unsigned a - word.unsigned b =
      word.unsigned (word.sub a b) - 2^width * (if word.ltu a b then 1 else 0).
Proof.
  intros.
  rewrite word.unsigned_ltu.
  destr (Z.ltb (word.unsigned a) (word.unsigned b)); ZnWords.
Qed.

Lemma full_sub_ok : program_logic_goal_for_function! br_full_sub.
Proof.
  repeat straightline.
  rewrite ltu_as_borrow.
  assert (subtrahends_comm: forall m n o, m - n - o = m - o - n) by lia.
  rewrite subtrahends_comm. clear subtrahends_comm.
  rewrite ltu_as_borrow.
  repeat
    (match goal with
     | X := _ |- _  => subst X end).
  destruct (word.ltu x y);
    destruct (word.ltu (word.sub x y) borrow); ZnWords.
Qed.


Lemma ctime_ltu_ok : program_logic_goal_for_function! ctime_ltu.
Proof.
  cbv [spec_of_ctime_ltu].
  repeat straightline.
  straightline_call.
  { ZnWords. }
  repeat straightline.
  straightline_call.
  { trivial. }
  repeat straightline.
  case (word.ltu_spec (width:=width)); split; ZnWords.
Qed.

Lemma bytearray_load_of_sep addr (addr' : word) n (values : list byte) R m
  (Hsep : (sep (bytearray addr values) R m))
  (Haddr : addr' = (word.add addr (word.of_Z (Z.of_nat n))))
  (Hlength : (n < length values)) :
  Memory.load (mem:=mem) access_size.one m addr' =
  Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n))).
Proof.
  rewrite nth_default_eq.
  rewrite <-(firstn_nth_skipn _ n values Byte.x00) in Hsep by lia.
  do 2 seprewrite_in @bytearray_append Hsep.
  seprewrite_in @array_cons Hsep.
  seprewrite_in @array_nil Hsep.
  rewrite length_firstn, min_l, <-Haddr in Hsep by lia.
  eapply load_one_of_sep.
  ecancel_assumption.
Qed.

(* TODO make global/ export in the right place? or fix in specs, i think the one i declared there may be broken.*)
Add Ring wring : (Properties.word.ring_theory (width := width))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (width := width)),
       constants [Properties.word_cst]).


Lemma bytearray_load_of_sep' (addr addr': word) (values : list byte) R m :
  (sep (bytearray addr values) R m) ->
  let offset := word.unsigned (word.sub addr' addr) in
    (let n := Z.to_nat offset in (n < length values) ->
    Memory.load (mem:=mem) access_size.one m addr' =
    Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n)))).
Proof.
  intros.
  eapply bytearray_load_of_sep; eauto.
  subst offset n.
  rewrite Z2Nat.id by apply word.unsigned_range.
  rewrite word.of_Z_unsigned.
  ring.
Qed.

Lemma extract_limb_at_bit_zify a b i :
  0 <= a < 2^8 ->
  0 <= b < 2^8 ->
  word.unsigned (word.and
    (word.sru (word.or (word.of_Z a) (word.slu (word.of_Z b) (word.of_Z 8))) (word.and i (word.of_Z 7)))
    (word.sub (word.slu (word.of_Z 1) (word.of_Z w)) (word.of_Z 1))) =
  Z.land ((Z.shiftr (Z.lor a (Z.shiftl b 8)) (Z.land (word.unsigned (width:=width) i) (Z.ones 3)))) (Z.ones w).
Proof.
  intros. pose proof Naive.word64_ok.
  assert ((word.wrap (Z.shiftl 1 5) - 1) = Z.ones 5) as H5 by (cbn; trivial).
  repeat rewrite ?word.unsigned_sru_nowrap, ?word.unsigned_and_nowrap, ?word.unsigned_of_Z_nowrap,
    ?word.unsigned_or_nowrap, ?word.unsigned_slu, ?word.unsigned_sub_nowrap, ?H5;
      try (cbn; ZnWords).
  2: change (7) with (Z.ones 3); rewrite Z.land_ones by lia; ZnWords.
  repeat f_equal; try ZnWords.
Qed.


Lemma bytelist_extract_two num i b1 b2:
  let idx := i / 8  in
  b1 = (nth_default Byte.x00 num (Z.to_nat idx)) ->
  b2 = (nth_default Byte.x00 num (S (Z.to_nat (idx)))) ->
  0 <= i < length num * 8 ->
  Z.land ((Z.shiftr (Z.lor (byte.unsigned b1) (Z.shiftl (byte.unsigned b2) 8)) (Z.land i (Z.ones 3)))) (Z.ones w) =
  (LittleEndianList.le_combine num / 2 ^ i) mod 2 ^ w.
Proof.
  intros ? Hb1 Hb2. intros.  pose proof Naive.word64_ok.

  rewrite (Z.land_ones _ 3) by lia.
  replace (i mod 2^3) with (i - idx*8) by ZnWords.

  replace (LittleEndianList.le_combine num) with
      (LittleEndianList.le_combine
        ((firstn (Z.to_nat (idx)) num) ++ [b1] ++ [b2] ++ (skipn (S (S (Z.to_nat (idx)))) num)));cycle 1.
  { rewrite Hb1, Hb2, !nth_default_eq, app_assoc.
    rewrite firstn_nth by ZnWords.
    destruct (Nat.eq_dec (S (Z.to_nat idx)) ((length num))) as [Hlength|?].
    { rewrite <- (le_combine_snoc_0 num).
      f_equal.
      rewrite List.skipn_all, nth_overflow by lia.
      rewrite Hlength, firstn_all, app_nil_r.
      reflexivity. }
    { f_equal. rewrite firstn_nth_skipn by ZnWords. reflexivity. }}
  repeat rewrite LittleEndianList.le_combine_app.
  rewrite <-(byte.wrap_unsigned b1), <-(byte.wrap_unsigned b2); cbv [byte.wrap].

  rewrite le_combine_firstn, ?le_combine_1.
  rewrite !length_cons, !length_nil, firstn_length_le, Z2Nat.id by ZnWords.

  rewrite <-(byte.wrap_unsigned b1), <-(byte.wrap_unsigned b2); cbv [byte.wrap].

  apply Z.bits_inj'; intros.
  repeat rewrite
    <-?Z.shiftr_div_pow2, ?Z.testbit_mod_pow2,
    ?bitblast.Z.shiftr_spec', ?bitblast.Z.shiftl_spec', ?Z.land_spec, ?Z.lor_spec,
    ?Z.testbit_mod_pow2, ?Z.testbit_ones_nonneg
    by (lia || ZnWords).

  repeat (trivial; case Z.ltb_spec; intros; try lia;
    repeat rewrite
      ?Z.add_sub_assoc,
      ?Bool.andb_true_r, ?Bool.andb_true_l,
      ?Bool.andb_false_r, ?Bool.andb_false_l,
      ?Bool.orb_true_r, ?Bool.orb_true_l,
      ?Bool.orb_false_r, ?Bool.orb_false_l;
    repeat match goal with |- context [Z.testbit ?a ?b] => rewrite (Z.testbit_neg_r a b) by ZnWords end).
Qed.

Lemma extract_limb_at_bit_ok : program_logic_goal_for_function! extract_limb_at_bit.
Proof.
  cbv [spec_of_extract_limb_at_bit].
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  (* First byte load. *)
  eexists _.
  split. {
    eapply bytearray_load_of_sep'; eauto.
    ZnWords. }
  repeat straightline.
  (* Second byte load. *)
  eexists _.
  split.
  { repeat straightline. }
  split; intro cond; repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  { eexists _.
    split.
    { eapply bytearray_load_of_sep'; eauto.
      revert cond.
      case (word.ltu_spec (width:=width)); intros; ZnWords. }
    repeat straightline.
    subst r t s v b.
    revert cond; case (word.ltu_spec (width:=width)); intros; [|ZnWords].

    rewrite extract_limb_at_bit_zify by apply byte.unsigned_range.

    erewrite bytelist_extract_two; [reflexivity | | | ZnWords ].
    all: repeat f_equal; ZnWords.
  }
  subst r t s b.
  revert cond; case (word.ltu_spec (width:=width)); intros cond ?; [ZnWords|].

  rewrite extract_limb_at_bit_zify by (try apply byte.unsigned_range; lia).

  replace 0 with (byte.unsigned Byte.x00).
  erewrite bytelist_extract_two; [reflexivity | | | ZnWords ].
  { repeat f_equal; try ZnWords. }

  rewrite nth_default_eq, nth_overflow.
  { reflexivity. }
  ZnWords.
Qed.

Lemma decompose_to_limbs_ok : program_logic_goal_for_function! decompose_to_limbs.
Proof.
  cbv [spec_of_decompose_to_limbs].
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                   HList.polymorphic_list.nil))
    (* program variables *) (["p_output";"p_input";"total_bits";"i"] : list String.string))
    (fun v output R t m p_output p_input total_bits_ i => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned i /\
      total_bits_ = total_bits /\ (* input = inside loop *)
      m =* bytearray p_output output * bytearray p_input input * R /\
      8 * (length input - 1) < total_bits <= 8 * length input /\
      w * (length output - 1) < total_bits - i <= w * length output /\
      le_combine input < 2^total_bits /\
      total_bits + w <= $(-1))
    (fun            T M P_OUTPUT P_INPUT TOTAL_BITS I => (* postcondition *)
      exists OUTPUT,
      M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
      length output = length OUTPUT /\
      T = t /\
      p_input = P_INPUT /\
      total_bits = TOTAL_BITS /\ (* inside loop = output *)
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
      le_combine input / 2^i = positional_bytes (2^w) OUTPUT))
    (fun n m => m < n <= total_bits + w) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.gt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; ZnWords. }
  { intros v output_ R_ t_ m_ p_output_ p_input_ total_bits_ i_.
    repeat straightline; subst br.
    { destruct (word.ltu_spec i_ total_bits);
      rewrite word.unsigned_of_Z_nowrap in * by ZnWords; try lia.
      straightline_call. (* call extract_limb_at_bit *)
      { ssplit; try (eexists _; ecancel_assumption); trivial; ZnWords. }
      repeat straightline.
      destruct output_ as [| out0 output_rest].
      { (* Empty list case. *)
        rewrite List.length_nil in *.
        lia. }
      cbn [bytearray] in * |-.
      repeat straightline.
      eexists _, _, _.
      repeat straightline.
      { cbn [length] in *.
        ssplit; try ecancel_assumption; trivial; ZnWords. }
      split.
      { (* loop test *)
        ZnWords. }
      repeat straightline.
      eexists (_ :: _).
      ssplit; try (cbn [bytearray]; ecancel_assumption); trivial.
      { rewrite !length_cons. ZnWords. }
      { (* Forall bound on output. *)
        apply Forall_cons.
        { match goal with H: ?x = _ |- context [?x] => rewrite H end.
          rewrite byte.unsigned_of_Z.
          cbv [byte.wrap].
          rewrite Z.mod_small; ZnWords. }
        assumption. }
      rewrite positional_bytes_cons.
      match goal with H: _ = ?x |- context [?x] => rewrite <-H end.
      match goal with H: ?x = _ |- context [?x] => rewrite H end.
      subst i.
      rewrite word.unsigned_add_nowrap, word.unsigned_of_Z_nowrap by ZnWords.
      rewrite byte.unsigned_of_Z.
      cbv [byte.wrap].
      rewrite Z.mod_small, Z.pow_add_r, <-Z.div_div, Z.add_comm, <-Z.div_mod by ZnWords.
      reflexivity. }
    (* base case *)
    eexists output_.
    destruct (word.ltu_spec i_ total_bits);
    rewrite word.unsigned_of_Z_nowrap in * by ZnWords; try lia.
    ssplit; try ecancel_assumption; trivial;
    assert (length output_ = 0%nat) by ZnWords;
    rewrite length_zero_iff_nil in *;
    subst output_.
    { apply Forall_nil. }
    cbn [positional_bytes positional map fold_right].
    assert (2 ^ word.unsigned total_bits <= 2 ^ word.unsigned i_) by (apply Z.pow_le_mono_r; ZnWords).
    assert (le_combine input < 2 ^ word.unsigned i_) by ZnWords.
    apply Z.div_small.
    split; [apply le_combine_bound | trivial]. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
  subst i.
  match goal with H: _ = ?x |- context [?x] => rewrite <-H end.
  rewrite word.unsigned_of_Z_0, Z.pow_0_r, Z.div_1_r.
  reflexivity.
Qed.

Lemma signed_recode_carry_ok : program_logic_goal_for_function! signed_recode_carry.
Proof.
  cbv [spec_of_signed_recode_carry].
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                   HList.polymorphic_list.nil))
    (* program variables *) (["p_limbs";"ci";"n"] : list String.string))
    (fun v limbs R t m p_limbs ci n => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned n /\
      m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\ 0 <= ci <= 1)
    (fun           T M P_LIMBS (CO : word) N => T = t /\ (* postcondition *)
      exists LIMBS,
      M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
      positional_signed_bytes (2^w) LIMBS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) limbs /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS /\ 0 <= CO <= 1))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.lt_wf. }
  { repeat straightline.
    ssplit; try ecancel_assumption; trivial. }
  { clear dependent limbs.
    intros v limbs R_ t_ m_ p_limbs_ ci_ n_.
    repeat straightline.
    { (* Take the first element from the limbs list. *)
      destruct limbs as [| w0 limbs_rest].
      { rewrite List.length_nil in *; lia. }
      { cbn [array] in * |-.
        repeat straightline.
        (* call ctime_lt *)
        straightline_call.
        { match goal with H: Forall _ _ |- _ => apply Forall_inv in H end.
          ZnWords. }
        repeat straightline.
        (* call br_cmov *)
        straightline_call; trivial.
        repeat straightline.
        exists limbs_rest; eexists _; exists (v - 1).
        repeat straightline.
        { ssplit.
          { ZnWords. }
          { ecancel_assumption. }
          { subst n.
            rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_1;
            rewrite List.length_cons in *;
            try ZnWords. }
          { match goal with H: Forall _ _ |- _ => inversion H end; trivial. }
          all: subst x; case (word.ltu_spec (width:=width)); ZnWords. }
        { split.
          { lia. }
          { repeat straightline.
            eexists (_ :: _).
            ssplit.
            { cbn [array].
              ecancel_assumption. }
            { rewrite length_cons; ZnWords. }
            {
              match goal with H: context[positional_signed_bytes] |- _ => revert H end.
              unfold positional_signed_bytes, positional_bytes.
              rewrite Zeq_plus_swap.
              cbn [map positional fold_right]. intros ->.
              rewrite Z.mul_sub_distr_l.

              subst n.
              rewrite <- !Z.add_assoc, <- Z.sub_sub_distr, Z.add_sub_assoc, <- Z.sub_0_r.
              f_equal.
              2:{ rewrite word.unsigned_sub_nowrap, word.unsigned_of_Z_1, Z.mul_assoc, <- Z.pow_add_r by ZnWords.
                rewrite Zeq_minus; [trivial|].
                do 2 f_equal. lia. }

              cbv [x0 x v0 byte.signed].
              match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
              case (word.ltu_spec (width:=width)); case Z.eqb_spec; [ZnWords | | | ZnWords];
              repeat rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_0, ?word.unsigned_sub_nowrap,
                ?word.unsigned_sub, ?word.unsigned_add_nowrap, ?byte.unsigned_of_Z, ?byte.swrap_wrap by ZnWords; intros.
              { rewrite word.byte_swrap_word_wrap by ZnWords.
                cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
              { cbv [byte.swrap]. rewrite Z.mod_small; ZnWords. }
            }
            { constructor.
              { cbv [x0 x v0].
                match goal with | H: Forall _ (_ :: _) |- _ => apply Forall_inv in H end.
                case (word.ltu_spec (width:=width)); case Z.eqb_spec;
                repeat rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_0, ?word.unsigned_sub_nowrap,
                ?word.unsigned_add_nowrap, ?word.unsigned_sub, ?word.unsigned_of_Z_nowrap by ZnWords;
                intros; try ZnWords; unfold byte.signed; rewrite byte.unsigned_of_Z, byte.swrap_wrap;
                rewrite ?word.byte_swrap_word_wrap by ZnWords;
                cbv [byte.swrap]; rewrite Z.mod_small; try ZnWords. }
                assumption. }
            all: lia. } } } }
    { assert (length limbs = 0%nat) by ZnWords.
      rewrite length_zero_iff_nil in *.
      subst limbs.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      cbn [positional_signed_bytes positional_bytes positional List.map fold_right].
      match goal with H: ?x = _ |- context [?x] => rewrite H end.
      lia. }
  }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma positional_bound (l : list Z) L U :
  let n := length l in
  Forall (fun b => (L <= 2*b <= U)) l ->
  positional (2^w) (List.repeat L n) <= 2 * (positional (2^w) l) <= positional (2^w) (List.repeat U n).
Proof.
  induction 1.
  { subst n.
    rewrite length_nil, ?positional_nil.
    lia. }
  { subst n.
    rewrite length_cons, positional_cons.
    cbn [repeat].
    rewrite ?positional_cons.
    cbv [id] in *.
    lia. }
Qed.

Lemma signed_recode_ok : program_logic_goal_for_function! signed_recode.
Proof.
  cbv [spec_of_signed_recode].
  repeat straightline.
  straightline_call. (* call signed_recode_carry *)
  { ssplit; try ecancel_assumption; trivial; ZnWords. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
  assert (word.unsigned x <> 1).
  { intros Hx.
    rewrite word.unsigned_of_Z_0, Z.add_0_l, Hx, Z.mul_1_r in *.
    epose proof positional_bound (map byte.signed x0) (- 2 ^ w + 2) (2 ^ w) ltac:(apply Forall_map; assumption).
    rewrite length_map in *.
    progress fold (positional_signed_bytes (2 ^ w) x0) in *.
    assert (2*positional_signed_bytes (2 ^ w) x0 < -2^(w*n)) by lia.
    assert (positional (2 ^ w) (repeat (- 2 ^ w + 2) (length x0)) < -2 ^ (w * n)) by lia.
    match goal with H: _ = word.unsigned n |- _ => rewrite <-H in * end.
    rewrite Nat2Z.id in *.
    lia. }
  ZnWords.
Qed.

End WithParameters.
