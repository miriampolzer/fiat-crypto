Require Import coqutil.Datatypes.List Coq.Lists.List.
Require Import Bedrock.P256.Specs.
Require Import coqutil.Tactics.Tactics.

Import Specs.point
bedrock2.Syntax
bedrock2.NotationsCustomEntry
micromega.Lia
ProgramLogic
WeakestPrecondition
ProgramLogic.Coercions
SeparationLogic
letexists
BasicC64Semantics
ListIndexNotations
SepAutoArray
OfListWord
ListNotations
BinInt
PrimeFieldTheorems
symmetry
Arith
Array
memcpy.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
(at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

#[local] Notation sizeof_point := 96%nat.

Definition p256_precompute_table := func! (p_table, p_P) {
  p256_set_zero(p_table);
  br_memcpy(p_table + $sizeof_point, p_P, $sizeof_point);

  i = $2;
  while (i < $17) {
    if (i & $1) {
      p256_point_add_nz_nz_neq(
        p_table + (point_size * i),
        p_table + (point_size * (i - $1)),
        p_P
      )
    } else {
      p256_point_double(
        p_table + (point_size * i),
        p_table + (point_size * (i<<$1))
      )
    };
    i = i + $1
  }
}.

(* todo move to specs? *)
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Module W.
  Import Crypto.Bedrock.P256.Specs(a, b).

  Definition a := a.
  Definition b := b.
  Definition mul := ScalarMult.scalarmult_ref
    (G := W.point
    (a := a)
    (b := b)
    )
    (add := W.add)
    (zero := W.zero)
    (opp := W.opp).

  (* Creates 0..(n-1)*A *)
  Fixpoint multiples (n : nat) (P : W.point) : list W.point :=
    match n with
      | 0%nat => []
      | S n => (multiples n P) ++ [(mul n P)]
    end.

  Lemma length_multiples (n : nat) (A : W.point) :
    Logic.eq (List.length (multiples n A)) n.
  Proof.
    induction n.
    - cbv [multiples length]. reflexivity.
    - unfold multiples. fold multiples. rewrite length_app.
      rewrite IHn. simpl. Lia.lia.
  Qed.


  Lemma multiples_correct (n : nat) (A : W.point) :
    forall k : nat, k < n ->
    (List.nth_error (multiples n A) k) = Some (mul k A).
  Proof.
    destruct n; intros; try lia.
    induction n.
    - intros. assert (Logic.eq k 0%nat) by Lia.lia. subst. simpl. reflexivity.
    - intros. unfold multiples. fold multiples. destruct (Nat.eq_dec k (S n)).
      + subst. erewrite <- length_multiples at 1.
        admit.
      + admit. (*erewrite app_nth1.
        2: { rewrite length_app. erewrite length_multiples. simpl. Lia.lia. }
        apply IHn. Lia.lia.*)
  Admitted.
End W.

Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
(* todo implement *)
Local Instance spec_of_p256_set_zero : spec_of "p256_set_zero" :=
  fnspec! "p256_set_zero" p_P / P R,
  { requires t m :=
    m =* P$@p_P * R;
    ensures T M := exists (Q : point),
    M =* Q$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.zero) /\
    T = t
  }.

Notation pointarray := (array (fun p (Q : point) => Q$@p) (word.of_Z sizeof_point)).
(*or use bytes arrays?*)

#[export] Instance spec_of_p256_precompute_table : spec_of "p256_precompute_table" :=
  fnspec! "p256_precompute_table" p_table p_P / out (P : point) R,
  { requires t m := m =* out$@p_table * P$@p_P * R /\ length out = (sizeof_point * 17)%nat;
    ensures t' m := t' = t /\ exists out_multiples,
      map Jacobian.to_affine out_multiples = W.multiples 17 (Jacobian.to_affine P) /\
      m =* pointarray p_table out_multiples * P$@p_P * R
  }%sep.


Lemma split_list p l offset :
    (length l >= offset)%nat ->
    (length l <= 2^64) ->
    Lift1Prop.iff1
    (l $@ p)
    ((skipn offset l)$@(p.+offset) * (firstn offset l)$@p)%sep.
  Proof.
    intros.
    rewrite <- (firstn_skipn offset l) at 1. (*todo ssreflect rewrite?*)
    rewrite (map.of_list_word_at_app_n _ _ _ offset); try (rewrite ?length_firstn, ?length_skipn; lia).
    { unshelve (epose proof (map.adjacent_arrays_disjoint_n p (firstn offset l) (skipn offset l) offset _ _) as HD);
        try (rewrite ?length_firstn, ?length_skipn; lia).
        exact (sep_eq_putmany _ _ HD).
    }
  Qed.

  Require Import bedrock2.bottom_up_simpl.
  Require Import bedrock2.ZnWords.
Local Ltac fancy_lia := try (rewrite ?length_skipn, ?length_firstn, ?length_point in *; try pose proof Naive.word64_ok; ZnWords; better_lia).

Lemma p256_precompute_table_ok : program_logic_goal_for_function! p256_precompute_table.
Proof.
  repeat straightline.

  seprewrite_in (split_list p_table out sizeof_point) H3; try fancy_lia.
  bottom_up_simpl_in_hyp H3.
  remember (skipn 96 out) as out1. (* if i do not put this, ecancel will unfold the skipn*)
  assert (length out1 = (96 * 16)%nat). { subst out1; fancy_lia. }

  straightline_call.
  {
    ecancel_assumption.
  }

  repeat straightline.

  seprewrite_in (split_list (p_table.+96) out1 sizeof_point) H7; try fancy_lia.
  bottom_up_simpl_in_hyp H7.
  remember (skipn 96 out1) as out2. (* if i do not put this, ecancel will unfold the skipn*)
  assert (length out2 = (96 * 15)%nat). { subst out2. subst out1. fancy_lia. }

  straightline_call; ssplit.
  {
    ecancel_assumption.
  }
  all: try fancy_lia.

  repeat straightline.

  Local Open Scope sep_scope.
  refine ((Loops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
    (HList.polymorphic_list.nil)))
      (["p_table";"p_P";"i"]))
      (fun (j:nat) todo partial_multiples t m p_table' p_P' i => PrimitivePair.pair.mk (
        m =* (todo$@(p_table.+(Z.mul i sizeof_point)) *
              pointarray p_table partial_multiples * P$@p_P * R)%sep /\
              2 <= i <= 16 /\
              j = (17%nat - (Z.to_nat (word.unsigned i)))%nat/\
              length todo = (j * sizeof_point)%nat /\
        map Jacobian.to_affine partial_multiples =
            W.multiples (Z.to_nat (word.unsigned i)) (Jacobian.to_affine P)
          )
      (fun T M (P_TABLE P_P I : word) => t = T /\
                      exists multiples : list point,
                        M =* pointarray p_table multiples * P$@p_P * R /\
                        map Jacobian.to_affine multiples =
                          (W.multiples 17%nat) (Jacobian.to_affine P)
                        ))
      lt
      _ _ _ _ _ _ _); Loops.loop_simpl.
      { cbv [Loops.enforce]; cbn. split; exact eq_refl. }
      { eapply Wf_nat.lt_wf. }
      { repeat straightline. ssplit.

        { subst i. instantiate (1:= ([x; P])).
          cbv [array]. bottom_up_simpl_in_goal. ecancel_assumption. }

        {  subst i. fancy_lia.
        }
        {  subst i. fancy_lia.
        }
        {
          bottom_up_simpl_in_goal. exact eq_refl.
        }
        {
          fancy_lia.
        }

        { subst i. bottom_up_simpl_in_goal. cbv [W.multiples map].
          admit. (* match up zero and p. should be easy.*) }
      }
      { intros ?j ?todo ?partial_multiples ?t ?m ?p_table ?p_P ?i.
        repeat straightline.

        {
        (* split it out the first element of todo, which is the one we will fill *)
        seprewrite_in (split_list (p_table.+word.unsigned i0 * Z.of_nat 96) todo sizeof_point) H9;
          try (subst j; fancy_lia).
        bottom_up_simpl_in_hyp H9.
        remember (skipn 96 todo) as next_todo.
        assert (length next_todo = ((17 - (Z.to_nat (word.unsigned i0) + 1)) * 96)%nat).
        { subst next_todo. fancy_lia. }

        (* todo continue here, take apart the if clause and do them separately. *)
