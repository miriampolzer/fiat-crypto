Require Import ZArith Coq.Lists.List.
Local Open Scope Z_scope.
Local Open Scope list_scope.
From coqutil Require Import Byte Word.Naive Word.Interface Word.LittleEndianList.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia.
From coqutil Require Import Tactics.Tactics Word.Properties Datatypes.List.
Import List.ListNotations.

Open Scope nat_scope.
Open Scope Z_scope.
Coercion Z.of_nat: nat >-> Z.

#[local] Notation N := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.
#[local] Notation w := 5.
(* TODO generalize, i think with some nice distance property lia may actually be able to solve this.*)

#[local] Notation signed_limb_bounded k := (-2^w + 2 <= 2*k <= 2^w) (only parsing).

(* little endian, positional 10 [2;1] = 12.*)
Definition positional B : list Z -> Z :=
  fold_right (fun a s => a + B*s) 0.

  Lemma positional_cons B h t :
  positional B (h :: t) = h + B*(positional B t).
Proof.
  constructor.
Qed.

Lemma positional_app B t1 t2 :
  positional B (t1 ++ t2) =
    (positional B t1) + (B^(length t1) * (positional B t2)).
Proof.
  generalize dependent t2.
  induction t1.
  - intros. rewrite app_nil_l. rewrite length_nil.
    replace (positional B []) with 0.
    { lia. } cbv. reflexivity.
  - intros. rewrite <- app_comm_cons.
    rewrite !positional_cons. rewrite IHt1.
    rewrite length_cons.
    replace (Z.of_nat (S (length t1))) with (Z.of_nat (length t1) + 1) by lia.
    rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma signed_limb_ineq_shifted_postivie_num (num : list Z) (limb : Z):
  signed_limb_bounded limb ->
  Forall (fun x => signed_limb_bounded x) num ->
  0 <= 2^w * positional (2^w) num < N -> (* Pretty sure this will hold for any curve and w fow which N + max_limb works *)
  ~ (positional (2^w) num = 0 /\ limb = 0) ->
  (2^w * positional (2^w) num) mod N <> limb mod N.
Proof.
  intros.
  rewrite Z.cong_iff_0.
  rewrite Z.mod_divide by lia.
  intros [x].
  rewrite ?positional_cons in *.
  lia.
Qed.

Lemma positive_shifted_out_of_limb_range :
  forall k, k > 0 -> 2 * 2^w * k > 2^w.
Proof.
    intros.
    nia.
Qed.

Lemma negative_shifted_out_of_limb_range :
  forall k, k < 0 -> 2 * 2^w * k < -2^w.
Proof.
  intros.
  nia.
Qed.

Lemma last_cons {T}: forall (x y : T) xs, last (x :: y :: xs) = last (y :: xs).
Proof.
  cbv [last]. reflexivity.
Qed.

Lemma last_rev_hd {T} : forall (l : list T) (d : T), last (rev l) d = hd d l.
Proof.
  destruct l.
  - reflexivity.
  - intros. cbn. rewrite last_last. reflexivity.
Qed.

Lemma highest_negative_implies_all_negative: forall (num: list Z),
  0 > (last num 0) ->
  Forall (fun b => signed_limb_bounded b) num ->
  positional (2^w) num < 0.
Proof.
  induction num.
  - simpl; intros; lia.
  - destruct num.
    + simpl; intros; lia.
    + intros. rewrite last_cons in H.
      assert (Hf: Forall (fun b : Z => signed_limb_bounded b) (z :: num)).
      { eapply Forall_inv_tail; eassumption. }
      apply IHnum in H; [ | assumption ].
      rewrite positional_cons.
      apply negative_shifted_out_of_limb_range in H.
      apply Forall_inv in H0.
      better_lia.
Qed.

Open Scope list_scope.


Fixpoint remove_prefix_zeroes(num : list Z) :=
  match num with
   | 0 :: num => remove_prefix_zeroes num
   | num => num
  end.

Lemma remove_prefix_zeroes_split (num : list Z) :
  exists n : nat, num = repeat 0 n ++ remove_prefix_zeroes num.
Proof.
  induction num as [|h t IH].
  - exists 0%nat. reflexivity.
  - destruct (Z.eq_dec h 0) as [Heq | Hneq].
    + subst. simpl. destruct IH as [n Hn].
      exists (S n). simpl. rewrite <- Hn. reflexivity.
    + exists 0%nat. destruct h; try reflexivity.
      exfalso. apply Hneq. reflexivity.
Qed.

(* TODO use some existing function? there is drop_while but it has no helper lemmas either. *)
Definition remove_trailing_zeroes (num : list Z) := rev (remove_prefix_zeroes (rev num)).

Lemma remove_trailing_zeroes_split (num : list Z) :
  exists n : nat, num = (remove_trailing_zeroes num) ++ repeat 0 n.
Proof.
  unfold remove_trailing_zeroes.
  pose proof (remove_prefix_zeroes_split (rev num)) as H.
  destruct H as [n H].
  exists n.
  apply (f_equal (@rev Z)) in H.
  rewrite rev_app_distr, rev_involutive, rev_repeat in H. apply H.
Qed.

Lemma positional_rep_zero x :
  positional (2^w) (repeat 0 x) = 0.
Proof.
  induction x.
  - reflexivity.
  - cbn [repeat]. rewrite positional_cons.
    rewrite IHx. reflexivity.
Qed.

Lemma positional_zeroes (num: list Z) x :
  positional (2 ^ w) (num ++ repeat 0 x) = positional (2^w) num.
Proof.
  induction num.
  - apply positional_rep_zero.
  - rewrite <- app_comm_cons. rewrite !positional_cons. rewrite IHnum. reflexivity.
Qed.

Lemma trailing_zeroes_id (num : list Z) :
  positional (2^w) (remove_trailing_zeroes num) = positional (2^w) num.
Proof.
  destruct (remove_trailing_zeroes_split num) as [n H].
  rewrite H at 2.
  rewrite positional_zeroes.
  reflexivity.
Qed.

Lemma prefix_zeroes_ok (num : list Z) :
  positional (2^w) num <> 0 ->
  hd 0 (remove_prefix_zeroes num) <> 0.
Proof.
  intros.
  induction num.
  - simpl in *. trivial.
  - destruct (Z.eq_dec a 0) as [Heq | Hneq].
    + subst. simpl. apply IHnum. rewrite positional_cons in H. lia.
    + simpl. destruct a; try lia; cbv [hd]; assumption.
Qed.

Lemma trailing_zeroes_ok (num : list Z) :
   positional (2^w) num <> 0 ->
  last (remove_trailing_zeroes num) 0 <> 0.
Proof.
  intros H.
  unfold remove_trailing_zeroes.
  rewrite last_rev_hd.
  intro H0.
  apply H.
  assert (Hf : Forall (eq 0) (rev num)).
  { clear H. induction (rev num) as [|a l IHl]; simpl in *.
    - constructor.
    - destruct (Z.eq_dec a 0) as [Heq|Hneq].
      + subst. constructor; [reflexivity|]. apply IHl. assumption.
      + destruct a; try (elim Hneq; reflexivity); simpl in H0; inversion H0.
  }
  apply Forall_rev in Hf.
  rewrite rev_involutive in Hf.
  apply Forall_eq_repeat in Hf.
  rewrite Hf.
  apply positional_rep_zero.
Qed.

Lemma skipn_repeat {T} x n (v:T): skipn n (repeat v x) = (repeat v (x - n)%nat).
Proof.
  generalize dependent x.
  induction n.
  - intros. simpl. rewrite Nat.sub_0_r. reflexivity.
  - intros. destruct x.
    + simpl. reflexivity.
    + simpl. rewrite IHn. reflexivity.
Qed.

(* If a number is positive, then the last nonzero limb is positive *)
Lemma positional_positive_last_positive: forall (num : list Z),
  Forall (fun b => signed_limb_bounded b) num ->
  0 < positional (2^w) num ->
  0 < positional (2^w) [(last (remove_trailing_zeroes num) 0)].
Proof.
  intros.
  apply Znot_ge_lt. intros P.
  pose proof (highest_negative_implies_all_negative (remove_trailing_zeroes num)).
  cbv [positional fold_right map] in P.
  rewrite Z.mul_0_r, Z.add_0_r in P.
  pose proof (trailing_zeroes_ok num).
  assert (Hpos : positional (2^w) num <> 0) by lia.
  apply H2 in Hpos.
  assert (Hlast_neg : 0 > last (remove_trailing_zeroes num) 0) by lia.
  assert (Hf : Forall (fun b => signed_limb_bounded b) (remove_trailing_zeroes num)).
  { unfold remove_trailing_zeroes.
    apply Forall_rev.
    pose proof (remove_prefix_zeroes_split (rev num)) as [n Hrev].
    assert (Hfrev : Forall (fun b => signed_limb_bounded b) (rev num)).
    { apply Forall_rev. assumption. }
    rewrite Hrev in Hfrev.
    apply Forall_app in Hfrev.
    destruct Hfrev; assumption.
  }
  apply H1 in Hlast_neg; [ | assumption ].
  rewrite trailing_zeroes_id in Hlast_neg.
  lia.
Qed.

Lemma skipn_last: forall l, l <> [] -> (skipn (length l - 0 - 1) l) =  [(last l 0)].
Proof.
  intros l H. induction l; [congruence|].
  destruct l; [reflexivity|].
  simpl in *. assert (Heq: (length l - 0)%nat = length l) by lia.
  rewrite Heq in IHl. apply IHl; congruence.
Qed.

(* If the last byte is positive, then every non-empty suffix of the number is positive. *)
(* This will help prove that we always stay below the modulo, because we can then
show that the number never grows beyond it and negative numbers are irrelevant. *)
Lemma last_positive_all_suffix_positive: forall (num : list Z),
  Forall (fun b => signed_limb_bounded b) num ->
  0 < positional (2^w) [(last num 0)] ->
  forall i : nat,
  i < (length num) ->
  0 < positional (2^w) (skipn (length num - i - 1) num).
Proof.
  induction i.
    - intros Hlen. rewrite skipn_last.
    + assumption.
    + destruct num; [ simpl in Hlen; lia | congruence ].
  - intros.
    assert (Hnth : nth_error num (length num - i - 2) = Some (nth (length num - i - 2) num 0)).
    { apply nth_error_nth'. lia. }
    apply firstn_skipn_middle in Hnth.
    rewrite <- Hnth.
    repeat rewrite ?firstn_length, ?length_app, ?skipn_length, ?length_cons.
    assert (Hlen_math : (Init.Nat.min (length num - i - 2) (length num) + S (length num - S (length num - i - 2)) - S i - 1 = length num - i - 2)%nat) by lia.
    rewrite Hlen_math.
    rewrite skipn_app. rewrite skipn_all; [ | rewrite firstn_length; lia ].
    rewrite firstn_length.
    replace (length num - i - 2 - Init.Nat.min (length num - i - 2) (length num))%nat with 0%nat by lia.
    rewrite skipn_0, app_nil_l.
    replace (S (length num - i - 2))%nat with (length num - i - 1)%nat by lia.
    rewrite positional_cons.
    assert (Hi_bound : i < length num) by lia.
    specialize (IHi Hi_bound).
    assert (Hbound: signed_limb_bounded (nth (length num - i - 2) num 0)).
    { apply (Forall_In H). apply nth_In. lia. }
    lia.
Qed.

Lemma num_positive_suffix_non_negative: forall (num : list Z),
  Forall (fun b => signed_limb_bounded b) num ->
  0 < positional (2^w) num ->
  forall i : nat, i <= length num ->
  0 <= positional (2^w) (skipn i num).
Proof.
  intros.
  pose proof (remove_trailing_zeroes_split num).
  destruct H2.

  destruct (Z.lt_decidable (i) (length (remove_trailing_zeroes num))).
  (* case 1: something of num stays, that means the whole thing is positive. *)
  {
    assert (Hforall_rtz : Forall (fun b : Z => - 2 ^ 5 + 2 <= 2 * b <= 2 ^ 5) (remove_trailing_zeroes num)).
    { rewrite H2 in H. apply Forall_app in H. destruct H; assumption. }
    assert (Hpos_last : 0 < positional (2 ^ 5) [last (remove_trailing_zeroes num) 0]).
    { apply positional_positive_last_positive; assumption. }
    pose proof (last_positive_all_suffix_positive (remove_trailing_zeroes num) Hforall_rtz Hpos_last) as H4.
    rewrite H2.
    rewrite skipn_app.
    replace (i - length (remove_trailing_zeroes num))%nat with 0%nat by lia.
    rewrite skipn_0.

    rewrite positional_zeroes.
    replace i with (length (remove_trailing_zeroes num) - (length (remove_trailing_zeroes num) - i - 1) - 1)%nat by lia.
    assert (0 <
positional (2 ^ w)
(ListDef.skipn (length (remove_trailing_zeroes num) - (length (remove_trailing_zeroes num) - i - 1) - 1)
(remove_trailing_zeroes num))).
    {
      apply H4.
      lia.
    }
    lia.
  }
  (* case 2: we skip the whole content, only zeroes left. *)
  {
    rewrite H2.
    rewrite skipn_app.
    rewrite (skipn_all i (remove_trailing_zeroes num)); try lia.
    rewrite app_nil_l.
    rewrite skipn_repeat.
    rewrite positional_rep_zero.
    lia.
  }
Qed.

(* non standard bounds because we can have 2^w inclusive. overshoot a bit to simplify*)
Lemma limb_bounds_num (num : list Z):
  Forall (fun b => signed_limb_bounded b) num ->
  positional (2^5) num < 32^(length num).
Proof.
  intros.
  induction num.
  - simpl. lia.
  - rewrite positional_cons.
    Search Forall cons.
    pose proof H as HC.
    apply Forall_inv in H.
    apply Forall_inv_tail in HC.
    apply IHnum in HC.
    rewrite length_cons.
    replace (Z.of_nat (S (length num))) with (Z.of_nat ((length num))+ 1) by lia.
    assert (a <= 16) by lia.
    replace (32 ^ (Z.of_nat (length num) + 1)) with (32 * 32 ^ (Z.of_nat (length num))).
    + lia.
    + rewrite Z.pow_add_r; try lia.
Qed.

Lemma num_bounded_suffix_bounded: forall (num : list Z),
  length num = 52%nat ->
  Forall (fun b => signed_limb_bounded b) num ->
  positional (2^w) num < N ->
  forall i : nat, 0 < i <= length num ->
  2^w * positional (2^w) (skipn i num) < N.
Proof.
  intros.
  destruct i as [|i].
  { lia. }
  destruct i as [|i].
  { (* original i = 1 *)
    destruct num.
    { cbv. trivial. }
    { cbv [skipn] in *. rewrite positional_cons in H1.
      apply Forall_inv in H0.
      lia. } }
  { (* original i >= 2 *)
    assert (Hskipn : Forall (fun b : Z => - 2 ^ 5 + 2 <= 2 * b <= 2 ^ 5) (skipn (S (S i)) num)).
    { (* TODO this is Forall_skipn, can replace. *)
      rewrite List.Forall_forall.
      intros b' HIn'.
      rewrite List.Forall_forall in H0.
      apply H0.
      rewrite <- (List.firstn_skipn (S (S i)) num).
      apply List.in_or_app. right. assumption. }
    { pose proof (limb_bounds_num (skipn (S (S i)) num) Hskipn) as Hlimb.
      rewrite length_skipn in *.
      rewrite H in *.
      replace (Z.of_nat (52 - S (S i))) with (50 - i) in * by lia.
      assert (Hmax_pow : 2^5 * 32 ^ (50 - i) <= 2^5 * 32^50) by (apply Z.mul_le_mono_nonneg_l; [ lia | apply Z.pow_le_mono_r; lia ]).
      lia. } }
Qed.

(* This should hold, but I doubt lia can prove it for non-constants easily. *)
Lemma positional_mod_ineq_least_bit (num : list Z) (limb : Z) N w:
  (-2^w + 2 <= 2*limb <= 2^w) ->
  N > 2^w ->
  ~ (exists l x, (-2^w + 1 <= l <= 2^(w - 1)) /\ x * 2^w + l = N) -> (* this is equivalen to the bit at w-1 being set*)
  0 < positional (2^w) (limb :: num) < N ->
  (2^w * positional (2^w) num) mod N <> limb mod N.
Proof.
  intros.
  assert (Hw_pos: 2^w >= 2).
  { assert (2 ^ w >= 2 * limb) by lia.
    assert (2 * limb >= - 2 ^ w + 2) by lia.
    destruct (Z.lt_ge_cases w 1).
    - assert (w <= 0) by lia.
      destruct (Z.lt_ge_cases w 0).
      + cbv [Z.pow] in *. nia.
      + replace w with 0 in * by lia. cbv [Z.pow] in *. lia.
    - nia. }
  intro Hneg.
  rewrite Z.cong_iff_0 in Hneg.
  apply Z.mod_divide in Hneg; [ | lia ].
  destruct Hneg as [x Hx].
  rewrite positional_cons in H2.
  assert (Hsplit: 2 ^ w * positional (2 ^ w) num = x * N + limb) by lia.
  rewrite Hsplit in H2.
  assert (HN: N > 0) by lia.
  assert (Hxn: x = 0 \/ x = 1).
  { destruct (Z.lt_ge_cases x 0).
    { nia. }
    { destruct (Z.lt_ge_cases x 2).
      { nia. }
      { nia. } } }
  destruct Hxn as [Hx0 | Hx1].
  - subst x.
    assert (Hlimb0: limb = 0).
    { assert (Hmod: limb mod 2^w = 0).
      { rewrite (Z.mod_divide _ (2^w)) by lia.
        exists (positional (2^w) num).
        lia. }
      assert (Hrange: -2^w < limb < 2^w) by nia.
      apply Z.mod_divide in Hmod; [ | lia ].
      destruct Hmod as [k Hk].
      assert (k = 0) by nia.
      subst k. lia. }
    subst limb.
    lia.
  - subst x.
    apply H1.
    assert (Hw: w >= 1).
    { destruct (Z.lt_ge_cases w 1); [ | lia ].
      destruct (Z.lt_ge_cases w 0).
      + rewrite Z.pow_neg_r in * by lia. nia.
      + replace w with 0 in * by lia. rewrite Z.pow_0_r in *. lia. }
    assert (Hpow_split: 2 ^ w = 2 * 2 ^ (w - 1)).
    { replace w with (w - 1 + 1) at 1 by lia.
      rewrite Z.pow_add_r by lia. lia. }
    exists (-limb), (positional (2^w) num).
    split.
    { split; lia. }
    { lia. }
Qed.

