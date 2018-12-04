Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.

Definition Forallb {A} (P : A -> bool) (ls : list A) : bool
  := List.fold_right andb true (List.map P ls).

Lemma unfold_Forallb {A P} ls
  : @Forallb A P ls
    = match ls with
      | nil => true
      | cons x xs => andb (P x) (Forallb P xs)
      end.
Proof. destruct ls; reflexivity. Qed.

Lemma Forall_Forallb_iff {A} (P : A -> bool) (Q : A -> Prop) (ls : list A)
      (H : forall x, In x ls -> P x = true <-> Q x)
  : Forallb P ls = true <-> Forall Q ls.
Proof.
  induction ls as [|x xs IHxs]; simpl; rewrite unfold_Forallb.
  { intuition. }
  { simpl in *.
    rewrite Bool.andb_true_iff, IHxs
      by (intros; apply H; eauto).
    split; intro H'; inversion H'; subst; constructor; intuition;
      apply H; eauto. }
Qed.

Local Ltac t_Forall2_step :=
  first [ progress intros
        | progress subst
        | progress destruct_head'_and
        | progress destruct_head'_ex
        | progress specialize_by_assumption
        | progress split_iff
        | apply conj
        | progress cbn [List.map List.seq List.repeat List.rev List.firstn List.skipn] in *
        | solve [ eauto ]
        | match goal with
          | [ |- List.Forall2 _ _ _ ] => constructor
          | [ |- List.Forall _ _ ] => constructor
          | [ H : List.Forall2 _ nil (cons _ _) |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) nil |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (cons _ _) ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x (cons _ _) |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ nil ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x nil |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall _ (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (List.app _ _) _ |- _ ] => apply Forall2_app_inv_l in H
          | [ H : List.Forall2 _ _ (List.app _ _) |- _ ] => apply Forall2_app_inv_r in H
          | [ H : nil = _ ++ _ |- _ ] => symmetry in H
          | [ H : _ ++ _ = nil |- _ ] => apply app_eq_nil in H
          | [ H : cons _ _ = nil |- _ ] => inversion H
          | [ H : nil = cons _ _ |- _ ] => inversion H
          | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
          | [ H : _ ++ _ :: nil = _ ++ _ :: nil |- _ ] => apply app_inj_tail in H
          | [ |- List.Forall2 _ (_ ++ _ :: nil) (_ ++ _ :: nil) ] => apply Forall2_app
          end ].
Local Ltac t_Forall2 := repeat t_Forall2_step.

Lemma Forall2_map_l_iff {A A' B R f ls1 ls2}
  : @List.Forall2 A' B R (List.map f ls1) ls2
    <-> @List.Forall2 A B (fun x y => R (f x) y) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_map_r_iff {A B B' R f ls1 ls2}
  : @List.Forall2 A B' R ls1 (List.map f ls2)
    <-> @List.Forall2 A B (fun x y => R x (f y)) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_Forall {A R ls}
  : @List.Forall2 A A R ls ls
    <-> @List.Forall A (Proper R) ls.
Proof using Type. induction ls as [|l ls IHls]; t_Forall2. Qed.
Lemma Forall_seq {R start len}
  : List.Forall R (seq start len) <-> (forall x, (start <= x < start + len)%nat -> R x).
Proof using Type.
  revert start; induction len as [|len IHlen]; intro start;
    [ | specialize (IHlen (S start)) ].
  all: repeat first [ t_Forall2_step
                    | lia
                    | exfalso; lia
                    | match goal with
                      | [ H : ?R ?x |- ?R ?y ]
                        => destruct (PeanoNat.Nat.eq_dec x y); [ subst; assumption | clear H ]
                      | [ H : _ |- _ ] => apply H; clear H
                      end ].
Qed.

Lemma Forall2_repeat_iff {A B R x y n m}
  : @List.Forall2 A B R (List.repeat x n) (List.repeat y m)
    <-> ((n <> 0%nat -> R x y) /\ n = m).
Proof using Type.
  revert m; induction n as [|n IHn], m as [|m]; [ | | | specialize (IHn m) ];
    t_Forall2; try congruence.
Qed.

Lemma Forall2_rev_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) (List.rev ls2)
    <-> @List.Forall2 A B R ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.

Lemma Forall2_rev_lr_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) ls2 <-> @List.Forall2 A B R ls1 (List.rev ls2).
Proof using Type.
  rewrite <- (rev_involutive ls2), Forall2_rev_iff, !rev_involutive; reflexivity.
Qed.

Lemma Forall2_firstn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.firstn n ls1) (List.firstn n ls2).
Proof using Type.
  revert ls1 ls2; induction n as [|n IHn], ls1 as [|l1 ls2], ls2 as [|l2 ls2]; t_Forall2.
Qed.

Lemma Forall2_skipn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.skipn n ls1) (List.skipn n ls2).
Proof using Type.
  revert ls1 ls2; induction n as [|n IHn], ls1 as [|l1 ls2], ls2 as [|l2 ls2]; t_Forall2.
Qed.
