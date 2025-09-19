From Coq Require Import Morphisms.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Curves.Edwards.XYZT.Basic.

Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Notations Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.

Section ExtendedCoordinates.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
          {Feq_dec:DecidableRel Feq}.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone. Local Notation "2" := (Fadd 1 1).
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x).

  Context {a d: F}
          {nonzero_a : a <> 0}
          {square_a : exists sqrt_a, sqrt_a^2 = a}
          {nonsquare_d : forall x, x^2 <> d}.
  Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).
  Local Notation Eadd := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).

  (* Match this context to the Basic.ExtendedCoordinates context *)
  Local Notation point := (point(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).
  Local Notation coordinates := (coordinates(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).
  Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d} {nonzero_d: d<>0}.
  Local Notation m1add := (m1add(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fone:=Fone)(Fopp:=Fopp)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)(Finv:=Finv)(Fdiv:=Fdiv)(field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=Feq_dec)(a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)(a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).
  Local Notation zero := (zero(nonzero_a:=nonzero_a)).

  (* Define a new cached point type *)
  Definition cached :=
    { C | let '(half_YmX,half_YpX,Z,Td) := C in
          let X := half_YpX - half_YmX in
          let Y := half_YpX + half_YmX in
          let T := Td / d in
            a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
            /\ X * Y = Z * T
            /\ Z <> 0 }.
  Definition cached_coordinates (C:cached) : F*F*F*F := proj1_sig C.
  Definition cached_eq (C1 C2:cached) :=
    let '(hYmX1, hYpX1, Z1, _) := cached_coordinates C1 in
    let '(hYmX2, hYpX2, Z2, _) := cached_coordinates C2 in
    Z2*(hYpX1-hYmX1) = Z1*(hYpX2-hYmX2) /\ Z2*(hYpX1+hYmX1) = Z1*(hYpX2+hYmX2).

  (* Stolen from Basic; should be a way to reuse instead? *)
  Ltac t_step :=
    match goal with
    | |- Proper _ _ => intro
    | _ => progress intros
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' @E.point
    | _ => progress destruct_head' @Basic.point
    | _ => progress destruct_head' @cached
    | _ => progress destruct_head' and
    | _ => progress cbv [eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add E.opp fst snd cached_coordinates coordinates E.coordinates proj1_sig] in *
    | |- _ /\ _ => split | |- _ <-> _ => split
    end.
  Ltac t := repeat t_step; try Field.fsatz.

  (* Stolen from Basic *)
  Program Definition to_twisted (P:point) : Epoint :=
    let XYZTT := coordinates P in let Ta := snd XYZTT in
                                  let XYZT  := fst XYZTT in
                                  let Tb := snd XYZT in
                                  let XYZ := fst XYZT in      let Z := snd XYZ in
                                                              let XY   := fst XYZ in       let Y := snd XY in
                                                                                           let X    := fst XY in
                                                                                           let iZ := Finv Z in ((X*iZ), (Y*iZ)).
  Next Obligation. t. Qed.
  Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted.
  Proof using Type. cbv [to_twisted]; t. Qed.

  Program Definition cached_to_twisted (C:cached) : Epoint :=
    let MPZT := cached_coordinates C in
      let Td  := snd MPZT in
      let MPZ := fst MPZT in
        let Z  := snd MPZ in
        let MP := fst MPZ in
          let hYpX := snd MP in
          let hYmX := fst MP in
            let iZ := Finv Z in (((hYpX-hYmX)*iZ), ((hYpX+hYmX)*iZ)).
  Next Obligation. t. Qed.

  Program Definition m1_prep (P : point) : cached :=
      match coordinates P return F*F*F*F with
        (X, Y, Z, Ta, Tb) =>
        let half_YmX := (Y-X)/2 in
        let half_YpX := (Y+X)/2 in
        let Td := Ta*Tb*d in
        (half_YmX, half_YpX, Z, Td)
      end.
  Next Obligation. t. Qed.

  Program Definition m1_readd
      (P1 : point) (C : cached) : point :=
    match coordinates P1, C return F*F*F*F*F with
      (X1, Y1, Z1, Ta1, Tb1), (half_YmX, half_YpX, Z2, Td) =>
      let A := (Y1-X1)*half_YmX in
      let B := (Y1+X1)*half_YpX in
      let C := (Ta1*Tb1)*Td in
      let D := Z1*Z2 in
      let E := B-A in
      let F := D-C in
      let G := D+C in
      let H := B+A in
      let X3 := E*F in
      let Y3 := G*H in
      let Z3 := F*G in
      (X3, Y3, Z3, E, H)
    end.
  Next Obligation.
    match goal with
    | [ |- match (let (_, _) := coordinates ?P1 in let (_, _) := _ in let (_, _) := _ in let (_, _) := _ in let (_, _) := proj1_sig ?C in _) with _ => _ end ]
      => pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P1))  _ _  (proj2_sig (cached_to_twisted C)))
    end; t. Qed.

  Create HintDb points_as_coordinates discriminated.
  Hint Unfold XYZT.Basic.point XYZT.Basic.coordinates XYZT.Basic.m1add
       E.point E.coordinates m1_readd m1_prep : points_as_coordinates.
  Lemma readd_correct P Q :
    Basic.eq (m1_readd P (m1_prep Q)) (m1add P Q).
  Proof. cbv [m1add m1_readd m1_prep]; t. Qed.

(* TODO probably want this in a new scalar multiplication file, together with any other things I'll need for the proofs. *)
Import PeanoNat.

(* This exists already in a primer file for complete curves, but for E.point. Figure out which one I want to use.*)
Fixpoint scalarmult (n : nat) (A : point) : point :=
    match n with
      | 0 => zero
      | S n => m1add (scalarmult n A) A
    end.
  
  Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

  (* Creates 0..(n-1)*A *)
  Fixpoint multiples (n : nat) (A : point) : list point :=
    match n with
      | 0 => []
      | S n => (multiples n A) ++ [(scalarmult n A)]
    end.
  
  Lemma length_multiples (n : nat) (A : point) :
    Logic.eq (List.length (multiples n A)) n.
  Proof.
    induction n.
    - cbv [multiples length]. reflexivity.
    - unfold multiples. fold multiples. rewrite length_app.
      rewrite IHn. simpl. Lia.lia.
  Qed.


  Lemma multiples_correct (n : nat) (A : point) :
    forall k default, k < n -> Logic.eq (List.nth k (multiples n A) default) (scalarmult k A).
  Proof.
    destruct n. intros. apply Nat.nlt_0_r in H. contradiction.
    induction n.
    - intros. assert (Logic.eq k 0%nat) by Lia.lia. subst. simpl. reflexivity.
    - intros. unfold multiples. fold multiples. destruct (Nat.eq_dec k (S n)).
      + subst. erewrite <- length_multiples at 1.
        eapply nth_middle.
      + erewrite app_nth1.
        2: { rewrite length_app. erewrite length_multiples. simpl. Lia.lia. }
        apply IHn. Lia.lia. 
  Qed.


  (* didn't need those*)
  Lemma multiples_app_index (n : nat) (A : point) :
    forall i, i < n -> Logic.eq (multiples n A) ((firstn i (multiples n A)) ++ [scalarmult i A] ++ skipn (i + 1) (multiples n A)).
  Proof.
    intros.
    eapply (nth_ext). Unshelve. 3,4: exact A.
    - rewrite length_app, length_firstn, length_app, length_skipn, length_multiples. simpl. Lia.lia.
    - rewrite length_multiples. 
      intros. destruct (dec (n0 < i)).
      + rewrite app_nth1. 2: { rewrite length_firstn, length_multiples. Lia.lia. }
        rewrite nth_firstn. replace (n0 <? i) with true.
        2:{ symmetry. rewrite Nat.ltb_lt. assumption. }
        reflexivity.
      + rewrite app_nth2. 2: { rewrite length_firstn, length_multiples. Lia.lia. } destruct (dec (n0 > i)).
        * rewrite app_nth2. 2: {rewrite length_firstn, length_multiples. simpl. Lia.lia. }
          rewrite nth_skipn, length_firstn, length_multiples. simpl.
          replace ((i + 1 + (n0 - Init.Nat.min i n - 1))%nat) with n0.
          2: {Lia.lia. } reflexivity.
        * assert (Logic.eq i n0)%nat by Lia.lia.
          rewrite app_nth1. 2: { rewrite length_firstn, length_multiples. simpl. Lia.lia. }
          rewrite length_firstn, length_multiples. replace (n0 - Init.Nat.min i n)%nat with 0%nat.
          rewrite multiples_correct. simpl. subst. reflexivity.
          assumption. Lia.lia.
  Qed. 

  Lemma firstn_multiples (n : nat) (A : point) :
    forall k, Logic.eq (firstn k (multiples n A)) (multiples (min k n) A).
  Proof.
    intros k.
    eapply (nth_ext). Unshelve. 3,4: exact A.
    - rewrite length_firstn, !length_multiples. Lia.lia.
    - rewrite length_firstn, !length_multiples. intros ? ?. rewrite nth_firstn. 
      rewrite !multiples_correct ; try Lia.lia.
      replace (n0 <? k) with true.
      2:{ symmetry. rewrite Nat.ltb_lt. Lia.lia. }
      reflexivity.
  Qed.

  Lemma applast_multiples (n : nat) (A : point) :
    n > 0 -> Logic.eq (multiples n A) ((multiples (n - 1) A) ++ [scalarmult (n - 1) A]).
  Proof.
    destruct n. intros. apply Nat.nlt_0_r in H. contradiction.
    intros. replace (S n - 1)%nat with n by Lia.lia.
    simpl. reflexivity.
  Qed.  

End ExtendedCoordinates.
