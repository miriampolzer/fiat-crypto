Require Import bedrock2.Array.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.SepAutoArray.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import compiler.MMIO.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Naive.
From Coq Require Import Init.Byte.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Curves.Edwards.XYZT.Basic.
Require Import Curves.Edwards.XYZT.Precomputed.
Require Import Curves.Edwards.XYZT.Readdition.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(* Size of a field element in bytes. This is the same as computing eval in felem_size_bytes, but we want a notation instead of definition. *)
Local Notation felem_size := 40.

(* Notations help treat curve points like C structs. To avoid notation clashes, projective coordinates are capitalized. *)

(* Member access notation for projective points: (X, Y, Z, Ta, Tb). *)
Local Notation "A .X" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Y" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Ta" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Tb" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for precomputed points: (half_ypx, half_ymx, xyd). *)
Local Notation "A .half_ypx" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_ymx" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .xyd" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for cached points: (half_YmX, half_YpX, Z, Td). *)
Local Notation "A .half_YmX" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_YpX" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Td" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Adds a precomputed point p_b to projective point p_a and puts the result in p_out. *)
Definition add_precomputed := func! (p_out, p_a, p_b) {
  stackalloc felem_size as YpX1;
  fe25519_add(YpX1, p_a.Y, p_a.X);
  stackalloc felem_size as YmX1;
  fe25519_sub(YmX1, p_a.Y, p_a.X);
  stackalloc felem_size as A;
  fe25519_mul(A, YmX1, p_b.half_ymx);
  stackalloc felem_size as B;
  fe25519_mul(B, YpX1, p_b.half_ypx);
  stackalloc felem_size as T1;
  fe25519_mul(T1, p_a.Ta, p_a.Tb);
  stackalloc felem_size as C;
  fe25519_mul(C, p_b.xyd, T1);
  fe25519_sub(p_out.Ta, B, A);
  stackalloc felem_size as F;
  fe25519_sub(F, p_a.Z, C);
  stackalloc felem_size as G;
  fe25519_add(G, p_a.Z, C);
  fe25519_add(p_out.Tb, B, A);
  fe25519_mul(p_out.X, p_out.Ta, F);
  fe25519_mul(p_out.Y, G, p_out.Tb);
  fe25519_mul(p_out.Z, F, G)
}.

(* Doubles a projective point. Equivalent of m1double in src/Curves/Edwards/XYZT/Basic.v *)
Definition double := func! (p_out, p_a) {
  stackalloc felem_size as trX;
  fe25519_square(trX, p_a.X);
  stackalloc felem_size as trZ;
  fe25519_square(trZ, p_a.Y);
  stackalloc felem_size as t0;
  fe25519_square(t0, p_a.Z);
  stackalloc felem_size as trT;
  fe25519_carry_add(trT, t0, t0);
  stackalloc felem_size as rY;
  fe25519_add(rY, p_a.X, p_a.Y);
  fe25519_square(t0, rY);
  fe25519_carry_add(p_out.Tb, trZ, trX);
  stackalloc felem_size as cZ;
  fe25519_carry_sub(cZ, trZ, trX);
  fe25519_sub(p_out.Ta, t0, p_out.Tb);
  stackalloc felem_size as cT;
  fe25519_sub(cT, trT, cZ);
  fe25519_mul(p_out.X, p_out.Ta, cT);
  fe25519_mul(p_out.Y, p_out.Tb, cZ);
  fe25519_mul(p_out.Z, cZ, cT)
}.

(* Converts a projective point p_a to a cached point p_out to prepare it for readdition. 
   Uses the field's parameter d, which is passed as p_d for now. *)
Definition to_cached := func! (p_out, p_a, p_d) {
  fe25519_sub(p_out.half_YmX, p_a.Y, p_a.X);
  fe25519_half(p_out.half_YmX, p_out.half_YmX); (* An implementation doesn't exist yet, work with spec for now. *)
  fe25519_add(p_out.half_YpX, p_a.Y, p_a.X);
  fe25519_half(p_out.half_YpX, p_out.half_YpX);
  fe25519_mul(p_out.Td, p_a.Ta, p_a.Tb);
  fe25519_mul(p_out.Td, p_out.Td, p_d);
  fe25519_copy(p_out.Z, p_a.Z)
}.

(* Equivalent of m1_readd in src/Curves/Edwards/XYZT/Readdition.v 
   Adds a projective point p_a and cached point p_c and stores the result as projective point in p_out. *)
Definition readd := func! (p_out, p_a, p_c) {
  stackalloc felem_size as A;
  fe25519_sub(A, p_a.Y, p_a.X);
  fe25519_mul(A, A, p_c.half_YmX);
  stackalloc felem_size as B;
  fe25519_add(B, p_a.Y, p_a.X);
  fe25519_mul(B, B, p_c.half_YpX);
  stackalloc felem_size as C;
  fe25519_mul(C, p_a.Ta, p_a.Tb);
  fe25519_mul(C, C, p_c.Td);
  stackalloc felem_size as D;
  fe25519_mul(D, p_a.Z, p_c.Z);
  fe25519_sub(p_out.Ta, B, A);
  stackalloc felem_size as F;
  fe25519_sub(F, D, C);
  stackalloc felem_size as G;
  fe25519_add(G, D, C);
  fe25519_add(p_out.Tb, B, A);
  fe25519_mul(p_out.X, p_out.Ta, F);
  fe25519_mul(p_out.Y, G, p_out.Tb);
  fe25519_mul(p_out.Z, F, G)
}.

(* Size of a projective point in bytes. *)
Local Notation pp_size := 200.
(* Size of a cached point in bytes. *)
Local Notation pc_size := 160.

(* TODO I guess we can unify P256 and this one? *)
Definition memcopy := func! (d, s, n) {
  memmove(d, s, n)
}.

Definition copy_projective_point := func! (p_out, p_in) {
  memcopy(p_out, p_in, $pp_size)
}.

Definition zero_projective_point := func! (zero) {
  fe25519_from_word(zero.X, $0);
  fe25519_from_word(zero.Y, $1);
  fe25519_from_word(zero.Z, $1);
  fe25519_from_word(zero.Ta, $0);
  fe25519_from_word(zero.Tb, $1)
}.

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  (* TODO: Can we provide actual values/proofs for these, rather than just sticking them in the context? *)
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a d: F M_pos}
          {nonzero_a : a <> F.zero}
          {square_a : exists sqrt_a, (F.mul sqrt_a sqrt_a) = a}
          {nonsquare_d : forall x, (F.mul x x) <> d}.
  Context {a_eq_minus1:a = F.opp F.one} {twice_d} {k_eq_2d:twice_d = (F.add d d)} {nonzero_d: d<>F.zero}.

Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).

Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation felem_size_in_bytes := (felem_size_in_bytes(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation word := (Naive.word 32).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation point := (point(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation cached := (cached(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(d:=d)).
Local Notation coordinates := (coordinates(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation cached_coordinates := (cached_coordinates(Fzero:=F.zero)(Fadd:=F.add)(Fdiv:=F.div)(Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation precomputed_coordinates := (precomputed_coordinates(Fone:=F.one)(Fadd:=F.add)(Fmul:=F.mul)(Fsub:=F.sub)(Feq:=Logic.eq)(a:=a)(d:=d)).
Local Notation m1double :=
  (m1double(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).
Local Notation m1_prep :=
  (m1_prep(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
                  (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
                  (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
                  (a:=a)(d:=d)(nonzero_a:=nonzero_a)(a_eq_minus1:=a_eq_minus1)
                  (twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(nonzero_d:=nonzero_d)). 
Local Notation m1_readd :=
  (m1_readd(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(nonzero_d:=nonzero_d)).
Local Notation m1add_precomputed_coordinates :=
  (m1add_precomputed_coordinates(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
           (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
           (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
           (a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)
           (a_eq_minus1:=a_eq_minus1)).

Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).

Definition precomputed_repr (P : precomputed_point) := { p | let '(half_ymx, half_ypx, xyd) := p in
                            precomputed_coordinates P = (feval half_ymx, feval half_ypx, feval xyd) /\
                            bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\ bounded_by loose_bounds xyd }.
Local Notation "c 'p3@' p" := (let '(half_ymx, half_ypx, xyd) := proj1_sig c in (
                                (FElem (p) half_ymx) * 
                                (FElem (p .+ felem_size) half_ypx) *
                                (FElem (p .+ (felem_size + felem_size)) xyd)))%sep
                              (at level 10, format "c 'p3@' p").
                            

Definition projective_repr P := { p | let '(x,y,z,ta,tb) := p in
                            (* exists P', (Basic.eq P P') /\ TODO try to add this here, see how it goes (replace P with P' below). I'll need to be more vague here, but there may be a better way to do it *)
                            coordinates P = (feval x, feval y, feval z, feval ta, feval tb) /\
                            bounded_by tight_bounds x /\ bounded_by tight_bounds y /\ bounded_by tight_bounds z /\
                              bounded_by loose_bounds ta /\ bounded_by loose_bounds tb }.
Definition p5at {a} (c : projective_repr a) p := (let '(x,y,z,ta,tb) := proj1_sig c in sep (sep (sep (sep 
                              (FElem (p) x) 
                              (FElem (p .+ felem_size) y))
                              (FElem (p .+ (felem_size + felem_size)) z)) 
                              (FElem (p .+ (felem_size + felem_size + felem_size)) ta))
                              (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) tb)).
Local Notation "c 'p5@' p" := (p5at c p) (at level 10, format "c 'p5@' p").

Definition cached_repr (P : cached) := { p | let '(half_ymx, half_ypx,z,td) := p in
                            cached_coordinates P = (feval half_ymx, feval half_ypx, feval z, feval td) /\
                            bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\bounded_by loose_bounds z /\ bounded_by loose_bounds td }.
Definition p4at {a} (c : cached_repr a) p := (let '(half_ymx, half_ypx,z,td) := proj1_sig c in sep (sep (sep 
                              (FElem (p) half_ymx) 
                              (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) z)) 
                              (FElem (p .+ (felem_size + felem_size + felem_size)) td)).
Local Notation "c 'p4@' p" := (p4at c p) (at level 10, format "c 'p4@' p").

Instance spec_of_fe25519_half : spec_of "fe25519_half" :=
  fnspec! "fe25519_half"
    (result_location input_location: word) / (old_result input: felem)
    (R: _ -> Prop),
  { requires t m :=
    bounded_by loose_bounds input /\
    (exists Ra, m =* (FElem input_location input) * Ra) /\
    m =* (FElem result_location old_result) * R;
    ensures t' m' :=
      t = t' /\
      exists result,
        bounded_by tight_bounds result /\
        feval result = F.div (feval input) (F.add F.one F.one) /\
        m' =* (FElem result_location result)  * R}.

Global Instance spec_of_add_precomputed : spec_of "add_precomputed" :=
  fnspec! "add_precomputed"
    (p_out p_a p_b: word) / (a: point) (b: precomputed_point) (a_repr: projective_repr a) (b_repr: precomputed_repr b) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_a * b_repr p3@ p_b * R/\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a_plus_b : projective_repr (m1add_precomputed_coordinates a b),
          m' =* a_plus_b p5@ p_out * a_repr p5@ p_a * b_repr p3@ p_b * R
    }.
Global Instance spec_of_double : spec_of "double" :=
  fnspec! "double"
    (p_out p_a: word) /
    (a: point) (a_repr: projective_repr a) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' := 
        t = t' /\
        exists a_double: projective_repr (m1double a),
          m' =* a_double p5@ p_out * a_repr p5@ p_a * R
    }.

Global Instance spec_of_to_cached: spec_of "to_cached" :=
  fnspec! "to_cached"
    (p_out p_a p_d: word) /
    (a: point) (a_repr: projective_repr a) (d1: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_a * FElem p_d d1 * R /\
        Datatypes.length out = Z.to_nat (4 * felem_size) /\
        d = feval d1 /\
        bounded_by tight_bounds d1;
      ensures t' m' :=
        t = t' /\
        exists a_cached: cached_repr (m1_prep a),
          m' =* a_cached p4@ p_out * a_repr p5@ p_a * FElem p_d d1 * R
  }.

Global Instance spec_of_readd : spec_of "readd" :=
  fnspec! "readd"
    (p_out p_a p_c: word) /
    (a: point) (c: cached) (a_repr: projective_repr a) (c_repr: cached_repr c) (out : list byte) (R : _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_a * c_repr p4@ p_c * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a_plus_c: projective_repr (m1_readd a c),
          m' =* a_plus_c p5@ p_out * a_repr p5@ p_a * c_repr p4@ p_c * R
  }.

Global Instance spec_of_copy_projective_point : spec_of "copy_projective_point" :=
  fnspec! "copy_projective_point"
    (p_out p_in : word) /
    (a : point) (a_repr : projective_repr a) (out : list byte) (R : _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a_repr p5@ p_in * R /\
        Datatypes.length out = Z.to_nat (pp_size);
      ensures t' m' :=
        t = t' /\
        m' =* a_repr p5@ p_out * a_repr p5@ p_in * R
  }.

Local Notation zero := (zero(nonzero_a:=nonzero_a)).

Global Instance spec_of_zero_projective_point : spec_of "zero_projective_point" :=
  fnspec! "zero_projective_point"
    (p_zero : word) /
    (out : list byte) (R : _ -> Prop), {
      requires t m :=
        m =* out $@ p_zero * R /\
        Datatypes.length out = Z.to_nat (pp_size);
      ensures t' m' :=
        t = t' /\
        exists zero_repr: projective_repr (zero),
          m' =* zero_repr p5@ p_zero * R
    }.

(* TODO import from somewhere. *)
Local Instance spec_of_memcopy : spec_of "memcopy" :=
  fnspec! "memcopy" (p_d p_s n : word) / (d s : list byte) R,
  { requires t m := m =* d$@p_d * s$@p_s * R /\ List.length d = n :> Z /\ List.length s = n :> Z /\ n <= 2^31; (* I suppose.. *)
    ensures t' m' := t' = t /\ m' =* s$@p_d * s$@p_s * R }.

Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.
Local Instance spec_of_fe25519_carry_add : spec_of "fe25519_carry_add" := Field.spec_of_BinOp bin_carry_add.
Local Instance spec_of_fe25519_sub : spec_of "fe25519_sub" := Field.spec_of_BinOp bin_sub.
Local Instance spec_of_fe25519_carry_sub : spec_of "fe25519_carry_sub" := Field.spec_of_BinOp bin_carry_sub.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe26619_copy: spec_of "fe25519_copy" := Field.spec_of_felem_copy.

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.
Local Arguments word.add : simpl never.

Local Arguments feval : simpl never.

(* This is way too large to be unfolded here. *)
Local Opaque F.to_Z.

Local Ltac destruct_points :=
  repeat match goal with
    | _ => progress destruct_head' @Readdition.cached
    | _ => progress destruct_head' cached_repr
    | _ => progress destruct_head' @Basic.point
    | _ => progress destruct_head' projective_repr
    | _ => progress destruct_head' @precomputed_point
    | _ => progress destruct_head' precomputed_repr
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' and
    | _ => progress lazy beta match zeta delta [p5at p4at coordinates precomputed_coordinates cached_coordinates proj1_sig] in *
  end.

Local Ltac cbv_bounds H :=
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
  end.

 Ltac skipn_firstn_length :=
    change felem_size_in_bytes with 40 in *; listZnWords.

Ltac split_stack_at_n_in stack p n H := rewrite <- (firstn_skipn n stack) in H;
  rewrite (map.of_list_word_at_app_n _ _ _ n) in H; try skipn_firstn_length;
  let D := fresh in unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (firstn n stack) (skipn n stack) n _ _)) as D); try skipn_firstn_length;
  seprewrite_in D H; rewrite ?skipn_skipn in H; bottom_up_simpl_in_hyp H; clear D.

Local Ltac solve_mem :=
  try match goal with  | |- exists _ : _ -> Prop, _%sep _ => eexists end;
  match goal with  | H : _ %sep ?m |- _ %sep ?m => bottom_up_simpl_in_goal_nop_ok end;
  match goal with
  | |- _%sep _ => ecancel_assumption_impl
  | H: ?P%sep ?m |- ?G%sep ?m =>  (* Solve Placeholder goals when a fixed size list is given *)
    match P with context[map.of_list_word_at ?p ?stack] =>
    match G with context[Placeholder ?p _] =>
      solve [ cbv [Placeholder]; extract_ex1_and_emp_in_goal; bottom_up_simpl_in_goal_nop_ok; split; [ecancel_assumption | skipn_firstn_length] ]
    end end
  end.

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds;
  (* solve simple preconditions *) try listZnWords; try assumption.

(* Attempts to find anybytes terms in the goal and rewrites the first corresponding stack hypothesis to byte representation.
   straightline only supports deallocation for byte representation at the moment. *)
Ltac solve_deallocation :=
  lazy [FElem] in *;
  match goal with
    H: ?P%sep _ |- ?G =>
      repeat match G with context[anybytes ?p _ _] =>
        match P with context[Bignum.Bignum felem_size_in_words p ?v] =>
          seprewrite_in (Bignum.Bignum_to_bytes felem_size_in_words p) H
        end
      end;
      extract_ex1_and_emp_in H
  end;
  repeat straightline.

Ltac split_stack stack_var ptr_var num :=
  multimatch goal with
  | H : context[stack_var $@ ptr_var] |- _ =>
    split_stack_at_n_in stack_var ptr_var 40%nat H;
    split_stack_at_n_in (skipn 40 stack_var) (ptr_var.+40) 40%nat H;
    split_stack_at_n_in (skipn 80 stack_var) (ptr_var.+80) 40%nat H;
    match num with
    | 4 => idtac
    | 5 =>
      split_stack_at_n_in (skipn 120 stack_var) (ptr_var.+120) 40%nat H
    end
  end.

Require Import bedrock2.ArrayCasts.
(* projective_repr -> list byte TODO: felem -> list byte should go into Field.v *)
Definition projective_repr_to_list_byte {p} (r : projective_repr p) : list byte :=
  let '(x, y, z, ta, tb) := proj1_sig r in (ws2bs 4%nat x) ++ (ws2bs 4%nat y) ++ (ws2bs 4%nat z) ++ (ws2bs 4%nat ta) ++ (ws2bs 4%nat tb).

Lemma length_project_repr_to_list_byte {p} (r : projective_repr p) : Datatypes.length (projective_repr_to_list_byte r) = Z.to_nat (5 * 40).
Proof.
  destruct_points.
  cbv [FElem Bignum.Bignum projective_repr_to_list_byte proj1_sig].
  rewrite !app_length, !ws2bs_length. (* meh. length assumption about felem isn't ineherent to them .*)
Abort.

(* r p5@ p -> (projective_repr_to_list_byte c) @$ p *)                              
Lemma p5_impl_bytes : forall {p} (r : projective_repr p) p_r, 
  Lift1Prop.impl1 (r p5@ p_r) ((projective_repr_to_list_byte r) $@ p_r).
Proof.
  intros.
  destruct_points.
  cbv [FElem Bignum.Bignum projective_repr_to_list_byte proj1_sig].
  intros m H. extract_ex1_and_emp_in_hyps.
  unshelve (erewrite <- (array1_iff_eq_of_list_word_at _ _ _ _)).
  { change felem_size_in_words with 10%nat in *.
    rewrite !List.length_app, !ws2bs_length. lia. }
    
  repeat (epose (array_append _ _ _ _ _) as i;
  seprewrite0 i;
  clear i).
  repeat (
  epose (iff1_sym (bytes_of_words _ _)) as B;
  cbv [bytes_per] in B;
  change (bytes_per_word 32) with 4 in *;
  change (Z.to_nat 4) with 4%nat in *;
  seprewrite0 B;
  clear B).

  change (Z.of_nat 4) with 4.
  rewrite !ws2bs_length, !H_emp0, !H_emp1, !H_emp2, !H_emp3.
  change felem_size_in_words with 10%nat.
  bottom_up_simpl_in_goal. bottom_up_simpl_in_hyp H.
  ecancel_assumption.
Qed.

(* p5@ -> $@, I want to match on p5@ but I don't know how *)
Hint Extern 1 (Lift1Prop.impl1 (_) (sepclause_of_map (_ $@ ?p))) => (apply p5_impl_bytes) : ecancel_impl.

Lemma bytes_impl_p5 : forall {p} (r : projective_repr p) p_r, 
  Lift1Prop.impl1 ((projective_repr_to_list_byte r) $@ p_r) (r p5@ p_r).
Proof.
  intros.
  destruct_points.
  intros m H. cbv [projective_repr_to_list_byte proj1_sig] in *. 
Abort. (* I would need a length assumption somewhere. *)


Lemma copy_projective_point_ok: program_logic_goal_for_function! copy_projective_point.
Proof.
  do 4 straightline.

  repeat straightline.
  straightline_call. ssplit.
  { ecancel_assumption_impl. }
  { ZnWords. }
  { destruct_points. 
    cbv [projective_repr_to_list_byte proj1_sig].
    rewrite !length_app, !ws2bs_length.
    cbv [FElem Bignum.Bignum] in *.  (* super weird that the length of felems is only guaranteed by FElem *)
    extract_ex1_and_emp_in H0.
    rewrite !H0_emp0, !H0_emp1, !H0_emp2, !H0_emp3, H0_emp4.
    change felem_size_in_words with 10%nat.
    ZnWords. }
  { ZnWords. }
   
  repeat straightline.
  
  (* getting the lengths here is very annoyting, this should be inherent to felem, and not just in FElem. *)
  (* this is essentially the backwards direction of p5_impl_bytes, but with lengths from assumptions *)
  destruct_points. cbv [projective_repr_to_list_byte proj1_sig FElem Bignum.Bignum] in *.
  extract_ex1_and_emp_in_hyps. extract_ex1_and_emp_in_goal. ssplit; try assumption.

  (* TODO figure out how to do with with seprewrite directly, or create a tactic/lemma. *)
  repeat (epose ((bytes_of_words _ _)) as B;
  cbv [bytes_per] in B;
  change (bytes_per_word 32) with 4 in *;
  change (Z.to_nat 4) with 4%nat in *;
  change (Z.of_nat 4) with 4 in *; 
  seprewrite0 B;
  clear B).

  assert (Z.of_nat (Datatypes.length (ws2bs 4 f2 ++ ws2bs 4 f3 ++ ws2bs 4 f1 ++ ws2bs 4 f0 ++ ws2bs 4 f)) <= 2 ^ 32).
  {
     rewrite !List.length_app, !ws2bs_length, !H0_emp0, !H0_emp1, !H0_emp2, !H0_emp3, !H0_emp4.
     change felem_size_in_words with 10%nat. lia. 
  }
  epose (iff1_sym (array1_iff_eq_of_list_word_at _ _ _)) as B.
  seprewrite_in B H4.
  clear B.
  epose (iff1_sym (array1_iff_eq_of_list_word_at _ _ _)) as B.
  seprewrite_in B H4.
  clear B.
  Unshelve. all: try assumption.

  repeat (epose (array_append _ _ _ _ _) as B; seprewrite_in B H4; clear B).

  rewrite !ws2bs_length, !H0_emp0, !H0_emp1, !H0_emp2, !H0_emp3 in *.
  change felem_size_in_words with 10%nat in *.
  bottom_up_simpl_in_goal. bottom_up_simpl_in_hyp H4.
  ecancel_assumption.
Qed.

Set Ltac Profiling.

Lemma zero_projective_point_ok: program_logic_goal_for_function! zero_projective_point.
Proof.
  do 4 straightline.
  
  pose word32_ok. (* required to run listZnWords on goals without words but with nasty lists *)
  split_stack out p_zero 5.
  
  repeat straightline.
  repeat single_step.

  repeat straightline.
  unshelve eexists.
  eexists (x, x0, x1, x2, x3); ssplit. (* TODO don't name these directly, if I can avoid it*)
  cbv [zero coordinates proj1_sig]. rewrite H20, H17, H14, H11, H8. bottom_up_simpl_in_goal.
  f_equal.
  all: try solve_bounds.
  cbv [coordinates proj1_sig p4at p5at].
  ecancel_assumption_impl.
Qed.

Lemma to_cached_ok: program_logic_goal_for_function! to_cached.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  repeat straightline.
  destruct_points.
  split_stack out p_out 4.
  repeat straightline.

  repeat single_step.

  repeat straightline.
  lazy delta [cached_repr].
  unshelve eexists.
  eexists (_, _, _, _).
  2: solve_mem.
  lazy match zeta beta delta [bin_model bin_mul bin_add bin_carry_add bin_sub cached_coordinates coordinates proj1_sig m1_prep] in *.
  ssplit; try solve_bounds.
  congruence.
Qed.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].

  do 4 straightline.
  destruct_points.
  split_stack out p_out 5.
  repeat straightline.
 
  repeat single_step. (* Avoid performance regressions: Keep this around 90s*)

  repeat straightline.
  solve_deallocation.

  lazy beta match zeta delta [m1add_precomputed_coordinates projective_repr precomputed_coordinates coordinates proj1_sig].
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: solve_mem.
  ssplit; try solve_bounds.
  lazy [bin_model bin_add bin_mul bin_sub] in *. congruence.
Qed.

Lemma double_ok : program_logic_goal_for_function! double.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  do 3 straightline.
  destruct_points.
  split_stack out p_out 5.
  repeat straightline.

  repeat single_step.

  (* Solve the postconditions *)
  repeat straightline.
  solve_deallocation.
  lazy beta match zeta delta [projective_repr coordinates proj1_sig m1double bin_model bin_add bin_mul bin_sub bin_carry_add bin_sub bin_carry_sub un_model un_square] in *.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: solve_mem.
  ssplit; try solve_bounds.
  rewrite F.pow_2_r in *.
  Prod.inversion_prod. congruence.
Qed.

Lemma readd_ok : program_logic_goal_for_function! readd.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  do 4 straightline.
  destruct_points.
  split_stack out p_out 5.
  repeat straightline.

  repeat single_step.

  repeat straightline.
  solve_deallocation.
  unshelve eexists.
  eexists (_, _, _, _, _).
  2: solve_mem.
  lazy match beta zeta delta [m1_readd coordinates proj1_sig bin_model bin_mul bin_add bin_carry_add bin_sub] in *.
  ssplit; try solve_bounds.
  Prod.inversion_prod. congruence.
Qed.

Show Ltac Profile.

End WithParameters.
