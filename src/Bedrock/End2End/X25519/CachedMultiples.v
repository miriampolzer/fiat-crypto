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
Require Import Crypto.Bedrock.End2End.X25519.EdwardsXYZT. (* todo rename and move around properly, try to create a proper hierarchy of what needs what *)
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
(* Size of a projective point in bytes. *)
Local Notation pp_size := 200.
(* Size of a cached point in bytes. *)
Local Notation pc_size := 160.

(* Notations help treat curve points like C structs. To avoid notation clashes, projective coordinates are capitalized. *)

(* Member access notation for projective points: (X, Y, Z, Ta, Tb). *)
Local Notation "A .X" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Y" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Ta" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Tb" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Member access notation for cached points: (half_YmX, half_YpX, Z, Td). *)
Local Notation "A .half_YmX" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_YpX" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Td" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

(* Input is a projective point p, output is multiples of p as cached points, to be used for scalar multiplication. *)
Definition cached_multiples := func! (p_ai, p_a, p_d) {
  (* The first point is 0*A, so just zero. *)
  stackalloc pp_size as zero;
  zero_projective_point(zero);
  to_cached(p_ai, zero, p_d);

  (* The second point is 1*A.*)
  to_cached(p_ai+$pc_size, p_a, p_d);

  (* Helper array of normal points for double and add results, contains multiples of A. *)
  stackalloc 8*pp_size as p_ai_uncached;
  (* copy 1*A into the helper array at index 1. *)
  copy_projective_point(p_ai_uncached+$pp_size, p_a);

  (* Remaining points are generated in a loop. *)
  i = $2;
  stackalloc pp_size as temp;
  while (i < $16) {
    double(temp, p_ai_uncached+((i >> $1) * $pp_size)); (* Double (i/2)*A, now temp contains i*A. *)
    to_cached(p_ai+(i*$pc_size), temp, p_d); (* copy temp to Ai *)
    if (i < $8) {
      (* Save i*A for later, at index i. *)
      copy_projective_point(p_ai_uncached+(i*$pp_size), temp)
    };
    (* Now for the odd numbers, calculate (i+1)*A, store in temp. *)
    readd(temp, p_a, p_ai+(i*$pc_size));
    (* Store (i+1)*A in the result array. *)
    to_cached(p_ai+((i+$1)*$pc_size), temp, p_d);
    if (i < $7) {
      (* Save (i+1)*A for later. *)
      copy_projective_point(p_ai_uncached+((i+$1)*$pp_size), temp)
    };
    i = i + $2
  }
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

(* Avoid unfolding deeper than necessary. *)
Local Opaque F.to_Z word.rep word.wrap word.unsigned word.of_Z word.add feval.

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
Local Notation m1_prep :=
  (m1_prep(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
                  (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
                  (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
                  (a:=a)(d:=d)(nonzero_a:=nonzero_a)(a_eq_minus1:=a_eq_minus1)
                  (twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(nonzero_d:=nonzero_d)). 
Local Notation multiples :=
  (multiples(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
                  (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
                  (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
                  (a:=a)(d:=d)(nonzero_a:=nonzero_a)(a_eq_minus1:=a_eq_minus1)
                  (twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(square_a:=square_a)(nonsquare_d:=nonsquare_d)). 
Local Notation scalarmult :=
  (scalarmult(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
                  (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
                  (field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=F.eq_dec)
                  (a:=a)(d:=d)(nonzero_a:=nonzero_a)(a_eq_minus1:=a_eq_minus1)
                  (twice_d:=twice_d)(k_eq_2d:=k_eq_2d)(square_a:=square_a)(nonsquare_d:=nonsquare_d)). 

Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Notation "c 'p5@' p" := (p5at c p) (at level 10, format "c 'p5@' p").
Local Notation "c 'p4@' p" := (p4at c p) (at level 10, format "c 'p4@' p").

Definition cached_point (p : word) (a : cached) : map.rep -> Prop :=
  Lift1Prop.ex1 (fun a_repr : cached_repr a => (a_repr p4@ p)).
Definition projective_point (p : word) (a : point) : map.rep -> Prop :=
  Lift1Prop.ex1 (fun a_repr : projective_repr a => (a_repr p5@ p)).

Instance spec_of_cached_multiples : spec_of "cached_multiples" :=
  fnspec! "cached_multiples"
    (p_ai p_a p_d: word) /
    (a : point) (a_repr : projective_repr a) (d1: felem) (out : list byte) (R : _ -> Prop), {
      requires t m :=
        m =* out $@ p_ai * a_repr p5@ p_a * FElem p_d d1 *  R /\
        Datatypes.length out = Z.to_nat (16*pc_size) /\
        d = feval d1 /\
        bounded_by tight_bounds d1;
      ensures t' m' :=
        t = t' /\
        m' =* (array cached_point (word.of_Z pc_size) p_ai (List.map m1_prep (multiples 16 a))) * a_repr p5@ p_a * FElem p_d d1 * R
    }.

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

Local Instance spec_of_zero_projective_point: spec_of "zero_projective_point" := spec_of_zero_projective_point (a:=a) (d:=d) (nonzero_a:=nonzero_a).
Local Instance spec_of_to_cached : spec_of "to_cached" := spec_of_to_cached (nonzero_d:=nonzero_d) (k_eq_2d:=k_eq_2d) (twice_d:=twice_d) (a_eq_minus1:=a_eq_minus1) (nonzero_a:=nonzero_a) (d:=d) (a:=a).
Local Instance spec_of_copy_projective_point : spec_of "copy_projective_point" := spec_of_copy_projective_point (a:=a) (d:=d).
Local Instance spec_of_double : spec_of "double" := spec_of_double (k_eq_2d:=k_eq_2d) (a_eq_minus1:=a_eq_minus1) (nonsquare_d:=nonsquare_d) (square_a:=square_a) (nonzero_a:=nonzero_a) (a:=a) (d:=d) (twice_d:=twice_d).
Local Instance spec_of_of_readd : spec_of "readd" := spec_of_readd (nonzero_d:=nonzero_d) (k_eq_2d:=k_eq_2d) (twice_d:=twice_d) (a_eq_minus1:=a_eq_minus1) (nonsquare_d:=nonsquare_d) (square_a:=square_a) (nonzero_a:=nonzero_a) (d:=d) (a:=a).

Lemma cached_multiples_ok: program_logic_goal_for_function! cached_multiples.
Proof.
   (* Without this, resolution of cbv stalls out Qed. *)
   (* TODO can't I mark these as opaque in this section and the locally, in a tactic unopaque them when needed. (Or opaque below, where the actual harm happens, which is probably modulo arithmetics.)*)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].


  (* put zero into ai[0] *)
  repeat straightline.
  seprewrite_in array1_iff_eq_of_list_word_at H9; [lia|].
  single_step.
  repeat straightline.
  split_stack_at_n_in out p_ai 160%nat H21. (* split out ai[0] *)
  single_step.
  
  (* put A into ai[1] *)
  repeat straightline.
  split_stack_at_n_in (skipn 160 out) (p_ai.+160) 160%nat H22. (* split out ai[1]*)
  single_step.

  (* allocate helper array (and split it up here already? might make stuff slow) *)
  repeat straightline.
  seprewrite_in array1_iff_eq_of_list_word_at H23; [lia|]. (* because allocation uses array, best way is to build a switch for allocation to use $@. *)

  (* copy over 1*A to p_ai_uncached *)
  split_stack_at_n_in stack1 a4 200%nat H23. (* index 0 - unused*)
  split_stack_at_n_in (skipn 200 stack1) (a4.+200) 200%nat H23. (* index 1, will now be filled *)
  single_step.
  repeat straightline. 

  (* Loop! *)
  refine (let multiples_a := multiples 16 a0 in
          let cached_multiples_a := List.map m1_prep multiples_a in
          let uncached_multiples_a := List.firstn 8 multiples_a in
          tailrec
            (* I think R may change, so it'd be nice to have here, let's see.  *)
            (HList.polymorphic_list.cons (_(*temp_value*)) HList.polymorphic_list.nil)
            (*variables*)(["temp"; "i"; "p_ai_uncached"; "zero"; "p_a"; "p_d"; "p_ai"]) (* these must be all variables we have, even if we don't use them*)
            (*spec*)(fun v temp_value t m temp i p_ai_uncached zero p_a p_d p_ai=>
                let i_z := word.unsigned i in
                PrimitivePair.pair.mk
                  (* Invariant *)
                  (v = (8 - i_z / 2) /\
                   i_z mod 2 = 0 /\ 2 <= i_z < 16 /\
                   m =* 
                        (* p_ai contains 0 - (i-1) of cached_multiples *)
                        array cached_point (word.of_Z pc_size) p_ai (List.firstn (Z.to_nat (i_z)) cached_multiples_a) *
                        (* the remaining space of p_ai is unused*)
                        (skipn (Z.to_nat ((i_z) * pc_size)) out) $@ (p_ai .+ ((i_z) * pc_size)) *
                        (* p_ai_uncached contains 0 - (i-1) of uncached_multiples, maximum 0-7 *)
                        array projective_point (word.of_Z pp_size)
                          p_ai_uncached (List.firstn (Z.to_nat (i_z)) uncached_multiples_a) *
                        (* and (if there is any), the rest of its memory is unused *)
                        (skipn (Z.to_nat ((i_z) * pp_size)) stack1) $@ (p_ai_uncached .+ ((i_z) * pp_size)) *
                        (* temp can be anything, it's only used within the loop *)
                        temp_value $@ temp *
                        (* remaining memory is left untouched *)
                        a_repr p5@ p_a * FElem p_d d1 * R /\
                        Datatypes.length temp_value = Z.to_nat pp_size)
                  (* Postcondition Schema *)
                  (fun T_f M_f temp_f i_f p_ai_uncached_f zero_f p_a_f p_d_f p_ai_f =>
                     T_f = t /\ 
                     M_f =* array cached_point (word.of_Z pc_size) p_ai cached_multiples_a *
                            a_repr p5@ p_a * FElem p_d d1 * R)) (* hmmm, actually there's some more stuff in memory, right? I probably need that*)
            (*measure*)(fun n m : Z => 0 <= n < m) _ _ _ _ _ _); loop_simpl.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  {
    repeat straightline.
    ssplit; try ZnWords. 
    (* Memory precondition, the first two are filled. Actually they are not because I left out zero, probably should just shift the array by one - fix later and look at the body first. *)
    admit. admit.
  }
  {
    repeat straightline.
    (* Single out i/2 * A from uncached multiples. *)
    replace ((firstn (Z.to_nat (word.unsigned x4)) uncached_multiples_a)) with
            ((firstn (Z.to_nat (word.unsigned x4 /2)) (firstn (Z.to_nat (word.unsigned x4)) uncached_multiples_a)) ++ 
            (scalarmult (Z.to_nat (word.unsigned x4 /2)) a0) :: 
            (skipn (S(Z.to_nat (word.unsigned x4 /2))) (firstn (Z.to_nat (word.unsigned x4)) uncached_multiples_a)))%list
            in H36.
    2: {
      clear - H35 H38 H34.
      rewrite firstn_skipn_middle.
      2:{ cbv delta [uncached_multiples_a multiples_a]. erewrite nth_error_nth'. cbv delta [uncached_multiples_a multiples_a]. rewrite !firstn_multiples. rewrite multiples_correct. reflexivity. Lia.lia. rewrite !firstn_length, length_multiples. Lia.lia.  }
      reflexivity.
    }
    rewrite !array_app in H36. rewrite array_cons in H36 (* this crashes for some reason. fix next. *). unfold array at 3 in H36.

    replace (x5.+200 *Z.of_nat (Datatypes.length (firstn (Z.to_nat (word.unsigned x4 / 2)) (firstn (Z.to_nat (word.unsigned x4)) uncached_multiples_a)))) with
      ((word.add x5 (word.mul (word.sru x4 (word.of_Z 1)) (word.of_Z 200)))) in H36.
    cbv [projective_point] in H36. extract_ex1_and_emp_in H36.

    (* Double (i/2)*A -> temp contains i*A.  *)
    single_step.
    repeat straightline.
    
    (* split out ai[i]*)
    split_stack_at_n_in (skipn (Z.to_nat (word.unsigned x4 * 160)) out) (x9.+word.unsigned x4 * 160) 160%nat H41. 
    (* copy temp into ai[i] *)
    single_step.

    repeat straightline. (* why doesn't straightline work with my if? *)
    (* if condition and saving into p_ai_uncached is next. *)
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    repeat straightline.
    split. (* if cases - this may get weird cause the rest doesn't depend on the if... *)

    (*  i < 8 -> copy i*A into p_ai_uncached *)
    single_step.
    (* oh wait, wrong assumption *)

    Admitted.

End WithParameters.
