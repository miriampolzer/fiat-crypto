Require Import coqutil.Byte coqutil.Word.LittleEndianList.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZUtil.ModInv.
Local Open Scope Z_scope.
Import bedrock2.Memory.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : F M_pos; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)

    (* special wrapper for copy so that compilation lemmas can recognize it *)
    fe_copy := (@id (F M_pos));

    (** function names **)
    mul : string; add : string; carry_add : string; sub : string; carry_sub : string; opp : string;
    square : string; scmula24 : string; inv : string;
    from_bytes : string; to_bytes : string;
    select_znz : string;

    felem_copy : string;
    from_word : string;
  }.

Class FieldParameters_ok {field_parameters : FieldParameters} := {
  M_prime : Znumtheory.prime M
}.

Class FieldRepresentation
      {field_parameters : FieldParameters}
      {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
       :=
  { felem_size_in_words : nat;
    felem := {x : list word | length x = felem_size_in_words};
    feval : list word -> F M_pos;

    feval_bytes : list byte -> F M_pos;
    felem_size_in_bytes : Z := (Z.of_nat felem_size_in_words) * bytes_per_word width; (* for stack allocation *)
    encoded_felem_size_in_bytes : nat; (* number of bytes when serialized *)
    bytes_in_bounds : list byte -> Prop;

    (* Memory layout *)
    FElem : word -> felem -> mem -> Prop := fun px x =>
      (array scalar (word.of_Z (bytes_per_word width)) px (proj1_sig x));
    FElemBytes : word -> list byte -> mem -> Prop :=
      fun addr bs =>
        (emp (length bs = encoded_felem_size_in_bytes
              /\ bytes_in_bounds bs)
         * array ptsto (word.of_Z 1) addr bs)%sep;

    bounds : Type;
    bounded_by : bounds -> list word -> Prop;
    (* for saturated implementations, loose/tight bounds are the same *)
    loose_bounds : bounds;
    tight_bounds : bounds;
  }.

  (* TODO: Replace Placeholder usage with $@. *)
Definition Placeholder
        {field_parameters : FieldParameters}
        {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
        {field_representation : FieldRepresentation(mem:=mem)}
        (p : word) (bs : list byte): mem -> Prop :=
(sep (map.of_list_word_at p bs)
  (emp (Z.of_nat (length bs) = felem_size_in_bytes))).

Section FunctionSpecs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Class UnOp (name: string) :=
    { un_model: F M_pos -> F M_pos;
      un_xbounds: bounds;
      un_outbounds: bounds }.

  Import WeakestPrecondition.

  Coercion Z.to_nat : Z >-> nat.

  (*this won't work...
  Definition felem_to_list (x : felem) : list word := proj1_sig x.
  Coercion felem_to_list : felem >-> (list word).
  *)

  #[warnings="-uniform-inheritance", global]
  Coercion felem_to_list (x : felem) : list word := proj1_sig x.

  

  Definition unop_spec {name} (op: UnOp name) :=
    fnspec! name (pout px : word) / (x : felem) out Rr,
    { requires tr mem :=
        bounded_by un_xbounds x
        /\ length out = felem_size_in_bytes
        /\ (exists Ra, (FElem px x * Ra)%sep mem)
        /\ (out$@pout * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out : felem,
          feval out = un_model (feval x)
          /\ bounded_by un_outbounds out
          /\ (FElem pout out * Rr)%sep mem' }.

  Instance spec_of_UnOp {name} (op: UnOp name) : spec_of name :=
    unop_spec op.

  Class BinOp (name: string) :=
    { bin_model: F M_pos -> F M_pos -> F M_pos;
      bin_xbounds: bounds;
      bin_ybounds: bounds;
      bin_outbounds: bounds }.

  Definition binop_spec  {name} (op: BinOp name) :=
    fnspec! name (pout px py : word) / (x y : felem) out Rr,
    { requires tr mem :=
        bounded_by bin_xbounds x
        /\ bounded_by bin_ybounds y
        /\ length out = felem_size_in_bytes
        /\ (exists Rx, (FElem px x * Rx)%sep mem)
        /\ (exists Ry, (FElem py y * Ry)%sep mem)
        /\ (out$@pout * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out : felem,
          feval out = bin_model (feval x) (feval y)
          /\ bounded_by bin_outbounds out
          /\ (FElem pout out * Rr)%sep mem' }.

  Instance spec_of_BinOp {name} (op: BinOp name) : spec_of name :=
    binop_spec op.

  Instance bin_mul : BinOp mul :=
    {| bin_model := F.mul; bin_xbounds := loose_bounds; bin_ybounds := loose_bounds; bin_outbounds := tight_bounds |}.
  Instance un_square : UnOp square :=
    {| un_model := fun x => F.pow x 2; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance bin_add : BinOp add :=
    {| bin_model := F.add; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance bin_carry_add : BinOp carry_add :=
    {| bin_model := F.add; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := tight_bounds |}.
  Instance bin_sub : BinOp sub :=
    {| bin_model := F.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance bin_carry_sub : BinOp carry_sub :=
    {| bin_model := F.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := tight_bounds |}.
  Instance un_scmula24 : UnOp scmula24 :=
    {| un_model := F.mul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
    {| un_model := F.inv; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.
  Instance un_opp : UnOp opp :=
    {| un_model := F.opp; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

  Instance spec_of_from_bytes : spec_of from_bytes :=
    fnspec! from_bytes (pout px : word) / (out bs : list byte) Rr,
    { requires tr mem :=
        (exists Ra, (array ptsto (word.of_Z 1) px bs * Ra)%sep mem)
        /\ length out = felem_size_in_bytes
        /\ (out$@pout * Rr)%sep mem
        /\ Field.bytes_in_bounds bs;
      ensures tr' mem' :=
        tr = tr' /\
        exists X : felem, feval X = feval_bytes bs
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * Rr)%sep mem' }.

  Instance spec_of_to_bytes : spec_of to_bytes :=
    fnspec! to_bytes (pout px : word) / (out : list byte) (x : felem) Rr,
    { requires tr mem :=
        (array ptsto (word.of_Z 1) pout out * Rr)%sep mem /\
        length out = encoded_felem_size_in_bytes /\
        (exists Ra, (FElem px x * Ra)%sep mem) /\
        bounded_by tight_bounds x;
      ensures tr' mem' := tr = tr' /\
        let bs := le_split encoded_felem_size_in_bytes (F.to_Z (feval x)) in
        (array ptsto (word.of_Z 1) pout bs * Rr)%sep mem' /\
        Field.bytes_in_bounds bs }.

  Instance spec_of_felem_copy : spec_of felem_copy :=
    fnspec! felem_copy (pout px : word) / (x : felem) out R,
    { requires tr mem :=
        length out = felem_size_in_bytes /\
        (FElem px x * out$@pout * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem px x * FElem pout x * R)%sep mem' }.

  Instance spec_of_from_word : spec_of from_word :=
    fnspec! from_word (pout x : word) / out R,
    { requires tr mem :=
        length out = felem_size_in_bytes /\
        (out $@ pout * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists X : felem, feval X = F.of_Z _ (word.unsigned x)
             /\ bounded_by tight_bounds X
             /\ (FElem pout X * R)%sep mem' }.

    Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.

    Instance spec_of_selectznz  : spec_of select_znz :=
    fnspec! select_znz (pout pc px py : word) / out Rout Rx Ry x y,
    {
        requires tr mem :=
        length out = felem_size_in_bytes /\
        (out $@ pout * Rout)%sep mem /\
        (FElem px x * Rx)%sep mem /\
        (FElem py y * Ry)%sep mem /\
        ZRange.is_bounded_by_bool (word.unsigned pc) bit_range = true;
        ensures tr' mem' :=
        if ((word.unsigned pc) =? 1)
            then ((FElem pout y * Rout)%sep mem')
            else ((FElem pout x * Rout)%sep mem')
    }.

    (*Parameters for word-by-word Montgomery arithmetic*)
    Definition r := 2 ^ width.
    Definition m' := Z.modinv (- M) r.
    Definition r' := Z.modinv (r) M.

    Definition from_mont_model x := F.mul x (@F.of_Z M_pos (r' ^ (Z.of_nat felem_size_in_words)%Z)).
    Definition to_mont_model x := F.mul x (@F.of_Z M_pos (r ^ (Z.of_nat felem_size_in_words)%Z)).

    Instance un_from_mont {from_mont : string} : UnOp from_mont :=
      {| un_model := from_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

    Instance un_to_mont {to_mont : string} : UnOp to_mont :=
      {| un_model := to_mont_model; un_xbounds := tight_bounds; un_outbounds := loose_bounds|}.

End FunctionSpecs.

#[global]
Existing Instances spec_of_UnOp spec_of_BinOp bin_mul un_square bin_add bin_sub
         un_scmula24 un_inv spec_of_felem_copy spec_of_from_word.

Class FieldRepresentation_ok
      {field_parameters : FieldParameters}
      {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
      {field_representation : FieldRepresentation} := {
    relax_bounds :
      forall X : felem, bounded_by tight_bounds X
                        -> bounded_by loose_bounds X;
    felem_size_ok : felem_size_in_bytes <= 2^width
  }.

Section SpecProperties.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.    
  
  Lemma felem_length (x : felem) : Datatypes.length (felem_to_list x) = felem_size_in_words.
  Proof.
    cbv [felem_to_list]. destruct x. auto.
  Qed.

  (* nat equality is decidable, which means that all length proofs are equal and field
   elements are equal if their underlying lists are equal. *)
  Lemma eq_felem
      {x y : felem} : proj1_sig x = proj1_sig y -> x = y.
  Proof.
    destruct x as [x px], y as [y py].
    cbv [proj1_sig]. intro. subst.
    apply f_equal,  Eqdep_dec.UIP_dec. eapply Nat.eq_dec.
  Qed.

  Lemma bytes_per_as_Z : Memory.bytes_per (width:=width) access_size.word = Z.to_nat (bytes_per_word width).
  Proof.
    cbv [bytes_per_word bytes_per] in *; lia.
  Qed.
  Lemma bytes_per_of_nat_to_nat_id : Z.of_nat (Z.to_nat (bytes_per_word width)) = bytes_per_word width.
  Proof.
    pose Types.word_size_in_bytes_pos; lia.
  Qed.
  Hint Rewrite bytes_per_as_Z bytes_per_of_nat_to_nat_id : normalize_bytes_per.

  Lemma felem_size_in_bytes_mod :
         felem_size_in_bytes mod Memory.bytes_per_word width = 0.
  Proof. 
    apply Z_mod_mult.
  Qed.

  Lemma felem_size_in_bytes_mod_nat :
         (Z.to_nat felem_size_in_bytes mod Z.to_nat (Memory.bytes_per_word width) = 0)%nat.
  Proof. 
    pose proof Types.word_size_in_bytes_pos.
    cbv [bytes_per_word bytes_per felem_size_in_bytes] in *.
    rewrite Modulo.Z.mod_to_nat; try lia.
    rewrite Z_mod_mult. lia.
  Qed.

  Lemma ws2bs_felem_length (x : felem):
    length (ws2bs (width:=width) (Z.to_nat (bytes_per_word width)) x) = felem_size_in_bytes.
  Proof.
    rewrite ws2bs_length. rewrite felem_length.
    cbv [bytes_per_word felem_size_in_bytes] in *. lia.
  Qed.

  Lemma ws2bs_felem_width (x : felem):
    Z.of_nat (Datatypes.length (ws2bs (width:=width) (Z.to_nat (bytes_per_word width)) x)) <= 2 ^ width.
  Proof.
    destruct x. pose felem_size_ok. cbv [felem_size_in_bytes bytes_per_word bytes_per felem_to_list proj1_sig] in *.
    rewrite ws2bs_length. lia.
  Qed.

  Lemma bs2ws_felem_length bs : 
    length bs = felem_size_in_bytes ->
    length (bs2ws (word:=word) (bytes_per_word width) bs) = felem_size_in_words.
  Proof.
    intros H.
    pose felem_size_ok.
    pose Types.word_size_in_bytes_pos.
    pose felem_size_in_bytes_mod.
    cbv [felem_size_in_bytes] in *. rewrite bs2ws_length; try ZnWords; try lia.
    rewrite H. rewrite <- Z2Nat.inj_div; try lia.
    rewrite Z_div_mult; try lia. (* Neither lia nor ZnWords can solve this. *)
    rewrite H.
    rewrite Modulo.Z.mod_to_nat; try lia. (* Neither lia nor ZnWords can solve this. *)
  Qed.

  Lemma felem_to_bytes p x :
    Lift1Prop.iff1 (FElem p x) ((ws2bs (bytes_per_word width) x)$@p).
  Proof.
    cbv [FElem].
    epose proof (iff1ToEq (bytes_of_words _ _)) as Hbytes_of_words.
    epose proof (iff1ToEq (array1_iff_eq_of_list_word_at _ _ (ws2bs_felem_width _))) as Harray1_to_list_word_at.

    autorewrite with normalize_bytes_per in *.

    rewrite <- (Harray1_to_list_word_at).
    rewrite Hbytes_of_words.
    apply iff1_refl.
  Qed.

  Lemma felem_to_bytearray p x :
    Lift1Prop.iff1 (FElem p x) (array ptsto (word.of_Z 1) p (ws2bs (bytes_per_word width) x)).
  Proof.
    rewrite (iff1ToEq (felem_to_bytes _ _)).
    erewrite (iff1ToEq (array1_iff_eq_of_list_word_at _ _ (ws2bs_felem_width _))).
    apply iff1_refl.
  Qed.

  Program Definition bs2felem bs (H : length bs = felem_size_in_bytes) : felem := (bs2ws (bytes_per_word width) bs).
  Next Obligation.
    apply bs2ws_felem_length. assumption.
  Qed.

  Lemma felem_from_bytes p bs (H: length bs = felem_size_in_bytes) :
    Lift1Prop.iff1 (bs$@p) (FElem p (bs2felem bs H)).
  Proof.
    cbv [FElem].
    epose proof ((words_of_bytes _ _ _)) as Hwords_of_bytes.
    epose proof ((array1_iff_eq_of_list_word_at _ _ _)) as Harray1_to_list_word_at.

    autorewrite with normalize_bytes_per in *.

    rewrite <- (Harray1_to_list_word_at).
    rewrite Hwords_of_bytes.
    apply iff1_refl.
 
    Unshelve.
    rewrite H. autorewrite with normalize_bytes_per. apply felem_size_in_bytes_mod_nat.
    rewrite H. pose proof felem_size_ok. lia.
  Qed.

  Lemma felem_from_bytearray p bs (H: length bs = felem_size_in_bytes) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) p bs) (FElem p (bs2felem bs H)).
  Proof.
    rewrite <- (iff1ToEq (felem_from_bytes _ _ _)).
    erewrite <-(iff1ToEq (array1_iff_eq_of_list_word_at _ _ _)).
    apply iff1_refl.

    Unshelve.
    rewrite H. pose proof felem_size_ok. lia.
  Qed.

  Lemma M_nonzero : M <> 0.
  Proof. cbv [M]. congruence. Qed.
End SpecProperties.

(* FElem -> bytes for ecancel_assumption_impl. *)
#[export] Hint Extern 1 (Lift1Prop.impl1 (FElem ?px ?x) (sepclause_of_map (map.of_list_word_at ?px _))) => (rewrite felem_to_bytes; exact impl1_refl) : ecancel_impl.

