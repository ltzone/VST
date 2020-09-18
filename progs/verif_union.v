Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import Memdata.

Definition Gprog : funspecs :=
    ltac:(with_library prog (@nil(ident*funspec))).


Definition g_spec :=
 DECLARE _g
 WITH i: Z
 PRE [ size_t]
   PROP() PARAMS(Vptrofs (Ptrofs.repr i)) SEP()
 POST [ size_t ]
   PROP() RETURN (Vptrofs (Ptrofs.repr i)) SEP().

Lemma body_g: semax_body Vprog Gprog f_g g_spec.
Proof.
start_function.
forward.
forward.
forward.
cancel.
Qed.

Lemma decode_float32_int32:
  forall (bl: list memval) (x: float32),
 size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
 decode_val Mfloat32 bl = Vsingle x ->
 decode_val Mint32 bl = Vint (Float32.to_bits x).
Proof.
intros.
unfold decode_val,decode_int,rev_if_be in *.
destruct (proj_bytes bl) eqn:?H.
inv H0.
rewrite Float32.to_of_bits. auto.
inv H0.
Qed.

Lemma NOT_decode_int32_float32:
  Archi.ptr64=false ->
 ~ (forall (bl: list memval) (x: float32),
     size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
     decode_val Mint32 bl = Vint (Float32.to_bits x) ->
     decode_val Mfloat32 bl = Vsingle x).
(* This lemma illustrates a problem: it is NOT the case that
   if (bl: list memval) decodes to Vint (Float32.to_bits x) 
  then it also decodes to  Vsingle x.   
  See https://github.com/AbsInt/CompCert/issues/207  for a description
  of the problem; and see https://github.com/PrincetonUniversity/VST/issues/429
  for a description of the solution,  forward_store_union_hack  *)
Proof.
intro Hp.
intro.
set (x := Float32.zero). (* nothing special about zero, any value would do *)
set (i := Float32.to_bits x).
set (bl := [Fragment (Vint i) Q32 3; Fragment (Vint i) Q32 2; Fragment (Vint i) Q32 1; Fragment (Vint i) Q32 0]).
specialize (H bl x).
specialize (H (eq_refl _)).
assert (decode_val Mint32 bl = Vint (Float32.to_bits x)).
unfold decode_val, bl.
rewrite Hp.
simpl.
destruct (Val.eq (Vint i) (Vint i)); [ | congruence].
destruct (quantity_eq Q32 Q32); [ | congruence].
simpl.
reflexivity.
specialize (H H0).
clear - H. subst bl i.
unfold decode_val in H.
simpl in H. inversion H.
Qed.

Lemma fabs_float32_lemma:
  forall x: float32,
  Float32.of_bits (Int.and (Float32.to_bits x) (Int.repr 2147483647)) =
  Float32.abs x.
Proof.
Admitted.  (* Provable in the Flocq theory, we hope *)

Module Single.

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float32
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vsingle x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vsingle (Float32.abs x)) SEP().

Lemma union_field_address: forall id,
  tl composites = (Composite id Union ((_f, tfloat) :: (_i, tuint) :: nil) noattr :: nil) ->
 forall p,
  field_address (Tunion id noattr) [UnionField _f] p = field_address (Tunion id noattr) [UnionField _i] p.
Proof.
  intros.
  inversion H.
  assert (field_compatible (Tunion id noattr) [UnionField _f] p 
               <-> field_compatible (Tunion id noattr) [UnionField _i] p).
2: subst id;  unfold field_address; if_tac; if_tac; auto; tauto.
subst id.
  rewrite !field_compatible_cons; simpl.
  unfold in_members; simpl.
  tauto.
Qed.

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
entailer!.
f_equal.
apply fabs_float32_lemma.
Qed.
End Single.

Module Float.

 (* This experiment shows what kind of error message you get
   if you put the wrong LOCAL precondition.
   In fact, Vfloat x is wrong, leading to an unsatisfying precondition,
   it must be Vsingle. *)

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vfloat x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vfloat (Float.abs x)) SEP().

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
try (start_function; fail 99).
Abort.

End Float.
