Require Import floyd.base.
Local Open Scope logic.

Lemma nth_map':
  forall {A B} (f: A -> B) d d' i al,
  (i < length al)%nat ->
   nth i (map f al) d = f (nth i al d').
Proof.
induction i; destruct al; simpl; intros; try omega; auto.
apply IHi; omega.
Qed.

Lemma isptr_offset_val':
 forall i p, isptr p -> isptr (offset_val i p).
Proof. intros. destruct p; try contradiction; apply I. Qed.
Hint Resolve isptr_offset_val': norm.

Lemma sem_add_pi_ptr:
   forall t p i, 
    isptr p ->
    sem_add_pi t p (Vint i) = Some (offset_val (Int.mul (Int.repr (sizeof t)) i) p).
Proof. intros. destruct p; try contradiction. reflexivity. Qed.
Hint Rewrite sem_add_pi_ptr using (solve [auto with norm]) : norm.

Lemma force_val_e:
 forall v, force_val (Some v) = v. 
Proof. reflexivity. Qed.
Hint Rewrite force_val_e: norm.

Lemma sem_cast_neutral_ptr:
  forall p, isptr p -> sem_cast_neutral p = Some p.
Proof. intros. destruct p; try contradiction; reflexivity. Qed.
Hint Rewrite sem_cast_neutral_ptr using (solve [auto with norm]): norm.

Lemma sizeof_tuchar: sizeof tuchar = 1%Z.
Proof. reflexivity. Qed.
Hint Rewrite sizeof_tuchar: norm.

Hint Rewrite Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r : norm.

Definition nullval : val := Vint Int.zero.

Lemma writable_share_top: writable_share Tsh.
Admitted.
Hint Resolve writable_share_top.

Ltac safe_auto_with_closed := 
   (* won't instantiate evars by accident *)
 match goal with |- ?A => 
          solve [first [has_evar A | auto 50 with closed]]
 end.

Lemma closed_env_set:
 forall {B} i v (P: environ -> B) rho, 
     closed_wrt_vars (eq i) P -> 
     P (env_set rho i v) = P rho.
Proof.
 intros. hnf in H.
 symmetry; destruct rho; apply H.
 intros; simpl; destruct (ident_eq i i0). left; auto.
 right; rewrite Map.gso; auto.
Qed.
Hint Rewrite @closed_env_set using safe_auto_with_closed : norm.

Lemma subst_derives:
  forall id e P Q, P |-- Q -> subst id e P |-- subst id e Q.
Proof.
 intros. intro rho. unfold subst. apply H.
Qed.

(* no "semax" in this file, just assertions. *)
Global Transparent Int.repr.

Lemma liftTrue: forall rho, `True rho.
Proof. intro. unfold_lift; apply I. Qed.
Hint Resolve liftTrue.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
extensionality ek vl.
if_tac; normalize.
subst ek.
rewrite (prop_true_andp (EK_normal = _)) by auto.
auto.
apply pred_ext; normalize.
Qed.

Lemma normal_ret_assert_derives:
 forall (P Q: environ->mpred) rho,
  P rho |-- Q rho ->
  forall ek vl, normal_ret_assert P ek vl rho |-- normal_ret_assert Q ek vl rho.
Proof.
 intros.
 unfold normal_ret_assert; intros; normalize.
 simpl.
 apply andp_derives.
 apply derives_refl.
 apply andp_derives.
 apply derives_refl.
 auto.
Qed.
Hint Resolve normal_ret_assert_derives : norm.

Lemma normal_ret_assert_FF:
  forall ek vl, normal_ret_assert FF ek vl = FF.
Proof.
unfold normal_ret_assert. intros. normalize.
Qed.

Lemma frame_normal:
  forall P F, 
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (P * F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, normal_ret_assert.
normalize.
Qed.

Lemma frame_for1:
  forall Q R F, 
   frame_ret_assert (loop1_ret_assert Q R) F = 
   loop1_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, loop1_ret_assert.
destruct ek; normalize.
Qed.

Lemma frame_loop1:
  forall Q R F, 
   frame_ret_assert (loop2_ret_assert Q R) F = 
   loop2_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, loop2_ret_assert.
destruct ek; normalize.
Qed.


Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_loop1 
                 overridePost_normal: ret_assert.

Hint Rewrite eval_id_same : norm.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.

Hint Resolve @TT_right.

Hint Rewrite Int.sub_idem Int.sub_zero_l  Int.add_neg_zero : norm.

Lemma temp_types_init_same:
 forall Delta id t b, (temp_types Delta)!id = Some (t,b) ->
                         (temp_types (initialized id Delta)) ! id = Some (t,true).
Proof.
intros.
destruct Delta; simpl in *.
unfold initialized; simpl. rewrite H.
unfold temp_types; simpl.
rewrite PTree.gss; auto.
Qed.


Lemma type_eq_refl:
 forall t, proj_sumbool (type_eq t t) = true.
Proof.
intros.
apply proj_sumbool_is_true.
auto.
Qed.

Lemma overridePost_overridePost:
 forall P Q R, overridePost P (overridePost Q R) = overridePost P R.
Proof.
intros.
unfold overridePost.
extensionality ek vl; simpl.
if_tac; auto.
Qed.
Hint Rewrite overridePost_overridePost : norm.

Lemma overridePost_normal':
  forall P R, overridePost P R EK_normal None = P.
Proof.
 intros. unfold overridePost. rewrite if_true by auto.
 apply prop_true_andp. auto.
Qed.
Hint Rewrite overridePost_normal' : ret_assert.

Lemma eval_expr_Etempvar: 
  forall i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
Hint Rewrite eval_expr_Etempvar : eval.

Lemma eval_expr_binop: forall op a1 a2 t, eval_expr (Ebinop op a1 a2 t) = 
          `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1)  (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_binop : eval.

Lemma eval_expr_unop: forall op a1 t, eval_expr (Eunop op a1 t) = 
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_unop : eval.

Hint Unfold closed_wrt_modvars : closed. 

Lemma closed_wrt_local: forall S P, closed_wrt_vars S P -> closed_wrt_vars S (local P).
Proof.
intros.
hnf in H|-*; intros.
specialize (H _ _ H0).
unfold local, lift1.
f_equal; auto.
Qed.
Hint Resolve closed_wrt_local : closed.

Lemma closed_wrt_lift0: forall {A} S (Q: A), closed_wrt_vars S (lift0 Q).
Proof.
intros.
intros ? ? ?.
unfold lift0; auto.
Qed.
Hint Resolve closed_wrt_lift0 : closed. (*
Hint Extern 2 (@closed_wrt_vars _ _ _) => apply closed_wrt_lift0 : closed. (* match even if need some beta-eta conversion *)
*)

Lemma closed_wrt_lift0C: forall {B} S (Q: B), 
   closed_wrt_vars S (@liftx (LiftEnviron B) Q).
Proof.
intros.
intros ? ? ?.
unfold_lift; auto.
Qed.
Hint Resolve @closed_wrt_lift0C: closed.

Lemma closed_wrt_lift1: forall {A}{B} S (f: A -> B) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (lift1 f P).
Proof.
intros.
intros ? ? ?. specialize (H _ _ H0).
unfold lift1; f_equal; auto.
Qed.
Hint Resolve closed_wrt_lift1 : closed. (*
Hint Extern 2 (@closed_wrt_vars _ _ _) => apply closed_wrt_lift1 : closed. (* match even if need some beta-eta conversion *)
*)

Lemma closed_wrt_lift1C: forall {A}{B} S (f: A -> B) P, 
        closed_wrt_vars S P -> 
        closed_wrt_vars S (@liftx (Tarrow A (LiftEnviron B)) f P).
Proof.
intros.
intros ? ? ?. specialize (H _ _ H0).
unfold_lift; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift1C : closed.

Lemma closed_wrt_lift2: forall {A1 A2}{B} S (f: A1 -> A2 -> B) P1 P2, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S (lift2 f P1 P2).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H1).
specialize (H0 _ _ H1).
unfold lift2; f_equal; auto.
Qed.
Hint Resolve closed_wrt_lift2 : closed. (*
Hint Extern 2 (@closed_wrt_vars _ _ _) => apply closed_wrt_lift2 : closed. (* match even if need some beta-eta conversion *)
*)

Lemma closed_wrt_lift2C: forall {A1 A2}{B} S (f: A1 -> A2 -> B) P1 P2, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S (@liftx (Tarrow A1 (Tarrow A2 (LiftEnviron B))) f P1 P2).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H1).
specialize (H0 _ _ H1).
unfold_lift; f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift2C : closed.

Lemma closed_wrt_lift3: forall {A1 A2 A3}{B} S (f: A1 -> A2 -> A3 -> B) P1 P2 P3, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S P3 -> 
        closed_wrt_vars S (lift3 f P1 P2 P3).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H2).
specialize (H0 _ _ H2).
specialize (H1 _ _ H2).
unfold lift3; f_equal; auto.
Qed.
Hint Resolve closed_wrt_lift3 : closed. (*
Hint Extern 2 (@closed_wrt_vars _ _ _) => apply closed_wrt_lift3 : closed. (* match even if need some beta-eta conversion *)
*)

Lemma closed_wrt_lift3C: forall {A1 A2 A3}{B} S (f: A1 -> A2 -> A3 -> B) P1 P2 P3, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S P3 -> 
        closed_wrt_vars S (@liftx (Tarrow A1 (Tarrow A2 (Tarrow A3 (LiftEnviron B)))) f P1 P2 P3).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H2).
specialize (H0 _ _ H2).
specialize (H1 _ _ H2).
unfold_lift. f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift3C : closed.

Lemma closed_wrt_lift4: forall {A1 A2 A3 A4}{B} S (f: A1 -> A2 -> A3 -> A4 -> B)
       P1 P2 P3 P4,  
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S P3 -> 
        closed_wrt_vars S P4 -> 
        closed_wrt_vars S (lift4 f P1 P2 P3 P4).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H3).
specialize (H0 _ _ H3).
specialize (H1 _ _ H3).
specialize (H2 _ _ H3).
unfold lift4; f_equal; auto.
Qed.
Hint Resolve closed_wrt_lift4 : closed. (*
Hint Extern 2 (@closed_wrt_vars _ _ _) => apply closed_wrt_lift4 : closed. (* match even if need some beta-eta conversion *)
*)

Lemma closed_wrt_lift4C: forall {A1 A2 A3 A4}{B} S (f: A1 -> A2 -> A3 -> A4 -> B) P1 P2 P3 P4, 
        closed_wrt_vars S P1 -> 
        closed_wrt_vars S P2 -> 
        closed_wrt_vars S P3 -> 
        closed_wrt_vars S P4 -> 
        closed_wrt_vars S (@liftx (Tarrow A1 (Tarrow A2 (Tarrow A3 (Tarrow A4 (LiftEnviron B))))) f P1 P2 P3 P4).
Proof.
intros.
intros ? ? ?.
specialize (H _ _ H3).
specialize (H0 _ _ H3).
specialize (H1 _ _ H3).
specialize (H2 _ _ H3).
unfold liftx; simpl.
unfold lift. f_equal; auto.
Qed.
Hint Resolve @closed_wrt_lift3C : closed.

Lemma closed_wrt_const: 
 forall A (P: A) S, closed_wrt_vars S (fun rho: environ => P).
Proof.
intros. hnf; intros.
simpl. auto.
Qed.
Hint Resolve @closed_wrt_const : closed.

Lemma closed_wrt_eval_var:
  forall S id t, closed_wrt_vars S (eval_var id t).
Proof.
unfold closed_wrt_vars, eval_var; intros.
simpl.
auto.
Qed.
Hint Resolve closed_wrt_eval_var : closed.

Lemma closed_wrt_cmp_ptr : forall S e1 e2 c,
  expr_closed_wrt_vars S e1 ->
  expr_closed_wrt_vars S e2 ->
  closed_wrt_vars S (`(cmp_ptr_no_mem c) (eval_expr e1) (eval_expr e2)).
Proof.
intros. 

unfold closed_wrt_vars. intros.
super_unfold_lift. 
unfold expr_closed_wrt_vars in *. 
specialize (H rho te' H1). 
specialize (H0 rho te' H1). 
unfold cmp_ptr_no_mem. rewrite H0. rewrite H. 
reflexivity. 
Qed. 
Hint Resolve closed_wrt_cmp_ptr : closed. 

Lemma closed_wrt_eval_id: forall S i,
    ~ S i -> closed_wrt_vars S (eval_id i).
Proof.
intros.
intros ? ? ?.
unfold eval_id, force_val.
simpl.
destruct (H0 i).
contradiction.
rewrite H1; auto.
Qed.
Hint Resolve closed_wrt_eval_id : closed.

Lemma closed_wrt_get_result1 :
  forall (S: ident -> Prop) i , ~ S i -> closed_wrt_vars S (get_result1 i).
Proof.
intros. unfold get_result1. simpl.
 hnf; intros.
 simpl. f_equal.
apply (closed_wrt_eval_id _ _ H); auto.
Qed.
Hint Resolve closed_wrt_get_result1 : closed.


Lemma closed_wrt_andp: forall S (P Q: environ->mpred),
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P && Q).
Admitted.

Lemma closed_wrt_sepcon: forall S (P Q: environ->mpred),
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P * Q).
Admitted.

Lemma closed_wrt_emp {A} {ND: NatDed A} {SL: SepLog A}:
  forall S, closed_wrt_vars S emp.
Proof. repeat intro. reflexivity. Qed.
Hint Resolve (@closed_wrt_emp mpred Nveric Sveric) : closed.


Lemma closed_wrt_main_pre:
  forall prog u S, closed_wrt_vars S (main_pre prog u).
Admitted.
Lemma closed_wrt_globvars:
  forall S v, closed_wrt_vars S (globvars2pred v).
Admitted.
Hint Resolve closed_wrt_main_pre closed_wrt_globvars: closed.


Fixpoint temp_free_in (id: ident) (e: expr) := 
 match e with
 | Econst_int _ _ => false
 | Econst_long _ _ => false
 | Econst_float _ _ => false
 | Evar _ _ => false
 | Etempvar i _ => eqb_ident id i
 | Ederef e1 _ => temp_free_in id e1
 | Eaddrof e1 _ => temp_free_in id e1
 | Eunop _ e1 _ => temp_free_in id e1
 | Ebinop _ e1 e2 _ => orb (temp_free_in id e1) (temp_free_in id e2) 
 | Ecast e1 _ => temp_free_in id e1
 | Efield e1 _ _ => temp_free_in id e1
end.

Lemma closed_wrt_ideq: forall a b e,
  a <> b ->
  temp_free_in a e = false ->
  closed_wrt_vars (eq a) (fun rho => !! (eval_id b rho = eval_expr e rho)).
Proof.
Admitted.

Hint Resolve closed_wrt_andp closed_wrt_sepcon : closed.

Hint Extern 2 (closed_wrt_vars (eq _) _) => 
      (apply closed_wrt_ideq; [solve [let Hx := fresh in (intro Hx; inv Hx)] | reflexivity]) : closed.

(* Hint Resolve @Forall_cons @Forall_nil : closed.   don't add these, already in core HintDb *)

Lemma closed_wrt_not1:
  forall (i j: ident), 
   i<>j ->
   not (eq i j).
Proof.
intros.
hnf.
intros; subst; congruence.
Qed.
Hint Resolve closed_wrt_not1 : closed.


Lemma closed_wrt_tc_expr:
  forall Delta S e, expr_closed_wrt_vars S e ->
             closed_wrt_vars S (tc_expr Delta e).
Proof.
intros.
Admitted.
Hint Resolve closed_wrt_tc_expr : closed.


Lemma closed_wrt_tc_temp_id :
  forall Delta S e id t, expr_closed_wrt_vars S e ->
                         expr_closed_wrt_vars S (Etempvar id t) ->
             closed_wrt_vars S (tc_temp_id id t Delta e).
Admitted.
Hint Resolve closed_wrt_tc_temp_id : closed.


Lemma expr_closed_tempvar:
 forall S i t, ~ S i -> expr_closed_wrt_vars S (Etempvar i t).
Admitted.
Hint Resolve expr_closed_tempvar : closed.

Hint Extern 1 (not (@eq ident _ _)) => (let Hx := fresh in intro Hx; inversion Hx) : closed.

Lemma expr_closed_const_int:
  forall S i t, expr_closed_wrt_vars S (Econst_int i t).
Proof.
intros. unfold expr_closed_wrt_vars. simpl; intros.
super_unfold_lift. auto.
Qed.
Hint Resolve expr_closed_const_int : closed.

Lemma expr_closed_cast: forall S e t, 
     expr_closed_wrt_vars S e -> 
     expr_closed_wrt_vars S (Ecast e t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift.
 destruct (H rho te' H0); auto.
Qed.
Hint Resolve expr_closed_cast : closed.

Lemma expr_closed_field: forall S e f t,
  lvalue_closed_wrt_vars S e ->
  expr_closed_wrt_vars S (Efield e f t).
Proof.
 unfold lvalue_closed_wrt_vars, expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift.
 f_equal.
 f_equal. apply H.  auto.
Qed.
Hint Resolve expr_closed_field : closed.

Lemma expr_closed_binop: forall S op e1 e2 t, 
     expr_closed_wrt_vars S e1 -> 
     expr_closed_wrt_vars S e2 -> 
     expr_closed_wrt_vars S (Ebinop op e1 e2 t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift. f_equal; auto.
Qed.
Hint Resolve expr_closed_binop : closed.


Lemma expr_closed_unop: forall S op e t, 
     expr_closed_wrt_vars S e -> 
     expr_closed_wrt_vars S (Eunop op e t).
Proof.
 unfold expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift. f_equal; auto.
Qed.
Hint Resolve expr_closed_unop : closed.

Lemma closed_wrt_stackframe_of:
  forall S f, closed_wrt_vars S (stackframe_of f).
Admitted.
Hint Resolve closed_wrt_stackframe_of : closed.


Definition included {U} (S S': U -> Prop) := forall x, S x -> S' x.

Lemma closed_wrt_TT:
 forall  (S: ident -> Prop),
  closed_wrt_vars S (@TT (environ -> mpred) _).
Proof.
intros. hnf; intros. reflexivity.
Qed.
Hint Resolve closed_wrt_TT : closed.

Lemma closed_wrt_subset:
  forall (S S': ident -> Prop) (H: included S' S) B (f: environ -> B),
       closed_wrt_vars S f -> closed_wrt_vars S' f.
Proof.
intros. hnf. intros. specialize (H0 rho te').
apply H0.
intro i; destruct (H1 i); auto.
Qed.
Hint Resolve closed_wrt_subset : closed.

Lemma closed_wrt_Forall_subset:
  forall S S' (H: included S' S) B (f: list (environ -> B)),
 Forall (closed_wrt_vars S) f ->
 Forall (closed_wrt_vars S') f.
Proof.
induction f; simpl; auto.
intro.
inv H0.
constructor.
apply (closed_wrt_subset _ _ H). auto.
auto.
Qed.

Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : norm.

Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
extensionality rho.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite Map.gso; auto.
Qed.

Lemma closed_wrt_map_subst:
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         map (subst id e) Q = Q.
Proof.
induction Q; intros.
simpl; auto.
inv H.
simpl; f_equal; auto.
apply closed_wrt_subst; auto.
Qed.
Hint Rewrite @closed_wrt_map_subst using safe_auto_with_closed : subst.
Hint Rewrite @closed_wrt_subst using safe_auto_with_closed : subst.

Lemma lvalue_closed_tempvar:
 forall S i t, ~ S i -> lvalue_closed_wrt_vars S (Etempvar i t).
Admitted.
Hint Resolve lvalue_closed_tempvar : closed.


Lemma expr_closed_addrof: forall S e t, 
     lvalue_closed_wrt_vars S e -> 
     expr_closed_wrt_vars S (Eaddrof e t).
Proof.
 unfold lvalue_closed_wrt_vars, expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift. apply H.  auto.
Qed.
Hint Resolve expr_closed_addrof : closed.

Lemma lvalue_closed_field: forall S e f t,
  lvalue_closed_wrt_vars S e ->
  lvalue_closed_wrt_vars S (Efield e f t).
Proof.
 unfold lvalue_closed_wrt_vars, expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift. f_equal; apply H.  auto.
Qed.
Hint Resolve lvalue_closed_field : closed.

Lemma lvalue_closed_deref: forall S e t,
  expr_closed_wrt_vars S e ->
  lvalue_closed_wrt_vars S (Ederef e t).
Proof.
 unfold lvalue_closed_wrt_vars, expr_closed_wrt_vars; intros.
 simpl.
 super_unfold_lift. f_equal; apply H.  auto.
Qed.
Hint Resolve lvalue_closed_deref : closed.

Hint Resolve  eval_expr_Etempvar.

Lemma eval_expr_Etempvar' : forall i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
Hint Resolve  eval_expr_Etempvar'.


Lemma subst_eval_id_eq:
 forall id v, subst id v (eval_id id) = v.
Proof. unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite Map.gss; auto.
Qed.

Lemma subst_eval_id_neq:
  forall id v j, id<>j -> subst id v (eval_id j) = eval_id j.
Proof.
    unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite Map.gso; auto.
Qed.

Hint Rewrite subst_eval_id_eq : subst.
Hint Rewrite subst_eval_id_neq using safe_auto_with_closed : subst.


Lemma liftx3_liftx2:
 forall {A1 A2 A3 B} f (x: A1),
  @liftx (Tarrow A1 (Tarrow A2 (Tarrow A3 (LiftEnviron B)))) f (@liftx (LiftEnviron A1) x) =
  @liftx (Tarrow A2 (Tarrow A3 (LiftEnviron B))) (f x).
Proof. reflexivity. Qed.

Lemma liftx2_liftx1:
 forall {A1 A2 B} f (x: A1),
  @liftx (Tarrow A1 (Tarrow A2 (LiftEnviron B))) f (@liftx (LiftEnviron A1) x) =
  @liftx (Tarrow A2 (LiftEnviron B)) (f x).
Proof. reflexivity. Qed.

Lemma liftx1_liftx0:
  forall {A1 B} f (x: A1),
  @liftx (Tarrow A1 (LiftEnviron B)) f (@liftx (LiftEnviron A1) x) =
  @liftx (LiftEnviron B) (f x).
Proof. reflexivity. Qed.

Hint Rewrite @liftx3_liftx2 @liftx2_liftx1 @liftx1_liftx0 : norm.

Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @lift1_lift0 : norm.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.
Hint Rewrite const_liftx0 : norm.

Lemma lift_identity:
  forall A f, `(fun v: A => v) f = f.
Proof. intros. reflexivity. Qed.
Hint Rewrite lift_identity : norm.

Lemma tc_eval_gvar_zero:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some (Global_var t) ->
            exists b, eval_var i t rho = Vptr b Int.zero.
Proof.
 intros. unfold eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
  destruct H as [_ [? [? ?]]].
  unfold typecheck_var_environ in  *. 
  unfold typecheck_glob_environ in *. 
  unfold same_env in *. 
  destruct (H3 _ _ H1).
  unfold Map.get; rewrite H4.
  destruct (H2 _ _ H1) as [b [? ?]].
   rewrite H5. simpl. rewrite eqb_type_refl.
  eauto.
  destruct H4; congruence.
Qed.

Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some (Global_var t) ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros.
 destruct (tc_eval_gvar_zero _ _ _ _ H H0 H1) as [b ?].
 rewrite H2; apply I.
Qed.

Lemma local_lift2_and: forall P Q, local (`and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local; super_unfold_lift.   
simpl.
 apply pred_ext; normalize. destruct H; normalize.
Qed.
Hint Rewrite local_lift2_and : norm.

Lemma subst_TT {A}{NA: NatDed A}: forall i v, subst i v TT = TT.
Admitted.
Lemma subst_FF {A}{NA: NatDed A}: forall i v, subst i v FF = FF.
Admitted.
Hint Rewrite @subst_TT @subst_FF: subst.
Hint Rewrite (@subst_TT mpred Nveric) (@subst_FF mpred Nveric): subst.

Lemma eval_expr_Econst_int: forall i t, eval_expr (Econst_int i t) = `(Vint i).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_Econst_int : eval.

Lemma subst_eval_var:
  forall id v id' t, subst id v (eval_var id' t) = eval_var id' t.
Proof.
intros. unfold subst, eval_var. extensionality rho.
simpl. auto.
Qed.
Hint Rewrite subst_eval_var : subst.

Lemma subst_local: forall id v P,
  subst id v (local P) = local (subst id v P).
Proof. reflexivity. Qed.
Hint Rewrite subst_local : subst.

Lemma eval_lvalue_Ederef:
  forall e t, eval_lvalue (Ederef e t) = `force_ptr (eval_expr e).
Proof. reflexivity. Qed.
Hint Rewrite eval_lvalue_Ederef : eval.

Lemma local_lift0_True:     local (`True) = TT.
Proof. reflexivity. Qed.
Hint Rewrite local_lift0_True : norm.

Lemma overridePost_EK_return: 
  forall Q P, overridePost Q P EK_return = P EK_return.
Proof. unfold overridePost; intros. 
  extensionality vl rho; rewrite if_false by congruence. auto.
Qed.
Hint Rewrite overridePost_EK_return : ret_assert.

Lemma frame_ret_assert_emp:
  forall P, frame_ret_assert P emp = P.
Proof. intros.
 extensionality ek. extensionality vl. extensionality rho.
 unfold frame_ret_assert.
 rewrite sepcon_emp. auto.
Qed.

Hint Rewrite frame_ret_assert_emp : ret_assert.

Lemma frame_ret_assert_EK_return:
 forall P Q vl, frame_ret_assert P Q EK_return vl =  P EK_return vl * Q.
Proof. reflexivity. Qed.
Hint Rewrite frame_ret_assert_EK_return : ret_assert.

Lemma function_body_ret_assert_EK_return:
  forall t P vl, function_body_ret_assert t P EK_return vl = bind_ret vl t P.
Proof. reflexivity. Qed.
Hint Rewrite function_body_ret_assert_EK_return : ret_assert.

Lemma bind_ret1_unfold:
  forall v t Q, bind_ret (Some v) t Q = !!tc_val t v && `Q (make_args (ret_temp :: nil)(v::nil)).
Proof. reflexivity. Qed.
Hint Rewrite bind_ret1_unfold : norm.

Lemma bind_ret1_unfold':
  forall v t Q rho, 
  bind_ret (Some v) t Q rho = !!(tc_val t v) && Q (make_args (ret_temp::nil)(v::nil) rho).
Proof.
 intros. reflexivity.
Qed.
Hint Rewrite bind_ret1_unfold' : norm.  (* put this in AFTER the unprimed version, for higher priority *)

Lemma normal_ret_assert_derives': 
  forall P Q, P |-- Q -> normal_ret_assert P |-- normal_ret_assert Q.
Proof. 
  intros. intros ek vl rho. apply normal_ret_assert_derives. apply H.
Qed.

Lemma normal_ret_assert_eq:
  forall P ek vl, normal_ret_assert P ek vl =
             (!! (ek=EK_normal) && (!! (vl=None) && P)).
Proof. reflexivity. Qed.
(* Hint Rewrite normal_ret_assert_eq: ret_assert.  NO! *)

Lemma normal_ret_assert_elim:
 forall P, normal_ret_assert P EK_normal None = P.
Proof.
intros. unfold normal_ret_assert.
repeat rewrite prop_true_andp by auto.
auto.
Qed.

Lemma overridePost_EK_break:
 forall P Q, overridePost P Q EK_break None = Q EK_break None.
Proof. intros. unfold overridePost.
 rewrite if_false; congruence.
Qed.

Lemma loop1_ret_assert_EK_break:
 forall P Q, loop1_ret_assert P Q EK_break None = Q EK_normal None.
Proof. intros. reflexivity.
Qed.

Hint Rewrite overridePost_EK_break loop1_ret_assert_EK_break
  normal_ret_assert_elim : ret_assert.

Lemma loop1_ret_assert_normal:
  forall P Q, loop1_ret_assert P Q EK_normal None = P.
Proof. reflexivity. Qed.
Hint Rewrite loop1_ret_assert_normal: ret_assert.

Lemma unfold_make_args': forall fsig args rho,
    make_args' fsig args rho = make_args (map (@fst _ _) (fst fsig)) (args rho) rho.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args' : norm.
Lemma unfold_make_args_cons: forall i il v vl rho,
   make_args (i::il) (v::vl) rho = env_set (make_args il vl rho) i v.
Proof. reflexivity. Qed.
Lemma unfold_make_args_nil: make_args nil nil = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite unfold_make_args_cons unfold_make_args_nil : norm.

Lemma clear_make_args':
 forall (P: mpred) fsig args,
    @liftx (Tarrow environ (LiftEnviron mpred))
                    (@liftx (LiftEnviron mpred) P)
      (make_args' fsig args) = `P.
Proof. intros. reflexivity. Qed.
Hint Rewrite clear_make_args': norm.


Lemma eval_make_args':
  forall (Q: val -> Prop) i fsig args,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (@liftx (Tarrow val (LiftEnviron Prop)) Q (eval_id i))
   (make_args' fsig args) =
  `Q (`(eval_id i) (make_args' fsig args)).
Proof. reflexivity. Qed.
Hint Rewrite eval_make_args' : norm.

Lemma eval_make_args_same:
 forall i t fsig t0 tl (e: expr) el,
 `(eval_id i) (make_args' ((i,t)::fsig, t0) (eval_exprlist (t::tl) (e::el))) = 
   `force_val (`(sem_cast (typeof e) t) (eval_expr e)).
Proof.
intros.
extensionality rho.
unfold make_args'.
unfold_lift.
simpl.
unfold eval_id.
simpl.
rewrite Map.gss.
simpl.
unfold_lift.
reflexivity.
Qed.

Lemma eval_make_args_other:
 forall i j fsig t0 t t' tl (e: expr) el,
   i<>j ->
  `(eval_id i) (make_args' ((j,t)::fsig, t0) (eval_exprlist (t'::tl) (e::el))) =
   `(eval_id i) (make_args' (fsig, t0) (eval_exprlist tl el)).
Proof.
intros. extensionality rho.
unfold make_args'.
unfold_lift.
simpl.
unfold eval_id.
simpl.
rewrite Map.gso; auto.
Qed.

Hint Rewrite eval_make_args_same : norm.
Hint Rewrite eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Infix "oo" := Basics.compose (at level 54, right associativity).
Arguments Basics.compose {A B C} g f x / .

Lemma compose_backtick:
  forall A B C (F: B -> C) (G: A -> B) (J: environ -> A),
   `F (`G  J) = `(Basics.compose F G) J.
Proof. reflexivity. Qed.
Hint Rewrite compose_backtick : norm.

Lemma compose_eval_make_args_same:
  forall (Q: val -> Prop) i t fsig t0 tl e el,
  @liftx (Tarrow environ (LiftEnviron Prop))
      (Q oo (eval_id i)) (make_args' ((i,t)::fsig,t0) (eval_exprlist (t::tl) (e::el))) =
  `Q (`force_val (`(sem_cast (typeof e) t) (eval_expr e))).
Proof. 
  intros.
  rewrite <- compose_backtick.
  f_equal. apply eval_make_args_same.
Qed.

Lemma compose_eval_make_args_other:
  forall Q i j fsig t0 t t' tl (e: expr) el,
   i<>j ->
    @liftx (Tarrow environ (LiftEnviron Prop))
     (Q oo (eval_id i)) (make_args' ((j,t)::fsig, t0) (eval_exprlist (t'::tl) (e::el))) =
     `Q (`(eval_id i) (make_args' (fsig, t0) (eval_exprlist tl el))).
Proof.
  intros.
  rewrite <- compose_backtick.
  f_equal. apply eval_make_args_other; auto.
Qed.

Hint Rewrite compose_eval_make_args_same : norm.
Hint Rewrite compose_eval_make_args_other using (solve [clear; intro Hx; inversion Hx]) : norm.

Lemma substopt_unfold {A}: forall id v, @substopt A (Some id) v = @subst A id v.
Proof. reflexivity. Qed.
Lemma substopt_unfold_nil {A}: forall v (P:  environ -> A), substopt None v P = P.
Proof. reflexivity. Qed.
Hint Rewrite @substopt_unfold @substopt_unfold_nil : subst.

Lemma get_result_unfold: forall id, get_result (Some id) = get_result1 id.
Proof. reflexivity. Qed.
Lemma get_result_None: get_result None = globals_only.
Proof. reflexivity. Qed.
Hint Rewrite get_result_unfold get_result_None : norm.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) ! i = None /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros. 
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl. 
destruct H as [_ [? [? ?]]].
destruct (H2 i g H0).
unfold Map.get; rewrite H3; auto.
destruct H3.
congruence.
Qed.

Hint Rewrite elim_globals_only using (split3; [eassumption | reflexivity.. ]) : norm.

Lemma elim_globals_only': 
 forall a: mpred, 
 (@liftx (Tarrow environ (LiftEnviron mpred)) (`a) globals_only) = `a.
Proof. reflexivity. Qed.
Hint Rewrite elim_globals_only' : norm.

Lemma eval_expropt_Some: forall e, eval_expropt (Some e) = `Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: eval_expropt None = `None.
Proof. reflexivity. Qed.
Hint Rewrite eval_expropt_Some eval_expropt_None : eval.

Definition Ews (* extern_write_share *) := Share.splice extern_retainer Tsh.

Lemma globfun_eval_var:
  forall Delta rho id f,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  (Global_func f) ->
     exists b, exists z,  eval_var id (type_of_funspec f) rho = Vptr b z /\
             ge_of rho id = Some (Vptr b z, type_of_funspec f).
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
repeat rewrite andb_true_iff in H.
destruct H as [Ha [Hb [Hc Hd]]].
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [Hc Hc']].
exists b; exists Int.zero.
unfold eval_var; simpl.
apply Hd in H1. 
destruct H1 as [? | [? ?]]; [ | congruence].
unfold Map.get; rewrite H. rewrite Hc.
rewrite eqb_type_refl; auto.
Qed.

Lemma globvar_eval_var:
  forall Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  (Global_var t) ->
     exists b,  eval_var id t rho = Vptr b Int.zero /\ ge_of rho id = Some (Vptr b Int.zero, t).
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
destruct H as [Ha [Hb [Hc Hd]]].
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [Hc Hc']].
exists b.
unfold eval_var; simpl.
apply Hd in H1. 
destruct H1 as [? | [? ?]]; [ | congruence].
unfold Map.get; rewrite H. rewrite Hc.
rewrite eqb_type_refl; auto.
Qed.

Lemma globvars2pred_unfold: forall vl rho, 
    globvars2pred vl rho = 
    fold_right sepcon emp (map (fun idv => globvar2pred idv rho) vl).
Proof. intros. unfold globvars2pred.
   induction vl; simpl; auto. normalize; f_equal; auto.
Qed.
Hint Rewrite globvars2pred_unfold : norm.

Lemma writable_Ews: writable_share Ews.
Admitted.
Hint Resolve writable_Ews.


 Lemma offset_offset_val:
  forall v i j, offset_val j (offset_val i v) = offset_val (Int.add i j) v.
Proof. intros; unfold offset_val.
 destruct v; auto. rewrite Int.add_assoc; auto.
Qed.
Hint Rewrite offset_offset_val: norm.

Lemma add_repr: forall i j, Int.add (Int.repr i) (Int.repr j) = Int.repr (i+j).
Proof. intros.
  rewrite Int.add_unsigned.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.
Hint Rewrite add_repr : norm.

Lemma mul_repr:
 forall x y, Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof.
intros. unfold Int.mul.
apply Int.eqm_samerepr.
repeat rewrite Int.unsigned_repr_eq.
apply Int.eqm_mult; unfold Int.eqm; apply Int.eqmod_sym;
apply Int.eqmod_mod; compute; congruence.
Qed.
Hint Rewrite mul_repr : norm.

Lemma sub_repr: forall i j,
  Int.sub (Int.repr i) (Int.repr j) = Int.repr (i-j).
Proof.
  intros.
 unfold Int.sub.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_sub; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.
Hint Rewrite sub_repr : norm.

Lemma ltu_repr: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_repr_false: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma int_add_assoc1:
  forall z i j, Int.add (Int.add z (Int.repr i)) (Int.repr j) = Int.add z (Int.repr (i+j)).
Admitted.
Hint Rewrite int_add_assoc1 : norm.

Lemma align_0: forall z, 
    z > 0 -> align 0 z = 0.
Proof. unfold align; intros. rewrite Zdiv_small; omega.
Qed.
Hint Rewrite align_0 using omega : norm.

Lemma deref_noload_tarray:
  forall ty n, deref_noload (tarray ty n) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_tarray : norm.

Lemma deref_noload_Tarray:
  forall ty n a, deref_noload (Tarray ty n a) = (fun v => v).
Proof. 
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_Tarray : norm.


Lemma TT_sepcon {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
   forall (P: A), P |-- (TT * P).
Proof. intros. rewrite sepcon_comm; apply sepcon_TT.
Qed.

Hint Resolve (@derives_refl mpred _) : cancel.
Hint Resolve (@now_later mpred _ _) : cancel.

Lemma cancel1_start:
 forall P Q : mpred, 
   P |-- Q * emp ->
   P |-- Q.
Proof. intros. rewrite sepcon_emp in H; auto.
Qed.

Lemma cancel1_here:
  forall P P' Q1 Q2 Q3 : mpred, 
  P' |-- Q2 ->
  P |-- Q1 * Q3 ->
  P * P' |-- Q1 * Q2 * Q3.
Proof.
intros. rewrite (sepcon_comm Q1).
rewrite sepcon_assoc.  rewrite sepcon_comm. apply sepcon_derives; auto.
Qed.

Lemma cancel1_next:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * (Q2 * Q3) ->
   P |-- Q1 * Q2 * Q3.
Proof. intros. rewrite sepcon_assoc; auto. Qed.

Lemma cancel1_last:
  forall P P' Q2 Q3 : mpred,
  P' |-- Q2 ->
  P |-- Q3 ->
  P * P' |-- Q2 * Q3.
Proof.
 intros. rewrite sepcon_comm; apply sepcon_derives; auto.
Qed.

Lemma cancel1_finish1:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * Q2 * Q3 ->
   P |-- Q1 * (Q2 * Q3).
Proof.
 intros. rewrite <- sepcon_assoc. auto.
Qed.

Lemma cancel1_finish2:
  forall P Q : mpred, 
    P |-- Q ->
   P |-- Q * emp.
Proof. intros. rewrite sepcon_emp; auto.
Qed.

Ltac cancel1 := 
 first [
   simple apply cancel1_here; [solve [eauto with nocore cancel] | ]
 | simple apply cancel1_next; cancel1
 | simple apply cancel1_last; [solve [eauto with nocore cancel] | ]
 ].

Ltac cancel2 := 
  simple apply cancel1_start;
  cancel1;
  repeat simple apply cancel1_finish1; 
  try simple apply cancel1_finish2.

Ltac lift1 a e1 rho  :=
 match e1 with
 | lift0 rho => constr:(a)
 | lift0 ?a1 => constr: (lift0 (a a1))
 | _ => constr:(lift1 a e1)
 end.

Ltac lift2 a e1 e2 rho :=
 match e1 with
 |  lift0 ?a1 => lift1 (a a1) e2 rho
 | _ => constr:(lift2 a e1 e2)
 end.

Ltac lift3 a e1 e2 e3 rho :=
 match e1 with
 |  lift0 ?a1 => lift2 (a a1) e2 e3 rho
 | _ => constr:(lift3 a e1 e2 e3)
 end.

Ltac lift4 a e1 e2 e3 e4 rho :=
 match e1 with
 |  lift0 ?a1 => lift3 (a a1) e2 e3 e4 rho
 | _ => constr:(lift4 a e1 e2 e3 e4)
 end.

Ltac abstract_env rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp (environ->mpred) _ _)
   | @sepcon mpred _ _ ?e1 ?e2 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
       in constr:(@sepcon (environ->mpred) _ _ e1' e2')
   | ?a0 ?a1 ?a2 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1  in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1 a2) e1' e2' e3' e4' rho
   | ?a0 ?a1 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1) e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 ?e4 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift4 a0 e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 a0 e1' e2' e3' rho
   | ?a0 ?e1 ?e2 => 
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
      in lift2 a0 e1' e2' rho
   | ?a0 ?e1 => let e1' := abstract_env rho e1 in lift1 a0 e1' rho
   | rho => constr: (lift1)
   | ?a => constr:(lift0 a)
   end.

Lemma cancel_frame0{A}{ND: NatDed A}{SL: SepLog A}:
  forall rho: environ, emp rho |-- fold_right sepcon emp nil rho.
Proof. intro; apply derives_refl. Qed.

Lemma cancel_frame2: forall (P Q: environ->mpred) F (rho: environ),
     Q rho |-- 	fold_right sepcon emp F rho ->
    (P * Q) rho |-- fold_right sepcon emp (P::F) rho.
Proof. intros. simpl. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame1: forall P (rho: environ), 
         P rho |-- fold_right sepcon emp (P::nil) rho.
Proof. intros. unfold fold_right. rewrite sepcon_emp; apply derives_refl.
Qed.

Ltac fixup_lifts := 
 repeat 
 match goal with
 | |- appcontext [@lift0 mpred] => change (@lift0 mpred) with (@liftx (LiftEnviron mpred))
 | |- appcontext [@lift1 ?A] => change (@lift1 A mpred) with (@liftx (Tarrow A (LiftEnviron mpred)))
 | |- appcontext [@lift2 ?A ?B] =>  change (@lift2 A B mpred) with (@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))))
 | |- appcontext [@lift3 ?A ?B ?C] => change (@lift3 A B C mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (LiftEnviron mpred)))))
 | |- appcontext [@lift4 ?A ?B ?C ?D] => change (@lift4 A B C D mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (Tarrow D (LiftEnviron mpred))))))
 end.

Ltac cancel_frame := 
match goal with |- ?P |-- fold_right _ _ ?F ?rho  =>
     let P' := abstract_env rho P in  
       change ( P' rho |-- fold_right sepcon emp F rho);
   fixup_lifts; cbv beta;
    repeat rewrite sepcon_assoc;
    repeat apply cancel_frame2; 
    try (unfold F; apply cancel_frame1);
    try (instantiate (1:=nil) in (Value of F); unfold F; apply cancel_frame0)
 end.

Ltac cancel :=
repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
match goal with |- ?P |-- ?Q =>
  (* The "emp" is a marker to notice when one complete pass has been made *)
   apply derives_trans with (emp * P) ; [ rewrite (emp_sepcon P); apply derives_refl | ]
 end;
repeat rewrite <- sepcon_assoc;
repeat
match goal with 
   | |- sepcon _ emp |-- _ => fail 1
   | |- sepcon _ TT |-- _ => pull_left (@TT mpred _)
   | |- sepcon _ ?P' |-- _ => first [ cancel2 | pull_left P' ]
 end;
  repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
  pull_left (@TT mpred _);
  first [apply derives_refl
          | apply TT_right
          | apply sepcon_TT 
          | apply TT_sepcon
          | cancel_frame
          | idtac
          ].

Lemma exp_trivial {A}{NA: NatDed A}:
  forall {T: Type} (any: T) (P: A), exp (fun x:T => P) = P.
Proof.
 intros. apply pred_ext. apply exp_left; auto.
 apply exp_right with any; auto.
Qed.

Hint Rewrite @exp_trivial : norm.

(* Admitted: move these next two to assert_lemmas *)
Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.
Hint Rewrite tc_andp_TT1 tc_andp_TT2 : norm.

Lemma prop_derives {A}{ND: NatDed A}: 
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros; apply prop_left; intro; apply prop_right; auto.
Qed.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 =>  Int.cmpu Ceq n1 n2 = true  /\ Int.cmpu Ceq n1 (Int.repr 0) = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Lemma ptr_eq_e: forall v1 v2, ptr_eq v1 v2 -> v1=v2.
Proof.
intros. destruct v1; destruct v2; simpl in H; try contradiction.
pose proof (Int.eq_spec i i0). destruct H. 
rewrite H in H0. subst; auto.
destruct H; subst.
f_equal.
pose proof (Int.eq_spec i i0). rewrite H0 in H; auto.
Qed.

Lemma ptr_eq_True:
   forall p, is_pointer_or_null p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Int.eq_true. auto.
Qed.
Hint Rewrite ptr_eq_True using assumption : norm.

Lemma flip_lifted_eq:
  forall (v1: environ -> val) (v2: val),
    `eq v1 `v2 = `(eq v2) v1.
Proof.
intros. unfold_lift. extensionality rho. apply prop_ext; split; intro; auto.
Qed.
Hint Rewrite flip_lifted_eq : norm.

Lemma isptr_is_pointer_or_null: 
  forall v, isptr v -> is_pointer_or_null v.
Proof. intros. destruct v; inv H; simpl; auto.
Qed.
Hint Resolve isptr_is_pointer_or_null.

Lemma eval_var_isptr:
  forall Delta t i rho, 
            tc_environ Delta rho ->
            ((var_types Delta) ! i = Some t \/ 
             (var_types Delta)!i = None /\
            (glob_types Delta) ! i = Some (Global_var t)) ->
            type_is_volatile t = false ->
            isptr (eval_var i t rho).
Proof.
 intros. rename H1 into NONVOL.
  unfold isptr, eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
 repeat rewrite andb_true_iff in H.
  destruct H as [_ [? [? ?]]].
  hnf in H,H1.
  destruct H0.
  specialize (H _ _ H0). destruct H; rewrite H.
  rewrite eqb_type_refl.
  rewrite NONVOL. simpl. auto.
  destruct H0. 
  destruct (H1 _ _ H3) as [b [? ?]].
  rewrite H4. simpl.
 destruct (H2 _ _ H3).
 unfold Map.get; rewrite H6.
 rewrite eqb_type_refl. auto.
 destruct H6. congruence.
Qed.


Definition repable_signed (z: Z) :=
  Int.min_signed <= z <= Int.max_signed.

Definition repable_signed_dec (z: Z) : {repable_signed z}+{~repable_signed z}.
Proof.
 intros. unfold repable_signed.
 destruct (zlt z Int.min_signed).
 right; intros [? _]; unfold Int.min_signed; omega. 
 destruct (zlt Int.max_signed z).
 right; intros [_ ?]; unfold Int.max_signed; omega.
 left; split; omega. 
Defined.

Definition add_ptr_int' (ty: type) (v: val) (i: Z) : val :=
  if repable_signed_dec (sizeof ty * i)
   then match v with
      | Vptr b ofs => 
           Vptr b (Int.add ofs (Int.repr (sizeof ty * i)))
      | _ => Vundef
      end
  else Vundef.

Definition add_ptr_int (ty: type) (v: val) (i: Z) : val :=
           eval_binop Oadd (tptr ty) tint v (Vint (Int.repr i)).

Lemma repable_signed_mult2:
  forall i j, i<>0 -> repable_signed (i*j) -> repable_signed j.
Admitted.
Lemma repable_signed_mult1:
  forall i j, j<>0 -> repable_signed (i*j) -> repable_signed i.
Proof.
intros.
 rewrite Zmult_comm in H0.
 apply repable_signed_mult2 in H0; auto.
Qed.

Lemma add_ptr_int_eq:
  forall ty v i, repable_signed (sizeof ty * i) ->
       add_ptr_int' ty v i = add_ptr_int ty v i.
Proof.
 intros.
 unfold add_ptr_int, add_ptr_int'.
 rewrite if_true by auto.
 destruct v; simpl; auto.
 unfold force_val2; simpl; auto.
 f_equal. f_equal.
 destruct (Z.eq_dec i 0).
    subst. rewrite Int.mul_zero. rewrite Zmult_0_r. auto.
 assert (repable_signed (sizeof ty)). eapply repable_signed_mult1; eauto.
 assert (repable_signed i). apply repable_signed_mult2 in H; auto.
        pose proof (sizeof_pos ty); omega.
 rewrite Int.mul_signed. 
 rewrite <- (Int.signed_repr _ H).
 repeat rewrite Int.repr_signed.
 rewrite (Int.signed_repr _ H0).
 rewrite (Int.signed_repr _ H1). auto.
Qed.

Lemma add_ptr_int_offset:
  forall t v n, 
  repable_signed (sizeof t) ->
  repable_signed n ->
  add_ptr_int t v n = offset_val (Int.repr (sizeof t * n)) v.
Proof.
 unfold add_ptr_int; intros.
 unfold eval_binop, force_val2; destruct v; simpl; auto.
 rewrite Int.mul_signed.
 rewrite Int.signed_repr by auto.
  rewrite Int.signed_repr by auto.
 auto.
Qed.

Lemma add_ptr_int'_offset:
  forall t v n, 
  repable_signed (sizeof t * n) ->
  add_ptr_int' t v n = offset_val (Int.repr (sizeof t * n)) v.
Proof.
 intros.
 destruct (Z.eq_dec n 0).
 subst.
 unfold add_ptr_int'.
 rewrite if_true. destruct v; simpl; auto. auto.
 rewrite add_ptr_int_eq by auto.
 unfold add_ptr_int; intros.
 unfold eval_binop, force_val2; destruct v; simpl; auto.
 rewrite Int.mul_signed.
 rewrite Int.signed_repr.
  rewrite Int.signed_repr.
 auto.
 apply repable_signed_mult2 in H; auto.
 pose proof (sizeof_pos t); omega.
  apply repable_signed_mult1 in H; auto.
Qed.


Lemma typed_false_cmp:
  forall op i j , 
   typed_false tint (force_val (sem_cmp op tint tint true2 (Vint i) (Vint j))) ->
   Int.cmp (negate_comparison op) i j = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
rewrite Int.negate_cmp.
destruct (Int.cmp op i j); auto. inv H.
Qed.

Lemma typed_true_cmp:
  forall op i j, 
   typed_true tint (force_val (sem_cmp op tint tint true2 (Vint i) (Vint j))) ->
   Int.cmp op i j = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
destruct (Int.cmp op i j); auto. inv H.
Qed.

Definition Zcmp (op: comparison) : Z -> Z -> Prop :=
 match op with 
 | Ceq => eq
 | Cne => (fun i j => i<>j)
 | Clt => Zlt
 | Cle => Zle
 | Cgt => Zgt 
 | Cge => Zge
 end.

Lemma int_cmp_repr:
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = true ->
   Zcmp op i j.
Proof.
intros.
unfold Int.cmp, Int.eq, Int.lt in H1.
replace (if zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j))
             then true else false)
 with (if zeq i j then true else false) in H1.
Focus 2.
destruct (zeq i j); destruct (zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j))); 
 auto.
subst. contradiction n; auto.
clear - H H0 e n.
apply Int.signed_repr in H. rewrite Int.signed_repr_eq in H.
apply Int.signed_repr in H0; rewrite Int.signed_repr_eq in H0.
contradiction n; clear n.
repeat rewrite Int.unsigned_repr_eq in e.
 match type of H with
           | context [if ?a then _ else _] => destruct a
           end;
 match type of H0 with
           | context [if ?a then _ else _] => destruct a
           end; omega.
unfold Zcmp.
rewrite (Int.signed_repr _ H) in H1; rewrite (Int.signed_repr _ H0) in H1.
repeat match type of H1 with
           | context [if ?a then _ else _] => destruct a
           end; try omegaContradiction;
 destruct op; auto; simpl in *; try discriminate; omega.
Qed.


Lemma typed_false_cmp_repr:
  forall op i j, 
   repable_signed i -> repable_signed j -> 
   typed_false tint (force_val (sem_cmp op tint tint true2
                              (Vint (Int.repr i)) 
                              (Vint (Int.repr j)) )) ->
   Zcmp (negate_comparison op) i j.
Proof.
 intros.
 apply typed_false_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Lemma typed_true_cmp_repr:
  forall op i j, 
   repable_signed i -> repable_signed j -> 
   typed_true tint (force_val (sem_cmp op tint tint true2
                              (Vint (Int.repr i)) 
                              (Vint (Int.repr j)) )) ->
   Zcmp op i j.
Proof.
 intros.
 apply typed_true_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Ltac intcompare H :=
 (apply typed_false_cmp_repr in H || apply typed_true_cmp_repr in H);
   [ simpl in H | auto; unfold repable_signed, Int.min_signed, Int.max_signed in *; omega .. ].


Lemma derives_refl' {A}{NA: NatDed A}: forall P Q: A, P=Q -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

Lemma derives_refl'' {A}{NA: NatDed A}: forall P Q: A, Q=P -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

Lemma isptr_deref_noload:
 forall t p, access_mode t = By_reference -> isptr (deref_noload t p) = isptr p.
Proof.
intros.
unfold deref_noload. rewrite H. reflexivity.
Qed.
Hint Rewrite isptr_deref_noload using reflexivity : norm.

Lemma isptr_offset_val_zero:
  forall v, isptr v -> offset_val Int.zero v = v.
Proof. intros. destruct v; inv H; subst; simpl.  rewrite Int.add_zero; reflexivity.
Qed.

Hint Rewrite isptr_offset_val_zero using solve [auto] : norm.

Lemma isptr_offset_val:
 forall i p, isptr (offset_val i p) = isptr p.
Proof.
intros.
unfold isptr.
destruct p; simpl; auto.
Qed.
Hint Rewrite isptr_offset_val : norm.

Lemma isptr_force_ptr: forall v, isptr v -> force_ptr v = v.
Proof. intros. destruct v; inv H; auto. Qed.
Hint Rewrite isptr_force_ptr using solve [auto] : norm.

Lemma isptr_force_ptr' : forall p, isptr (force_ptr p) =  isptr p.
Proof.
intros. destruct p; reflexivity.
Qed.
Hint Rewrite isptr_force_ptr' : norm.

Fixpoint subst_eval_expr (j: ident) (v: environ -> val) (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Etempvar id ty => if eqb_ident j id then v else eval_id id 
 | Eaddrof a ty => subst_eval_lvalue j v a 
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (subst_eval_expr j v a) 
 | Ebinop op a1 a2 ty =>  
                  `(eval_binop op (typeof a1) (typeof a2)) (subst_eval_expr j v a1) (subst_eval_expr j v a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (subst_eval_expr j v a)
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (subst_eval_expr j v a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (subst_eval_lvalue j v a))
 end

 with subst_eval_lvalue (j: ident) (v: environ -> val) (e: expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (subst_eval_expr j v a)
 | Efield a i ty => `(eval_field (typeof a) i) (subst_eval_lvalue j v a)
 | _  => `Vundef
 end.

Lemma subst_eval_expr_eq:
    forall j v e, subst j v (eval_expr e) = subst_eval_expr j v e
with subst_eval_lvalue_eq: 
    forall j v e, subst j v (eval_lvalue e) = subst_eval_lvalue j v e.
Proof.
intros j v; clear subst_eval_expr_eq; induction e; intros; simpl; try auto.
unfold eqb_ident.
unfold subst, eval_id, env_set, te_of. extensionality rho. 
pose proof (Pos.eqb_spec j i).
destruct H. subst. rewrite Map.gss. reflexivity.
rewrite Map.gso; auto.
rewrite <- IHe; clear IHe.
unfold_lift.
extensionality rho; unfold subst.
reflexivity.
unfold_lift.
extensionality rho; unfold subst.
rewrite <- IHe; reflexivity.
unfold_lift.
extensionality rho; unfold subst.
rewrite <- IHe1, <- IHe2; reflexivity.
unfold_lift.
extensionality rho; unfold subst.
rewrite <- IHe; reflexivity.
unfold_lift.
rewrite <- subst_eval_lvalue_eq.
extensionality rho; unfold subst.
f_equal. f_equal.

intros j v; clear subst_eval_lvalue_eq; induction e; intros; simpl; try auto.
unfold_lift.
rewrite <- subst_eval_expr_eq.
extensionality rho; unfold subst.
f_equal.
unfold_lift.
extensionality rho; unfold subst.
rewrite <- IHe.
f_equal.
Qed.

Hint Rewrite subst_eval_expr_eq subst_eval_lvalue_eq : subst.

Lemma closed_wrt_map_subst':
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         @map (LiftEnviron A) _ (subst id e) Q = Q.
Proof.
apply @closed_wrt_map_subst.
Qed.

Hint Rewrite @closed_wrt_map_subst' using safe_auto_with_closed : norm.
Hint Rewrite @closed_wrt_map_subst' using safe_auto_with_closed : subst.
Lemma closed_wrt_subst_eval_expr:
  forall j v e, 
   closed_wrt_vars (eq j) (eval_expr e) ->
   subst_eval_expr j v e = eval_expr e.
Proof.
intros; rewrite <- subst_eval_expr_eq.
apply closed_wrt_subst; auto.
Qed.
Lemma closed_wrt_subst_eval_lvalue:
  forall j v e, 
   closed_wrt_vars (eq j) (eval_lvalue e) ->
   subst_eval_lvalue j v e = eval_lvalue e.
Proof.
intros; rewrite <- subst_eval_lvalue_eq.
apply closed_wrt_subst; auto.
Qed.
Hint Rewrite closed_wrt_subst_eval_expr using solve [auto 50 with closed] : subst.
Hint Rewrite closed_wrt_subst_eval_lvalue using solve [auto 50 with closed] : subst.

Fixpoint closed_eval_expr (j: ident) (e: expr) : bool :=
 match e with
 | Econst_int i ty => true
 | Econst_long i ty => true
 | Econst_float f ty => true
 | Etempvar id ty => negb (eqb_ident j id)
 | Eaddrof a ty => closed_eval_lvalue j a 
 | Eunop op a ty =>  closed_eval_expr j a
 | Ebinop op a1 a2 ty =>  andb (closed_eval_expr j a1) (closed_eval_expr j a2)
 | Ecast a ty => closed_eval_expr j a
 | Evar id ty => true
 | Ederef a ty => closed_eval_expr j a
 | Efield a i ty => closed_eval_lvalue j a
 end

 with closed_eval_lvalue (j: ident) (e: expr) : bool := 
 match e with 
 | Evar id ty => true
 | Ederef a ty => closed_eval_expr j a
 | Efield a i ty => closed_eval_lvalue j a
 | _  => false
 end.

Lemma closed_eval_expr_e: 
    forall j e, closed_eval_expr j e = true -> closed_wrt_vars (eq j) (eval_expr e)
with closed_eval_lvalue_e: 
    forall j e, closed_eval_lvalue j e = true -> closed_wrt_vars (eq j) (eval_lvalue e).
Proof.
intros j e; clear closed_eval_expr_e; induction e; intros; simpl; auto with closed.
simpl in H. destruct (eqb_ident j i) eqn:?; inv H.
apply Pos.eqb_neq in Heqb. auto with closed.
simpl in H.
rewrite andb_true_iff in H. destruct H.
auto with closed.
intros j e; clear closed_eval_lvalue_e; induction e; intros; simpl; auto with closed.
Qed.

Hint Extern 2 (closed_wrt_vars (eq _) (eval_expr _)) => (apply closed_eval_expr_e; reflexivity) : closed.
Hint Extern 2 (closed_wrt_vars (eq _) (eval_lvalue _)) => (apply closed_eval_lvalue_e; reflexivity) : closed.

Lemma closed_wrt_eval_expr: forall S e,
  expr_closed_wrt_vars S e -> 
  closed_wrt_vars S (eval_expr e).
Proof.
intros.
apply H.
Qed.
(* Hint Resolve closed_wrt_eval_expr : closed. *)

Lemma closed_wrt_lvalue: forall S e,
  access_mode (typeof e) = By_reference ->
  closed_wrt_vars S (eval_expr e) -> closed_wrt_vars S (eval_lvalue e).
Proof.
intros.
destruct e; simpl in *; auto with closed;
unfold closed_wrt_vars in *;
intros; specialize (H0 _ _ H1); clear H1; super_unfold_lift;
unfold deref_noload in *; auto; rewrite H in H0; auto.
Qed.
(* Hint Resolve closed_wrt_lvalue : closed. *)



