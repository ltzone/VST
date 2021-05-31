Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.address_conflict.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Cop2.
Require Import VST.veric.shares.
Require Import VST.veric.slice.

Require Import VST.veric.mpred.

(*Lenb: moved to mpred
Definition assert := environ -> mpred.  (* Unfortunately
   can't export this abbreviation through SeparationLogic.v because
  it confuses the Lift system *)
*)

Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable),
      identity (ghost_of w0) ->
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.

Definition permission_block (sh: Share.t)  (v: val) (t: type) : mpred :=
    match access_mode t with
         | By_value ch =>
            match v with
            | Vptr b ofs =>
                 nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs)
                       (size_chunk ch)
            | _ => FF
            end
         | _ => FF
         end.

Local Open Scope pred.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then (!!tc_val t v2 &&
             address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)) ||
            (!! (v2 = Vundef) &&
             EX v2':val, address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))
       else !! (tc_val' t v2 /\ (align_chunk ch | Ptrofs.unsigned ofs)) && nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Lemma address_mapsto_readable:
  forall m v sh a, address_mapsto m v sh a |-- 
           !! readable_share sh.
Proof.
intros.
unfold address_mapsto.
unfold derives.
simpl.
intros ? ?.
destruct H as [bl [[[? [? ?]] ?]] ].
specialize (H2 a).
rewrite if_true in H2.
destruct H2 as [rsh ?]. auto.
destruct a; split; auto.
clear; pose proof (size_chunk_pos m); omega.
Qed.

Lemma mapsto_tc_val': forall sh t p v, mapsto sh t p v |-- !! tc_val' t v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  if_tac; auto;
  destruct p; auto;
  try simple_if_tac; auto.
  + apply orp_left; apply andp_left1.
    - intros ?; simpl.
      apply tc_val_tc_val'.
    - intros ? ?; simpl in *; subst.
      apply tc_val'_Vundef.
  + apply andp_left1.
    intros ?; simpl; tauto.
Qed.

Lemma mapsto_value_range:
 forall sh v sz sgn i,
   readable_share sh ->
   mapsto sh (Tint sz sgn noattr) v (Vint i) =
    !! int_range sz sgn i && mapsto sh (Tint sz sgn noattr) v (Vint i).
Proof.
intros.
rename H into Hsh.
assert (GG: forall a b, (a || !!(Vint i = Vundef) && b) = a). {
intros. apply pred_ext; intros ? ?. hnf in H.
destruct H; auto; hnf in H; destruct H; discriminate.
left; auto.
}
apply pred_ext; [ | apply andp_left2; auto].
assert (MAX: Int.max_signed = 2147483648 - 1) by reflexivity.
assert (MIN: Int.min_signed = -2147483648) by reflexivity.
assert (Byte.min_signed = -128) by reflexivity.
assert (Byte.max_signed = 128-1) by reflexivity.
assert (Byte.max_unsigned = 256-1) by reflexivity.
destruct (Int.unsigned_range i).
assert (Int.modulus = Int.max_unsigned + 1) by reflexivity.
assert (Int.modulus = 4294967296) by reflexivity.
apply andp_right; auto.
unfold mapsto; intros.
replace (type_is_volatile (Tint sz sgn noattr)) with false
  by (destruct sz,sgn; reflexivity).
simpl.
destruct (readable_share_dec sh); [| tauto].
destruct sz, sgn, v; (try rewrite FF_and; auto);
 repeat rewrite GG;
 apply prop_andp_left; intros ? ? _; hnf; try omega.
 pose proof (Int.signed_range i); omega.
 destruct H6; subst;
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; omega.
 destruct H6; subst;
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; omega.
Qed.

Definition writable_block (id: ident) (n: Z): assert :=
   fun rho => 
        EX b: block,  EX sh: Share.t,
          !! (writable_share sh /\ ge_of rho id = Some b) && VALspec_range n sh (b, 0).

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 match bl with
  | nil =>  fun rho => emp
  | (b,n)::bl' =>  fun rho => writable_block b n rho * writable_blocks bl' rho
 end.

Fixpoint address_mapsto_zeros (sh: share) (n: nat) (adr: address) : mpred :=
 match n with
 | O => emp
 | S n' => address_mapsto Mint8unsigned (Vint Int.zero) sh adr 
               * address_mapsto_zeros sh n' (fst adr, Z.succ (snd adr))
end.

Definition address_mapsto_zeros' (n: Z) : spec :=
     fun (sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l (Z.max n 0))
                                  (fun l' => yesat NoneP (VAL (Byte Byte.zero)) sh l')
                                  noat) && noghost.

Lemma address_mapsto_zeros_eq:
  forall sh n,
   address_mapsto_zeros sh n =
   address_mapsto_zeros' (Z_of_nat n) sh.
Proof.
  induction n;
  extensionality adr; destruct adr as [b i].
  * (* base case *)
    simpl.
    unfold address_mapsto_zeros'.
    apply pred_ext.
    intros w ?.
    split; [intros [b' i']|].
    hnf.
    rewrite if_false.
    simpl. apply resource_at_identity; auto.
    intros [? ?]. unfold Z.max in H1;  simpl in H1. omega.
    apply ghost_of_identity; auto.
    intros w [].
    simpl.
    apply all_resource_at_identity.
    intros [b' i'].
    specialize (H (b',i')).
    hnf in H.
    rewrite if_false in H. apply H.
    clear; intros [? ?]. unfold Z.max in H0; simpl in H0. omega.
    auto.
  * (* inductive case *)
    rewrite inj_S.
    simpl.
    rewrite IHn; clear IHn.
    apply pred_ext; intros w ?.
    - (* forward case *)
      destruct H as [w1 [w2 [? [? [? Hg2]]]]].
      split.
      intros [b' i'].
      hnf.
      if_tac.
      + destruct H0 as [bl [[[? [? ?]] ?] _]].
        specialize (H5 (b',i')).
        hnf in H5.
        if_tac in H5.
       ** destruct H5 as [p ?]; exists p.
          hnf in H5.
          specialize (H1 (b',i')). hnf in H1. rewrite if_false in H1.
          assert (LEV := join_level _ _ _ H).
          {
            apply (resource_at_join _ _ _ (b',i')) in H.
            apply join_comm in H; apply H1 in H.
            rewrite H in H5.
            hnf. rewrite H5. f_equal.
            f_equal.
            simpl. destruct H6. simpl in H7. replace (i'-i) with 0 by omega.
            unfold size_chunk_nat in H0. simpl in H0.
            unfold nat_of_P in H0. simpl in H0.
            destruct bl; try solve [inv H0].
            destruct bl; inv H0.
            simpl.
            clear - H3.
            (* TODO: Clean up the following proof. *)
            destruct m; try solve [inv H3].
            rewrite decode_byte_val in H3.
            f_equal.
            assert (Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr 0) by
              (forget (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) as j; inv H3; auto).
            clear H3.
            assert (Int.unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) =
                Int.unsigned Int.zero) by (f_equal; auto).
            rewrite Int.unsigned_zero in H0.
            clear H.
            rewrite Int.zero_ext_mod in H0 by (compute; split; congruence).
            rewrite Int.unsigned_repr in H0.
            rewrite Zdiv.Zmod_small in H0.
            assert (Byte.repr (Byte.unsigned i) = Byte.zero).
            apply f_equal; auto.
            rewrite Byte.repr_unsigned in H. auto.
            apply Byte.unsigned_range.
            clear.
            pose proof (Byte.unsigned_range i).
            destruct H; split; auto.
            apply Z.le_trans with Byte.modulus.
            omega.
            clear.
            compute; congruence.
          }
          destruct H2.
          intros [? ?].
          destruct H6.
          clear - H7 H9 H10. simpl in H10. omega.
       ** assert (LEV := join_level _ _ _ H).
          apply (resource_at_join _ _ _ (b',i')) in H.
          apply H5 in H.
          specialize (H1 (b',i')).
          hnf in H1.
          if_tac in H1.
         -- destruct H1 as [p ?]; exists p.
            hnf in H1|-*.
            rewrite H in H1; rewrite H1.
            f_equal.
         -- contradiction H6.
            destruct H2.
            split; auto.
            simpl.
            subst b'.
            clear - H7 H8.
            assert (~ (Z.succ i <= i' < (Z.succ i + Z.max (Z_of_nat n) 0))).
            contradict H7; split; auto.
            clear H7.
            replace (Z.max (Z.succ (Z_of_nat n)) 0) with (Z.succ (Z_of_nat n)) in H8.
            replace (Z.max (Z_of_nat n) 0) with (Z_of_nat n) in H.
            omega.
            symmetry; apply Zmax_left.
            apply Z_of_nat_ge_O.
            symmetry; apply Zmax_left.
            clear.
            pose proof (Z_of_nat_ge_O n). omega. 
      + apply (resource_at_join _ _ _ (b',i')) in H.
        destruct H0 as [bl [[[? [? ?]] ?] _]].
        specialize (H5 (b',i')); specialize (H1 (b',i')).
        hnf in H1,H5.
        rewrite if_false in H5.
        rewrite if_false in H1.
       ** apply H5 in H.
          simpl in H1|-*.
          rewrite <- H; auto.
       ** clear - H2; contradict H2.
          destruct H2; split; auto.
          destruct H0.
          split; try omega.
          pose proof (Z_of_nat_ge_O n).
          rewrite Zmax_left in H1 by omega.
          rewrite Zmax_left by omega.
          omega.
       ** clear - H2; contradict H2; simpl in H2.
          destruct H2; split; auto.
          rewrite Zmax_left by omega.
          omega.
      + destruct H0 as (? & ? & Hg1).
        simpl; rewrite <- (Hg1 _ _ (ghost_of_join _ _ _ H)); auto.
    - (* backward direction *)
      destruct H as [H Hg].
      assert (H0 := H (b,i)).
      hnf in H0.
      rewrite if_true in H0
        by (split; auto; pose proof (Z_of_nat_ge_O n); rewrite Zmax_left; omega).
      destruct H0 as [H0 H1].
      pose proof I.
      destruct (make_rmap  (fun loc => if eq_dec loc (b,i) then 
       YES sh H0 (VAL (Byte Byte.zero)) NoneP
          else core (w @ loc)) (ghost_of w) (level w)) as [w1 [? ?]].
      extensionality loc. unfold compose.
      if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP
           | apply resource_fmap_core].
      { apply ghost_of_approx. }
      pose proof I.
      destruct (make_rmap (fun loc => if adr_range_dec (b, Z.succ i) (Z.max (Z.of_nat n) 0) loc
                       then YES sh H0 (VAL (Byte Byte.zero)) NoneP
          else core (w @ loc)) (ghost_of w) (level w)) as [w2 [? ?]].
      extensionality loc. unfold compose.
      if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP
           | apply resource_fmap_core].
      { apply ghost_of_approx. }
      exists w1; exists w2; split3; auto.
+apply resource_at_join2; try congruence.
  intro loc; destruct H4; rewrite H4; destruct H7; rewrite H7.
 clear - H.
 specialize (H loc).  unfold jam in H. hnf in H.
 rewrite Zmax_left by (pose proof (Z_of_nat_ge_O n); omega).
 rewrite Zmax_left in H by (pose proof (Z_of_nat_ge_O n); omega).
 if_tac. rewrite if_false.
 subst. rewrite if_true in H.
  destruct H as [H' H]; rewrite H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit2.
 constructor. auto.
 apply YES_ext; auto.
 split; auto; omega.
 subst. intros [? ?]; omega.
 if_tac in H.
 rewrite if_true.
 destruct H as [H' H]; rewrite H; clear H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit1.
 constructor; auto.
 apply YES_ext; auto.
 destruct loc;
 destruct H2; split; auto.
 assert (z<>i) by congruence.
 omega.
 rewrite if_false.
 unfold noat in H. simpl in H.
 apply join_unit1; [apply core_unit | ].
 clear - H.
 apply H. apply join_unit2. apply core_unit. auto.
 destruct loc. intros [? ?]; subst. apply H2; split; auto; omega.
 destruct H4 as [_ ->], H7 as [_ ->].
 apply identity_unit'; auto.
+ exists (Byte Byte.zero :: nil); split.
 split. split. reflexivity. split.
 unfold decode_val. simpl. f_equal.
 apply Z.divide_1_l.
 intro loc. hnf. if_tac. exists H0.
 destruct loc as [b' i']. destruct H8; subst b'.
 simpl in H9. assert (i=i') by omega; subst i'.
 rewrite Zminus_diag. hnf. rewrite preds_fmap_NoneP.
  destruct H4; rewrite H4. rewrite if_true by auto. f_equal.
 unfold noat. simpl. destruct H4; rewrite H4. rewrite if_false. apply core_identity.
  contradict H8. subst. split; auto. simpl; omega.
  simpl; destruct H4 as [_ ->]; auto.
+ split. intro loc. hnf.
 if_tac. exists H0. hnf. destruct H7; rewrite H7.
 rewrite if_true by auto. rewrite preds_fmap_NoneP. auto.
 unfold noat. simpl. destruct H7; rewrite H7.
 rewrite if_false by auto. apply core_identity.
 simpl; destruct H7 as [_ ->]; auto.
Qed.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => 
    !! (0 <= Ptrofs.unsigned z  /\ n + Ptrofs.unsigned z < Ptrofs.modulus)%Z &&
    address_mapsto_zeros sh (Z.to_nat n) (b, Ptrofs.unsigned z)
  | _ => FF
  end.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Ptrofs.repr i))
         * memory_block' sh n' b (i+1)
 end.

Definition memory_block'_alt (sh: share) (n: nat) (b: block) (ofs: Z) : mpred :=
 if readable_share_dec sh 
 then VALspec_range (Z_of_nat n) sh (b, ofs)
 else nonlock_permission_bytes sh (b,ofs) (Z.of_nat n).

Lemma memory_block'_eq:
 forall sh n b i,
  0 <= i ->
  Z_of_nat n + i < Ptrofs.modulus ->
  memory_block' sh n b i = memory_block'_alt sh n b i.
Proof.
  intros.
  unfold memory_block'_alt.
  revert i H H0; induction n; intros.
  + unfold memory_block'.
    simpl.
    rewrite VALspec_range_0, nonlock_permission_bytes_0.
    if_tac; auto.
  + unfold memory_block'; fold memory_block'.
    rewrite (IHn (i+1)) by (rewrite inj_S in H0; omega).
    symmetry.
    rewrite (VALspec_range_split2 1 (Z_of_nat n)) by (try rewrite inj_S; omega).
    rewrite VALspec1.
    unfold mapsto_, mapsto.
    simpl access_mode. cbv beta iota.
    change (type_is_volatile (Tint I8 Unsigned noattr)) with false. cbv beta iota.
    destruct (readable_share_dec sh).
    - f_equal.
      assert (i < Ptrofs.modulus) by (rewrite Nat2Z.inj_succ in H0; omega).
      rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega); clear H1.
      forget (Share.unrel Share.Lsh sh) as rsh.
      forget (Share.unrel Share.Rsh sh) as sh'.
      clear.

      assert (EQ: forall loc, jam (adr_range_dec loc (size_chunk Mint8unsigned)) = jam (eq_dec loc)).
      intros [b' z']; unfold jam; extensionality P Q loc;
       destruct loc as [b'' z'']; apply exist_ext; extensionality w;
       if_tac; [rewrite if_true | rewrite if_false]; auto;
        [destruct H; subst; f_equal;  simpl in H0; omega
        | contradict H; inv H; split; simpl; auto; omega].
      apply pred_ext.
      * intros w ?.
        right; split; hnf; auto.
        destruct H as [H Hg].
        assert (H':= H (b,i)).
        hnf in H'. rewrite if_true in H' by auto.
        destruct H' as [v H'].
        pose (l := v::nil).
        destruct v; [exists Vundef | exists (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned i0)))) | exists Vundef];
        exists l; split; auto; (split; [ split3; [reflexivity |unfold l; (reflexivity || apply decode_byte_val) |  apply Z.divide_1_l ] | ]);
          rewrite EQ; intro loc; specialize (H loc);
         hnf in H|-*; if_tac; auto; subst loc; rewrite Zminus_diag;
         unfold l; simpl nth; auto.
      * apply orp_left.
        apply andp_left2.
        { intros w [l [[[? [? ?]] ?] Hg]].
          split; auto.
          intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
            hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
          destruct l; inv H. exists m.
          destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
          f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        }
        { rewrite prop_true_andp by auto.
          intros w [v2' [l [[[? [? ?]] ?] Hg]]].
          split; auto.
          intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
            hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
          destruct l; inv H. exists m.
          destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
          f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        }
    - rewrite Ptrofs.unsigned_repr by (rewrite Nat2Z.inj_succ in H0; unfold Ptrofs.max_unsigned; omega).
      change (size_chunk Mint8unsigned) with 1.
      rewrite prop_true_andp by (split; [apply tc_val'_Vundef | apply Z.divide_1_l]).
      apply nonlock_permission_bytes_split2.
      * rewrite Nat2Z.inj_succ; omega.
      * omega.
      * omega.
Qed.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => (!!(Ptrofs.unsigned ofs + n < Ptrofs.modulus)) && memory_block' sh (Z.to_nat n) b (Ptrofs.unsigned ofs)
 | _ => FF
 end.

Lemma mapsto__exp_address_mapsto: forall sh t b i_ofs ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  readable_share sh ->
  mapsto_ sh t (Vptr b i_ofs) = EX  v2' : val,
            address_mapsto ch v2' sh (b, (Ptrofs.unsigned i_ofs)).
Proof.
  pose proof (@FF_orp (pred rmap) (algNatDed _)) as HH0.
  change seplog.orp with orp in HH0.
  change seplog.FF with FF in HH0.
  pose proof (@ND_prop_ext (pred rmap) (algNatDed _)) as HH1.
  change seplog.prop with prop in HH1.

  intros. rename H1 into RS.
  unfold mapsto_, mapsto.
  rewrite H, H0.
  rewrite if_true by auto.
  assert (!!(tc_val t Vundef) = FF). {
    clear; unfold FF; f_equal; apply prop_ext; intuition.
    apply (tc_val_Vundef _ H).
  }
  rewrite H1.

  rewrite FF_and, HH0.
  assert (!!(Vundef = Vundef) = TT) by (apply HH1; tauto).
  rewrite H2.
  rewrite TT_and.
  reflexivity.
Qed.

Lemma exp_address_mapsto_VALspec_range_eq:
  forall ch sh l,
    EX v: val, address_mapsto ch v sh l = !! (align_chunk ch | snd l) && VALspec_range (size_chunk ch) sh l.
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intro.
    apply andp_right; [| apply address_mapsto_VALspec_range].
    unfold address_mapsto.
    apply exp_left; intro.
    do 2 apply andp_left1.
    apply (@prop_derives (pred rmap) (algNatDed _)); tauto.
  + apply prop_andp_left; intro.
    apply VALspec_range_exp_address_mapsto; auto.
Qed.

Lemma VALspec_range_exp_address_mapsto_eq:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l = EX v: val, address_mapsto ch v sh l.
Proof.
  intros.
  apply pred_ext.
  + apply VALspec_range_exp_address_mapsto; auto.
  + apply exp_left; intro; apply address_mapsto_VALspec_range.
Qed.

Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  mapsto_ sh t (Vptr b ofs) = memory_block sh (size_chunk ch) (Vptr b ofs).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_eq.
  2: pose proof Ptrofs.unsigned_range ofs; omega.
  2: rewrite Z2Nat.id by (pose proof size_chunk_pos ch; omega); omega.
  destruct (readable_share_dec sh).
 *
  rewrite mapsto__exp_address_mapsto with (ch := ch); auto.
  unfold memory_block'_alt. rewrite if_true by auto.
  rewrite Z2Nat.id by (pose proof size_chunk_pos ch; omega).
  rewrite VALspec_range_exp_address_mapsto_eq by (exact H1).
  rewrite <- (TT_and (EX  v2' : val,
   address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))) at 1.
  f_equal.
  pose proof (@ND_prop_ext (pred rmap) _).
  simpl in H3.
  change TT with (!! True).
  apply H3.
  tauto.
 * unfold mapsto_, mapsto, memory_block'_alt.
   rewrite prop_true_andp by auto.
   rewrite H, H0.
  rewrite !if_false by auto.
   rewrite prop_true_andp by (split; [apply tc_val'_Vundef | auto]).
   rewrite Z2Nat.id by (pose proof (size_chunk_pos ch); omega).
   auto.
Qed.

Lemma nonreadable_memory_block_mapsto: forall sh b ofs t ch v,
  ~ readable_share sh ->
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  tc_val' t v ->
  memory_block sh (size_chunk ch) (Vptr b ofs) = mapsto sh t (Vptr b ofs) v.
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_eq.
  2: pose proof Ptrofs.unsigned_range ofs; omega.
  2: rewrite Z2Nat.id by (pose proof size_chunk_pos ch; omega); omega.
  destruct (readable_share_dec sh).
 * tauto.
 * unfold mapsto_, mapsto, memory_block'_alt.
   rewrite prop_true_andp by auto.
   rewrite H0, H1.
   rewrite !if_false by auto.
   rewrite prop_true_andp by auto.
   rewrite Z2Nat.id by (pose proof (size_chunk_pos ch); omega).
   auto.
Qed.

Lemma mapsto_share_join:
 forall sh1 sh2 sh t p v,
   join sh1 sh2 sh ->
   mapsto sh1 t p v * mapsto sh2 t p v = mapsto sh t p v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct (type_is_volatile t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct p; try solve [rewrite FF_sepcon; auto].
  destruct (readable_share_dec sh1), (readable_share_dec sh2).
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    pose proof (@guarded_sepcon_orp_distr (pred rmap) (algNatDed _) (algSepLog _)).
    simpl in H0; rewrite H0 by (intros; subst; pose proof tc_val_Vundef t; tauto); clear H0.
    f_equal; f_equal.
    - apply address_mapsto_share_join; auto.
    - rewrite exp_sepcon1.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H0; apply H0; clear H0; intro.
      rewrite exp_sepcon2.
      transitivity
       (address_mapsto m v0 sh1 (b, Ptrofs.unsigned i) *
        address_mapsto m v0 sh2 (b, Ptrofs.unsigned i)).
      * apply pred_ext; [| apply (exp_right v0); auto].
        apply exp_left; intro.
        pose proof (fun sh0 sh3 a => 
            (@add_andp (pred rmap) (algNatDed _) _ _ (address_mapsto_value_cohere m v0 x sh0 sh3 a))).
        simpl in H0; rewrite H0; clear H0.
        apply normalize.derives_extract_prop'; intro; subst; auto.
      * apply address_mapsto_share_join; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    rewrite distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop;
    pose proof (@andp_prop_ext (pred rmap) _);
    (simpl in H0; apply H0; clear H0; [reflexivity | intro]).
    - rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * apply tc_val_tc_val' in H0; tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H1; apply H1; clear H1; intro.
      rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * subst; pose proof tc_val'_Vundef t. tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eexists; apply join_comm in H; eauto | auto]).
    rewrite sepcon_comm, distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop;
    pose proof (@andp_prop_ext (pred rmap) _);
    (simpl in H0; apply H0; clear H0; [reflexivity | intro]).
    - rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * apply tc_val_tc_val' in H0; tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H1; apply H1; clear H1; intro.
      rewrite (address_mapsto_align _ _ sh).
      rewrite (andp_comm (address_mapsto _ _ _ _)), sepcon_andp_prop1.
      pose proof (@andp_prop_ext (pred rmap) _); simpl in H1; apply H1; clear H1; intros.
      * subst; pose proof tc_val'_Vundef t. tauto.
      * apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_false by (eapply join_unreadable_shares; eauto).
    rewrite sepcon_andp_prop1, sepcon_andp_prop2, <- andp_assoc, andp_dup.
    f_equal.
    apply nonlock_permission_bytes_share_join; auto.
Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct v; auto.
  if_tac.
  + apply orp_left.
    apply orp_right2.
    apply andp_left2.
    apply andp_right.
    - intros ? _; simpl; auto.
    - apply exp_right with v'; auto.
    - apply andp_left2. apply exp_left; intro v2'.
      apply orp_right2. apply andp_right; [intros ? _; simpl; auto |]. apply exp_right with v2'.
      auto.
  + apply andp_derives; [| auto].
    intros ? [? ?].
    split; auto.
    apply tc_val'_Vundef.
Qed.

Lemma mapsto_not_nonunit: forall sh t p v, ~ nonunit sh -> mapsto sh t p v |-- emp.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].
  if_tac.
  + apply readable_nonidentity in H0.
    apply nonidentity_nonunit in H0; tauto.
  + apply andp_left2.
    apply nonlock_permission_bytes_not_nonunit; auto.
Qed.

Lemma mapsto_pure_facts: forall sh t p v,
  mapsto sh t p v |-- !! ((exists ch, access_mode t = By_value ch) /\ isptr p).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].

  pose proof (@seplog.prop_right (pred rmap) (algNatDed _)).
  simpl in H; apply H; clear H.
  split.
  + eauto.
  + simpl; auto.
Qed.

Lemma mapsto_overlap: forall sh {cs: compspecs} t1 t2 p1 p2 v1 v2,
  nonunit sh ->
  pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
  mapsto sh t1 p1 v1 * mapsto sh t2 p2 v2 |-- FF.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try (rewrite FF_sepcon; auto).
  destruct (access_mode t2) eqn:AM2; try (rewrite normalize.sepcon_FF; auto).
  destruct (type_is_volatile t1); try (rewrite FF_sepcon; auto).
  destruct (type_is_volatile t2); try (rewrite normalize.sepcon_FF; auto).
  destruct p1; try (rewrite FF_sepcon; auto).
  destruct p2; try (rewrite normalize.sepcon_FF; auto).
  if_tac.
  + apply derives_trans with ((EX  v : val,
          address_mapsto m v sh (b, Ptrofs.unsigned i)) *
      (EX  v : val,
          address_mapsto m0 v sh (b0, Ptrofs.unsigned i0))).
    - apply sepcon_derives; apply orp_left.
      * apply andp_left2, (exp_right v1).
        auto.
      * apply andp_left2; auto.
      * apply andp_left2, (exp_right v2).
        auto.
      * apply andp_left2; auto.
    - clear v1 v2.
      rewrite exp_sepcon1.
      apply exp_left; intro v1.
      rewrite exp_sepcon2.
      apply exp_left; intro v2.
      clear H H1; rename H0 into H.
      destruct H as [? [? [? [? ?]]]].
      inversion H; subst.
      inversion H0; subst.
      erewrite !size_chunk_sizeof in H1 by eauto.
      apply address_mapsto_overlap; auto.
  + rewrite sepcon_andp_prop1, sepcon_andp_prop2.
    apply andp_left2, andp_left2.
    apply nonlock_permission_bytes_overlap; auto.
    clear H H1; rename H0 into H.
    erewrite !size_chunk_sizeof in H by eauto.
    destruct H as [? [? [? [? ?]]]].
    inversion H; subst.
    inversion H0; subst.
    auto.
Qed.

Lemma Nat2Z_add_lt: forall n i, Ptrofs.unsigned i + n < Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i < Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite Z2Nat.id by omega. omega.
  + rewrite Z2Nat_neg by omega.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    omega.
Qed.

Lemma Nat2Z_add_le: forall n i, Ptrofs.unsigned i + n <= Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i <= Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite Z2Nat.id by omega. omega.
  + rewrite Z2Nat_neg by omega.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    omega.
Qed.

Lemma memory_block_overlap: forall sh p1 n1 p2 n2, nonunit sh -> pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 * memory_block sh n2 p2 |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try solve [rewrite FF_sepcon; auto].
  destruct p2; try solve [rewrite normalize.sepcon_FF; auto].
  rewrite sepcon_andp_prop1.
  rewrite sepcon_andp_prop2.
  apply normalize.derives_extract_prop; intros.
  apply normalize.derives_extract_prop; intros. 
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; omega | apply Nat2Z_add_lt; omega].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i0; omega | apply Nat2Z_add_lt; omega].
  unfold memory_block'_alt.
  if_tac.
  + clear H2.
    apply VALspec_range_overlap.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Z2Nat.id by omega.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H4.
    subst.
    auto.
  + apply nonlock_permission_bytes_overlap; auto.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Z2Nat.id by omega.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H5.
    subst.
    auto.
Qed.

Lemma mapsto_conflict:
  forall sh t v v2 v3,
  nonunit sh ->
  mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
  intros.
  rewrite (@add_andp (pred rmap) (algNatDed _) _ _ (mapsto_pure_facts sh t v v3)).
  simpl.
  rewrite andp_comm.
  rewrite sepcon_andp_prop.
  apply prop_andp_left; intros [[? ?] ?].
  unfold mapsto.
  rewrite H0.
  destruct (type_is_volatile t); try (rewrite FF_sepcon; auto).
  destruct v; try (rewrite FF_sepcon; auto).
  pose proof (size_chunk_pos x).
  if_tac.
*
  normalize.
  rewrite distrib_orp_sepcon. rewrite !distrib_orp_sepcon2;
  repeat apply orp_left;
  rewrite ?sepcon_andp_prop1;  repeat (apply prop_andp_left; intro);
  rewrite ?sepcon_andp_prop2;  repeat (apply prop_andp_left; intro);
  rewrite ?exp_sepcon1;  repeat (apply exp_left; intro);
  rewrite ?exp_sepcon2;  repeat (apply exp_left; intro);
  apply address_mapsto_overlap;
  exists (b, Ptrofs.unsigned i); repeat split; omega.
*
  rewrite ?sepcon_andp_prop1;  repeat (apply prop_andp_left; intro);
  rewrite ?sepcon_andp_prop2;  repeat (apply prop_andp_left; intro).
  apply nonlock_permission_bytes_overlap; auto.
  exists (b, Ptrofs.unsigned i); repeat split; omega.
Qed.



Lemma join_necR_aux: forall n x y z x' y' z',
  relation_power n age x x' -> 
  relation_power n age y y' -> join x y z -> join x' y' z' -> 
  relation_power n age z z'.
Proof.
  intros n. induction n.
  { intros. simpl in *. subst. eapply join_eq;eassumption. }
  intros.
  
  apply power_age_age1 in H. simpl in H.
  destruct (age1 x) as [x''|] eqn:Ex.
  2:{ inversion H. }
  apply power_age_age1 in H0. simpl in H0.
  destruct (age1 y) as [y''|] eqn:Ey.
  2:{ inversion H0. }
  pose proof @age1_join _ _ _ _ _ _ _ _ H1 Ex.
  destruct H3 as [y''' [z'' [H3 [? ?]]]].
  assert (y'' = y''').
  { hnf in H4. congruence. } subst y'''.
  exists z''. split.
  * auto.
  * eapply IHn;try eassumption;apply power_age_age1;auto.
Qed.

(* Lemma join_necR_aux2: forall n x y z x' y',
  relation_power n age x x' -> 
  relation_power n age y y' -> join x y z ->
  exists z', join x' y' z' /\ relation_power n age z z'.
Proof.
  intros n. induction n.
  { intros. simpl in *. subst.
    exists z. split;auto. }
  intros.  
  apply power_age_age1 in H. simpl in H.
  destruct (age1 x) as [x''|] eqn:Ex.
  2:{ inversion H. }
  apply power_age_age1 in H0. simpl in H0.
  destruct (age1 y) as [y''|] eqn:Ey.
  2:{ inversion H0. }
  pose proof @age1_join _ _ _ _ _ _ _ _ H1 Ex.
  destruct H2 as [y''' [z'' [H3 [? ?]]]].
  assert (y'' = y''').
  { hnf in H4. congruence. } subst y'''.
  Search age join.
  exists z''. split.
  * auto.
  * eapply IHn;try eassumption;apply power_age_age1;auto.
Qed. *)
  

Lemma relation_power_level: forall n x y,
   relation_power n age x y -> ((level x) = n + (level y))%nat.
Proof.
  intros n. induction n;intros.
  { simpl. hnf in H. f_equal. auto. }
  simpl in H. destruct H as [x' [? ?]].
  apply IHn in H0. simpl. rewrite <- H0.
  apply age_level. auto.
Qed.

Lemma join_necR_same_level: forall m n x y x' y',
  relation_power m age x x' -> 
  relation_power n age y y' -> level x = level y -> level x' = level y' -> m = n.
Proof.
  intros. apply relation_power_level in H. apply relation_power_level in H0.
  omega.
Qed.

Lemma join_necR: forall x y z x' y' z',
  necR x x' -> 
  necR y y' -> join x y z -> join x' y' z' -> 
  necR z z'.
Proof.
  intros.
  pose proof join_level _ _ _ H1 as [E1 E2].
  pose proof join_level _ _ _ H2 as [E3 E4].
  apply necR_power_age in H. apply necR_power_age in H0.
  destruct H as [n1 H], H0 as [n2 H0].
  assert (n1 = n2).
  { pose proof join_necR_same_level _ _ _ _ _ _ H H0.
    apply H3;congruence. }
  subst n2.
  pose proof join_necR_aux _ _ _ _ _ _ _ H H0 H1 H2.
  apply necR_power_age. exists n1. auto.
Qed.

Lemma join_necR_2: forall x y z x' y',
  necR x x' -> 
  necR y y' -> join x y z -> level x' = level y' ->
  exists z', join x' y' z' /\ necR z z'.
Proof.
  intros.
  epose proof nec_join H1 H.
  destruct H3 as [y'' [z' [? [? ?]]]].
  exists z'. split;auto.
  assert (y'' = y').
  { apply (necR_linear' H4 H0).
    apply join_level in H1. apply join_level in H3. omega. }
  subst. auto.
Qed.


Ltac unfold_Byte_const :=
  unfold Byte.max_unsigned in *;
  unfold Byte.modulus in *;
  unfold two_power_pos in *;
  unfold Byte.wordsize in *; simpl in *;
  repeat (unfold Int.modulus in *; unfold Int.wordsize in *;
  unfold Wordsize_32.wordsize in *; unfold Int.half_modulus in *;
  unfold two_power_nat, two_power_pos in *;
  unfold Int.max_unsigned, Int.min_signed, Int.max_signed,
  Int.zwordsize in *; simpl in *).


Lemma Byte_unsigned_inj: forall i1 i2,
  Byte.unsigned i1 = Byte.unsigned i2 -> i1 = i2.
Proof.
  intros.
  eapply Byte.same_bits_eq; intros.
  destruct i1, i2. simpl in *. unfold Byte.testbit.
  unfold Byte.unsigned. simpl. rewrite H. reflexivity.
Qed.

Lemma Byte_unsigned_inj_32: forall ia1 ia2 ib1 ib2,
  Byte.unsigned ia1 + Byte.unsigned ia2 * 256
   = Byte.unsigned ib1 + Byte.unsigned ib2 * 256-> 
  ia1 = ib1 /\ ia2 = ib2.
Proof.
  intros.
  assert ((Byte.unsigned ia1 + Byte.unsigned ia2 * 256) mod 256
         = ( Byte.unsigned ib1 + Byte.unsigned ib2 * 256) mod 256).
  { rewrite H. reflexivity. }
  rewrite !Z_mod_plus_full in H0.
  rewrite (Z.mod_small) in H0. 2:{ apply Byte.unsigned_range. }
  rewrite (Z.mod_small) in H0. 2:{ apply Byte.unsigned_range. }
  apply Byte_unsigned_inj in H0. split;auto.
  assert ( Byte.unsigned ia2 = Byte.unsigned ib2).
  { subst. omega. }
  apply Byte_unsigned_inj in H1. auto.
Qed.


Lemma decode_byte_deterministic: forall i1 i2,
  decode_val Mint8signed (Byte i1 :: nil) = decode_val Mint8signed (Byte i2 :: nil) ->
  i1 = i2.
Proof.
  intros. unfold decode_val in *.
  simpl in H. apply Vint_inj in H.
  unfold decode_int in H.
  assert (Ht1: rev_if_be (i1 :: nil) = i1::nil).
  { unfold rev_if_be. 
    destruct (Archi.big_endian);auto. }
  assert (Ht2: rev_if_be (i2 :: nil) = i2::nil).
    { unfold rev_if_be. 
      destruct (Archi.big_endian);auto. }
  rewrite Ht1, Ht2 in *. clear Ht1. clear Ht2.
  { simpl in H. rewrite !Z.add_0_r in H.
    pose proof Byte.unsigned_range i1.
    pose proof Byte.unsigned_range i2.
    remember (Byte.unsigned i1) as v1.
    remember (Byte.unsigned i2) as v2.
    assert (E: 0 < 8 < Int.zwordsize). 
    { unfold_Byte_const. omega. }
    pose proof Int.eqmod_sign_ext _ ((Int.repr v1)) E as E1.
    pose proof Int.eqmod_sign_ext _ ((Int.repr v2)) E as E2.
    rewrite H in E1. apply Zbits.eqmod_sym in E1.
    pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
    apply Zbits.eqmod_mod_eq in E3.
    2:{ unfold_Byte_const. omega. }
    rewrite !Int.unsigned_repr_eq in E3.
    unfold_Byte_const.
    assert (v1 = v2).
    { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 256) in E3; try omega.
      rewrite (Z.mod_small v1 256) in E3; try omega.
    }
    apply Byte_unsigned_inj. rewrite <- Heqv1, <- Heqv2. omega.
  }
Qed.


Lemma decode_byte_deterministic_unsigned: forall i1 i2,
  decode_val Mint8unsigned (Byte i1 :: nil) = 
  decode_val Mint8unsigned (Byte i2 :: nil) ->
  i1 = i2.
Proof.
  intros. unfold decode_val in *.
  simpl in H. apply Vint_inj in H.
  unfold decode_int in H.
  assert (Ht1: rev_if_be (i1 :: nil) = i1::nil).
  { unfold rev_if_be. 
    destruct (Archi.big_endian);auto. }
  assert (Ht2: rev_if_be (i2 :: nil) = i2::nil).
    { unfold rev_if_be. 
      destruct (Archi.big_endian);auto. }
  rewrite Ht1, Ht2 in *. clear Ht1. clear Ht2.
  { simpl in H. rewrite !Z.add_0_r in H.
    pose proof Byte.unsigned_range i1.
    pose proof Byte.unsigned_range i2.
    remember (Byte.unsigned i1) as v1.
    remember (Byte.unsigned i2) as v2.
    assert (E: 0 <= 8 < Int.zwordsize). 
    { unfold_Byte_const. omega. }
    pose proof Int.eqmod_zero_ext _ ((Int.repr v1)) E as E1.
    pose proof Int.eqmod_zero_ext _ ((Int.repr v2)) E as E2.
    rewrite H in E1. apply Zbits.eqmod_sym in E1.
    pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
    apply Zbits.eqmod_mod_eq in E3.
    2:{ unfold_Byte_const. omega. }
    rewrite !Int.unsigned_repr_eq in E3.
    unfold_Byte_const.
    assert (v1 = v2).
    { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 256) in E3; try omega.
      rewrite (Z.mod_small v1 256) in E3; try omega.
    }
    apply Byte_unsigned_inj. rewrite <- Heqv1, <- Heqv2. omega.
  }
Qed.

Lemma Int_unsign_ext_inj_byte: forall ia1 ia2 ib1 ib2,
Int.zero_ext 16 (Int.repr (int_of_bytes ((ia1 :: ia2 :: nil)))) =
Int.zero_ext 16 (Int.repr (int_of_bytes ((ib1 :: ib2 :: nil)))) ->
ia1 :: ia2 :: nil = ib1 :: ib2 :: nil.
Proof.
  intros. 
  { simpl in H. rewrite !Z.add_0_r in H.
    pose proof Byte.unsigned_range ia1.
    pose proof Byte.unsigned_range ia2.
    pose proof Byte.unsigned_range ib1.
    pose proof Byte.unsigned_range ib2.
    remember (Byte.unsigned ia1 + Byte.unsigned ia2 * 256) as v1.
    remember (Byte.unsigned ib1 + Byte.unsigned ib2 * 256) as v2.
    assert (E: 0 <=  16 < Int.zwordsize). 
    { unfold_Byte_const. omega. }
    pose proof Int.eqmod_zero_ext _ ((Int.repr v1)) E as E1.
    pose proof Int.eqmod_zero_ext _ ((Int.repr v2)) E as E2.
    rewrite H in E1. apply Zbits.eqmod_sym in E1.
    pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
    apply Zbits.eqmod_mod_eq in E3.
    2:{ unfold_Byte_const. omega. }
    rewrite !Int.unsigned_repr_eq in E3.
    unfold_Byte_const.
    assert (v1 = v2).
    { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 65536) in E3; try omega.
      rewrite (Z.mod_small v1 65536) in E3; try omega.
    } 
    rewrite Heqv1, Heqv2 in H4.
    apply Byte_unsigned_inj_32 in H4.
    destruct H4;subst. auto.
  }
Qed.


Lemma Int_sign_ext_inj_byte: forall ia1 ia2 ib1 ib2,
Int.sign_ext 16 (Int.repr (int_of_bytes ((ia1 :: ia2 :: nil)))) =
Int.sign_ext 16 (Int.repr (int_of_bytes ((ib1 :: ib2 :: nil)))) ->
ia1 :: ia2 :: nil = ib1 :: ib2 :: nil.
Proof.
  intros. 
  { simpl in H. rewrite !Z.add_0_r in H.
    pose proof Byte.unsigned_range ia1.
    pose proof Byte.unsigned_range ia2.
    pose proof Byte.unsigned_range ib1.
    pose proof Byte.unsigned_range ib2.
    remember (Byte.unsigned ia1 + Byte.unsigned ia2 * 256) as v1.
    remember (Byte.unsigned ib1 + Byte.unsigned ib2 * 256) as v2.
    assert (E: 0 <  16 < Int.zwordsize). 
    { unfold_Byte_const. omega. }
    pose proof Int.eqmod_sign_ext _ ((Int.repr v1)) E as E1.
    pose proof Int.eqmod_sign_ext _ ((Int.repr v2)) E as E2.
    rewrite H in E1. apply Zbits.eqmod_sym in E1.
    pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
    apply Zbits.eqmod_mod_eq in E3.
    2:{ unfold_Byte_const. omega. }
    rewrite !Int.unsigned_repr_eq in E3.
    unfold_Byte_const.
    assert (v1 = v2).
    { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 4294967296) in E3; try omega.
      rewrite (Z.mod_small v2 65536) in E3; try omega.
      rewrite (Z.mod_small v1 65536) in E3; try omega.
    } 
    rewrite Heqv1, Heqv2 in H4.
    apply Byte_unsigned_inj_32 in H4.
    destruct H4;subst. auto.
  }
Qed.

Lemma bm_unique: forall (bm1 bm2 : list memval) 
  (bm: AV.address) (m: memory_chunk) (v: val),
    Datatypes.length bm1 = size_chunk_nat m ->
      decode_val m bm1 = v -> 
    Datatypes.length bm2 = size_chunk_nat m ->
      decode_val m bm2 = v -> (align_chunk m | snd bm) ->
      v <> Vundef -> 
    bm1 = bm2.
Proof.
  intros.
  pose proof decode_val_undef.
  destruct m; simpl in *;
    unfold size_chunk_nat in *; unfold size_chunk in *.
  { destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    rewrite <- H0 in H2.
    destruct m, m0; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    { apply decode_byte_deterministic in H2. subst. reflexivity. }
  }
  { destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    rewrite <- H0 in H2.
    destruct m, m0; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    { apply decode_byte_deterministic_unsigned in H2.
      subst. reflexivity. }
  }
  { destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    rewrite <- H0 in H2.
    destruct m, m0; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    destruct m1, m2; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    unfold decode_val in H2. simpl in H2.
    apply Vint_inj in H2. unfold decode_int in H2.
    unfold rev_if_be in H2. destruct (Archi.big_endian).
    { replace (rev (i0 :: i2 :: nil)) 
        with (i2 :: i0 :: nil) in * by reflexivity.
      replace (rev (i :: i1 :: nil)) 
        with (i1 :: i :: nil) in * by reflexivity.
      apply Int_sign_ext_inj_byte in H2.
      inv H2. reflexivity. }
    { apply Int_sign_ext_inj_byte in H2.
      inv H2. reflexivity. }
  }
  { destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    destruct bm1; try solve [inv H].
    destruct bm2; try solve [inv H1].
    rewrite <- H0 in H2.
    destruct m, m0; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    destruct m1, m2; try solve [inv H2; try reflexivity; 
      unfold decode_val in *; simpl in *; try congruence].
    unfold decode_val in H2. simpl in H2.
    apply Vint_inj in H2. unfold decode_int in H2.
    unfold rev_if_be in H2. destruct (Archi.big_endian).
    { replace (rev (i0 :: i2 :: nil)) 
        with (i2 :: i0 :: nil) in * by reflexivity.
      replace (rev (i :: i1 :: nil)) 
        with (i1 :: i :: nil) in * by reflexivity.
      apply Int_unsign_ext_inj_byte in H2.
      inv H2. reflexivity. }
    { apply Int_unsign_ext_inj_byte in H2.
      inv H2. reflexivity. }
  }
  { repeat (destruct bm1; try solve [inv H]).
    repeat (destruct bm2; try solve [inv H1]).
    unfold decode_val in H0, H2.
    destruct (Archi.ptr64) eqn:Eptr64.
    { destruct m, m0, m1, m2; try solve [inv H2; try reflexivity; 
        unfold decode_val in *; simpl in *; try congruence].
      destruct m3, m4, m5, m6; try solve [inv H2; try reflexivity; 
        unfold decode_val in *; simpl in *; try congruence].
      simpl in H0. simpl in H2. rewrite <- H2 in H0.
      unfold decode_int in H0.
      admit.
    }
    { destruct m3.
      { simpl in H2. congruence. }
      { admit. }
      { destruct m4; try solve [
          simpl in H2; rewrite andb_false_r in H2; congruence].
        destruct m5; try solve [
          simpl in H2; rewrite !andb_false_r in H2; congruence].
        destruct m6; try solve [
          simpl in H2; rewrite !andb_false_r in H2; congruence].
        simpl in H2. destruct (Val.eq v0 v0).
        2:{ simpl in H2. congruence. }
        simpl in H2. destruct (quantity_eq Q32 q).
        2:{ simpl in H2;
            repeat (rewrite !andb_false_r in H2;
                    rewrite !andb_false_l in H2). congruence. }
        simpl in H2. repeat (destruct n as [|n]; 
                      try solve [simpl in H2; congruence]).
        simpl in H2. destruct (Val.eq v0 v1).
        2:{ simpl in H2. congruence. }
        simpl in H2. destruct (quantity_eq Q32 q0).
        2:{ simpl in H2;
            repeat (rewrite !andb_false_r in H2;
                    rewrite !andb_false_l in H2). congruence. }
        simpl in H2. repeat (destruct n0 as [|n0]; 
                      try solve [simpl in H2; congruence]).
        destruct (Val.eq v0 v0).
        2:{ simpl in H2. congruence. }
        simpl in H2. destruct (quantity_eq Q32 q).
        2:{ simpl in H2;
            repeat (rewrite !andb_false_r in H2;
                    rewrite !andb_false_l in H2). congruence. }
        simpl in H2. repeat (destruct n as [|n]; 
                      try solve [simpl in H2; congruence]).
        simpl in H2. destruct (Val.eq v0 v2).
        2:{ simpl in H2. congruence. }
        simpl in H2. destruct (quantity_eq Q32 q1).
        2:{ simpl in H2;
            repeat (rewrite !andb_false_r in H2;
                    rewrite !andb_false_l in H2). congruence. }
        simpl in H2. repeat (destruct n1 as [|n1]; 
                      try solve [simpl in H2; congruence]).
        simpl in H2. destruct (Val.eq v0 v3).
        2:{ simpl in H2. congruence. }
        simpl in H2. destruct (quantity_eq Q32 q2).
        2:{ simpl in H2;
            repeat (rewrite !andb_false_r in H2;
                    rewrite !andb_false_l in H2). congruence. }
        simpl in H2. repeat (destruct n2 as [|n2]; 
                      try solve [simpl in H2; congruence]).
        simpl in H2.
        destruct m.
        { simpl in H0. congruence. }
        { simpl in H0.
          destruct m0, m1, m2; simpl in H0; try congruence.
          subst. destruct v3; try solve [inv H2].
          
(* 
          Search Fragment.


          Search Archi.ptr64 false.
          Search Archi.ptr64.
         *)
        }
      admit.
      }
    }
  }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Admitted.

Lemma resource_at_expand_share: forall 
  (r1 r2 r : rmap) (sh : share)
  (p: preds) l k
  (rsh: readable_share sh),
  join r1 r2 r -> 
  r1 @ l = YES sh rsh k p ->
  exists sh' (rsh':readable_share sh'),
  join_sub sh sh' /\
  r @ l = YES sh' rsh' k p.
Proof.
  intros.
  pose proof resource_at_join _ _ _ l H.
  inv H1; try congruence.
  - exists sh3, rsh3.
    rewrite H0 in H3. inv H3.
    split;auto. exists sh2. auto.
  - exists sh3, rsh3.
    rewrite H0 in H3. inv H3.
    split;auto. exists sh2. auto.
Qed.

Lemma share_sub_lub: forall sh1 sh2 sh3,
  join_sub sh1 sh2 ->
  join_sub sh1 sh3 ->
  join_sub sh1 (Share.lub sh2 sh3).
Proof.
  intros. destruct H. destruct H0.
  destruct H. destruct H0.
  exists (Share.lub x x0).
  split.
  - rewrite Share.distrib1. rewrite H. rewrite H0. rewrite Share.lub_bot. reflexivity.
  - rewrite <- (Share.lub_idem sh1).
    rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh1 x).
    rewrite H1. rewrite (Share.lub_commute sh2 x0).
    rewrite <- Share.lub_assoc. rewrite H2.
    rewrite Share.lub_commute. reflexivity.
Qed.

(* TODO: IMPORTANT LEMMA *)

Definition join_sub_share sh1 res :=
  match res with
  | YES sh _ _ _ | NO sh _ => join_sub sh1 sh
  | _ => True
  end.

Definition share_of res:= 
  match res with
  | YES sh _ _ _ | NO sh _ => sh
  | _ => Share.top
  end.


Lemma join_rem_nsh rall sh1 sh2 
  (nsh:  ~ readable_share (share_of rall))
  (JS1:join_sub sh1 (share_of rall)) (JS2:join_sub sh2 (share_of rall)) :
  ~ readable_share (Share.glb (share_of rall) (Share.comp (Share.lub sh1 sh2))).
Proof.
  intros.
  intros C. apply nsh. destruct rall. 
  { simpl in *. destruct JS1 as [sh1' H], JS2 as [sh2' H0].
    pose proof share_cross_split _ _ _ _ _ H H0.
    destruct X as [shs E].
    destruct shs as [[[sh11 sh12] sh21] sh22].
    destruct E as (E1 & E2 & E3 & E4).
    apply join_comm in E2. apply join_comm in H.
    epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
    assert (Share.lub sh1 sh2 = sh_u).
    { destruct E5. rewrite <- H2. rewrite Share.lub_commute.
      destruct E3. rewrite <- H4.
      destruct E1. rewrite <- !H6.
      rewrite (Share.lub_commute sh11 sh21).
      rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
      rewrite Share.lub_idem. reflexivity. }
    rewrite H1 in C.
    assert (Share.glb sh (Share.comp sh_u) = sh22).
    { destruct E6. rewrite <- H3.
      rewrite Share.glb_commute. rewrite Share.distrib1.
      rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
      rewrite Share.lub_bot. apply share_lemma87.
      rewrite Share.glb_commute. assumption. }
    rewrite H2 in C.
    eapply readable_share_join.
    { apply E6. } auto. }
  { simpl in *. destruct JS1 as [sh1' H], JS2 as [sh2' H0].
    pose proof share_cross_split _ _ _ _ _ H H0.
    destruct X as [shs E].
    destruct shs as [[[sh11 sh12] sh21] sh22].
    destruct E as (E1 & E2 & E3 & E4).
    apply join_comm in E2. apply join_comm in H.
    epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
    assert (Share.lub sh1 sh2 = sh_u).
    { destruct E5. rewrite <- H2. rewrite Share.lub_commute.
      destruct E3. rewrite <- H4.
      destruct E1. rewrite <- !H6.
      rewrite (Share.lub_commute sh11 sh21).
      rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
      rewrite Share.lub_idem. reflexivity. }
    rewrite H1 in C.
    assert (Share.glb sh (Share.comp sh_u) = sh22).
    { destruct E6. rewrite <- H3.
      rewrite Share.glb_commute. rewrite Share.distrib1.
      rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
      rewrite Share.lub_bot. apply share_lemma87.
      rewrite Share.glb_commute. assumption. }
    rewrite H2 in C.
    eapply readable_share_join.
    { apply E6. } auto. }
  { simpl in C. simpl. auto. }
Qed.


Definition join_rem_of sh1 sh2 rall
  (JS1:join_sub sh1 (share_of rall))
  (JS2:join_sub sh2 (share_of rall)) :=
  match rall with
  | YES sh rsh k p =>
      let sh' := Share.glb sh (Share.comp (Share.lub sh1 sh2)) in
      match (dec_readable sh') with
      | left rsh' => YES sh' rsh' k p
      | right nsh' => NO sh' nsh'
      end
  | NO sh nsh =>
      let sh' := Share.glb (share_of rall) 
          (Share.comp (Share.lub sh1 sh2)) in
      match (dec_readable (share_of rall)) with
      | left rsh' => NO Share.bot bot_unreadable
      | right nsh' =>
          NO sh' (join_rem_nsh rall sh1 sh2 nsh' JS1 JS2)
      end
  | PURE k p => PURE k p
  end.

Inductive cut_resource_rmap (sh:share) ls: rmap -> rmap -> Prop :=
| cut_resource_intro: forall (b: memval) r_mapsto r1 r2,
    ((ALL y, jam (fun l' => in_dec EqDec_address l' ls)
        (fun l' => yesat NoneP (VAL b) sh l') noat y) && noghost) r_mapsto ->
    join r_mapsto r1 r2 ->
    cut_resource_rmap sh ls r1 r2.
(* TODO: b in fact can be any *)

Lemma cut_resource_rmap_unique: forall sh ls r1 r2 r,
  cut_resource_rmap sh ls r1 r ->
  cut_resource_rmap sh ls r2 r ->
  r1 = r2.
Proof.
  intros. inv H. inv H0.
  pose proof join_join_sub H2.
  pose proof join_join_sub H3.
  assert (r_mapsto = r_mapsto0).
  { apply rmap_ext.
    + apply join_level in H2. apply join_level in H3.
      destruct H2, H3. congruence.
    + intros. hnf in H1. destruct H1, H.
      apply resource_at_join with (loc:=l) in H2.
      apply resource_at_join with (loc:=l) in H3.
      specialize (H1 l).
      specialize (H l). hnf in H1, H.
      if_tac in H1;subst.
      * destruct H1, H. rewrite H1, H. f_equal. apply proof_irr.
        f_equal. rewrite H1, H in *. inv H2; inv H3; try congruence.
      * do 3 red in H,H1.
        apply resource_at_join_sub with (l:=l) in H0. 
        eapply join_sub_same_identity; eauto.
        - apply identity_unit'; auto.
        - apply (resource_at_join_sub _ _ l) in H4.
          eapply join_sub_unit_for; eauto.
          apply identity_unit'; auto.
    + destruct H1, H. 
      eapply same_identity; auto.
      * destruct H0 as [? H0%ghost_of_join].
        rewrite (H5 _ _ H0) in H0. eauto.
      * destruct H4 as [? H4%ghost_of_join].
        rewrite (H6 _ _ H4) in H4; eauto.
  }
  subst r_mapsto0. clear H0 H4 H.
  apply rmap_ext.
  { apply join_level in H2. apply join_level in H3.
    destruct H2, H3. congruence. }
  { intros. hnf in H1. destruct H1.
    specialize (H l).
    apply resource_at_join with (loc:=l) in H2.
    apply resource_at_join with (loc:=l) in H3. hnf in H.
    if_tac in H.
    + hnf in H. destruct H as [rsh H]. rewrite H in *.
      inv H2; inv H3; try congruence;rewrite <- H10 in H9; inv H9.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. f_equal. apply proof_irr.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. contradiction.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. contradiction.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. f_equal. apply proof_irr.
    + apply H in H2. apply H in H3. congruence.
  }
  { hnf in H1. destruct H1.
    apply ghost_of_join in H2.
    apply ghost_of_join in H3.
    apply H0 in H2. apply H0 in H3.
    congruence. }
Qed.

Lemma share_resource_join_aux: forall sh1 sh2 sh3 sh5 sh,
join sh1 sh3 sh -> join sh2 sh5 sh -> join (Share.lub sh1 sh2) (Share.glb sh (Share.comp (Share.lub sh1 sh2))) sh.
Proof.
  intros.
  pose proof share_cross_split _ _ _ _ _ H H0.
  destruct X as [shs E].
  destruct shs as [[[sh11 sh12] sh21] sh22].
  destruct E as (E1 & E2 & E3 & E4).
  apply join_comm in E2. apply join_comm in H.
  epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
  assert (Share.lub sh1 sh2 = sh_u).
  { destruct E5. rewrite <- H2. rewrite Share.lub_commute.
    destruct E3. rewrite <- H4.
    destruct E1. rewrite <- !H6.
    rewrite (Share.lub_commute sh11 sh21).
    rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
    rewrite Share.lub_idem. reflexivity. }
  rewrite H1.
  assert (Share.glb sh (Share.comp sh_u) = sh22).
  { destruct E6. rewrite <- H3.
    rewrite Share.glb_commute. rewrite Share.distrib1.
    rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
    rewrite Share.lub_bot. apply share_lemma87.
    rewrite Share.glb_commute. assumption. }
  rewrite H2.
  auto.
Qed.


Lemma cut_resource_join: forall sh1 sh2 ls r1 r2 r
  (rsh1: readable_share sh1) (rsh2: readable_share sh2),
  cut_resource_rmap sh1 ls r1 r ->
  cut_resource_rmap sh2 ls r2 r ->
  exists r3, cut_resource_rmap (Share.lub sh1 sh2) ls r3 r.
Proof.
  intros. inversion H as [b1 r_mapsto1 ? ? [Hm1 Hg1] HJ1];subst.
  inversion H0 as [b2 r_mapsto2 ? ? [Hm2 Hg2] HJ2];subst.
  assert (rsh:readable_share (Share.lub sh1 sh2)).
  { apply readable_share_lub. auto. }
  assert (JS1: forall l, In l ls -> join_sub sh1 (share_of (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ1 as Hl1.
    pose proof Hm1 l as Hml1. hnf in Hml1.
    if_tac in Hml1;try tauto.
    - destruct Hml1. rewrite H3 in Hl1.
      inv Hl1;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  assert (JS2: forall l, In l ls -> join_sub sh2 (share_of (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ2 as Hl2.
    pose proof Hm2 l as Hml2. hnf in Hml2.
    if_tac in Hml2;try tauto.
    - destruct Hml2. rewrite H3 in Hl2.
      inv Hl2;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  exists (squash (level r, (
    (fun l => match in_dec EqDec_address l ls with
              | left i => join_rem_of sh1 sh2 (r @ l) (JS1 l i) (JS2 l i)
              | right _ => (r @ l) end),
    ghost_of r1))).
  apply cut_resource_intro with (b:=b1)
  (r_mapsto:= (squash (level r, (
    (fun l => if in_dec EqDec_address l ls
              then YES (Share.lub sh1 sh2) rsh (VAL b1) NoneP
              else match (r @ l) with
              | PURE k p => (r @ l)
              | _ => (NO Share.bot bot_unreadable) end),
    ghost_of r_mapsto1)))).
  - split.
    2:{ simpl. unfold ghost_of. rewrite unsquash_squash. simpl.
        replace (level r) with (level r_mapsto1).
        2:{ apply join_level in HJ1. tauto.  }
        rewrite ghost_of_approx. auto. }
    intros l.
    pose proof resource_at_join _ _ _ l HJ1 as Hl1.
    pose proof resource_at_join _ _ _ l HJ2 as Hl2.
    pose proof Hm1 l as Hml1. pose proof Hm2 l as Hml2.
    hnf in Hml1, Hml2. hnf. if_tac.
    + hnf. exists rsh. hnf. rewrite rmap_level_eq.
      unfold resource_at. rewrite unsquash_squash. simpl.
      unfold compose. if_tac;try tauto.
    + simpl. unfold resource_at at 1. rewrite unsquash_squash.
      simpl. unfold compose. if_tac;try tauto.
      destruct (r@l);simpl;try apply NO_identity; try apply PURE_identity.
  - apply join_unsquash. constructor.
    + rewrite !unsquash_squash. simpl.
      rewrite rmap_level_eq. constructor;auto.
    + rewrite !unsquash_squash. simpl. constructor.
      { unfold join. unfold Join_pi. intros l.
        pose proof resource_at_join _ _ _ l HJ1 as Hl1.
        pose proof resource_at_join _ _ _ l HJ2 as Hl2.
        pose proof Hm1 l as Hml1. pose proof Hm2 l as Hml2.
        hnf in Hml1. hnf in Hml2.
        simpl. unfold compose. if_tac; simpl.
        * simpl. 
          assert (join_sub sh1 (share_of (r@l))).
          { apply JS1. auto. }
          pose proof proof_irr (JS1 l H1) H2. rewrite H3. clear H3.
          clear JS1.
          assert (join_sub sh2 (share_of (r@l))).
          { apply JS2. auto. }
          pose proof proof_irr (JS2 l H1) H3. rewrite H4. clear H4.
          clear JS2. unfold join_rem_of.
          destruct (r@l) eqn:E;simpl.
          + destruct (dec_readable);try contradiction.
            destruct Hml1. rewrite H4 in Hl1. inv Hl1.
          + destruct Hml1 as [rsha Hml1], Hml2 as [rshb Hml2].
            rewrite Hml1 in Hl1. rewrite Hml2 in Hl2.
            unfold resource_at in E. rewrite E.
            inv Hl1; inv Hl2;destruct (dec_readable);
            constructor; eapply share_resource_join_aux;eassumption.
          + destruct Hml1 as [rsha Hml1], Hml2 as [rshb Hml2].
            rewrite Hml1 in Hl1. rewrite Hml2 in Hl2. inv Hl1.
        * simpl. 
          replace (fst (snd (unsquash r)) l) with (r@l) by reflexivity.
          destruct (r @ l) eqn:E.
          - simpl. constructor. apply bot_join_eq.
          - rewrite <- E. rewrite resource_at_approx. simpl.
            rewrite E. constructor. apply bot_join_eq.
          - rewrite <- E. rewrite resource_at_approx. simpl.
            rewrite E. constructor.
      }
      { simpl.
        replace (level r) with (level r_mapsto1).
        2:{ apply join_level in HJ1. tauto. }
        rewrite ghost_of_approx.
        replace (level r_mapsto1) with (level r1).
        2:{ apply join_level in HJ1. omega. }
        rewrite ghost_of_approx. apply ghost_of_join.
        auto. }
Qed.

Lemma resource_at_nonlock_expand_share: forall r1 r2 r b m sh,
  join r1 r2 r -> 
  (ALL y, jam (adr_range_dec b (size_chunk m))
      (fun i : address => shareat i sh && nonlockat i) noat y) r1 ->
  exists sh',
    join_sub sh sh' /\
    (ALL y, jam (adr_range_dec b (size_chunk m))
      (fun i : address => shareat i sh' && nonlockat i) noat y) r.
Proof.
Admitted.

Lemma mapsto_join_andp: forall  sh1 sh2 t p v1 v2,
  (* tc_val t v2 -> can't be undefined *)
  v1 <> Vundef -> v2 <> Vundef ->
  (mapsto sh1 t p v1 * TT) && (mapsto sh2 t p v2 * TT)
  |-- EX (sh':share), (mapsto sh' t p v1 * TT) && !!(v1 = v2).
Proof.
  intros. unfold mapsto.
  assert (E: forall P, FF * TT && (FF * TT) |-- P).
  { rewrite !FF_sepcon. rewrite FF_and.
    apply FF_derives. }
  destruct (access_mode t);auto.
  destruct (type_is_volatile t);auto.
  destruct p;auto.
  if_tac; if_tac.
  - hnf. intros r.
    intros E0.
    destruct E0 as [Ea Eb].
    destruct Ea as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
    destruct Eb as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
    destruct Eb1 as [Eb1 | Eb1].
    2:{ simpl in Eb1. tauto. }
    destruct Eb1 as [Eb1 Ec1].
    destruct Eb2 as [Eb2 | Eb2].
    2:{ simpl in Eb2. tauto. }
    destruct Eb2 as [Eb2 Ec2].
    { destruct Ec1 as [bm1 [[Ec1 Ed1] Ee1]]. unfold jam in Ed1.
      simpl in Ed1. 
      pose proof (Ed1 (b, Ptrofs.unsigned i)) as Ef1.
      destruct Ec2 as [bm2 [[Ec2 Ed2] Ee2]].
      simpl in Ed2. 
      pose proof (Ed2 (b, Ptrofs.unsigned i)) as Ef2.
      destruct (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk m) (b, Ptrofs.unsigned i)).
      2:{ exfalso. apply n. hnf. split;auto. destruct m;simpl; omega. }
      destruct Ef1 as [rsh1 Ef1].
      destruct Ef2 as [rsh2 Ef2].
      pose proof resource_at_expand_share _ _ _ _ _ _ _ rsh1 Ea1 Ef1 as Eg1.
      pose proof resource_at_expand_share _ _ _ _ _ _ _ rsh2 Ea2 Ef2 as Eg2.
      destruct Eg1 as [sh1' [rsh1' [Eg1 Eh1]]].
      destruct Eg2 as [sh2' [rsh2' [Eg2 Eh2]]].
      rewrite Eh1 in Eh2. inv Eh2.
      assert (bm1 = bm2) by admit. subst.
      exists sh2'. if_tac;try tauto.
      rewrite distrib_orp_sepcon. split.
      2:{ simpl in Ec1, Ec2. simpl. destruct Ec1 as [? [? ?]].
          destruct Ec2 as [? [? ?]]. congruence. }
      left.
      pose proof make_rmap.
      assert (Ersh'': ~ readable_share Share.bot). { admit. }

      specialize (X (fun add => if adr_range_dec (b, Ptrofs.unsigned i) (size_chunk m) add
        then
         YES sh2' rsh2'
           (VAL (nth (Z.to_nat 0) bm2 Undef))
           (SomeP (rmaps.ConstType unit) (fun _ : list Type => tt))
      else match r @ add with
      | PURE _ _  => r @ add
      | _ => NO Share.bot Ersh'' end) (ghost_of r1_maps) (level r)).
      destruct X as [r1 Hr1].
      { unfold compose. extensionality.
        if_tac;simpl;try reflexivity.
        destruct (r@x) eqn:E';try reflexivity.
        rewrite <- !E'. rewrite resource_at_approx. reflexivity. } 
      { assert (level r1_maps = level r) by admit.
        rewrite <- !H4. apply ghost_of_approx. }
      
      pose proof make_rmap (fun add => if adr_range_dec (b, Ptrofs.unsigned i) (size_chunk m) add
      then  NO Share.bot Ersh''
      else (r @ add)) (ghost_of r1_rem) (level r).
      destruct X as [r2 Hr2].
      { unfold compose. extensionality.
        if_tac;simpl;try rewrite resource_at_approx;auto. }
      { assert (level r1_rem = level r) by admit.
        rewrite <- !H4. apply ghost_of_approx. }
      exists r1 , r2. repeat split;auto.
      { destruct Hr1 as [?Hra [?Hra ?Hra]].
        destruct Hr2 as [?Hrb [?Hrb ?Hrb]]. apply resource_at_join2;auto.
        { intros.
          rewrite Hra0. rewrite Hrb0. if_tac.
          { assert (loc = (b, Ptrofs.unsigned i)) by admit.
            rewrite H6. rewrite Eh1. unfold snd. replace (Ptrofs.unsigned i - Ptrofs.unsigned i) with 0 by omega.
            constructor. apply join_bot_eq. }
          { destruct (r@loc);try constructor; try apply bot_join_eq. }
        }
        { rewrite Hrb1. rewrite Hra1. apply ghost_of_join.
          auto. }
      }
      { hnf. exists bm2. 
        destruct Ec1 as [? [? ?]].
        repeat split;auto.
        2:{ simpl. rewrite (proj2 (proj2 Hr1)). apply Ee1. }
        hnf. intros. hnf. if_tac.
        {  exists rsh2'. simpl.
            assert (b0 = (b, Ptrofs.unsigned i)) by admit.
            rewrite H9. simpl. 
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i) with 0 by omega.
            rewrite (proj1 (proj2 Hr1)). simpl.
            if_tac;auto. congruence. }
        { simpl. rewrite (proj1 (proj2 Hr1)).
          if_tac.
          { contradiction. }
          { destruct (r@b0).
            + apply NO_identity.
            + apply NO_identity.
            + apply PURE_identity.
          }
        }
      }
    }
  - hnf. intros r.
    intros E0.
    destruct E0 as [Ea Eb].
    destruct Ea as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
    destruct Eb as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
Admitted.


Lemma mapsto_join_andp2: forall  sh t v v2 P1 P2,
  (* tc_val t v2 -> can't be undefined *)
  v2 <> Vundef ->
  (mapsto sh t v v2 * P1) && (mapsto sh t v v2 * P2)
  |-- (mapsto sh t v v2 * (P1 && P2)).
Proof.
  intros. hnf. rename H into Hundef. intros.
  hnf in H. destruct H as [H1 H2].
  hnf in H1. hnf in H2.
  destruct H1 as [r_mapsto [r1 [Ea1 [Ea2 Ea3]]]].
  destruct H2 as [r_mapsto' [r2 [Eb1 [Eb2 Eb3]]]].
  unfold mapsto in *.
  destruct (access_mode t);try solve [inv Ea2].
  destruct (type_is_volatile t);try solve [inv Ea2].
  destruct (v);try solve [inv Ea2].
  if_tac in Ea2.
  { destruct Ea2.
    + destruct Eb2.
      * destruct H0. destruct H1.
        pose proof join_join_sub Eb1.
        pose proof join_join_sub Ea1.
        Search address_mapsto.
        Locate compcert_rmaps.R.rmap.
        Search address_mapsto eq.
        pose proof address_mapsto_precise  _ _ _ _ _ _ _ H2 H3 H5 H4. subst.
        apply join_comm in Ea1. apply join_comm in Eb1.
        unfold rmap in *.
        assert (r1 = r2).
        { Search Canc_alg. assert (Canc_alg compcert_rmaps.R.rmap) as T. { admit. }
          apply (join_canc Ea1 Eb1). }
        subst r1. 
        simpl. exists r_mapsto', r2. split;auto.
      * destruct H1. simpl in H1. tauto.
    + destruct H0. simpl in H0. tauto.
  }
  { destruct Ea2. destruct Eb2.
    pose proof join_join_sub Eb1.
    pose proof join_join_sub Ea1.
    pose proof nonlock_permission_bytes_precise  _ _ _ _ _ _ H1 H3 H5 H4.
    subst r_mapsto'. assert (r1 = r2).
    { assert (Canc_alg compcert_rmaps.R.rmap) as T. { admit. }
      apply join_comm in Ea1. apply join_comm in Eb1.
      apply (join_canc Ea1 Eb1). }
    subst r1. simpl. exists r_mapsto, r2. split;auto.
  }
Admitted.

Lemma address_mapsto_level_precise: forall m v sh bm r r' rw,
  address_mapsto m v sh bm r -> 
  address_mapsto m v sh bm r' ->
  (level r = level r')%nat -> 
  joins r rw -> joins r' rw -> v <> Vundef ->
  r = r'.
Proof.
  intros. rename H2 into Hjoin1. rename H3 into Hjoin2.
  rename H4 into Hv.
  (* pose proof address_mapsto_VALspec_range _ _ _ _ _ H as E1.
  pose proof address_mapsto_VALspec_range _ _ _ _ _ H0 as E2. *)
  unfold address_mapsto in H.
  simpl in H. destruct H as [bm1 [[Hv1 H]  Hg1]].
  unfold address_mapsto in H0.
  simpl in H0. destruct H0 as [bm2 [[Hv2 H0]  Hg2]].
  assert (forall l : AV.address, r @ l = r' @ l).
  { intros.
    pose proof H l. pose proof H0 l.
    if_tac in H2.
    { destruct H2 as [rsh1 H8].
      destruct H3 as [rsh2 H9].
      rewrite H8 in *. rewrite H9 in *.
      assert (rsh1 = rsh2).
      { extensionality. congruence. } subst rsh2.
      { f_equal. Locate Fragment.
        assert (bm1 = bm2).
        { destruct Hv1 as [? [? ?]].
          destruct Hv2 as [? [? ?]].
          eapply bm_unique ;try eassumption. }
        subst. reflexivity.
      }
    }
    { destruct Hjoin1 as [r1 Hjoin1].
      destruct Hjoin2 as [r2 Hjoin2].
      pose proof resource_at_join _ _ _ l Hjoin1.
      pose proof resource_at_join _ _ _ l Hjoin2.
      pose proof H2 _ _ H5.
      pose proof H3 _ _ H6.
      rewrite H7 in *. rewrite H8 in *.
      pose proof empty_NO _ H2.
      pose proof empty_NO _ H3.
      destruct H9, H10;auto; try congruence.
      { destruct H10 as [k [pds H10]].
        inv H5; inv H6; try congruence. }
      { destruct H9 as [k [pds H9]].
        inv H5; inv H6; try congruence. }
      { destruct H9 as [k [pds H9]].
        destruct H10 as [k' [pds' H10]].
        inv H5; inv H6; try congruence. }
    }
  }
  eapply rmap_ext;auto.
  destruct Hjoin1 as [r1 Hjoin1].
  destruct Hjoin2 as [r2 Hjoin2].
  pose proof ghost_of_join _ _ _ Hjoin1.
  pose proof ghost_of_join _ _ _ Hjoin2.
  pose proof Hg1 _ _ H3. pose proof Hg2 _ _ H4.
  rewrite H5 in *. rewrite H6 in *.
  eapply same_identity; auto.
  * eauto.
  * eauto.
Qed.

Lemma nonlock_permission_bytes_level_precise: forall sh p n r r' rw,
  nonlock_permission_bytes sh p n r ->
  nonlock_permission_bytes sh p n r' ->
  (level r = level r')%nat -> 
  joins r rw -> joins r' rw ->
  r = r'.
Proof.
Admitted.

Lemma necR_split_1n: forall n r1 r2,
  relation_power (S n) age r1 r2 -> exists y, age r1 y /\ necR y r2.
Proof.
  intros n. induction n.
  - intros. destruct H as [?[? ?]]. exists x. split;auto.
    apply necR_power_age. exists 0%nat. auto.
  - intros. destruct H as [?[? ?]].
    apply IHn in H0. exists x. split;auto.
    destruct H0 as [? [? ?]].
    eapply rt_trans;[|apply H1]. apply rt_step. auto.
Qed.

Lemma address_mapsto_necR_precise: forall m v sh bm n r r' rw rw', 
  address_mapsto m v sh bm r ->
  address_mapsto m v sh bm r' ->
  (level r = n + level r')%nat ->
  joins r rw -> joins r' rw' -> necR rw rw' -> v <> Vundef ->
  necR r r'.
Proof.
  intros.
  rename H2 into Hjoin1.
  rename H3 into Hjoin2. rename H4 into Hrw.
  rename H5 into Hv.
  apply necR_power_age. exists n. 
  revert r r' rw rw' H H0 H1 Hjoin1 Hjoin2 Hrw.
  induction n;intros.
  + simpl.
    assert (rw = rw').
    { destruct Hjoin1. destruct Hjoin2.
      apply join_level  in H2. apply join_level in H3.
      destruct H2, H3.
      assert (level rw = level rw') by omega.
      pose proof necR_refl rw.
      pose proof necR_linear' H7 Hrw H6. auto. }
    subst rw'.
    eapply address_mapsto_level_precise;eassumption.
  + simpl in H1.
    pose proof levelS_age1 _ _ H1. destruct H2 as [r'' H2].
    exists r''. split;auto.
    (* find rw'' *)
    destruct Hjoin1 as [ra Hjoin1].
    pose proof join_level _ _ _ Hjoin1.
    destruct Hjoin2 as [ra' Hjoin2].
    pose proof join_level _ _ _ Hjoin2.
    pose proof age_level _ _ H2.
    apply clos_rt_rt1n in Hrw.
    inv Hrw. { omega. }
    apply IHn with (rw:=y) (rw':=rw');auto.
    2:{ apply age_level in H2. rewrite H1 in H2. inv H2. auto. }
    { assert (necR r r'').
      { constructor. apply H2. }
      apply pred_nec_hereditary with (a:= r);auto. }
    { pose proof join_necR_2 _ _ _ _ _ (rt_step _ _ _ _ H2) (rt_step _ _ _ _ H6) Hjoin1.
      destruct H8 as [ra'' [? ?]]. { pose proof age_level _ _ H6. omega. }
      exists ra''. auto. }
    { exists ra'. auto. }
    { apply clos_rt1n_rt. auto. }
Qed.

Lemma nonlock_permission_bytes_necR_precise: 
forall sh p n m r r' rw rw', 
  nonlock_permission_bytes sh p n r ->
  nonlock_permission_bytes sh p n r' ->
  (level r = m + level r')%nat ->
  joins r rw -> joins r' rw' -> necR rw rw' ->
  necR r r'.
Proof.
  intros.
  rename H2 into Hjoin1.
  rename H3 into Hjoin2. rename H4 into Hrw.
  apply necR_power_age. exists m. 
  revert r r' rw rw' H H0 H1 Hjoin1 Hjoin2 Hrw.
  induction m;intros.
  + simpl.
    assert (rw = rw').
    { destruct Hjoin1. destruct Hjoin2.
      apply join_level  in H2. apply join_level in H3.
      destruct H2, H3.
      assert (level rw = level rw') by omega.
      pose proof necR_refl rw.
      pose proof necR_linear' H7 Hrw H6. auto. }
    subst rw'.
    eapply nonlock_permission_bytes_level_precise;eassumption.
  + simpl in H1.
    pose proof levelS_age1 _ _ H1. destruct H2 as [r'' H2].
    exists r''. split;auto.
    (* find rw'' *)
    destruct Hjoin1 as [ra Hjoin1].
    pose proof join_level _ _ _ Hjoin1.
    destruct Hjoin2 as [ra' Hjoin2].
    pose proof join_level _ _ _ Hjoin2.
    pose proof age_level _ _ H2.
    apply clos_rt_rt1n in Hrw.
    inv Hrw. { omega. }
    apply IHm with (rw:=y) (rw':=rw');auto.
    2:{ apply age_level in H2. rewrite H1 in H2. inv H2. auto. }
    { assert (necR r r'').
      { constructor. apply H2. }
      apply pred_nec_hereditary with (a:= r);auto. }
    { pose proof join_necR_2 _ _ _ _ _ (rt_step _ _ _ _ H2) (rt_step _ _ _ _ H6) Hjoin1.
      destruct H8 as [ra'' [? ?]]. { pose proof age_level _ _ H6. omega. }
      exists ra''. auto. }
    { exists ra'. auto. }
    { apply clos_rt1n_rt. auto. }
Qed.


Lemma mapsto_precise: forall sh t v v2 P,
  P |-- mapsto sh t v v2 -> v2 <> Vundef ->
  P |-- mapsto sh t v v2 * (mapsto sh t v v2 -* P).
Proof.
  intros. rename H0 into Hundef.
  assert (P |-- mapsto sh t v v2 *TT).
  { eapply derives_trans. { apply normalize.sepcon_TT. }
    apply sepcon_derives;auto.
  }
  unfold mapsto in *.
  assert (Haux:  P |-- FF -> P |-- FF * (FF -* P)).
  { hnf.  intros.
    eapply derives_trans. apply H1.
    apply FF_derives. }
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct v;auto. clear Haux. hnf.
  intros r. intros.
  pose proof H0 _ H1. if_tac in H2.
  - hnf in H2. destruct H2 as [r_mapsto [r_rem [Hr [H2 _]]]].
    hnf in H2. hnf. exists r_mapsto, r_rem.
    repeat split;auto. hnf. intros r_rem' r_mapsto' r'.
    intros. destruct H2.
    + (* address mapsto *)
      destruct H6.
      * destruct H2. destruct H6.
        simpl in H2. simpl in H6.
        assert (v2 <> Vundef).
        { intros C. subst. eapply tc_val_Vundef;eassumption. }
        assert (necR r_mapsto r_mapsto').
        { pose proof (proj1 (necR_power_age _ _)) H4.
          destruct H10 as [n H4'].
          pose proof relation_power_level _ _ _ H4'.
          eapply address_mapsto_necR_precise with (n:=n);
             try eassumption.
          - apply join_level in Hr. apply join_level in H5. omega.
          - eexists. apply Hr.
          - eexists. apply join_comm. apply H5.
         }
         apply join_comm in H5.
         pose proof join_necR _ _ _ _ _ _ H10 H4 Hr H5.
         epose proof pred_nec_hereditary _ _ _ H11. auto.
      * destruct H2. destruct H6. congruence.
    + destruct H6.
      * destruct H2. destruct H6. congruence.
      * destruct H2. destruct H6. congruence.
  - hnf in H2. destruct H2 as [r_mapsto [r_rem [Hr [H2 _]]]].
    destruct H2 as [H2a H2b].
    simpl in H2a. destruct H2a as [H2a1 H2a2].
    exists r_mapsto, r_rem. split;auto. split.
    { split;auto. simpl. auto. }
    hnf. intros r_rem' r_mapsto' r'.
    intros. destruct H5 as [H5a H5b].
    assert (necR r_mapsto r_mapsto').
    { pose proof (proj1 (necR_power_age _ _)) H2.
      destruct H5 as [n H4'].
      pose proof relation_power_level _ _ _ H4'.
      eapply nonlock_permission_bytes_necR_precise with (m:=n);
          try eassumption.
      - apply join_level in Hr. apply join_level in H4. omega.
      - eexists. apply Hr.
      - eexists. apply join_comm. apply H4.
      }
      apply join_comm in H4.
      pose proof join_necR _ _ _ _ _ _ H5 H2 Hr H4.
      epose proof pred_nec_hereditary _ _ _ H6. auto.
Qed.



Lemma memory_block_conflict: forall sh n m p,
  nonunit sh ->
  0 < n <= Ptrofs.max_unsigned -> 0 < m <= Ptrofs.max_unsigned ->
  memory_block sh n p * memory_block sh m p |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p; try solve [rewrite FF_sepcon; auto].
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite sepcon_comm.
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; omega | rewrite Z2Nat.id; omega].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; omega | rewrite Z2Nat.id; omega].
  unfold memory_block'_alt.
  if_tac.
  + apply VALspec_range_overlap.
    exists (b, Ptrofs.unsigned i).
    simpl; repeat split; auto; try omega;
    rewrite Z2Nat.id; omega.
  + apply nonlock_permission_bytes_overlap; auto.
    exists (b, Ptrofs.unsigned i).
    repeat split; auto; try rewrite Z2Nat.id; omega.
Qed.

Lemma memory_block_non_pos_Vptr: forall sh n b z, n <= 0 -> memory_block sh n (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  rewrite Z_to_nat_neg by auto.
  unfold memory_block'.
  pose proof Ptrofs.unsigned_range z.
  assert (Ptrofs.unsigned z + n < Ptrofs.modulus) by omega.
  apply pred_ext; normalize.
  apply andp_right; auto.
  intros ? _; simpl; auto.
Qed.

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) = emp.
Proof.
  intros; apply memory_block_non_pos_Vptr.
  omega.
Qed.

Lemma mapsto_zeros_memory_block: forall sh n p,
  readable_share sh ->
  mapsto_zeros n sh p |--
  memory_block sh n p.
Proof.
  intros.
  unfold mapsto_zeros.
  destruct p; try solve [intros ? ?; contradiction].
  rename i into ofs.
  intros. rename H into RS. pose proof I.
  unfold memory_block.
  destruct (zlt n 0).   {
     rewrite Z_to_nat_neg by omega. simpl.
     apply andp_derives; auto.
     intros ? ?. simpl in *. destruct H0.
     omega. 
  }
 apply prop_andp_left; intros [? ?].
 rewrite prop_true_andp by omega.
 assert (n <= Ptrofs.modulus) by omega. clear H H0. rename H1 into H'.
 assert (0 <= n <= Ptrofs.modulus) by omega. clear H2 g.
    rewrite <- (Z2Nat.id n) in H', H by omega.
    forget (Z.to_nat n) as n'.
    clear n.
    remember (Ptrofs.unsigned ofs) as ofs'.
    assert (Ptrofs.unsigned (Ptrofs.repr ofs') = ofs')
      by (subst; rewrite Ptrofs.repr_unsigned; reflexivity).
    assert (0 <= ofs' /\ ofs' + Z.of_nat n' <= Ptrofs.modulus).
    {
      pose proof Ptrofs.unsigned_range ofs.
      omega.
    }
    clear Heqofs' H'.
    assert (Ptrofs.unsigned (Ptrofs.repr ofs') = ofs' \/ n' = 0%nat) by tauto.
    clear H0; rename H2 into H0.
    revert ofs' H H1 H0; induction n'; intros.
    - simpl; auto.
    - destruct H1.
      rewrite inj_S in H2. unfold Z.succ in H2. simpl.
      apply sepcon_derives; auto.
      * unfold mapsto_, mapsto. simpl.
        rewrite if_true by auto.
        apply orp_right2.
        rewrite prop_true_andp by auto.
        apply exp_right with (Vint Int.zero).
        destruct H0; [| omega].
        rewrite H0.
        auto.
      * fold address_mapsto_zeros. fold memory_block'.
        apply IHn'. omega. omega.
        destruct (zlt (ofs' + 1) Ptrofs.modulus).
        rewrite Ptrofs.unsigned_repr; [left; reflexivity | ].
        unfold Ptrofs.max_unsigned; omega.
        right.
           destruct H0; [| inversion H0].
           omega.
Qed.

Lemma memory_block'_split:
  forall sh b ofs i j,
   0 <= i <= j ->
    j <= j+ofs < Ptrofs.modulus ->
   memory_block' sh (Z.to_nat j) b ofs =
      memory_block' sh (Z.to_nat i) b ofs * memory_block' sh (Z.to_nat (j-i)) b (ofs+i).
Proof.
  intros.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try omega.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try omega.
  rewrite memory_block'_eq; try rewrite Z2Nat.id; try omega.
  unfold memory_block'_alt.
  repeat (rewrite Z2Nat.id; try omega).
  if_tac.
  + etransitivity ; [ | eapply VALspec_range_split2; [reflexivity | omega | omega]].
    f_equal.
    omega.
  + apply nonlock_permission_bytes_split2; omega.
Qed.

Lemma memory_block_split:
  forall (sh : share) (b : block) (ofs n m : Z),
  0 <= n ->
  0 <= m ->
  n + m <= n + m + ofs < Ptrofs.modulus ->
  memory_block sh (n + m) (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh n (Vptr b (Ptrofs.repr ofs)) *
  memory_block sh m (Vptr b (Ptrofs.repr (ofs + n))).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_split with (i := n); [| omega |].
  2:{
    pose proof Ptrofs.unsigned_range (Ptrofs.repr ofs).
    pose proof Ptrofs.unsigned_repr_eq ofs.
    assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; omega).
    omega.
  } 
  replace (n + m - n) with m by omega.
  replace (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr ofs) + n)) with
    (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr (ofs + n)))).
  2: {
    destruct (zeq m 0).
    + subst. reflexivity.
    + assert (ofs + n < Ptrofs.modulus) by omega.
      rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
      reflexivity.
  }
  apply pred_ext.
  + apply prop_andp_left; intros.
    apply sepcon_derives; (apply andp_right; [intros ? _; simpl | apply derives_refl]).
    - omega.
    - rewrite Ptrofs.unsigned_repr_eq.
      assert ((ofs + n) mod Ptrofs.modulus <= ofs + n) by (apply Z.mod_le; omega).
      omega.
  + apply andp_right; [intros ? _; simpl |].
    - rewrite Ptrofs.unsigned_repr_eq.
      assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; omega).
      omega.
    - apply sepcon_derives; apply andp_left2; apply derives_refl.
Qed.

Lemma memory_block_share_join:
  forall sh1 sh2 sh n p,
   sepalg.join sh1 sh2 sh ->
   memory_block sh1 n p * memory_block sh2 n p = memory_block sh n p.
Proof.
  intros.
  destruct p; try solve [unfold memory_block; rewrite FF_sepcon; auto].
  destruct (zle 0 n).
  2:{
    rewrite !memory_block_non_pos_Vptr by omega.
    rewrite emp_sepcon; auto.
  }
  unfold memory_block.
  destruct (zlt (Ptrofs.unsigned i + n) Ptrofs.modulus).
  + rewrite !prop_true_andp by auto.
    repeat (rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; omega | rewrite Z2Nat.id; omega]).
    unfold memory_block'_alt.
    destruct (readable_share_dec sh1), (readable_share_dec sh2).
    - rewrite if_true by (eapply readable_share_join; eauto).
      apply VALspec_range_share_join; auto.
    - rewrite if_true by (eapply readable_share_join; eauto).
      rewrite sepcon_comm.
      apply nonlock_permission_bytes_VALspec_range_join; auto.
    - rewrite if_true by (eapply readable_share_join; eauto).
      apply nonlock_permission_bytes_VALspec_range_join; auto.
    - rewrite if_false.
      * apply nonlock_permission_bytes_share_join; auto.
      * eapply join_unreadable_shares; eauto.
  + rewrite !prop_false_andp by auto.
    rewrite FF_sepcon; auto.
Qed.

Lemma mapsto_pointer_void:
  forall sh t a, 
   eqb_type (Tpointer t a) int_or_ptr_type = false ->
   eqb_type (Tpointer Tvoid a) int_or_ptr_type = false ->
   mapsto sh (Tpointer t a) = mapsto sh (Tpointer Tvoid a).
Proof.
intros.
unfold mapsto.
extensionality v1 v2.
unfold tc_val', tc_val. rewrite H, H0.
reflexivity.
Qed.

Lemma is_pointer_or_null_nullval: is_pointer_or_null nullval.
Proof.
unfold is_pointer_or_null, nullval.
simple_if_tac; auto.
Qed.
Hint Resolve is_pointer_or_null_nullval : core.

Lemma tc_val_pointer_nullval':
 forall t a, tc_val (Tpointer t a) nullval.
Proof.
 intros. hnf. unfold nullval.
 simple_if_tac; hnf;
 simple_if_tac; auto.
Qed.
Hint Resolve tc_val_pointer_nullval' : core.

Arguments type_is_volatile ty / .

Definition is_int32_noattr_type t :=
 match t with
 | Tint I32 _ {| attr_volatile := false; attr_alignas := None |} => True
 | _ => False
 end.

Lemma mapsto_mapsto_int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto sh t2 p v.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
apply derives_refl.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto_ sh t2 p.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
unfold mapsto_. apply mapsto_mapsto_.
Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh (Tint I32 Unsigned noattr) = mapsto sh (Tint I32 Signed noattr).
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma tc_val_pointer_nullval:
 forall t, tc_val (Tpointer t noattr) nullval.
Proof.
 intros. unfold nullval; simpl.
 rewrite andb_false_r.
 hnf. simple_if_tac; auto.
Qed.
Hint Resolve tc_val_pointer_nullval : core.

Lemma mapsto_tuint_tptr_nullval:
  forall sh p t, mapsto sh (Tpointer t noattr) p nullval = mapsto sh size_t p nullval.
Proof.
intros.
unfold mapsto, size_t.
destruct p; try reflexivity.
destruct Archi.ptr64 eqn:Hp.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile;  cbv beta iota.
unfold Mptr; rewrite Hp. 
if_tac.
rewrite !prop_true_andp by auto.
f_equal.
rewrite prop_true_andp; auto.
unfold nullval;rewrite Hp; apply I.
f_equal.
f_equal.
f_equal.
apply prop_ext; split; intros _ _;
unfold nullval; rewrite Hp; hnf; auto.
simple_if_tac; simpl; rewrite Hp; auto.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile;  cbv beta iota.
unfold Mptr; rewrite Hp. 
if_tac.
rewrite !prop_true_andp by auto.
f_equal.
rewrite prop_true_andp; auto.
unfold nullval;rewrite Hp; apply I.
f_equal.
f_equal.
f_equal.
apply prop_ext; split; intros _ _;
unfold nullval; rewrite Hp; hnf; auto.
simple_if_tac; simpl; rewrite Hp; auto.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
   Archi.ptr64 = false -> 
             mapsto sh (Tint I32 Signed noattr) v nullval =
             mapsto sh (Tpointer t noattr) v nullval.
Proof.
  intros.
  try solve [inversion H];
 (
  unfold mapsto, nullval; rewrite H;
  simpl;
  destruct v; auto; f_equal; auto;
  if_tac;
   [f_equal; f_equal; rewrite andb_false_r;
   unfold is_pointer_or_null; rewrite H;
   apply pred_ext; unfold derives; simpl; tauto
   | f_equal; f_equal;
      unfold tc_val';
      f_equal; simpl; 
      simple_if_tac; simpl; rewrite H; auto;
      apply prop_ext; intuition]).
Qed.
