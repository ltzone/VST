Require Import progs.ghost.
Require Import mailbox.verif_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.hashtable1.
Require Import mailbox.hashtable.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition integer_hash_spec :=
 DECLARE _integer_hash
  WITH i : Z
  PRE [ _i OF tint ]
   PROP () LOCAL (temp _i (vint i)) SEP ()
  POST [ tint ]
   PROP () LOCAL (temp ret_temp (vint (i * 654435761))) SEP ().
(* One might think it should just return an unknown number, but in fact it needs to follow a known hash
   function at the logic level to be useful. *)

Definition tentry := Tstruct _entry noattr.

Instance hf1 : hash_fun := { size := 16384; hash i := (i * 654435761) mod 16384 }.
Proof.
  - computable.
  - intro; apply Z_mod_lt; computable.
Defined.

(* Once set, a key is never reset. *)
Definition k_R (h : list hist_el) (v : Z) := !!(Forall int_op h /\
  forall e, In e h -> value_of e <> vint 0 -> vint v = value_of e) && emp.

Definition v_R (h : list hist_el) (v : Z) := emp.

(* Entries are no longer consecutive. *)
Definition wf_hists h := Forall (fun x => (ordered_hist (fst x) /\ Forall int_op (map snd (fst x))) /\
  (ordered_hist (snd x) /\ Forall int_op (map snd (snd x)))) h.

Definition make_map h :=
  map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs)))) h.

Definition atomic_entry sh pk pv hk hv :=
  atomic_loc_hist sh pk 0 k_R hk * atomic_loc_hist sh pv 0 v_R hv.

Definition atomic_entries sh entries hists := fold_right sepcon emp
  (map (fun x => let '((pk, pv), (hk, hv)) := x in atomic_entry sh pk pv hk hv) (combine entries hists)).

Definition failed_CAS k (a b : hist * hist) := exists t r, newer (fst a) t /\ repable_signed r /\
  (fst b = fst a ++ [(t, Load (vint r))] \/
   exists t1 t2, (t < t1 < t2)%nat /\
     fst b = fst a ++ [(t, Load (vint 0)); (t1, CAS (vint r) (vint 0) (vint k)); (t2, Load (vint r))]) /\
  r <> 0 /\ r <> k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = vint r).

Definition found_key k (a b : hist) := (exists t, newer a t /\
  (b = a ++ [(t, Load (vint k))] \/ exists t1, (t < t1)%nat /\
   (b = a ++ [(t, Load (vint 0)); (t1, CAS (vint 0) (vint 0) (vint k))] \/ exists t2, (t1 < t2)%nat /\
    b = a ++ [(t, Load (vint 0)); (t1, CAS (vint k) (vint 0) (vint k)); (t2, Load (vint k))]))) /\
  let v := value_of_hist a in v <> vint 0 -> v = vint k.

Definition set_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ found_key k (fst (Znth i h ([], []))) (fst (Znth i h' ([], []))) /\
  (exists tv, newer (snd (Znth i h ([], []))) tv /\
   snd (Znth i h' ([], [])) = snd (Znth i h ([], [])) ++ [(tv, Store (vint v))]) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist),
   PROP (set_item_trace h key value i h')
   LOCAL ()
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').
(* set_item_trace_map describes the properties on the resulting map. *)

Definition failed_load k (a b : hist * hist) := exists t r, newer (fst a) t /\ repable_signed r /\
  fst b = fst a ++ [(t, Load (vint r))] /\ r <> 0 /\ r <> k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = vint r).

(* get_item can return 0 in two cases: if the key is not in the map, or if its value is 0.
   In correct use, the latter should only occur if the value has not been initialized.
   Conceptually, this is still linearizable because we could have just checked before the key was added,
   but at a finer-grained level we can tell the difference from the history, so we might as well keep
   this information. *)
Definition get_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\
  (let '(hk, hv) := Znth i h ([], []) in exists t r, newer hk t /\
     fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint r))] /\
     (v = 0 /\ r = 0 /\ snd (Znth i h' ([], [])) = hv \/
      r = k /\ exists tv, Forall (fun x => fst x < tv)%nat hv /\
        snd (Znth i h' ([], [])) = hv ++ [(tv, Load (vint v))]) /\
    (let v := value_of_hist hk in v <> vint 0 -> v = vint r)) /\
  forall j, (In j (indices (hash k) i) -> failed_load k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tint ]
   EX value : Z, EX i : Z, EX h' : list (hist * hist),
   PROP (repable_signed value; get_item_trace h key value i h')
   LOCAL (temp ret_temp (vint value))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').

Definition add_item_trace (h : list (hist * hist)) k v i (success : bool) h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ (let '(hk, hv) := Znth i h ([], []) in if success then
    exists t t1 tv, newer hk t /\ newer hv tv /\ (t < t1)%nat /\ fst (Znth i h' ([], [])) =
      hk ++ [(t, Load (vint 0)); (t1, CAS (vint 0) (vint 0) (vint k))] /\
      snd (Znth i h' ([], [])) = hv ++ [(tv, Store (vint v))] /\ value_of_hist hk = vint 0
    else (exists t, newer hk t /\ (fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint k))] \/
      exists t1 t2, (t < t1 < t2)%nat /\ fst (Znth i h' ([], [])) =
        hk ++ [(t, Load (vint 0)); (t1, CAS (vint k) (vint 0) (vint k)); (t2, Load (vint k))])) /\
      snd (Znth i h' ([], [])) = hv /\ let v := value_of_hist hk in v <> vint 0 -> v = vint k) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

Definition add_item_spec :=
 DECLARE _add_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tint ]
   EX success : bool, EX i : Z, EX h' : list (hist * hist),
   PROP (add_item_trace h key value i success h')
   LOCAL (temp ret_temp (Val.of_bool success))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').

Notation empty_hists := (repeat ([] : hist, [] : hist) (Z.to_nat size)).

Definition init_table_spec :=
 DECLARE _init_table
  WITH p : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _m_entries p)
   SEP (data_at_ Ews (tarray tentry size) p)
  POST [ tvoid ]
   EX entries : list (val * val),
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray tentry size) entries p; atomic_entries Tsh entries empty_hists).

Definition freeze_table_spec :=
 DECLARE _freeze_table
  WITH sh : share, p : val, entries : list (val * val), h : list (hist * hist), keys : val, values : val
  PRE [ _keys OF tptr tint, _values OF tptr tint ]
   PROP (readable_share sh; Zlength h = Zlength entries)
   LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries Tsh entries h;
        data_at_ Tsh (tarray tint size) keys; data_at_ Tsh (tarray tint size) values)
  POST [ tvoid ]
   EX lk : list Z, EX lv : list Z,
   PROP (Forall repable_signed lk; Forall repable_signed lv;
         Forall2 full_hist (map fst h) lk; Forall2 full_hist (map snd h) lv;
         Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e) (map fst h) lk)
   LOCAL ()
   SEP (data_at_ sh (tarray tentry size) p;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lk) keys;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lv) values).

Inductive add_items_trace : list (hist * hist) -> list (Z * Z * Z * bool) -> list (hist * hist) -> Prop :=
| add_nil_items : forall h, add_items_trace h [] h
| add_snoc_items : forall h la h' k v i s h'' (Hn : add_items_trace h la h')
    (Hadd : add_item_trace h' k v i s h''), add_items_trace h (la ++ [(k, v, i, s)]) h''.

Definition f_lock_inv sh entries p t locksp lockt resultsp res :=
  (EX h : list (hist * hist), EX li : list Z, EX ls : list bool,
  !!(Zlength li = 3 /\ Zlength ls = 3 /\
     add_items_trace empty_hists (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls) h) &&
   data_at sh (tarray tentry size) entries p * atomic_entries sh entries h *
   data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
   data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp *
   data_at Tsh tint (vint (Zlength (filter id ls))) res).

Definition f_lock_pred tsh sh entries p t locksp lockt resultsp res :=
  selflock (f_lock_inv sh entries p t locksp lockt resultsp res) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * list (val * val) * val * Z * val * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
   PROP (0 <= t < 3; isptr lockt; readable_share sh; readable_share tsh)
   LOCAL (temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res; lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs := ltac:(with_library prog [verif_atomics.makelock_spec; freelock2_spec;
  verif_atomics.acquire_spec; release2_spec; spawn_spec; surely_malloc_spec;
  make_atomic_spec; free_atomic_spec; load_SC_spec; store_SC_spec; CAS_SC_spec;
  integer_hash_spec; set_item_spec; get_item_spec; add_item_spec; init_table_spec; freeze_table_spec;
  f_spec; main_spec]).

Set Default Timeout 100.

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Ltac entailer_for_return ::= go_lower; entailer'.

Lemma indices_next : forall i j, ((j - i) mod size) < size - 1 -> indices i (j + 1) = indices i j ++ [j mod size].
Proof.
  intros; unfold indices.
  exploit (Z_mod_lt (j - i) size); [apply size_pos | intro].
  rewrite Z.add_sub_swap, <- Zplus_mod_idemp_l, Zmod_small by omega.
  rewrite Z2Nat.inj_add by omega.
  rewrite upto_app, map_app; simpl.
  change (upto 1) with [0]; simpl.
  rewrite Z2Nat.id, Z.add_0_r by (apply Z_mod_lt; computable).
  rewrite Zplus_mod_idemp_r, Zplus_minus; auto.
Qed.

Lemma update_entries_hist : forall sh entries h i hk hv pki pvi (Hlen : Zlength entries = Zlength h)
  (Hpi : Znth i entries (Vundef, Vundef) = (pki, pvi)) (Hi : 0 <= i < Zlength entries),
  atomic_entries sh entries (upd_Znth i h (hk, hv)) =
  fold_right sepcon emp (upd_Znth i (map (fun x => let '(pk, pv, (hk, hv)) := x in
    atomic_loc_hist sh pk 0 k_R hk * atomic_loc_hist sh pv 0 v_R hv) (combine entries h))
    (atomic_loc_hist sh pki 0 k_R hk * atomic_loc_hist sh pvi 0 v_R hv)).
Proof.
  intros; unfold atomic_entries.
  f_equal.
  erewrite upd_Znth_map with (v := (pki, pvi, (hk, hv))), combine_upd_Znth2, Hpi; auto.
Qed.

Lemma incr_invariant : forall (P : _ -> _ -> Prop) i1 i key (h h' : list (hist * hist)) h1
  (Hi1 : i1 = (i + hash key) mod size) (Hh' : Zlength h' = size) (Hinv : forall j,
  (In j (indices (hash key) (i + hash key)) -> P (Znth j h ([], [])) (Znth j h' ([], []))) /\
  (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
  (HP : P (Znth i1 h ([], [])) h1) (Hi : i mod size < size - 1) j,
  (In j (indices (hash key) ((i + 1) + hash key)) -> P (Znth j h ([], [])) (Znth j (upd_Znth i1 h' h1) ([], []))) /\
  (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j (upd_Znth i1 h' h1) ([], []) = Znth j h ([], [])).
Proof.
  intros; specialize (Hinv j); destruct Hinv.
  rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
  assert (0 <= i1 < Zlength h') by (subst; rewrite Hh'; apply Z_mod_lt, size_pos).
  assert (~ In i1 (indices (hash key) (i + hash key))) as Hnew.
  { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
    rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
    subst; rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
    rewrite Zmod_small in Heq; [omega|].
    destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
  split.
  * intros [Hin | Hin].
    { rewrite upd_Znth_diff'; auto.
      intro; contradiction Hnew; subst; auto. }
    simpl in Hin; destruct Hin; [subst | contradiction].
    simpl in *; rewrite upd_Znth_same; auto.
  * intro Hout; rewrite upd_Znth_diff'; auto.
    intro; contradiction Hout; subst; simpl; auto.
  * rewrite Z.add_simpl_r; auto.
Qed.

Lemma k_R_precise : forall v, precise (EX h : _, k_R h v).
Proof.
  intros; apply derives_precise' with (Q := emp); auto.
  unfold k_R; entailer!.
Qed.

Lemma v_R_precise : forall v, precise (EX h : _, v_R h v).
Proof.
  intros; apply derives_precise' with (Q := emp); auto.
  unfold v_R; entailer!.
Qed.
Hint Resolve k_R_precise v_R_precise.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.

Ltac solve_efield_denote Delta P Q R efs gfs H ::=   evar (gfs : list gfield);
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfs) as H; 
  [
    unfold efs, gfs;
    match goal with
    | efs := nil |- _ =>
      instantiate (1 := nil);
      apply prop_right, I
    | efs := ?ef :: ?efs' |- _ =>
      let efs0 := fresh "efs" in
      let gfs0 := fresh "gfs" in
      let H0 := fresh "H" in
      pose efs' as efs0;
      solve_efield_denote Delta P Q R efs0 gfs0 H0;
      match goal with
      | gfs0 := ?gfs0' |- _ =>
        match ef with
        | eArraySubsc ?ei => 

          let HA := fresh "H" in
          let vi := fresh "vi" in evar (vi: val);
          do_compute_expr Delta P Q R ei vi HA;

          revert vi HA;
          let vvvv := fresh "vvvv" in
          let HHHH := fresh "HHHH" in
            match goal with
            | |- let vi := ?V in _ => remember V as vvvv eqn:HHHH
            end;
          autorewrite with norm in HHHH;
      
          match type of HHHH with
          | _ = Vint (Int.repr _) => idtac
          | _ = Vint (Int.sub _ _) => unfold Int.sub in HHHH
          | _ = Vint (Int.add _ _) => unfold Int.add in HHHH
          | _ = Vint (Int.mul _ _) => unfold Int.mul in HHHH
          | _ = Vint (Int.and _ _) => unfold Int.and in HHHH
          | _ = Vint (Int.or _ _) => unfold Int.or in HHHH
          | _ = Vint ?V =>
            replace V with (Int.repr (Int.unsigned V)) in HHHH
              by (rewrite (Int.repr_unsigned V); reflexivity)
          end;
          (* subst vvvv; *)
          rewrite HHHH in *; clear HHHH; (* Without this replacement, subst fails, and the next forward runs forever! *)
          intros vi HA;

          match goal with
          | vi := Vint (Int.repr ?i) |- _ => instantiate (1 := ArraySubsc i :: gfs0')
          end;
          
          let HB := fresh "H" in
          assert (match typeof ei with | Tint _ _ _ => True | _ => False end) as HB by (simpl; auto);
          
          apply (efield_denote_cons_array _ _ _ _ _ H0 HA HB)

        | eStructField ?i =>
          instantiate (1 := StructField i :: gfs0');
          apply efield_denote_cons_struct, H0
        | eUnionField ?i =>
          instantiate (1 := UnionField i :: gfs0');
          apply efield_denote_cons_union, H0
        end
      end
    end
  |].

    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki 0 k_R hki emp (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v.
    simpl; Intros t.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
      forward_if (EX hki' : hist, PROP (found_key key hki hki') (LOCALx Q
        (SEPx (atomic_loc_hist sh pki 0 k_R hki' :: R)))) end.
    + match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v = 0) (LOCALx Q (SEPx R))) end.
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint v))], hvi)).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
        rewrite sepcon_assoc; auto. }
      { forward.
        entailer!. }
      Intros; subst.
      forward_call (ACAS_witness sh pki 0 k_R (hki ++ [(t, Load (vint 0))]) 0 key emp
        (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
      { entailer!.
        setoid_rewrite Hpi; auto. }
      { repeat (split; auto).
        apply ACAS_hist_spec; auto.
        intros ???????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; [| |contradiction].
          * intros.
            if_tac; auto; absurd (value_of e = vint 0); auto.
            subst; symmetry; auto.
          * subst; simpl; intros.
            if_tac; if_tac; auto; [subst; absurd (vint 0 = vint 0); auto|].
            absurd (v' = 0); auto; apply repr_inj_signed; auto; congruence.
        + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
          exploit Hhist.
          { rewrite in_app; eauto. }
          intro X; apply nth_error_In in X; subst; auto. }
      Intros v t'.
      assert (t < t')%nat.
      { match goal with H : newer (hki ++ _) _ |- _ => unfold newer in H; rewrite Forall_app in H;
          destruct H as (_ & Ht); inv Ht; auto end. }
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
        forward_if (EX hki' : hist, PROP (found_key key hki hki') ((LOCALx Q)
        (SEPx (atomic_loc_hist sh pki 0 k_R hki' :: R)))) end.
      * destruct (eq_dec 0 v); [discriminate|].
        forward_call (AL_witness sh pki 0 k_R (hki ++ [(t, Load (vint 0)); (t', CAS (vint v) (vint 0) (vint key))]) emp (fun v' => !!(v' = v) && emp)).
        { entailer!.
          simpl in *; rewrite Hpi; auto. }
        { rewrite <- app_assoc; fast_cancel. }
        { repeat (split; auto).
          apply AL_hist_spec; auto.
          intros ???????????? Ha.
          unfold k_R in *; simpl in *.
          eapply semax_pre, Ha.
          go_lowerx; entailer!.
          repeat split.
          + rewrite Forall_app; repeat constructor; auto.
          + intros ? Hin; rewrite in_app in Hin.
            destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
          + match goal with H : forall e, In e h'0 -> _ |- _ =>
              exploit (H (CAS (vint v) (vint 0) (vint key))) end.
            { eapply nth_error_In, Hhist.
              rewrite in_app; simpl; eauto. }
            { simpl.
              if_tac; [absurd (v = 0)|]; auto.
              apply repr_inj_signed; auto; congruence. }
            simpl.
            if_tac; [absurd (v = 0)|]; auto; intros; apply repr_inj_signed; auto; congruence. }
        Intros v'; simpl; Intros t''; subst.
        assert (t' < t'')%nat.
        { match goal with H : newer (hki ++ [_; _]) _ |- _ => unfold newer in H; rewrite Forall_app in H;
            destruct H as (_ & Ht); inversion Ht as [|??? Ht']; inv Ht'; auto end. }
        match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROP (v = key) (LOCALx Q (SEPx R))) end.
        { eapply semax_pre; [|apply semax_continue].
          unfold POSTCONDITION, abbreviate, overridePost.
          destruct (eq_dec EK_continue EK_normal); [discriminate|].
          unfold loop1_ret_assert.
          go_lower.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++
            [(t, Load (vint 0)); (t', CAS (vint v) (vint 0) (vint key)); (t'', Load (vint v))], hvi)).
          apply andp_right.
          { apply prop_right; split.
            { rewrite upd_Znth_Zlength; auto; omega. }
            rewrite Zmod_mod.
            split; auto; split; auto; split; auto.
            apply incr_invariant; auto; simpl in *; try omega.
            * rewrite Heq, Hhi; do 3 eexists; [|split; [|split; [right; do 3 eexists; [|reflexivity]|]]]; auto.
              repeat split; auto.
              match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
                symmetry; apply H; auto end.
              rewrite ordered_last_value; auto.
            * admit. (* list is long enough *) }
          apply andp_right; [apply prop_right; auto|].
          fast_cancel.
          rewrite <- app_assoc.
          erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
          rewrite sepcon_assoc; auto. }
        { forward.
          entailer!. }
        intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        rewrite <- app_assoc; Exists (hki ++
          [(t, Load (vint 0)); (t', CAS (vint v) (vint 0) (vint key)); (t'', Load (vint v))]); entailer!.
        split; [do 2 eexists; eauto; right; do 2 eexists; eauto|].
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * forward.
        destruct (eq_dec 0 v); [|discriminate].
        subst; rewrite <- app_assoc.
        Exists (hki ++ [(t, Load (vint 0)); (t', CAS (vint 0) (vint 0) (vint key))]); entailer!.
        split; [do 2 eexists; eauto|].
        intros ? X; contradiction X.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        Intros hki'.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        Exists hki'; entailer!.
    + forward.
      subst; Exists (hki ++ [(t, Load (vint key))]); entailer!.
      split; [eauto|].
      match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
        symmetry; apply H; auto end.
      apply ordered_last_value; auto.
    + rewrite (atomic_loc_isptr _ pvi).
      Intros hki'.
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (AS_witness sh pvi 0 v_R hvi value emp emp).
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      { repeat (split; auto).
        apply AS_hist_spec; auto.
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!. }
      Intros t'.
      forward.
      Exists (i1 mod size) (upd_Znth (i1 mod size) h' (hki', hvi ++ [(t', Store (vint value))])).
      apply andp_right; auto.
      apply andp_right.
      { apply prop_right; split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split; auto.
        split; eauto.
        assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
        { unfold indices.
          replace (i1 mod size) with ((i + hash key) mod size).
          rewrite Zminus_mod_idemp_l; auto. }
        simpl in Hindex; split.
        + intro Hin; simpl in *.
          rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          rewrite Hindex; auto.
          { intro; contradiction Hnew; subst.
            rewrite Hindex; auto. }
        + intros Hout ?; rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          { intro; contradiction Hout; subst; simpl.
            rewrite <- Hindex; auto. } }
      apply andp_right; auto.
      fast_cancel.
      erewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_loc_hist _ _ _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; auto; omega.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki 0 k_R hki emp (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v; simpl; Intros t.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v <> key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ pvi).
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (AL_witness sh pvi 0 v_R hvi emp (fun (v : Z) => emp)).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { repeat (split; auto).
        apply AL_hist_spec; auto.
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!. }
      subst; Intros v; simpl; Intros t'.
      forward.
      Exists v (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint key))],
        hvi ++ [(t', Load (vint v))])).
      apply andp_right.
      { apply prop_right.
        split; auto.
        split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
          { unfold indices.
            replace (i1 mod size) with ((i + hash key) mod size).
            rewrite Zminus_mod_idemp_l; auto. }
          simpl in Hindex; split.
          + intro Hin; simpl in *.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
      apply andp_right; [apply prop_right; auto|].
      fast_cancel.
      erewrite <- !sepcon_assoc, (sepcon_assoc _ (atomic_loc _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; [|omega].
      rewrite (sepcon_comm (atomic_loc_hist _ _ _ _ _)); auto.
    + forward.
      entailer!.
    + Intros; match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v <> 0) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists 0 (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0))], hvi)).
        apply andp_right.
        { apply prop_right.
          split; [split; computable|].
          split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
          { unfold indices.
            replace (i1 mod size) with ((i + hash key) mod size).
            rewrite Zminus_mod_idemp_l; auto. }
          simpl in Hindex; split.
          + intro Hin; simpl in *.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      * forward.
        entailer!.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint v))], hvi)).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size).
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_add_item : semax_body Vprog Gprog f_add_item add_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert (0 <= i1 mod size < Zlength h) by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki 0 k_R hki emp (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v; simpl; Intros t.
    assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
    { unfold indices.
      replace (i1 mod size) with ((i + hash key) mod size).
      rewrite Zminus_mod_idemp_l; auto. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v <> key) (LOCALx Q (SEPx R))) end.
    { forward.
      Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint key))], hvi));
        entailer!.
      + split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [auto|].
        setoid_rewrite Heq; rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl.
        split; [repeat split; eauto|].
        { match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto. }
        simpl in Hindex; split.
        * intro Hin; simpl in *.
          rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          simpl in *; rewrite Hindex; auto.
          { intro; contradiction Hnew; subst.
            simpl in *; rewrite Hindex; auto. }
        * intros Hout ?; rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          { intro; contradiction Hout; subst; simpl.
            rewrite <- Hindex; auto. }
      + erewrite replace_nth_sepcon, update_entries_hist; eauto; [|omega].
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto. }
    { forward.
      entailer!. }
    Intros.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v = 0) (LOCALx Q (SEPx R))) end.
    { eapply semax_pre; [|apply semax_continue].
      unfold POSTCONDITION, abbreviate, overridePost.
      destruct (eq_dec EK_continue EK_normal); [discriminate|].
      unfold loop1_ret_assert.
      instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
        PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
        forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
          (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
        LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
        SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
      Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint v))], hvi)).
      go_lower.
      apply andp_right.
      { apply prop_right; split.
        { rewrite upd_Znth_Zlength; auto; omega. }
        rewrite Zmod_mod.
        split; auto; split; auto; split; auto.
        apply incr_invariant; auto; simpl in *; try omega.
        * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        * admit. (* list is long enough *) }
      apply andp_right; [apply prop_right; auto|].
      fast_cancel.
      erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
      rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto. }
    { forward.
      entailer!. }
    Intros; subst.
    forward_call (ACAS_witness sh pki 0 k_R (hki ++ [(t, Load (vint 0))]) 0 key emp (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply ACAS_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; [| |contradiction].
        * intros.
          assert (vint v' = value_of e) by auto.
          if_tac; auto.
          subst; absurd (value_of e = vint 0); auto.
        * subst; simpl; intros.
          if_tac; if_tac; auto; [absurd (vint v' = vint 0); subst; auto|].
          absurd (v' = 0); auto; apply repr_inj_signed; auto; congruence.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        exploit Hhist.
        { rewrite in_app; eauto. }
        intro X; apply nth_error_In in X; subst; auto. }
    Intros v; simpl; Intros t'.
    assert (t < t')%nat.
    { match goal with H : newer (hki ++ _) _ |- _ => unfold newer in H; rewrite Forall_app in H;
        destruct H as (_ & Ht); inv Ht; auto end. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v = 0) ((LOCALx Q) (SEPx R))) end.
    { destruct (eq_dec 0 v); [discriminate|].
      forward_call (AL_witness sh pki 0 k_R (hki ++ [(t, Load (vint 0)); (t', CAS (vint v) (vint 0) (vint key))])
        emp (fun v' => !!(v' = v) && emp)).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { rewrite <- app_assoc; fast_cancel. }
      { repeat (split; auto).
        apply AL_hist_spec; auto.
        intros ???????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
        + match goal with H : forall e, In e _ -> _ |- _ =>
            exploit (H (CAS (vint v) (vint 0) (vint key))) end.
          { eapply nth_error_In, Hhist.
            rewrite in_app; simpl; eauto. }
          { simpl.
            if_tac; [absurd (v = 0)|]; auto; apply repr_inj_signed; auto; congruence. }
          simpl.
          if_tac; [absurd (v = 0)|]; auto; intros; apply repr_inj_signed; auto; congruence. }
      Intros v'; simpl; Intros t''; subst.
      assert (t' < t'')%nat.
      { match goal with H : newer (hki ++ [_; _]) _ |- _ => unfold newer in H; rewrite Forall_app in H;
          destruct H as (_ & Ht); inversion Ht as [|??? Ht']; inv Ht'; auto end. }
      match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (fun _ : environ => FF) end.
      - forward.
        Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0));
          (t', CAS (vint key) (vint 0) (vint key)); (t'', Load (vint key))], hvi));
          entailer!.
        + split.
          { rewrite upd_Znth_Zlength; auto. }
          split; [auto|].
          setoid_rewrite Heq; rewrite Hhi; simpl.
          rewrite upd_Znth_same by auto; simpl.
          split; [repeat split; [do 2 eexists; [|right; eauto]|]|]; auto.
          { match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto. }
          simpl in Hindex; split.
          * intro Hin; simpl in *.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          * intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. }
        + erewrite <- app_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
          rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      - eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        go_lower.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++
          [(t, Load (vint 0)); (t', CAS (vint v) (vint 0) (vint key)); (t'', Load (vint v))], hvi)).
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; do 3 eexists; [|split; [|split; [right; do 3 eexists; [|reflexivity]|]]]; auto;
              repeat split; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- app_assoc, <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      - intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; go_lowerx; contradiction. }
    { forward.
      destruct (eq_dec 0 v); [|discriminate].
      entailer!. }
    rewrite (atomic_loc_isptr _ pvi).
    Intros; subst; simpl in Hpi.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    forward_call (AS_witness sh pvi 0 v_R hvi value emp emp).
    { entailer!.
      rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AS_hist_spec; auto.
      intros ???????????? Ha.
      unfold v_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!. }
    Intros tv.
    forward.
    Exists true (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0));
      (t', CAS (vint 0) (vint 0) (vint key))], hvi ++ [(tv, Store (vint value))])).
    apply andp_right.
    { apply prop_right; split; auto.
      split.
      { rewrite upd_Znth_Zlength; auto. }
      split; [auto|].
      setoid_rewrite Heq.
      rewrite Hhi; simpl.
      rewrite upd_Znth_same by auto; simpl; split; [repeat eexists; auto|].
      { destruct (eq_dec (value_of_hist hki) (vint 0)); auto.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
          symmetry; apply H; auto end.
        rewrite ordered_last_value; auto. }
      split.
      + intro Hin.
        rewrite upd_Znth_diff'; auto.
        match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
        rewrite Hindex; auto.
        { intro; contradiction Hnew; subst.
          rewrite Hindex; auto. }
      + intros Hout ?; simpl in *; rewrite upd_Znth_diff'; auto.
        match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
        { intro; contradiction Hout; subst; simpl.
          rewrite <- Hindex; auto. } }
    apply andp_right; [apply prop_right; auto|].
    fast_cancel.
    erewrite <- app_assoc, <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; [|omega].
    rewrite (sepcon_assoc _ (atomic_loc _ _ _)), sepcon_comm; auto.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Opaque size.
Opaque Znth.

Lemma Zlength_empty : Zlength empty_hists = size.
Proof.
  rewrite Zlength_repeat, Z2Nat.id; auto.
  pose proof size_pos; omega.
Qed.

Lemma body_init_table : semax_body Vprog Gprog f_init_table init_table_spec.
Proof.
  start_function.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p)
    SEP (EX entries : list (val * val),
      !!(Zlength entries = i) &&
        @data_at CompSpecs Ews (tarray tentry size) (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i))) p *
        atomic_entries Tsh entries (repeat ([], []) (Z.to_nat i)))).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil (val * val)); entailer!.
    rewrite data_at__eq; unfold default_val; simpl.
    rewrite repeat_list_repeat, Z.sub_0_r; auto.
  - Intros entries.
    forward_call (MA_witness 0 k_R).
    { unfold k_R; entailer!. }
    { split; [|split; computable].
      apply MA_hist_spec; auto. }
    Intro k.
    forward.
    forward_call (MA_witness 0 v_R).
    { unfold v_R; entailer!. }
    { split; [|split; computable].
      apply MA_hist_spec; auto. }
    Intro v.
    forward.
    assert (0 <= Zlength entries < Zlength (entries ++
      repeat (Vundef, Vundef) (Z.to_nat (size - Zlength entries)))).
    { rewrite Zlength_app, Zlength_repeat, Z2Nat.id; omega. }
    subst; rewrite upd_Znth_twice, upd_complete_gen by (auto; omega).
    Exists (entries ++ [(k, v)]); entailer!.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; auto.
    + rewrite upd_Znth_same by auto.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
      unfold atomic_entries.
      rewrite Z2Nat.inj_add, repeat_plus by omega; simpl.
      rewrite combine_app, map_app, sepcon_app; simpl.
      unfold atomic_entry, atomic_loc_hist; entailer!.
      { rewrite repeat_length, Zlength_correct, Nat2Z.id; auto. }
  - Intros entries.
    rewrite Zminus_diag, app_nil_r.
    forward.
    Exists entries; entailer!.
Qed.

Lemma body_freeze_table : semax_body Vprog Gprog f_freeze_table freeze_table_spec.
Proof.
  start_function.
  assert_PROP (Zlength entries = size) as Hlen by entailer!.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         atomic_entries Tsh (sublist i (Zlength entries) entries) (sublist i (Zlength entries) h);
         EX lk : list Z, EX lv : list Z, !!(Zlength lk = i /\ Zlength lv = i /\
           Forall repable_signed lk /\ Forall repable_signed lv /\
           Forall2 full_hist (map fst (sublist 0 i h)) lk /\ Forall2 full_hist (map snd (sublist 0 i h)) lv /\
           Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
             (map fst (sublist 0 i h)) lk) &&
           data_at Tsh (tarray tint size) (map (fun x => vint x) lk ++ repeat Vundef (Z.to_nat (Zlength entries - i))) keys *
           data_at Tsh (tarray tint size) (map (fun x => vint x) lv ++ repeat Vundef (Z.to_nat (Zlength entries - i))) values)).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil Z) (@nil Z); rewrite sublist_nil.
    go_lower; repeat (apply andp_right; [apply prop_right; auto|]).
    rewrite !sublist_same by (auto; omega).
    repeat (apply sepcon_derives; [auto|]).
    + apply andp_right; [apply prop_right; repeat (split; auto)|].
      rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
    + rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
  - Intros lk lv.
    unfold atomic_entries.
    rewrite sublist_next with (d := (Vundef, Vundef)) by omega.
    rewrite sublist_next with (d := ([], [])) by omega; simpl.
    destruct (Znth i entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth i h ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pki, hist_R pki 0 k_R).
    unfold hist_R; Intros ki lki.
    gather_SEP 3 0; rewrite hist_ref_join by (apply Share.nontrivial).
    Intro hk'; unfold hist_sub; rewrite eq_dec_refl; Intros; subst hk'.
    forward.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pvi, hist_R pvi 0 v_R).
    unfold hist_R; Intros vi lvi.
    gather_SEP 5 0; rewrite hist_ref_join by (apply Share.nontrivial).
    Intro hv'; unfold hist_sub; rewrite eq_dec_refl; Intros; subst hv'.
    forward.
    Exists (lk ++ [ki]) (lv ++ [vi]).
    go_lower.
    unfold v_R, k_R; Intros.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    apply andp_right.
    + apply prop_right.
      repeat (split; [repeat split; auto; omega|]).
      rewrite sublist_split with (mid := i), sublist_len_1 with (d := ([], [])), !map_app, Hhi by omega.
      do 2 (split; [rewrite Forall_app; auto|]).
      split; [|split]; apply Forall2_app; auto; repeat constructor; unfold full_hist; eauto.
      intros t e Hin; match goal with H : hist_list hki _ |- _ => apply H, nth_error_in in Hin; auto end.
    + rewrite !sepcon_emp, !sepcon_assoc.
      rewrite <- emp_sepcon; apply sepcon_derives; [admit|]. (* deallocate ghost *)
      rewrite <- emp_sepcon; apply sepcon_derives; [admit|].
      apply sepcon_derives; [auto|].
      apply sepcon_derives; [auto|].
      rewrite !map_app; simpl.
      replace (i + 1) with (Zlength (map (fun x => vint x) lk ++ [vint ki]))
        by (rewrite Zlength_app, Zlength_map, Zlength_cons, Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      replace (Zlength (map _ _ ++ _)) with (Zlength (map (fun x => vint x) lv ++ [vint vi]))
        by (rewrite !Zlength_app, !Zlength_map, !Zlength_cons, !Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      rewrite !Zlength_map.
      apply sepcon_derives; [replace i with (Zlength lk) | replace i with (Zlength lv)]; auto.
  - Intros lk lv; forward.
    rewrite Hlen, Zminus_diag, !app_nil_r, !sublist_nil.
    repeat match goal with H : Forall2 _ (map _ (sublist _ _ _)) _ |- _ =>
      rewrite sublist_same in H by (auto; omega) end.
    Exists lk lv; entailer!.
Admitted.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma add_item_trace_wf : forall h k v i s h' (Hwf : wf_hists h) (Htrace : add_item_trace h k v i s h'),
  wf_hists h'.
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
  apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
  destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
  - subst; rewrite Hhi in *.
    destruct s.
    + destruct Hi as (? & ? & ? & ? & ? & ? & Hi1 & Hi2 & ?); rewrite Hi1, Hi2.
      rewrite !map_app, !Forall_app; repeat constructor; auto; try (apply ordered_snoc; auto).
      rewrite app_cons_assoc; repeat apply ordered_snoc; auto.
      apply newer_snoc; auto.
    + destruct Hi as ((? & ? & Hi1) & -> & ?).
      split; auto.
      destruct Hi1 as [-> | (? & ? & ? & ->)]; rewrite !map_app, !Forall_app; repeat constructor; auto;
        try (apply ordered_snoc; auto).
      rewrite 2app_cons_assoc; repeat apply ordered_snoc; auto; repeat apply newer_snoc; auto; omega.
  - destruct Hrest as ((? & ? & ? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
    split; auto.
    destruct Hcase as [-> | (? & ? & (? & ?) & ->)]; rewrite map_app, Forall_app; repeat constructor; auto.
    + apply ordered_snoc; auto.
    + rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
        repeat apply newer_snoc; auto.
  - destruct Hrest as (_ & ->); auto.
Qed.

Corollary add_items_trace_wf : forall h la h', add_items_trace h la h' ->
  wf_hists h -> wf_hists h'.
Proof.
  induction 1; auto.
  intro; apply add_item_trace_wf in Hadd; auto.
Qed.

Lemma wf_empty : wf_hists empty_hists.
Proof.
  apply Forall_repeat; repeat split; simpl; auto; apply ordered_nil.
Qed.
Hint Resolve wf_empty.

Lemma add_items_length : forall h la h', add_items_trace h la h' -> Zlength h' = Zlength h.
Proof.
  induction 1; auto.
  destruct Hadd; omega.
Qed.

Lemma f_pred_precise : forall tsh sh entries p t locksp lockt resultsp res, readable_share sh ->
  precise (f_lock_pred tsh sh entries p t locksp lockt resultsp res).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_precise.
  unfold f_lock_inv.
  eapply derives_precise' with (Q := data_at_ _ _ _ *
    fold_right sepcon emp (map (fun p => (EX h : hist, atomic_loc_hist sh (fst p) 0 k_R h) *
                                         (EX h : hist, atomic_loc_hist sh (snd p) 0 v_R h)) entries) *
    data_at_ sh _ _ * data_at_ _ _ _ * data_at_ _ _ _).
  - Intros hists li ls; assert_PROP (Zlength entries = size) as Hlene by entailer!.
    repeat (apply sepcon_derives; try apply data_at_data_at_).
    exploit add_items_length; eauto.
    rewrite Zlength_empty; intro Hlenh.
    assert (Zlength entries <= Zlength hists) by omega.
    apply sepcon_list_derives; rewrite !Zlength_map, Zlength_combine, Z.min_l; auto.
    intros; rewrite Znth_map with (d' := ((Vundef, Vundef), ([], [])))
      by (rewrite Zlength_combine, Z.min_l; auto).
    rewrite Znth_map with (d' := (Vundef, Vundef)) by auto.
    rewrite Znth_combine by (setoid_rewrite Hlene; auto).
    unfold atomic_entry.
    destruct (Znth i entries (Vundef, Vundef)) eqn: Hpi.
    simpl in *; rewrite Hpi at 1.
    destruct (Znth i hists ([], [])) as (hk, hv).
    Exists hk hv; setoid_rewrite Hpi; auto.
  - repeat (apply precise_sepcon; auto).
    apply precise_fold_right.
    rewrite Forall_map, Forall_forall; intros; simpl.
    apply precise_sepcon; apply atomic_loc_hist_precise; auto.
Qed.

Lemma f_pred_positive : forall tsh sh entries p t locksp lockt resultsp res,
  positive_mpred (f_lock_pred tsh sh entries p t locksp lockt resultsp res).
Proof.
  intros; apply selflock_positive.
Qed.
Hint Resolve f_pred_precise f_pred_positive.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (data_at_isptr Tsh); Intros.
  assert (force_val (sem_cast_neutral tid) = tid) as Htid.
  { destruct tid; try contradiction; auto. }
  replace_SEP 2 (data_at Tsh tint (vint t) (force_val (sem_cast_neutral tid))).
  { rewrite Htid; entailer!. }
  forward.
  rewrite <- lock_struct_array.
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  rewrite !upd_Znth_same by auto.
  forward.
  focus_SEP 2.
  forward_call (tid, sizeof tint).
  { rewrite Htid; apply sepcon_derives; [apply data_at_memory_block | cancel_frame]. }
  forward_for_simple_bound 3 (EX i : Z, EX ls : list bool,
    PROP (Zlength ls = i)
    LOCAL (temp _total (vint (Zlength (filter id ls))); temp _res res; temp _l lockt; temp _t (vint t);
           temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         EX h : list (hist * hist), EX li : list Z,
           !!(Zlength li = i /\ add_items_trace empty_hists (combine (combine (combine (sublist 0 i [1; 2; 3])
              (sublist 0 i [1; 1; 1])) li) ls) h) && atomic_entries sh entries h;
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
         data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
         data_at_ Tsh tint res;
         lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res))).
  - Exists (@nil bool) (empty_hists : list (hist * hist)) (@nil Z); entailer!.
    constructor.
  - Intros h li.
    forward_call (i + 1, 1, p, sh, entries, h).
    { repeat (split; auto; try computable; try omega).
      + pose proof (Int.min_signed_neg); omega.
      + transitivity 4; [omega | computable].
      + erewrite add_items_length, Zlength_empty; [reflexivity | eauto].
      + eapply add_items_trace_wf; eauto. }
    apply extract_exists_pre; intros ((s, j), h'); simpl; Intros.
    match goal with |- semax _ (PROP () (LOCALx (?a :: ?b :: temp _total _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROP () (LOCALx (a :: b :: temp _total (vint (Zlength (filter id (x ++ [s])))) :: Q)
                 (SEPx R))) end.
    + forward.
      subst; rewrite filter_app, Zlength_app; entailer!.
    + forward.
      subst; rewrite filter_app, Zlength_app; entailer!.
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
      repeat (apply andp_right; [apply prop_right; auto|]).
      Exists (x ++ [s]) h' (li ++ [j]); entailer!.
      erewrite !sublist_split with (lo := 0)(mid := Zlength x)(hi := Zlength x + 1), !sublist_len_1;
        rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; auto; try omega.
      split; auto; split; [omega|].
      rewrite !combine_app'; rewrite ?Zlength_combine, ?Zlength_sublist, ?Z.min_l; rewrite ?Z.min_l, ?Zlength_cons, ?Zlength_nil;
        try omega; simpl.
      econstructor; eauto.
      change [1; 2; 3] with (map Z.succ (upto 3)); change [1; 1; 1] with (repeat 1 3).
      rewrite Znth_map', Znth_upto, Znth_repeat; auto; simpl; omega.
  - Intros ls h li.
    forward.
    forward_call (lockt, tsh, f_lock_inv sh entries p t locksp lockt resultsp res,
                  f_lock_pred tsh sh entries p t locksp lockt resultsp res).
    { lock_props.
      { apply selflock_rec. }
      unfold f_lock_pred.
      rewrite selflock_eq at 2.
      unfold f_lock_inv at 2.
      rewrite lock_struct_array.
      Exists h li ls; entailer!.
      subst Frame; instantiate (1 := []); simpl; rewrite sepcon_emp; apply lock_inv_later. }
    forward.
Qed.

Lemma lock_struct : forall p, data_at_ Tsh (Tstruct _lock_t noattr) p |-- data_at_ Tsh tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
  (* temporarily broken *)
Admitted.

Fixpoint join_hists (h1 h2 : list (hist * hist)) :=
  match (h1, h2) with
  | ((k1, v1) :: rest1, (k2, v2) :: rest2) => (k1 ++ k2, v1 ++ v2) :: join_hists rest1 rest2
  | _ => []
  end.

Lemma join_hists_spec : forall h1 h2 i, Zlength h1 = Zlength h2 ->
  Znth i (join_hists h1 h2) ([], []) =
  (fst (Znth i h1 ([], [])) ++ fst (Znth i h2 ([], [])),
  (snd (Znth i h1 ([], [])) ++ snd (Znth i h2 ([], [])))).
Proof.
  induction h1; destruct h2; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *.
  - rewrite Znth_nil; auto.
  - pose proof (Zlength_nonneg h2); omega.
  - pose proof (Zlength_nonneg h1); omega.
  - destruct a, p.
    destruct (zlt i 0).
    { rewrite !Znth_underflow; auto. }
    destruct (eq_dec i 0).
    + subst; rewrite !Znth_0_cons; auto.
    + rewrite !Znth_pos_cons by omega.
      apply IHh1; omega.
Qed.

Lemma join_empty : forall h, Zlength h = size -> join_hists empty_hists h = h.
Proof.
  intros.
  rewrite Zlength_correct in H.
  assert (length h = Z.to_nat size) as Hlen by Omega0.
  forget (Z.to_nat size) as n; clear H.
  revert dependent h; induction n; destruct h; auto; intros; inv Hlen; simpl.
  destruct p; rewrite IHn; auto.
Qed.

Lemma atomic_entries_join : forall sh1 sh2 sh entries hists1 hists2 hists (Hjoin : sepalg.join sh1 sh2 sh)
  (Hhists : join_hists hists1 hists2 = hists)
  (Hlen : Zlength entries = Zlength hists1) (Hlen1 : Zlength hists1 = Zlength hists2)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_entries sh1 entries hists1 * atomic_entries sh2 entries hists2 =
  !!(forall i, disjoint (fst (Znth i hists1 ([], []))) (fst (Znth i hists2 ([], []))) /\
               disjoint (snd (Znth i hists1 ([], []))) (snd (Znth i hists2 ([], [])))) &&
    atomic_entries sh entries hists.
Proof.
  induction entries; unfold atomic_entries; simpl; intros.
  { exploit Zlength_nil_inv; eauto; intro; subst.
    exploit (Zlength_nil_inv hists2); auto; intro; subst.
    rewrite prop_true_andp, sepcon_emp; auto.
    intro; rewrite Znth_nil; simpl; auto. }
  destruct hists1; [exploit (Zlength_nil_inv (a :: entries)); eauto; discriminate|].
  destruct hists2; [exploit Zlength_nil_inv; eauto; discriminate|].
  rewrite !Zlength_cons in *; simpl in *.
  destruct a, p as (hk1, hv1), p0 as (hk2, hv2); subst; simpl.
  unfold atomic_entry.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2)); [apply mpred_ext; cancel|] end.
  setoid_rewrite (IHentries _ _ _ Hjoin eq_refl); auto; try omega.
  match goal with |- (?P1 * ?Q1 * (?P2 * ?Q2) * ?R) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2) * R); [apply mpred_ext; cancel|] end.
  erewrite !atomic_loc_hist_join by eauto.
  apply mpred_ext; entailer!.
  - intros.
    destruct (zlt i 0); [rewrite !Znth_underflow; simpl; auto|].
    destruct (eq_dec i 0).
    + subst; rewrite !Znth_0_cons; auto.
    + rewrite !Znth_pos_cons by omega; auto.
  - pose proof (H 0) as H0.
    rewrite !Znth_0_cons in H0; destruct H0; split; auto; split; auto.
    intro i; specialize (H (i + 1)).
    destruct (zlt i 0); [rewrite !Znth_underflow; simpl; auto|].
    rewrite !Znth_pos_cons, Z.add_simpl_r in H by omega; auto.
Qed.

Corollary atomic_entries_join_nil : forall sh1 sh2 sh entries
  (Hjoin : sepalg.join sh1 sh2 sh) (Hlen : Zlength entries = size)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_entries sh1 entries empty_hists * atomic_entries sh2 entries empty_hists =
  atomic_entries sh entries empty_hists.
Proof.
  intros; erewrite atomic_entries_join with (sh := sh).
  rewrite prop_true_andp; eauto.
  - intro; rewrite Znth_repeat; simpl; auto.
  - auto.
  - apply join_empty, Zlength_empty.
  - rewrite Zlength_empty; auto.
  - reflexivity.
  - auto.
  - auto.
Qed.

Lemma join_hists_length : forall h1 h2, Zlength h1 = Zlength h2 ->
  Zlength (join_hists h1 h2) = Zlength h1.
Proof.
  induction h1; auto; simpl; intros.
  destruct h2; [apply Zlength_nil_inv in H; discriminate|].
  destruct a, p; rewrite !Zlength_cons in *; rewrite IHh1; auto; omega.
Qed.

Corollary fold_join_hists_length : forall lh h, Forall (fun h' => Zlength h' = Zlength h) lh ->
  Zlength (fold_right join_hists h lh) = Zlength h.
Proof.
  induction lh; auto; simpl; intros.
  inv H.
  rewrite join_hists_length; auto.
  rewrite IHlh; auto.
Qed.

Lemma join_empty_r : forall h, Zlength h = size -> join_hists h empty_hists = h.
Proof.
  intros.
  rewrite Zlength_correct in H.
  assert (length h = Z.to_nat size) as Hlen by Omega0.
  forget (Z.to_nat size) as n; clear H.
  revert dependent h; induction n; destruct h; auto; intros; inv Hlen; simpl.
  destruct p; rewrite IHn, !app_nil_r; auto.
Qed.

Lemma join_hists_assoc : forall a b c, join_hists a (join_hists b c) = join_hists (join_hists a b) c.
Proof.
  induction a; auto; simpl; intros.
  destruct a, b; auto; simpl.
  destruct p, c; auto; simpl.
  destruct p; rewrite IHa, !app_assoc; auto.
Qed.

Lemma join_hists_base : forall l h, Zlength h = size ->
  fold_right join_hists (join_hists h empty_hists) l = join_hists (fold_right join_hists empty_hists l) h.
Proof.
  induction l; simpl; intros.
  - rewrite join_empty, join_empty_r; auto.
  - rewrite IHl, join_hists_assoc; auto.
Qed.

Lemma add_rest_hists : forall k i h h' (Hrest : forall j,
  (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
  (~ In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], []))) j (Hj : j <> i),
  exists rest, Znth j h' ([], []) = (fst (Znth j h ([], [])) ++ rest, snd (Znth j h ([], []))) /\
    Forall (fun e => forall v, ~writes e v) (map snd rest).
Proof.
  intros.
  specialize (Hrest j).
  destruct (in_dec Z_eq_dec j (indices (hash k) i)).
  - destruct Hrest as ((? & r & ? & ? & [Hi1 | (? & ? & ? & Hi1)] & ? & ? & Hi2 & _) & _); auto;
      destruct (Znth j h' ([], [])); simpl in *; rewrite Hi1, Hi2; do 2 eexists; eauto; repeat constructor;
      auto.
    intros ? (? & ?).
    absurd (r = 0); auto; apply repr_inj_signed; auto; congruence.
  - destruct Hrest as (_ & Hrest); rewrite Hrest by auto.
    destruct (Znth j h ([], [])); exists []; rewrite app_nil_r; simpl; auto.
Qed.

Lemma key_hists_fail : forall h k v i h' j (Hfail : add_item_trace h k v i false h')
  (Hk : k <> 0) (Hrep : repable_signed k),
  exists rest, Znth j h' ([], []) = (fst (Znth j h ([], [])) ++ rest, snd (Znth j h ([], []))) /\
    Forall (fun e => forall v, ~writes e v) (map snd rest).
Proof.
  intros.
  destruct (eq_dec j i).
  - destruct Hfail as (? & ? & Hi & _).
    subst; destruct (Znth i h ([], [])), (Znth i h' ([], [])); simpl in *.
    destruct Hi as ((? & ? & [-> | (? & ? & ? & ->)]) & -> & _); do 2 eexists; eauto; repeat constructor; auto.
    intros ? (? & ?).
    contradiction Hk; apply repr_inj_signed; auto; congruence.
  - destruct Hfail as (? & ? & _ & Hrest).
    eapply add_rest_hists; eauto.
Qed.

Lemma add_item_trace_map : forall h k v i s h' (Hlenh : Zlength h = size)
  (Htrace : add_item_trace h k v i s h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  let m' := make_map (upd_Znth i h' (Znth i h ([], []))) in
    map_incl (make_map h) m' /\ lookup m' k = Some i /\
    if s then get (make_map h) k = None /\ make_map h' = upd_Znth i m' (k, v)
    else make_map h' = upd_Znth i m' (k, make_int (value_of_hist (snd (Znth i h' ([], []))))).
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  split.
  - intros k0 v0 j Hk0 Hj.
    exploit (Znth_inbounds j (make_map h) (0, 0)).
    { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
    intro; unfold make_map in *.
    rewrite Zlength_map in *.
    rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
    subst m'; rewrite Znth_map with (d' := ([], [])) by (rewrite upd_Znth_Zlength; omega).
    destruct (eq_dec j i); [subst; rewrite upd_Znth_same, Hhi by omega; auto|].
    rewrite upd_Znth_diff by (auto; omega).
    specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i));
      [|destruct Hrest as (_ & ->); auto].
    destruct Hrest as ((? & r1 & ? & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [-> | (? & ? & (? & ?) & ->)].
    + rewrite value_of_hist_snoc, Heq; auto.
    + rewrite 2app_cons_assoc, value_of_hist_snoc, Heq; auto.
  - assert (0 <= i < Zlength h') by (rewrite Hlen; auto).
    split.
    + subst m'; unfold lookup, make_map.
      assert (i = ((i - hash k) mod size + hash k) mod size) as Hmod.
      { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small by omega; auto. }
      pose proof (hash_range k).
      assert (Zlength (map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs))))
              (upd_Znth i h' (hk, hv))) = size) as Hlen1.
      { rewrite Zlength_map, upd_Znth_Zlength; auto; omega. }
      erewrite index_of'_succeeds; simpl.
      f_equal; symmetry; apply Hmod.
      { rewrite Zlength_rebase; rewrite ?Zlength_map, ?upd_Znth_Zlength; auto;
          replace (Zlength h') with size; auto; try omega.
        apply Z_mod_lt, size_pos. }
      { rewrite Forall_forall; intros x Hin.
        apply In_Znth with (d := (0, 0)) in Hin; destruct Hin as (j & Hj & Hx).
        exploit (Z_mod_lt (i - hash k) size); [apply size_pos | intro].
        rewrite Zlength_sublist in Hj; rewrite ?Zlength_rebase; rewrite ?Hlen1; try (simpl in *; omega).
        rewrite Znth_sublist, Z.add_0_r in Hx by (auto; omega).
        rewrite Znth_rebase in Hx by (simpl in *; omega).
        rewrite Hlen1, Znth_map with (d' := ([], [])) in Hx.
        subst x; simpl.
        specialize (Hrest ((j + hash k) mod size)); destruct Hrest as ((? & r1 & ? & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        simpl in *; destruct Hcase as [-> | (? & ? & ? & ->)]; [|rewrite 2app_cons_assoc];
          rewrite value_of_hist_snoc; simpl; rewrite Int.signed_repr; auto.
        * intro X; rewrite <- X, Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hj; try omega.
          destruct Hj; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos.
        * rewrite upd_Znth_Zlength by auto.
          replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos. }
      { rewrite <- Hlen1, Znth_rebase', Znth_map with (d' := ([], [])); simpl;
          rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try (simpl in *; omega).
        rewrite upd_Znth_same by auto; simpl.
        destruct s; [destruct Hi as (? & ? & ? & ? & ? & ? & ? & ? & ->); auto|].
        destruct Hi as (? & ? & Hr0).
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto; simpl.
        rewrite Int.signed_repr; auto. }
    + subst m'; unfold make_map; rewrite <- upd_Znth_map; destruct s; [split|].
      * unfold get, lookup.
        pose proof (index_of'_spec k (rebase (make_map h) (hash k))) as Hspec.
        unfold make_map in *; destruct (index_of' _ _); auto; simpl.
        assert (0 <= hash k < Zlength (make_map h)); unfold make_map in *.
        { rewrite Zlength_map, Hlenh; apply Z_mod_lt, size_pos. }
        rewrite Znth_map with (d' := ([], [])) by (rewrite Hlenh; apply Z_mod_lt, size_pos).
        destruct (eq_dec _ _); auto.
        destruct Hspec as (? & Hz & Hall).
        eapply Forall_sublist_le in Hall; rewrite ?Znth_rebase' with (i := i); auto; try omega.
        rewrite Zlength_rebase in * by auto.
        rewrite Znth_rebase, Znth_map with (d' := ([], [])) in Hz
          by (auto; rewrite Zlength_map; apply Z_mod_lt; omega); simpl in Hz.
        rewrite Zlength_map in *.
        rewrite Hlenh in *; destruct (eq_dec ((z + hash k) mod size) i).
        { simpl in e; rewrite e, Hhi in n; simpl in n.
          destruct Hi as (? & ? & ? & ? & ? & ? & ? & ? & Hzero); rewrite Hzero in n; contradiction. }
        destruct (eq_dec z ((i - hash k) mod size)).
        { subst z; contradiction n0.
          rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto. }
        destruct (Hrest ((z + hash k) mod size)) as ((? & r0 & ? & ? & ? & ? & Hrk & ? & Hr0) & ?).
        { unfold indices; rewrite in_map_iff.
          do 2 eexists; [rewrite Z.add_comm; eauto|].
          rewrite In_upto, Z2Nat.id; omega. }
        destruct Hz as [Hz | Hz]; [|contradiction].
        simpl in *; destruct (value_of_hist (fst _)); try contradiction; simpl in Hz; subst.
        subst; destruct (eq_dec (Vint i0) (vint 0)).
        { inv e; contradiction Hk; rewrite Int.signed_repr; auto. }
        assert (Vint i0 = vint r0) as Heq by auto.
        inv Heq; contradiction Hrk; rewrite Int.signed_repr; auto.
        { rewrite Zlength_map, Hlenh; apply Z_mod_lt, size_pos. }
        { rewrite Znth_map', Hhi; simpl.
          destruct Hi as (? & ? & ? & ? & ? & ? & ? & ? & ->); tauto. }
        { rewrite Zlength_map; auto. }
      * erewrite upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map; auto.
        rewrite Znth_map'.
        destruct Hi as (? & ? & ? & ? & ? & ? & Hi1 & Hi2 & ?).
        rewrite Hi1, Hi2, app_cons_assoc, !value_of_hist_snoc; simpl.
        rewrite !Int.signed_repr; auto.
      * erewrite upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map; auto.
        rewrite Znth_map'; f_equal.
        destruct Hi as ((? & ? & [-> | (? & ? & ? & ->)]) & ? & ?); [|rewrite 2app_cons_assoc];
          rewrite value_of_hist_snoc; simpl; rewrite Int.signed_repr; auto.
Qed.

Definition add m k v i (s : bool) m' := lookup m k = Some i /\
  if s then fst (Znth i m (0, 0)) = 0 /\ m' = upd_Znth i m (k, v)
  else fst (Znth i m (0, 0)) = k /\ m' = m.

Inductive add_all m le : list (Z * Z) -> Prop :=
| add_nil (Hnil : Forall (fun x => x = []) le) : add_all m le m
| add_one j k v i s l m' m'' (Hj : Znth j le [] = l ++ [(k, v, i, s)])
    (Hadd1 : add_all m (upd_Znth j le l) m') (Hadd : add m' k v i s m'') : add_all m le m''.

Definition empty_map := repeat (0, 0) (Z.to_nat size).

Lemma make_nil : forall n, make_map (repeat ([], []) n) = repeat (0, 0) n.
Proof.
  induction n; auto; simpl.
  rewrite Int.signed_repr, IHn by computable; auto.
Qed.

Corollary make_empty : make_map empty_hists = empty_map.
Proof.
  apply make_nil.
Qed.

Lemma join_empty_hists : forall h n, Zlength h = size -> fold_right join_hists h (repeat empty_hists n) = h.
Proof.
  induction n; auto; simpl; intro.
  rewrite join_empty; auto.
  rewrite fold_join_hists_length; auto.
  apply Forall_repeat; rewrite Zlength_repeat, Z2Nat.id; auto.
  pose proof size_pos; omega.
Qed.

Lemma Znth_join_hists : forall i lh (Hlen : Forall (fun h => Zlength h = Zlength empty_hists) lh),
  Znth i (fold_right join_hists empty_hists lh) ([], []) =
  (concat (map fst (map (fun h => Znth i h ([], [])) lh)),
   concat (map snd (map (fun h => Znth i h ([], [])) lh))).
Proof.
  induction lh; simpl; intro.
  - rewrite Znth_repeat; auto.
  - inv Hlen.
    rewrite join_hists_spec by (rewrite fold_join_hists_length; auto).
    rewrite IHlh by auto; reflexivity.
Qed.

Lemma add_items_hist_length : forall h lr, Forall (fun '(la, h') => add_items_trace h la h') lr ->
  Forall (fun h' => Zlength h' = Zlength h) (map snd lr).
Proof.
  intros.
  rewrite Forall_map; eapply Forall_impl; [|eauto].
  simpl; intros (?, ?) ?.
  eapply add_items_length; eauto.
Qed.

Definition hists_mono (h1 h2 : list (hist * hist)) := Forall2 (fun a b =>
  (exists l, fst b = fst a ++ l) /\ (exists l, snd b = snd a ++ l)) h1 h2.

Instance hists_mono_refl : RelationClasses.Reflexive hists_mono.
Proof.
  intro; unfold hists_mono; rewrite Forall2_eq_upto with (d1 := ([], []))(d2 := ([], [])); split; auto.
  rewrite Forall_forall; intros j Hin; rewrite In_upto, Z2Nat.id in Hin by (apply Zlength_nonneg).
  split; exists []; rewrite app_nil_r; auto.
Qed.
Hint Resolve hists_mono_refl.

Instance hists_mono_trans : RelationClasses.Transitive hists_mono.
Proof.
  intro x; induction x; intros ?? H; inv H; intro H; inv H; auto.
  constructor; [|eapply IHx; eauto].
  match goal with H : (exists l, fst y = _ ++ l) /\ _ |- _ => destruct H as ((? & ->) & (? & ->)) end.
  match goal with H : (exists l, fst y0 = _ ++ l) /\ _ |- _ => destruct H as ((? & ->) & (? & ->)) end.
  rewrite <- !app_assoc; eauto.
Qed.

Lemma add_item_trace_mono : forall h k v i s h', add_item_trace h k v i s h' -> hists_mono h h'.
Proof.
  intros; destruct H as (? & ? & Hi & Hrest).
  unfold hists_mono; rewrite Forall2_eq_upto with (d1 := ([], []))(d2 := ([], [])); split; auto.
  rewrite Forall_forall; intros j Hin; rewrite In_upto, Z2Nat.id in Hin by omega.
  destruct (eq_dec j i).
  - subst; destruct (Znth i h ([], [])), s.
    + destruct Hi as (? & ? & ? & ? & ? & ? & -> & -> & ?); eauto.
    + destruct Hi as (Hi & -> & ?); split; [|exists []; rewrite app_nil_r; auto].
      destruct Hi as (? & ? & [-> | (? & ? & ? & ->)]); eauto.
  - exploit add_rest_hists; eauto; intros (? & -> & ?); simpl.
    split; eexists; eauto.
    rewrite app_nil_r; auto.
Qed.

Corollary add_items_trace_mono : forall h la h', add_items_trace h la h' ->
  hists_mono h h'.
Proof.
  induction 1; auto.
  etransitivity; eauto; eapply add_item_trace_mono; eauto.
Qed.

Lemma remove_last_full_hist : forall lh h j h' k v i k' i' (Hj : 0 <= j < Zlength lh) (Hh : Znth j lh [] = h)
  (Hi' : 0 <= i' < Zlength h) (Hadd : add_item_trace h' k v i false h) (Hk : k <> 0) (Hrep : repable_signed k)
  (Hfull : full_hist' (concat (map fst (map (fun h => Znth i' h ([], [])) lh))) k'),
  full_hist' (concat (upd_Znth j (map fst (map (fun h => Znth i' h ([], [])) lh))
    (fst (Znth i' h' ([], []))))) k'.
Proof.
  intros.
  apply key_hists_fail with (j := i') in Hadd; auto.
  destruct Hadd as (? & Heq & Hfail).
  eapply full_hist'_drop; eauto.
  - eapply concat_less_incl.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, Znth_map', Hh, Heq by (rewrite Zlength_map; auto); simpl; eauto.
  - rewrite concat_map in *.
    rewrite <- upd_Znth_map.
    eapply NoDup_concat_less.
    + destruct Hfull as (? & Hl & ?).
      rewrite <- concat_map; eapply hist_list_NoDup; eauto.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, !Znth_map', Hh, Heq by (rewrite !Zlength_map; auto); simpl.
      rewrite map_app; auto.
  - intros t e Hin Hout.
    rewrite in_concat in Hin, Hout.
    destruct Hin as (? & ? & Hin).
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    apply In_Znth with (d := []) in Hin; destruct Hin as (j' & ? & Hj').
    destruct (eq_dec j' j); subst.
    + rewrite Heq in H; simpl in H.
      rewrite in_app in H; destruct H.
      * contradiction Hout.
        do 2 eexists; eauto.
        apply upd_Znth_In.
      * rewrite Forall_map, Forall_forall in Hfail; specialize (Hfail _ H); auto.
    + contradiction Hout.
      do 2 eexists; eauto.
      rewrite upd_Znth_map, in_map_iff; do 2 eexists; eauto.
      rewrite upd_Znth_map with (f := fun h => Znth i' h ([], [])), in_map_iff; do 2 eexists; eauto.
      erewrite <- upd_Znth_diff with (j0 := j); auto.
      apply Znth_In; rewrite upd_Znth_Zlength; auto.
Qed.

Lemma remove_last_full_hist' : forall lh h j h' k v i k' i' (Hj : 0 <= j < Zlength lh) (Hh : Znth j lh [] = h)
  (Hi' : 0 <= i' < Zlength h) (Hadd : add_item_trace h' k v i true h) (Hk : k <> 0) (Hrep : repable_signed k)
  (Hfull : full_hist' (concat (map fst (map (fun h => Znth i' h ([], [])) lh))) k') (Hneq : i' <> i),
  full_hist' (concat (upd_Znth j (map fst (map (fun h => Znth i' h ([], [])) lh))
    (fst (Znth i' h' ([], []))))) k'.
Proof.
  intros.
  destruct Hadd as (? & ? & _ & Hrest); apply add_rest_hists with (j := i') in Hrest; auto.
  destruct Hrest as (? & Heq & Hfail).
  eapply full_hist'_drop; eauto.
  - eapply concat_less_incl.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, Znth_map', Hh, Heq by (rewrite Zlength_map; auto); simpl; eauto.
  - rewrite concat_map in *.
    rewrite <- upd_Znth_map.
    eapply NoDup_concat_less.
    + destruct Hfull as (? & Hl & ?).
      rewrite <- concat_map; eapply hist_list_NoDup; eauto.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, !Znth_map', Hh, Heq by (rewrite !Zlength_map; auto); simpl.
      rewrite map_app; auto.
  - intros t e Hin Hout.
    rewrite in_concat in Hin, Hout.
    destruct Hin as (? & Hin0 & Hin).
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    apply In_Znth with (d := []) in Hin; destruct Hin as (j' & ? & Hj').
    destruct (eq_dec j' j); subst.
    + rewrite Heq in Hin0; simpl in Hin0.
      rewrite in_app in Hin0; destruct Hin0 as [|Hin0].
      * contradiction Hout.
        do 2 eexists; eauto.
        apply upd_Znth_In.
      * rewrite Forall_map, Forall_forall in Hfail; specialize (Hfail _ Hin0); auto.
    + contradiction Hout.
      do 2 eexists; eauto.
      rewrite upd_Znth_map, in_map_iff; do 2 eexists; eauto.
      rewrite upd_Znth_map with (f := fun h => Znth i' h ([], [])), in_map_iff; do 2 eexists; eauto.
      erewrite <- upd_Znth_diff with (j0 := j); auto.
      apply Znth_In; rewrite upd_Znth_Zlength; auto.
Qed.

(* up *)
Lemma hist_list'_in : forall (h : hist) l (Hl : hist_list' h l) e, (exists t, In (t, e) h) <-> In e l.
Proof.
  induction 1.
  - split; [intros (? & ?)|]; contradiction.
  - intro; subst; split.
    + intros (? & Hin); rewrite in_app in *.
      destruct Hin as [? | [Heq | ?]]; try solve [left; rewrite <- IHHl; eexists; rewrite in_app; eauto].
      inv Heq; simpl; auto.
    + rewrite in_app; intros [Hin | [Heq | ?]]; [| inv Heq | contradiction].
      * rewrite <- IHHl in Hin; destruct Hin as (? & ?).
        eexists; rewrite in_app in *; simpl; destruct H; eauto.
      * eexists; rewrite in_app; simpl; eauto.
Qed.

(*Lemma remove_last_success_full_hist : forall lh h j h' k v i k' (Hj : 0 <= j < Zlength lh)
  (Hh : Znth j lh [] = h) (Hadd : add_item_trace h' k v i true h) (Hk : k <> 0) (Hrep : repable_signed k)
  (Hfull : full_hist' (concat (map fst (map (fun h => Znth i h ([], [])) lh))) k'),
  full_hist' (concat (upd_Znth j (map fst (map (fun h => Znth i h ([], [])) lh))
    (fst (Znth i h' ([], []))))) (vint 0).
Proof.
  intros.
  destruct Hadd as (? & ? & Hi & _).
  destruct (Znth i h' ([], [])) as (hk, hv) eqn: Hh'; simpl.
  destruct Hi as (t & t1 & tv & ? & ? & ? & Hi1 & Hi2 & Hzero).
  destruct Hfull as (l & Hl & Hv).
  assert (In (CAS (vint 0) (vint 0) (vint k)) l).
  { rewrite <- hist_list'_in by eauto.
    eexists; rewrite in_concat; do 2 eexists; [|repeat (rewrite in_map_iff; do 2 eexists; eauto)].
    rewrite in_app; simpl; eauto.
    { rewrite <- Hh; apply Znth_In; auto. } }
  exploit in_split; eauto; intros (l1 & l2 & ?); subst.
  
  Search hist_list' In.
  
  
  assert (lh = sublist 0 j lh ++ Znth j lh [] :: sublist (j + 1) (Zlength lh) lh) as Hlh.
  { rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; omega. }
  rewrite Hlh, !map_app, concat_app in Hfull; simpl in Hfull.
  rewrite Hh, Hi1 in Hfull.
  rewrite Hlh, !map_app; simpl.
  assert (Zlength (sublist 0 j lh) = j) as Hsub1 by (rewrite Zlength_sublist; omega).
  assert (Zlength (sublist (j + 1) (Zlength lh) lh) = Zlength lh - (j + 1)) by (rewrite Zlength_sublist; omega).
  rewrite upd_Znth_app2 by (rewrite Zlength_cons, !Zlength_map; omega).
  rewrite !Zlength_map, Hsub1, Zminus_diag, upd_Znth0, sublist_1_cons, Zlength_cons,
    sublist_same with (hi := _ - _) by (auto; omega).
  rewrite concat_app; simpl.
  eapply full_hist'_drop; eauto.
  - eapply concat_less_incl.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, Znth_map', Hh, Heq by (rewrite Zlength_map; auto); simpl; eauto.
  - rewrite concat_map in *.
    rewrite <- upd_Znth_map.
    eapply NoDup_concat_less.
    + destruct Hfull as (? & Hl & ?).
      rewrite <- concat_map; eapply hist_list_NoDup; eauto.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, !Znth_map', Hh, Heq by (rewrite !Zlength_map; auto); simpl.
      rewrite map_app; auto.
  - intros t e Hin Hout.
    rewrite in_concat in Hin, Hout.
    destruct Hin as (? & Hin0 & Hin).
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    apply In_Znth with (d := []) in Hin; destruct Hin as (j' & ? & Hj').
    destruct (eq_dec j' j); subst.
    + rewrite Heq in Hin0; simpl in Hin0.
      rewrite in_app in Hin0; destruct Hin0 as [|Hin0].
      * contradiction Hout.
        do 2 eexists; eauto.
        apply upd_Znth_In.
      * rewrite Forall_map, Forall_forall in Hfail; specialize (Hfail _ Hin0); auto.
    + contradiction Hout.
      do 2 eexists; eauto.
      rewrite upd_Znth_map, in_map_iff; do 2 eexists; eauto.
      rewrite upd_Znth_map with (f := fun h => Znth i' h ([], [])), in_map_iff; do 2 eexists; eauto.
      erewrite <- upd_Znth_diff with (j0 := j); auto.
      apply Znth_In; rewrite upd_Znth_Zlength; auto.
Qed.*)

Lemma add_key_success : forall la h' t e i v (Hadd : add_items_trace empty_hists la h')
  (Hin : In (t, e) (fst (Znth i h' ([], [])))) (Hval : writes e v)
  (Hnzk : Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) la),
  exists k v', In (k, v', i, true) la /\ v = vint k /\ e = CAS (vint 0) (vint 0) (vint k) /\ repable_signed k.
Proof.
  intros; remember empty_hists as h0; induction Hadd; subst.
  - rewrite Znth_repeat in Hin; contradiction.
  - rewrite Forall_app in Hnzk; destruct Hnzk as (? & Hnzk); inversion Hnzk as [|?? Hk].
    destruct Hk; subst.
    assert (0 <= i < Zlength h'').
    { apply Znth_inbounds with (d := ([], [])).
      intro X; rewrite X in Hin; contradiction. }
    assert (0 <= i < Zlength h').
    { destruct Hadd0; omega. }
    destruct (in_dec (EqDec_prod _ _ _ _) (t, e) (fst (Znth i h' ([], [])))).
    { exploit IHHadd; eauto.
      intros (? & ? & ? & ?); do 2 eexists; rewrite in_app; eauto. }
    destruct Hadd0 as (? & ? & Hi & Hrest).
    destruct (eq_dec i0 i).
    + subst; destruct (Znth i h' ([], [])).
      destruct s.
      * destruct Hi as (? & ? & ? & ? & ? & ? & Hi1 & ? & _); rewrite Hi1, in_app in Hin.
        destruct Hin as [? | [Heq | [Heq | ?]]]; try (inv Heq); try contradiction.
        simpl in Hval; destruct Hval.
        subst; do 2 eexists; rewrite in_app; simpl; split; eauto.
      * destruct Hi as ((? & ? & [Hi1 | (? & ? & ? & Hi1)]) & ? & ?); rewrite Hi1, in_app in Hin;
          destruct Hin as [? | [Hin | Hin]]; try (try (inv Hin); contradiction).
        destruct Hin as [Heq | [Heq | Heq]]; inv Heq; try contradiction.
        simpl in Hval; destruct Hval; subst.
        absurd (k = 0); auto; apply repr_inj_signed; auto; congruence.
    + exploit add_rest_hists; eauto; intros (? & Hh & Hw); rewrite Hh in Hin.
      simpl in Hin; rewrite in_app in Hin; destruct Hin as [|Hin]; [contradiction|].
      rewrite Forall_map, Forall_forall in Hw; exploit (Hw _ Hin); eauto; contradiction.
Qed.

Lemma add_val_success : forall la h' t e i v (Hadd : add_items_trace empty_hists la h')
  (Hin : In (t, e) (snd (Znth i h' ([], [])))) (Hval : value_of e = vint v) (Hv : repable_signed v)
  (Hrep : Forall (fun x => let '(_, v, _, _) := x in repable_signed v) la),
  exists k, In (k, v, i, true) la /\
    exists t', In (t', CAS (vint 0) (vint 0) (vint k)) (fst (Znth i h' ([], []))).
Proof.
  intros; remember empty_hists as h0; induction Hadd; subst.
  - rewrite Znth_repeat in Hin; contradiction.
  - rewrite Forall_app in Hrep; destruct Hrep as (? & Hrep); inv Hrep.
    assert (0 <= i < Zlength h'').
    { apply Znth_inbounds with (d := ([], [])).
      intro X; rewrite X in Hin; contradiction. }
    assert (0 <= i < Zlength h').
    { destruct Hadd0; omega. }
    destruct (in_dec (EqDec_prod _ _ _ _) (t, e) (snd (Znth i h' ([], [])))).
    { exploit IHHadd; eauto.
      intros (? & ? & ? & ?); eexists; rewrite in_app; split; eauto.
      eapply add_item_trace_mono, Forall2_Znth with (i2 := i) in Hadd0; auto.
      eexists; destruct Hadd0 as ((? & X) & _); rewrite X, in_app; eauto. }
    destruct Hadd0 as (? & ? & Hi & Hrest).
    destruct (eq_dec i0 i).
    + subst; destruct (Znth i h' ([], [])).
      destruct s.
      * destruct Hi as (? & ? & ? & ? & ? & ? & -> & Hi2 & _); rewrite Hi2, in_app in Hin.
        destruct Hin as [? | [Heq | ?]]; try contradiction; inv Heq.
        simpl in Hval; assert (v0 = v) by (apply repr_inj_signed; auto; congruence).
        subst; eexists; rewrite in_app; simpl; split; eauto.
        eexists; rewrite in_app; simpl; eauto.
      * destruct Hi as (? & ? & ?); subst; contradiction.
    + exploit add_rest_hists; eauto; intros (? & Hi2 & ?); rewrite Hi2 in Hin; contradiction.
Qed.

Lemma writes_val : forall i e h v v', writes e v -> apply_hist i (h ++ [e]) = Some v' -> v' = v.
Proof.
  intros; rewrite apply_hist_app in *.
  destruct (apply_hist i h); [|discriminate].
  exploit apply_one_value; eauto.
  destruct e; simpl in *; try contradiction; subst; auto.
  destruct H; subst.
  rewrite eq_dec_refl; auto.
Qed.

Lemma apply_no_write : forall i h l v (Hl : hist_list' h l) (Hv : apply_hist i l = Some v)
  (Hh : Forall (fun p => ~writes (snd p) v) h), v = i /\ Forall (fun e => forall w, ~writes e w) l.
Proof.
  induction 1; simpl; intros.
  - inv Hv; auto.
  - assert (forall w, writes e w -> w = v) as Hwrite.
    { intros; symmetry; eapply writes_val; eauto. }
    rewrite apply_hist_app in Hv; destruct (apply_hist i l) eqn: Hv'; [|discriminate].
    subst; rewrite Forall_app in Hh; destruct Hh as (? & Hh); inv Hh.
    destruct (eq_dec v0 v).
    + subst; exploit IHHl; auto.
      { rewrite Forall_app; auto. }
      intros (? & ?); rewrite Forall_app; repeat constructor; auto.
      intros ? Hw; specialize (Hwrite _ Hw); subst; contradiction.
    + exploit change_implies_write; eauto; intros (? & [? | ?] & ?); subst; contradiction.
Qed.

Lemma one_CAS_succeeds : forall h v a t1 t2 b1 b2 (Hl : full_hist' h v) (Hin1 : In (t1, CAS a a b1) h)
  (Hin2 : In (t2, CAS a a b2) h) (Ha : Forall (fun p => ~writes (snd p) a) h),
  t1 = t2 /\ b1 = b2.
Proof.
  intros.
  destruct Hl as (l & Hl & Hv).
  revert dependent v; induction Hl; [contradiction|].
  subst; intros; rewrite !in_app in *; simpl in *.
  rewrite Forall_app in Ha; destruct Ha as (? & Ha); inv Ha.
  rewrite apply_hist_app in Hv.
  destruct (apply_hist (vint 0) l) eqn: Hv'; [|discriminate].
  destruct (in_dec (EqDec_prod _ _ _ _) (t1, CAS a a b1) (h1 ++ h2)),
    (in_dec (EqDec_prod _ _ _ _) (t2, CAS a a b2) (h1 ++ h2)); rewrite in_app in *.
  - eapply IHHl; eauto.
    rewrite Forall_app; auto.
  - destruct Hin2 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    simpl in Hv.
    destruct (eq_dec _ _); inv Hv.
    exploit apply_no_write; eauto.
    { rewrite Forall_app; auto. }
    intros (? & Hout); subst.
    assert (In (CAS (vint 0) (vint 0) b1) l) as Hin.
    { rewrite <- hist_list'_in; eauto.
      eexists; rewrite in_app; eauto. }
    rewrite Forall_forall in Hout; specialize (Hout _ Hin); simpl in Hout.
    exploit Hout; eauto; contradiction.
  - destruct Hin1 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    simpl in Hv.
    destruct (eq_dec _ _); inv Hv.
    exploit apply_no_write; eauto.
    { rewrite Forall_app; auto. }
    intros (? & Hout); subst.
    assert (In (CAS (vint 0) (vint 0) b2) l) as Hin.
    { rewrite <- hist_list'_in; eauto.
      eexists; rewrite in_app; eauto. }
    rewrite Forall_forall in Hout; specialize (Hout _ Hin); simpl in Hout.
    exploit Hout; eauto; contradiction.
  - destruct Hin1 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    destruct Hin2 as [? | [Heq | ?]]; try solve [contradiction n0; auto]; inv Heq; auto.
Qed.

Lemma timestamp_unique : forall (h : list hist) l t e1 e2 i1 i2 (Hl : hist_list' (concat h) l)
  (Ht1 : In (t, e1) (Znth i1 h [])) (Ht2 : In (t, e2) (Znth i2 h [])), i1 = i2.
Proof.
  intros.
  apply hist_list_NoDup in Hl.
  exploit (Znth_inbounds i1 h).
  { intro X; rewrite X in Ht1; contradiction. }
  exploit (Znth_inbounds i2 h).
  { intro X; rewrite X in Ht2; contradiction. }
  intros.
  replace h with (sublist 0 i2 h ++ Znth i2 h [] :: sublist (i2 + 1) (Zlength h) h) in Ht1, Hl.
  rewrite concat_app in Hl; simpl in Hl; rewrite !map_app in Hl.
  exploit (Zlength_sublist 0 i2 h); try omega.
  rewrite Z.sub_0_r; intro Hsub.
  destruct (zlt i1 i2).
  - rewrite app_Znth1 in Ht1 by omega.
    rewrite app_assoc in Hl; apply NoDup_app in Hl; destruct Hl as (Hl & _).
    apply NoDup_app in Hl; destruct Hl as (_ & _ & Hl).
    exploit Hl; try contradiction.
    + rewrite in_map_iff; exists (t, e1); split; [reflexivity|].
      rewrite in_concat; do 2 eexists; eauto.
      apply Znth_In; omega.
    + simpl; rewrite in_map_iff; do 2 eexists; eauto; auto.
  - rewrite app_Znth2 in Ht1 by omega.
    rewrite Hsub in Ht1.
    destruct (eq_dec (i1 - i2) 0); [omega|].
    rewrite Znth_pos_cons in Ht1 by omega.
    apply NoDup_app in Hl; destruct Hl as (_ & Hl & _).
    apply NoDup_app in Hl; destruct Hl as (_ & _ & Hl).
    exploit Hl; try contradiction.
    + rewrite in_map_iff; exists (t, e2); split; [reflexivity | auto].
    + simpl; rewrite in_map_iff.
      exists (t, e1); split; auto.
      rewrite in_concat; do 2 eexists; eauto.
      apply Znth_In.
      rewrite Zlength_sublist; omega.
  - rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; omega.
Qed.

(* Possible approaches:
   1) Do without linearizability, prove what's needed for a specific application.
   2) Prove linearizability based on an ordering across locations.
   3) Prove linearizability with linearization points or some other method from the literature. *)

(*
(* If we're going to do this sort of thing, we'll want a general theory of linearizability from histories. *)
Lemma adds_lin : forall lr keys vals
  (Hadd : Forall (fun '(la, h) => add_items_trace empty_hists la h) lr)
  (Hfullk : Forall2 full_hist' (map fst (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) keys))
  (Hkeys : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr))) keys)
  (Hrepk : Forall repable_signed keys)
  (Hnzk : Forall (fun x => Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) (fst x)) lr)
  (Hfullv : Forall2 full_hist' (map snd (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) vals))
  (Hrepv : Forall repable_signed vals)
  (Hnzv : Forall (fun x => Forall (fun x => let '(_, v, _, _) := x in repable_signed v) (fst x)) lr),
  add_all empty_map (map fst lr) (combine keys vals).
Proof.
  intro; remember (length (concat (map fst lr))) as n.
  revert dependent lr; induction n; intros.
  { assert (Forall (fun x => x = []) (map fst lr)).
    { rewrite Forall_forall; intros [|a] ?; auto.
      assert (In a (concat (map fst lr))).
      { rewrite in_concat; do 2 eexists; eauto; simpl; auto. }
      destruct (concat (map fst lr)); [contradiction | discriminate]. }
    assert (map snd lr = repeat empty_hists (length lr)) as Hempty.
    { apply list_Znth_eq' with (d := empty_hists); rewrite Zlength_map.
      { rewrite !Zlength_repeat, <- Zlength_correct; auto. }
      intros; rewrite Znth_repeat, Znth_map with (d' := ([], [])); auto.
      apply Forall_Znth with (i := j)(d := ([], [])) in Hadd; auto.
      destruct (Znth j lr ([], [])) as (la, h) eqn: Hj.
      eapply Forall_Znth with (i := j) in H; [|rewrite Zlength_map; auto].
      rewrite Znth_map', Hj in H; simpl in *; subst.
      inv Hadd; auto.
      exploit app_cons_not_nil; eauto; contradiction. }
    rewrite Hempty, join_empty_hists, map_repeat in Hfullk, Hfullv by (apply Zlength_empty).
    erewrite full_hist_nil' with (l := keys) by eauto.
    erewrite full_hist_nil' with (l := vals) by eauto.
    rewrite combine_const1, map_repeat by (rewrite Zlength_repeat; omega).
    constructor; auto. }
  (* Find the last linearization point.
     Prove that we can remove the entire operation and everything else will be consistent.
     Recurse. *)
  exploit add_items_hist_length; eauto; intro Hlenh.
  assert (Zlength keys = size) as Hlenk.
  { rewrite <- (mem_lemmas.Forall2_Zlength Hkeys), Zlength_map, fold_join_hists_length, Zlength_empty; auto. }
  assert (Zlength vals = size) as Hlenv.
  { erewrite <- Zlength_map, <- (mem_lemmas.Forall2_Zlength Hfullv), Zlength_map, fold_join_hists_length,
      Zlength_empty; auto. }
  (* There are two basic approaches to this induction:
     1) Calculate from the op traces which op(s) can be last, and pull it to the end. This could involve, e.g.,
        matching values in gets to values in sets.
     2) Define linearization points and take the op with the last linearization point. This is quite general,
        but may be more complex in any given instance, since it imposes more ordering than we need. On the other
        hand, it may provide easier induction... maybe. *)
  (* As written, it's hard to tell the difference between a load made on the way to the target (not a
     linearization point) and one made at the end of a failed add (a linearization point). Not sure what the
     best way would be to fix this. *)
  destruct (existsb (fun '(_, _, _, s) => negb s) (map (fun x => last x (0, 0, 0, true)) (map fst lr)))
    eqn: Hfail.
  - (* There is a last failing add. *)
    rewrite existsb_exists in Hfail.
    destruct Hfail as ((((k, v), i), [|]) & Hin & ?); [discriminate|].
    rewrite in_map_iff in Hin; destruct Hin as (? & Hlast & Hin).
    rewrite in_map_iff in Hin; destruct Hin as ((la, h) & ? & Hin); subst.
    apply In_Znth with (d := ([], [])) in Hin; destruct Hin as (j & Hltj & Hj).
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hadd) as Haddj.
    rewrite Hj in Haddj.
    inv Haddj; [discriminate|].
    simpl in Hlast; rewrite last_snoc in Hlast; inv Hlast.
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hnzk) as Hk.
    rewrite Hj in Hk; simpl in Hk.
    rewrite Forall_app in Hk; destruct Hk as (Hk0 & Hk); inversion Hk as [|?? Hk1 _]; subst.
    destruct Hk1; clear Hk.
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hnzv) as Hv.
    rewrite Hj in Hv; simpl in Hv.
    rewrite Forall_app in Hv; destruct Hv as (Hv0 & Hv); inversion Hv as [|?? Hv1 _]; subst.
    assert (Zlength h' = size /\ Zlength h = size /\ 0 <= i < size) as (Hlenh' & ? & ?).
    { destruct Hadd0 as (? & ? & _).
      eapply Forall_Znth with (i0 := j) in Hlenh; [|rewrite Zlength_map; auto].
      rewrite Znth_map', Hj, Zlength_empty in Hlenh; simpl in *; omega. }
    econstructor.
    + erewrite Znth_map, Hj; simpl; eauto.
    + simpl.
      replace la0 with (fst (la0, h')) by auto; rewrite upd_Znth_map.
      assert (Forall (fun h => Zlength h = Zlength empty_hists) (map snd (upd_Znth j lr (la0, h')))).
      { rewrite Forall_map; apply Forall_upd_Znth.
        { rewrite <- Forall_map; apply add_items_hist_length; auto. }
        eapply add_items_length; eauto. }
      eapply IHn.
      * rewrite <- upd_Znth_map.
        erewrite length_concat_upd by (rewrite Zlength_map; auto).
        rewrite Znth_map', Hj; simpl.
        rewrite app_length; simpl; omega.
      * apply Forall_upd_Znth; auto.
      * instantiate (1 := keys).
        rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        intros; rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite <- !upd_Znth_map; simpl.
        eapply remove_last_full_hist with (h := h); eauto.
        { rewrite Zlength_map; auto. }
        { erewrite Znth_map, Hj; auto. }
        { omega. }
        { eapply Forall2_Znth with (i1 := i0)(d2 := vint 0) in Hfullk; auto.
          rewrite Znth_map', Znth_join_hists in Hfullk; eauto.
          { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. } }
      * rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        intros ???? Hin; rewrite Znth_map', Znth_join_hists in Hin by auto; simpl in Hin.
        eapply Forall2_Znth with (i1 := i0)(d2 := 0) in Hkeys.
        eapply Hkeys.
        rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite <- !upd_Znth_map in Hin.
        apply key_hists_fail with (j := i0) in Hadd0; auto.
        destruct Hadd0 as (? & Heq & ?).
        eapply concat_less_incl; eauto.
        { rewrite !Zlength_map; auto. }
        { erewrite Znth_map, !Znth_map', Hj by (rewrite !Zlength_map; auto); simpl.
          rewrite Heq; simpl; eauto. }
        { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. }
      * auto.
      * apply Forall_upd_Znth; auto.
      * instantiate (1 := vals).
        rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        intros; rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite <- !upd_Znth_map; simpl.
        erewrite upd_Znth_triv.
        { eapply Forall2_Znth with (i1 := i0)(d2 := vint 0) in Hfullv; auto.
          rewrite Znth_map', Znth_join_hists in Hfullv; eauto.
          { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. } }
        { rewrite !Zlength_map; auto. }
        { rewrite !Znth_map', Hj; simpl.
          apply key_hists_fail with (j := i0) in Hadd0; auto.
          destruct Hadd0 as (? & -> & ?); auto. }
      * auto.
      * apply Forall_upd_Znth; auto.
    + unfold add.
      assert (forall i' t e v, In (t, e) (fst (Znth i' h ([], []))) -> value_of e = vint v -> repable_signed v ->
        v <> 0 -> v = Znth i' keys 0) as Hkey.
      { intros; assert (0 <= i' < size).
        { exploit (Znth_inbounds i' h ([], [])); [|omega].
          intro X; rewrite X in *; contradiction. }
        eapply Forall2_Znth with (i0 := i')(d2 := 0) in Hkeys.
        exploit Hkeys.
        { rewrite Znth_map', Znth_join_hists by auto; simpl.
          rewrite in_concat; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; [|apply Znth_In with (i0 := j); auto].
          rewrite Hj; auto. }
        { intro; absurd (v0 = 0); auto; apply repr_inj_signed; auto; congruence. }
        intro; apply repr_inj_signed; auto.
        { apply Forall_Znth; auto; omega. }
        congruence.
        { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. } }
      assert (fst (Znth i (combine keys vals) (0, 0)) = k).
      { rewrite Znth_combine by omega.
        assert (exists t, In (t, Load (vint k)) (fst (Znth i h ([], [])))) as (t & Hload).
        { destruct Hadd0 as (? & ? & Hi & ?).
          destruct (Znth i h' ([], [])).
          destruct Hi as ((? & ? & [-> | (? & ? & ? & ->)]) & ?); eexists; rewrite in_app; simpl; eauto. }
        erewrite <- Hkey; simpl; eauto. }
      split; [|eauto].
      assert (Zlength (combine keys vals) = size) as Hcombine.
      { rewrite Zlength_combine, Z.min_l, Hlenk by omega; auto. }
      assert (Zlength (rebase (combine keys vals) (hash k)) = size) as Hrebase.
      { rewrite Zlength_rebase; rewrite Hcombine; auto.
        apply hash_range. }
      pose proof (Z_mod_lt (i - hash k) size size_pos).
      unfold lookup; rewrite index_of'_succeeds with (i := ((i - hash k) mod size)); try omega.
      * simpl.
        rewrite Zminus_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.sub_simpl_r, Zmod_small; auto.
      * rewrite Forall_forall_Znth with (d := (0, 0)), Zlength_sublist; intros.
        rewrite Znth_sublist by (auto; omega).
        rewrite Z.add_0_r, Znth_rebase; rewrite Zlength_combine, Z.min_l, Hlenk; try omega.
        destruct Hadd0 as (? & ? & _ & Hrest).
        destruct (Hrest ((i0 + hash k) mod size)) as ((? & r & ? & ? & Hr & ? & ? & _) & _).
        { unfold indices.
          rewrite in_map_iff, Z.add_comm; do 2 eexists; eauto.
          rewrite In_upto, Z2Nat.id; omega. }
        assert (exists t, In (t, Load (vint r)) (fst (Znth ((i0 + hash k) mod size) h ([], [])))) as (t & Hin).
        { destruct Hr as [-> | (? & ? & ? & ->)]; eexists; rewrite in_app; simpl; eauto. }
        exploit Hkey; eauto; auto.
        intro X; rewrite Znth_combine, <- X by omega; subst; auto.
        { apply hash_range. }
        { split; [omega | apply Z_mod_lt, size_pos]. }
        { rewrite Hrebase; omega. }
      * rewrite <- Hcombine, Znth_rebase'; auto; rewrite Hcombine; try omega.
        apply hash_range.
  - (* All threads finished with a successful add. Still, one thread's final add may be hit by another thread.
       We could search for one whose value isn't used - there must be one, but it's hard to compute which
       ops interfere because of chaining. We could choose the last one to CAS, except that operations on
       different locations are unordered. *)
    (* We could choose one that performed the final operation on a location, but it takes some complicated
       reasoning to prove this exists: e.g., we can't have two successful adds that each read the other.
       One approach would be to develop a theory of operations and orderings between them
       (e.g., if an op happens after your CAS it happens after everything before your CAS).
       It would look something like hb, and operate on tuples of i, timestamp, op. *)
       
Definition last_op (h : hist) e := exists t, In (t, e) h /\ Forall (fun '(m, _) => (m < t)%nat) h.
       
    assert (exists i k, last_op (Znth i (map fst
              (fold_right join_hists (repeat ([], []) (Z.to_nat size))
                 (map snd lr))) []) (CAS (vint 0) (vint 0) (vint k))).
    { 
    
    
    
    assert (exists j, 0 <= j < Zlength lr /\ Znth j (map fst lr) [] <> []) as (j & Hltj & Hnonnil).
    { destruct (concat (map fst lr)) eqn: Hconcat; [discriminate|].
      assert (In p (concat (map fst lr))) as Hin by (rewrite Hconcat; simpl; auto).
      rewrite in_concat in Hin; destruct Hin as (? & ? & Hin).
      eapply In_Znth in Hin; destruct Hin as (? & ? & Heq).
      rewrite Zlength_map in *; do 2 eexists; eauto.
      intro X; rewrite X in Heq; subst; contradiction. }
    exploit existsb_nth; eauto.
    { instantiate (1 := Z.to_nat j).
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id, <- Zlength_correct, !Zlength_map; tauto. }
    rewrite nth_Znth, Z2Nat.id by tauto.
    rewrite Znth_map', Znth_map' with (b := ([], [])).
    rewrite Znth_map with (d' := ([], [])) in Hnonnil by auto.
    destruct (Znth j lr ([], [])) as (la, h) eqn: Hj; simpl in *.
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hadd) as Haddj.
    rewrite Hj in Haddj.
    inv Haddj; [contradiction|].
    rewrite last_snoc; destruct s; [|discriminate].
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hnzk) as Hk.
    rewrite Hj in Hk; simpl in Hk.
    rewrite Forall_app in Hk; destruct Hk as (Hk0 & Hk); inversion Hk as [|?? Hk1 _]; subst.
    destruct Hk1; clear Hk.
    pose proof (Forall_Znth _ _ _ ([], []) Hltj Hnzv) as Hv.
    rewrite Hj in Hv; simpl in Hv.
    rewrite Forall_app in Hv; destruct Hv as (Hv0 & Hv); inversion Hv as [|?? Hv1 _]; subst.
    assert (Zlength h' = size /\ Zlength h = size /\ 0 <= i < size) as (Hlenh' & ? & ?).
    { destruct Hadd0 as (? & ? & _).
      eapply Forall_Znth with (i0 := j) in Hlenh; [|rewrite Zlength_map; auto].
      rewrite Znth_map', Hj, Zlength_empty in Hlenh; simpl in *; omega. }
    econstructor.
    + erewrite Znth_map, Hj; simpl; eauto.
    + replace la0 with (fst (la0, h')) by auto; rewrite upd_Znth_map.
      assert (Forall (fun h => Zlength h = Zlength empty_hists) (map snd (upd_Znth j lr (la0, h')))).
      { rewrite Forall_map; apply Forall_upd_Znth.
        { rewrite <- Forall_map; apply add_items_hist_length; auto. }
        eapply add_items_length; eauto. }
      eapply IHn.
      * rewrite <- upd_Znth_map.
        erewrite length_concat_upd by (rewrite Zlength_map; auto).
        rewrite Znth_map', Hj; simpl.
        rewrite app_length; simpl; omega.
      * apply Forall_upd_Znth; auto.
      * instantiate (1 := upd_Znth i keys 0).
        rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        { rewrite upd_Znth_Zlength; auto; omega. }
        intros ??; rewrite !Znth_map', Znth_join_hists by auto; simpl.
        instantiate (1 := 0).
        eapply Forall2_Znth with (i1 := i0) in Hfullk.
        rewrite !Znth_map', Znth_join_hists in Hfullk; auto; simpl in Hfullk.
        rewrite <- !upd_Znth_map.
        destruct (eq_dec i0 i).
        -- subst; rewrite upd_Znth_same by omega.
           destruct Hadd0 as (? & ? & Hi & _).
           simpl; destruct (Znth i h' ([], [])) eqn: Hh'.
           destruct Hi as (? & ? & ? & ? & ? & ? & Hi1 & Hi2 & Hzero).
           
        -- rewrite upd_Znth_diff' by (auto; omega).
           eapply remove_last_full_hist' with (h := h); eauto.
           { rewrite Zlength_map; auto. }
           { erewrite Znth_map, Hj; auto. }
           { omega. }
        -- rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto.
      * rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        { rewrite upd_Znth_Zlength; auto; omega. }
        intros ???? Hin; rewrite Znth_map', Znth_join_hists in Hin by auto; simpl in Hin.
        destruct (eq_dec i0 i).
        -- subst; rewrite upd_Znth_same by omega; intro.
           admit.
        -- rewrite upd_Znth_diff' by (auto; omega).
           eapply Forall2_Znth with (i1 := i0)(d2 := 0) in Hkeys.
           eapply Hkeys.
           rewrite Znth_map', Znth_join_hists by auto; simpl.
           rewrite <- !upd_Znth_map in Hin.
           admit.
(*           apply key_hists_fail with (j := i0) in Hadd0; auto.
        destruct Hadd0 as (? & Heq & ?).
        eapply concat_less_incl; eauto.
        { rewrite !Zlength_map; auto. }
        { erewrite Znth_map, !Znth_map', Hj by (rewrite !Zlength_map; auto); simpl.
          rewrite Heq; simpl; eauto. }*)
        { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. }
      * apply Forall_upd_Znth; auto.
      * apply Forall_upd_Znth; auto.
      * instantiate (1 := upd_Znth i vals 0).
        admit.
(*        rewrite Forall2_forall_Znth; split; rewrite !Zlength_map, fold_join_hists_length, Zlength_empty; auto.
        { rewrite upd_Znth_Zlength; auto; omega. }
        intros; rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite <- !upd_Znth_map; simpl.
        erewrite upd_Znth_triv.
        { eapply Forall2_Znth with (i1 := i0) in Hfullv; auto.
          rewrite Znth_map', Znth_join_hists in Hfullv; eauto.
          { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. } }
        { rewrite !Zlength_map; auto. }
        { rewrite !Znth_map', Hj; simpl.
          apply key_hists_fail with (j := i0) in Hadd0; auto.
          destruct Hadd0 as (? & -> & ?); auto. }*)
      * apply Forall_upd_Znth; auto.
      * apply Forall_upd_Znth; auto.
    + unfold add.
      rewrite combine_upd_Znth by omega.
      assert (Zlength (combine keys vals) = size) as Hcombine by (rewrite Zlength_combine, Z.min_l; omega).
      rewrite upd_Znth_same, upd_Znth_twice by (rewrite Hcombine; auto).
      assert (forall i' t e v, In (t, e) (fst (Znth i' h ([], []))) -> value_of e = vint v -> repable_signed v ->
        v <> 0 -> v = Znth i' keys 0) as Hkey.
      { intros; assert (0 <= i' < size).
        { exploit (Znth_inbounds i' h ([], [])).
          { intro X; rewrite X in *; contradiction. }
          destruct Hadd0; omega. }
        eapply Forall2_Znth with (i0 := i')(d2 := 0) in Hkeys.
        exploit Hkeys.
        { rewrite Znth_map', Znth_join_hists by auto; simpl.
          rewrite in_concat; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; eauto.
          rewrite in_map_iff; do 2 eexists; [|apply Znth_In with (i0 := j); auto].
          rewrite Hj; auto. }
        { intro; absurd (v0 = 0); auto; apply repr_inj_signed; auto; congruence. }
        intro; apply repr_inj_signed; auto.
        { apply Forall_Znth; auto; omega. }
        congruence.
        { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. } }
      pose proof (hash_range k).
      assert (Zlength (upd_Znth i (combine keys vals) (0, 0)) = size) as Hupd.
      { rewrite upd_Znth_Zlength; rewrite Hcombine; auto. }
      assert (Zlength (rebase (upd_Znth i (combine keys vals) (0, 0)) (hash k)) = size) as Hrebase.
      { rewrite Zlength_rebase; rewrite Hupd; auto. }
      pose proof (Z_mod_lt (i - hash k) size size_pos).
      split; [|split; auto].
      * unfold lookup; rewrite index_of'_succeeds with (i := ((i - hash k) mod size)); try omega.
        -- simpl.
           rewrite Zminus_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.sub_simpl_r, Zmod_small; auto.
        -- rewrite Forall_forall_Znth with (d := (0, 0)), Zlength_sublist.
           rewrite Z.sub_0_r; intros i0 Hi0.
           assert (0 <= i0 < size).
           { destruct Hi0; split; auto; etransitivity; eauto.
             apply Z_mod_lt, size_pos. }
           rewrite Znth_sublist by (auto; omega).
           rewrite Z.add_0_r, Znth_rebase; rewrite Hupd; auto.
           rewrite upd_Znth_diff'; try (rewrite Hcombine; auto).
           destruct Hadd0 as (? & ? & _ & Hrest).
           destruct (Hrest ((i0 + hash k) mod size)) as ((? & r & ? & ? & Hr & ? & ? & _) & _).
           { unfold indices.
             rewrite in_map_iff, Z.add_comm; do 2 eexists; eauto.
             rewrite In_upto, Z2Nat.id; omega. }
           assert (exists t, In (t, Load (vint r)) (fst (Znth ((i0 + hash k) mod size) h ([], [])))) as (t & Hin).
           { destruct Hr as [-> | (? & ? & ? & ->)]; eexists; rewrite in_app; simpl; eauto. }
           exploit Hkey; eauto; auto.
           intro X; rewrite Znth_combine, <- X by omega; subst; auto.
           { intro; subst.
             rewrite Zminus_mod_idemp_l, Z.add_simpl_r, Zmod_small in Hi0 by auto; omega. }
           { split; [omega | apply Z_mod_lt, size_pos]. }
           { rewrite Hrebase; omega. }
        -- rewrite <- Hupd, Znth_rebase' by (rewrite Hupd; auto).
           rewrite upd_Znth_same by (rewrite Hcombine; auto); auto.
      * erewrite upd_Znth_triv; auto.
        { rewrite Hcombine; auto. }
        rewrite Znth_combine by omega.
        destruct Hadd0 as (? & ? & Hi & _).
        destruct (Znth i h' ([], [])) eqn: Hh'.
        destruct Hi as (? & ? & tv & ? & ? & ? & Hi1 & Hi2 & ?).
        erewrite <- Hkey by (rewrite ?Hi1, ?in_app; simpl; eauto).
        instantiate (1 := 0).
        eapply Forall2_Znth with (i0 := i) in Hfullv;
          [|rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto].
        rewrite !Znth_map', Znth_join_hists in Hfullv by auto; simpl in Hfullv.
        instantiate (1 := 0) in Hfullv; destruct Hfullv as (lv & Hlv & Hval).
        assert (lv <> []) as Hnonnil'.
        { intro; subst.
          inv Hlv; [|eapply app_cons_not_nil; eauto].
          assert (In (tv, Store (vint v)) []); [|contradiction].
          replace [] with (concat (map snd (map (fun h => Znth i h ([], [])) (map snd lr)))).
          rewrite in_concat.
          do 2 eexists; [|repeat (rewrite in_map_iff; do 2 eexists; eauto); try (apply Znth_In; eauto)].
          { rewrite in_app; simpl; auto. }
          { rewrite Hj; auto. } }
        destruct (exists_last Hnonnil') as (lv0 & e' & ?); subst.
        rewrite apply_hist_app in Hval.
        destruct (apply_hist (vint 0) lv0) eqn: Hv'; [|discriminate].
        exploit apply_one_value; eauto; intro.
        apply f_equal.
        destruct (eq_dec e' (Store (vint v))).
        { subst; apply repr_inj_signed; auto; [apply Forall_Znth; auto; rewrite Hlenv; auto
          | simpl in *; congruence]. }
        assert (exists t, In (t, e') (concat (map snd (map (fun h => Znth i h ([], [])) (map snd lr)))) /\
          (tv < t)%nat) as (t & Hin & ?).
        { inv Hlv; [exploit app_cons_not_nil; eauto; contradiction|].
          exploit app_inj_tail; eauto; intros (? & ?); subst.
          eexists; rewrite He, in_app; simpl; split; eauto.
          unfold newer in Hlast; rewrite Forall_forall in Hlast; apply (Hlast (tv, Store (vint v))).
          assert (In (tv, Store (vint v)) (h1 ++ (t, e') :: h2)) as Hin'.
          { rewrite <- He, in_concat.
            exists (snd (Znth i h ([], []))); split; [rewrite Hi2, in_app; simpl; auto|].
            repeat (rewrite in_map_iff; do 2 eexists; eauto); [|apply Znth_In; eauto].
            rewrite Hj; auto. }
          rewrite in_app in Hin'; rewrite in_app; destruct Hin' as [? | [Heq | ?]]; auto.
          inv Heq; contradiction. }
        rewrite in_concat in Hin; destruct Hin as (? & Hin0 & Hin).
        rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
        rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
        rewrite in_map_iff in Hin; destruct Hin as ((?, h2) & ? & Hin); subst.
        assert (h2 = h).
        { rewrite Forall_forall in Hadd; generalize (Hadd _ Hin); simpl; intro.
          exploit add_val_success; try apply Hin0; eauto.
          { apply Forall_Znth; auto; omega. }
          { rewrite Forall_forall in Hnzv; specialize (Hnzv _ Hin); auto. }
          intros (k' & ? & tk & Hk').
          eapply Forall2_Znth with (i0 := i) in Hfullk;
            [|rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto].
          rewrite !Znth_map', Znth_join_hists in Hfullk by auto; simpl in Hfullk.
          instantiate (1 := 0) in Hfullk.
          exploit one_CAS_succeeds; eauto.
          { rewrite in_concat; do 2 eexists; eauto.
            rewrite in_map_iff; do 2 eexists; [|rewrite in_map_iff; do 2 eexists;
              [|rewrite in_map_iff; do 2 eexists; eauto]]; auto. }
          { rewrite in_concat; do 2 eexists; [|rewrite in_map_iff; do 2 eexists;
              [|rewrite in_map_iff; do 2 eexists; [|rewrite in_map_iff; do 2 eexists; [|apply Znth_In; eauto]]];
              rewrite ?Hj; eauto].
            rewrite in_app; simpl; eauto. }
          { rewrite Forall_forall; intros (?, ?) Hink.
            rewrite in_concat in Hink; destruct Hink as (? & ? & Hink); subst.
            do 2 (rewrite in_map_iff in Hink; destruct Hink as (? & ? & Hink); subst).
            rewrite in_map_iff in Hink; destruct Hink as ((?, ?) & ? & Hink); subst.
            specialize (Hadd _ Hink); simpl in Hadd.
            rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hink).
            intro; exploit add_key_success; try apply Hadd; eauto.
            intros (k'' & ? & Hin' & ?); rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin').
            simpl in *; absurd (k'' = 0); [tauto | apply repr_inj_signed; auto; [tauto | congruence]]. }
          intros (? & ?); subst.
          eapply In_Znth in Hin; destruct Hin as (j' & ? & Hj').
          assert (j' = j); [|subst; rewrite Hj in Hj'; inv Hj'; auto].
          destruct Hfullk as (? & ? & ?).
          eapply timestamp_unique; eauto.
          - erewrite Znth_map, !Znth_map', Hj' by (rewrite !Zlength_map; auto); eauto.
          - erewrite Znth_map, !Znth_map', Hj by (rewrite !Zlength_map; auto).
            simpl; rewrite Hi1, in_app; simpl; eauto. }
        subst; simpl in *; rewrite Hi2, in_app in Hin0.
        destruct Hin0 as [Hin0 | [Heq | ?]]; [ | inv Heq; contradiction | contradiction].
        match goal with H : newer _ tv |- _ => unfold newer in H; rewrite Forall_forall in H;
          specialize (H _ Hin0); simpl in H; omega end.
Admitted.*)

(*Lemma add_item_write : forall n keys values li ls h t e i v
  (Hadd : add_n_items_trace n empty_hists keys values li ls h)
  (Hin : In (t, e) (fst (Znth i h ([], [])))) (Hwrite : writes e (vint v))
  (Hkeys : Forall repable_signed keys) (Hnz : Forall (fun x => x <> 0) keys) (Hv : repable_signed v),
  exists j, 0 <= j < n /\ Znth j keys 0 = v /\ Znth j li 0 = i /\ Znth j ls false = true /\
    e = CAS (vint 0) (vint 0) (vint v).
Proof.
  remember empty_hists as h0; induction 1; subst; intros.
  { rewrite Znth_repeat in Hin; contradiction. }
  pose proof (add_n_items_lengths _ _ _ _ _ _ _ Hadd) as (? & ? & ? & ?).
  rewrite Forall_app in Hkeys; destruct Hkeys as (? & Hk); inv Hk.
  rewrite Forall_app in Hnz; destruct Hnz as (? & Hk); inv Hk.
  destruct Hadd0 as (? & ? & Hi & Hrest).
  destruct (in_dec (EqDec_prod _ _ _ _) (t, e) (fst (Znth i h' ([], [])))).
  { exploit IHHadd; auto.
    intros (j & ? & ? & ? & ? & ?); exists j; rewrite !app_Znth1; repeat split; auto; omega. }
  destruct (eq_dec i0 i).
  subst.
  destruct (Znth i h' ([], [])) eqn: Hh', s.
  - destruct Hi as (? & ? & ? & ? & ? & ? & Heq & ? & Hzero); rewrite Heq in *.
    rewrite in_app in Hin; destruct Hin as [? | [Hin | [Hin | ?]]]; try (inv Hin); try contradiction.
    exists (Zlength lk); rewrite !app_Znth2 by omega.
    repeat match goal with |-context[Znth ?a _ _] => replace a with 0 by omega; rewrite Znth_0_cons end.
    split; [pose proof (Zlength_nonneg lk); omega|].
    simpl in Hwrite; destruct Hwrite.
    assert (k = v) by (apply repr_inj_signed; auto; congruence); subst; auto.
  - destruct Hi as ((? & ? & [Hi | (? & ? & ? & Hi)]) & ?); rewrite Hi, in_app in *.
    + destruct Hin as [? | [Hin | ?]]; try (inv Hin); contradiction.
    + destruct Hin as [? | [Hin | [Hin | [Hin | ?]]]]; try (inv Hin); try contradiction.
      destruct Hwrite; absurd (k = 0); auto.
      apply repr_inj_signed; auto; [split; computable | congruence].
  - specialize (Hrest i).
    destruct (in_dec Z_eq_dec i (indices (hash k) i0)).
    + destruct Hrest as ((? & r & ? & ? & Hcase & ? & ? & ? & ?) & _); auto.
      destruct Hcase as [Hi1 | (? & ? & ? & Hi1)]; rewrite Hi1, in_app in *.
      * destruct Hin as [? | [Hin | ?]]; try (inv Hin); contradiction.
      * destruct Hin as [? | [Hin | [Hin | [Hin | ?]]]]; try (inv Hin); try contradiction.
        destruct Hwrite; absurd (r = 0); auto.
        apply repr_inj_signed; auto; [split; computable | congruence].
    + destruct Hrest as (_ & Hrest); rewrite Hrest in * by auto; contradiction.
Qed.

Lemma add_items_i_range : forall n h lk lv li ls h', add_n_items_trace n h lk lv li ls h' ->
  Forall (fun i => 0 <= i < Zlength h) li.
Proof.
  induction 1; auto.
  rewrite Forall_app; split; auto; constructor; auto.
  destruct Hadd as (? & ? & ?).
  erewrite <- add_n_items_length; eauto.
Qed.*)

Lemma add_items_Znth : forall h la h' j, add_items_trace h la h' -> 0 <= j < Zlength la ->
  exists h1 h2, let '(k, v, i, s) := Znth j la (0, 0, 0, false) in
    add_item_trace h1 k v i s h2 /\ hists_mono h h1 /\ hists_mono h2 h'.
Proof.
  induction 1; [rewrite Zlength_nil; omega | intros].
  rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
  destruct (eq_dec j (Zlength la)).
  - subst; do 2 eexists; rewrite !app_Znth2, Zminus_diag, Znth_0_cons by omega.
    split; eauto; split; auto; eapply add_items_trace_mono; eauto.
  - destruct IHadd_items_trace as (h1 & h2 & IH); [omega | exists h1, h2].
    rewrite !app_Znth1 by omega.
    destruct (Znth j la (0, 0, 0, false)) as (((?, ?), ?), ?); destruct IH as (? & ? & ?).
    split; [|split]; auto.
    etransitivity; eauto; eapply add_item_trace_mono; eauto.
Qed.

Lemma one_add_succeeds : forall lr keys
  (Hadd : Forall (fun '(la, h) => add_items_trace empty_hists la h) lr)
  (Hfullk : Forall2 full_hist' (map fst (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) keys))
  (Hkeys : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr))) keys)
  (Hrepk : Forall repable_signed keys)
  (Hnzk : Forall (fun x => Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) (fst x)) lr)
  k (Hin : In k (map fst (map fst (map fst (concat (map fst lr)))))),
  exists v i th t, In (k, v, i, true) (fst (Znth th lr ([], []))) /\
    In (t, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i (snd (Znth th lr ([], []))) ([], []))).
Proof.
  intros.
  repeat (rewrite in_map_iff in Hin; destruct Hin as ((?, ?) & ? & Hin); simpl in *; subst).
  rewrite in_concat in Hin; destruct Hin as (? & Hin0 & Hin); subst.
  rewrite in_map_iff in Hin; destruct Hin as ((la, h) & ? & Hin); subst.
  assert (repable_signed k /\ vint k <> vint 0) as (? & ?).
  { rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin).
    rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin0); destruct Hnzk as (Hk & ?).
    split; auto; intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  exploit add_items_hist_length; eauto; intro.
  destruct (existsb (Z.eqb k) keys) eqn: Hk.
  - rewrite existsb_exists in Hk.
    destruct Hk as (? & Hin' & Heq); rewrite Z.eqb_eq in Heq; symmetry in Heq; subst.
    apply In_Znth with (d := 0) in Hin'; destruct Hin' as (i & ? & Hi).
    eapply Forall2_Znth with (i0 := i) in Hfullk; [|rewrite (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map; auto].
    destruct Hfullk as (l & Hl & Hv); rewrite Znth_map', Hi in Hv.
    rewrite Znth_map', Znth_join_hists in Hl by auto; simpl in Hl.
    apply change_implies_write in Hv; auto.
    destruct Hv as (w & Hinw & Hw).
    rewrite <- hist_list'_in in Hinw by eauto.
    destruct Hinw as (t & Hinw).
    rewrite in_concat in Hinw; destruct Hinw as (h' & Hinw & Hin2).
    repeat (rewrite in_map_iff in Hin2; destruct Hin2 as (? & ? & Hin2); subst).
    rewrite Forall_forall in Hadd; specialize (Hadd _ Hin2).
    destruct x as (la2, h2).
    exploit add_key_success; try apply Hadd; eauto.
    { rewrite Forall_forall in Hnzk; apply (Hnzk (la2, h2)); auto. }
    intros (k & ? & ? & ? & ? & ?); subst.
    assert (Znth i keys 0 = k).
    { apply repr_inj_signed; auto; congruence. }
    eapply In_Znth in Hin2; destruct Hin2 as (? & ? & Heq).
    subst; do 5 eexists; rewrite Heq; eauto.
  - rewrite Forall_forall in Hadd; specialize (Hadd _ Hin).
    eapply In_Znth in Hin0; destruct Hin0 as (j & ? & Hj).
    apply add_items_Znth with (j := j) in Hadd; auto.
    destruct Hadd as (h1 & h2 & Hadd); rewrite Hj in Hadd.
    destruct Hadd as ((? & ? & Hi & _) & Hh1 & Hh).
    assert (exists t e, In (t, e) (fst (Znth z h2 ([], []))) /\ value_of e = vint k) as (t & e & ? & He).
    { destruct (Znth z h1 ([], [])), b.
      + destruct Hi as (? & ? & ? & ? & ? & ? & -> & ?).
        do 3 eexists; [rewrite in_app; simpl; eauto | auto].
      + destruct Hi as ((? & ? & [-> | (? & ? & ? & ->)]) & ?);
          do 3 eexists; try (rewrite in_app; simpl; eauto); auto. }
    clear Hi.
    assert (Zlength h1 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hh1), Zlength_empty; auto).
    eapply Forall2_Znth with (i := z)(d2 := 0) in Hkeys;
      [|rewrite Zlength_map, fold_join_hists_length, Zlength_empty by auto; omega].
    rewrite Znth_map', Znth_join_hists in Hkeys by auto; simpl in Hkeys.
    exploit (Hkeys t e).
    { eapply Forall2_Znth with (i := z) in Hh; [|omega].
      rewrite in_concat; do 2 eexists; [|repeat (rewrite in_map_iff; do 2 eexists; eauto)].
      simpl; destruct Hh as ((? & ->) & _).
      rewrite in_app; eauto. }
    { intro X; rewrite X in He.
      absurd (vint k = vint 0); auto. }
    intro X; rewrite <- X in He.
    assert (Zlength keys = size).
    { erewrite <- Zlength_map, <- (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map, fold_join_hists_length,
        Zlength_empty by auto; omega. }
    exploit existsb_nth; eauto.
    { apply Nat2Z.inj_lt; rewrite Z2Nat.id, <- Zlength_correct.
      instantiate (1 := z); omega.
      { tauto. } }
    rewrite nth_Znth with (d := 0), Z2Nat.id, Z.eqb_neq by tauto; intro Hn; contradiction Hn.
    apply repr_inj_signed; auto.
    { apply Forall_Znth; auto; omega. }
    congruence.
Qed.

Lemma only_one_add_succeeds : forall lr keys th1 th2 k v1 v2 i1 i2
  (Hadd : Forall (fun '(la, h) => add_items_trace empty_hists la h) lr)
  (Hfullk : Forall2 full_hist' (map fst (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) keys))
  (Hkeys : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr))) keys)
  (Hrepk : Forall repable_signed keys)
  (Hnzk : Forall (fun x => Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) (fst x)) lr)
  (Hsucc1 : In (k, v1, i1, true) (fst (Znth th1 lr ([], []))))
  (Hsucc2 : In (k, v2, i2, true) (fst (Znth th2 lr ([], [])))),
  th1 = th2 /\ i1 = i2.
Proof.
  intros.
  assert (0 <= th1 < Zlength lr) as Hth1.
  { exploit (Znth_inbounds th1 lr ([], [])); auto.
    intro X; rewrite X in Hsucc1; contradiction. }
  assert (0 <= th2 < Zlength lr) as Hth2.
  { exploit (Znth_inbounds th2 lr ([], [])); auto.
    intro X; rewrite X in Hsucc2; contradiction. }
  pose proof (Forall_Znth _ _ _ ([], []) Hth1 Hadd) as Hadd1.
  pose proof (Forall_Znth _ _ _ ([], []) Hth2 Hadd) as Hadd2.
  destruct (Znth th1 lr ([], [])) as (la1, h1) eqn: Hr1,
           (Znth th2 lr ([], [])) as (la2, h2) eqn: Hr2; simpl in *.
  eapply In_Znth in Hsucc1; destruct Hsucc1 as (j1 & ? & Hj1).
  apply add_items_Znth with (j := j1) in Hadd1; auto.
  destruct Hadd1 as (ha1 & hb1 & Hadd1); rewrite Hj1 in Hadd1.
  destruct Hadd1 as ((? & ? & Hi1 & Hrest1) & Hha1 & Hhb1).
  eapply In_Znth in Hsucc2; destruct Hsucc2 as (j2 & ? & Hj2).
  apply add_items_Znth with (j := j2) in Hadd2; auto.
  destruct Hadd2 as (ha2 & hb2 & Hadd2); rewrite Hj2 in Hadd2.
  destruct Hadd2 as ((? & ? & Hi2 & Hrest2) & Hha2 & Hhb2).
  exploit add_items_hist_length; eauto; intro.
  assert (Zlength ha1 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hha1), Zlength_empty; auto).
  assert (Zlength ha2 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hha2), Zlength_empty; auto).
  destruct (Znth i1 ha1 ([], [])) eqn: Hh1, (Znth i2 ha2 ([], [])) eqn: Hh2.
  destruct Hi1 as (? & t1 & ? & ? & ? & ? & Hi1 & _ & Hzero1).
  destruct Hi2 as (? & t2 & ? & ? & ? & ? & Hi2 & _ & Hzero2).
  assert (In (t1, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i1 h1 ([], [])))).
  { eapply Forall2_Znth with (i := i1) in Hhb1; [|omega].
    destruct Hhb1 as ((? & ->) & _); rewrite Hi1, !in_app; simpl; eauto. }
  assert (In (t2, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i2 h2 ([], [])))).
  { eapply Forall2_Znth with (i := i2) in Hhb2; [|omega].
    destruct Hhb2 as ((? & ->) & _); rewrite Hi2, !in_app; simpl; eauto. }
  assert (In h1 (map snd lr)) by (rewrite in_map_iff; do 2 eexists; [|apply Znth_In]; [rewrite Hr1|]; auto).
  assert (In h2 (map snd lr)) by (rewrite in_map_iff; do 2 eexists; [|apply Znth_In]; [rewrite Hr2|]; auto).
  destruct (eq_dec i1 i2).
  - split; auto.
    eapply Forall2_Znth with (i := i1) in Hfullk;
      [|rewrite Zlength_map, fold_join_hists_length, Zlength_empty by auto; omega].
    rewrite !Znth_map', Znth_join_hists in Hfullk by auto; simpl in Hfullk.
    instantiate (1 := 0) in Hfullk.
    exploit one_CAS_succeeds; eauto.
    { rewrite in_concat; exists (fst (Znth i1 h1 ([], []))); split; eauto.
      do 2 (rewrite in_map_iff; do 2 eexists; eauto). }
    { subst; rewrite in_concat; do 2 eexists; eauto.
      do 2 (rewrite in_map_iff; do 2 eexists; eauto). }
    { rewrite Forall_forall; intros (?, ?) Hink.
      rewrite in_concat in Hink; destruct Hink as (? & ? & Hink); subst.
      do 2 (rewrite in_map_iff in Hink; destruct Hink as (? & ? & Hink); subst).
      rewrite in_map_iff in Hink; destruct Hink as ((?, ?) & ? & Hink); subst.
      rewrite Forall_forall in Hadd; specialize (Hadd _ Hink); simpl in Hadd.
      rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hink).
      intro; exploit add_key_success; try apply Hadd; eauto.
      intros (k'' & ? & Hin' & ? & ? & ?); rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin').
      destruct Hnzk; absurd (k'' = 0); auto; apply repr_inj_signed; auto; congruence. }
    intros (? & ?); subst.
    destruct Hfullk as (? & ? & ?).
    eapply timestamp_unique; eauto.
    + erewrite Znth_map, !Znth_map', Hr1 by (rewrite !Zlength_map; auto); eauto.
    + erewrite Znth_map, !Znth_map', Hr2 by (rewrite !Zlength_map; auto); eauto.
  - set (i' := if zlt ((i1 - hash k) mod size) ((i2 - hash k) mod size) then i1 else i2).
    assert (0 <= i' < size) by (destruct (zlt _ _); subst i'; omega).
    assert (Zlength keys = size).
    { erewrite <- Zlength_map, <- (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map, fold_join_hists_length,
        Zlength_empty; auto. }
    assert (Znth i' keys 0 = k); [|assert (exists k', Znth i' keys 0 = k' /\ k' <> k) as (? & ? & ?); [|omega]].
    + eapply Forall2_Znth with (i := i')(d2 := 0) in Hkeys.
      assert (exists t' h', In (t', CAS (vint 0) (vint 0) (vint k)) (fst (Znth i' h' ([], []))) /\
        In h' (map snd lr)) as (t' & h' & Hin & Hh').
      { destruct (zlt _ _); do 3 eexists; eauto. }
      assert (repable_signed k /\ vint k <> vint 0) as (? & ?).
      { eapply Forall_Znth with (i := th1) in Hnzk; auto.
        rewrite Hr1 in Hnzk; simpl in Hnzk.
        eapply Forall_Znth with (i := j1) in Hnzk; auto.
        rewrite Hj1 in Hnzk; destruct Hnzk as (Hz & ?); split; auto.
        intro; contradiction Hz; apply repr_inj_signed; auto; congruence. }
      exploit Hkeys.
      { rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite in_concat; do 2 eexists; eauto.
        repeat (rewrite in_map_iff; do 2 eexists; eauto). }
      { auto. }
      simpl; intro; apply repr_inj_signed; auto.
      { apply Forall_Znth; auto; omega. }
      congruence.
      { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. }
    + set (j' := if zlt ((i1 - hash k) mod size) ((i2 - hash k) mod size) then i2 else i1).
      assert (exists ha hb h', Zlength hb = size /\ hists_mono hb h' /\ In h' (map snd lr) /\ forall j,
        In j (indices (hash k) j') -> failed_CAS k (Znth j ha ([], [])) (Znth j hb ([], [])))
        as (ha & hb & h' & ? & Hh' & Hin' & Hrest).
      { destruct (zlt _ _); subst i'; [exists ha2, hb2, h2 | exists ha1, hb1, h1];
          repeat split; auto; try omega; intro; [apply Hrest2 | apply Hrest1]. }
      specialize (Hrest i'); destruct Hrest as (? & r & ? & ? & Hi & ? & ? & ? & ?).
      { unfold indices; rewrite in_map_iff.
        exists ((i' - hash k) mod size); split.
        { rewrite Zplus_mod_idemp_r, Zplus_minus, Zmod_small; auto. }
        rewrite In_upto, Z2Nat.id by (apply Z_mod_lt, size_pos).
        destruct (zlt _ _); subst i' j'; split; try (apply Z_mod_lt, size_pos); try tauto.
        destruct (eq_dec ((i1 - hash k) mod size) ((i2 - hash k) mod size)); try omega.
        apply Zmod_plus_inv in e; [|apply size_pos].
        rewrite !Zmod_small in e; omega. }
      assert (exists t e, In (t, e) (fst (Znth i' hb ([], []))) /\ value_of e = vint r) as (? & ? & ? & ?).
      { destruct Hi as [-> | (? & ? & ? & ->)]; do 2 eexists; rewrite in_app; simpl; split; eauto. }
      eapply Forall2_Znth with (i := i')(d2 := 0) in Hkeys.
      exploit Hkeys.
      { rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite in_concat; exists (fst (Znth i' h' ([], []))); split.
        { eapply Forall2_Znth with (i := i') in Hh'; [|omega].
          destruct Hh' as ((? & ->) & _); rewrite in_app; eauto. }
        repeat (rewrite in_map_iff; do 2 eexists; eauto). }
      { intro; absurd (r = 0); auto; apply repr_inj_signed; auto; congruence. }
      intro; assert (Znth i' keys 0 = r); [|eauto].
      apply repr_inj_signed; auto.
      { apply Forall_Znth; auto; omega. }
      congruence.
      { rewrite Zlength_map, fold_join_hists_length, Zlength_empty; auto. }
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name m_entries _m_entries.
  name locksp _thread_locks.
  name resp _results.
  name keys _keys.
  name values _values.
  start_function.
  forward.
  forward_call m_entries.
  Intro entries.
  destruct (split_shares 3 Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite <- seq_assoc.
  destruct (split_readable_share Tsh) as (sh1 & sh2 & ? & ? & ?); auto.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _total (vint 0); lvar _values (tarray tint 16384) values;
           lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs Ews (tarray tentry size) entries m_entries;
         atomic_entries Tsh entries empty_hists;
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         EX res : list val, !!(Zlength res = i) &&
           data_at Ews (tarray (tptr tint) 3) (res ++ repeat Vundef (Z.to_nat (3 - i))) resp *
           fold_right sepcon emp (map (data_at_ Tsh tint) res) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) res) *
         EX locks : list val, !!(Zlength locks = i) &&
           data_at Ews (tarray (tptr (Tstruct _lock_t noattr)) 3)
             (locks ++ repeat Vundef (Z.to_nat (3 - i))) locksp *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) locks) *
           fold_right sepcon emp (map (fun j => lock_inv Tsh (Znth j locks Vundef)
             (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp (Znth j locks Vundef)
              resp (Znth j res Vundef))) (upto (Z.to_nat i))))).
  { Exists (@nil val) (@nil val); go_lower; entailer'. }
  { (* first loop *)
    Intros res locks.
    forward_call (sizeof (Tstruct _lock_t noattr)).
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro r.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    focus_SEP 3.
    forward_call (l, Tsh, f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp l resp r).
    { entailer!.
      destruct l; try contradiction; auto. }
    { apply sepcon_derives; [apply lock_struct | cancel_frame]. }
    Exists (res ++ [r]) (locks ++ [l]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    go_lower; entailer'.
    rewrite lock_inv_isptr, data_at__isptr; Intros.
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app by omega.
    simpl; change (upto 1) with [0]; simpl.
    rewrite Z2Nat.id, Z.add_0_r by omega.
    replace (Zlength res + 1) with (Zlength (res ++ [r]))
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; auto).
    rewrite <- upd_complete_gen by omega.
    replace (Zlength (res ++ [r])) with (Zlength (locks ++ [l]))
      by (rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; auto; omega).
    rewrite <- upd_complete_gen by omega.
    rewrite !app_Znth2 by omega.
    replace (Zlength locks) with (Zlength res); rewrite Zminus_diag, !Znth_0_cons.
    rewrite (sepcon_comm _ (@data_at CompSpecs Ews (tarray tentry size) entries m_entries)), !sepcon_assoc;
      apply sepcon_derives; [auto|].
    rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_entries Tsh entries empty_hists)), !sepcon_assoc;
      apply sepcon_derives; [auto|].
    rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc.
    rewrite <- !sepcon_assoc.
    match goal with |- _ |-- ?P * ?Q => rewrite (sepcon_comm P Q) end.
    rewrite !sepcon_assoc; apply sepcon_derives; [auto|].
    rewrite <- 2sepcon_assoc, sepcon_comm, !sepcon_assoc.
    destruct r; try contradiction.
    destruct l; try contradiction.
    repeat (apply sepcon_derives; [apply derives_refl|]).
    cancel.
    apply sepcon_list_derives; rewrite !Zlength_map, !Zlength_upto, <- Zlength_correct.
    { rewrite Z2Nat.id; auto; omega. }
    intros.
    erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- ?Zlength_correct, ?Z2Nat.id; auto; omega).
    rewrite !app_Znth1 by omega; auto. }
  Intros res locks.
  rewrite !app_nil_r.
  assert_PROP (Zlength entries = size) by entailer!.
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, EX sh : share,
    PROP (sepalg_list.list_join sh0 (sublist i 3 shs) sh)
    LOCAL (temp _total (vint 0); lvar _values (tarray tint 16384) values;
           lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries m_entries;
         EX sh' : share, !!(sepalg.join sh (Share.comp Ews) sh') && atomic_entries sh' entries empty_hists;
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at sh (tarray (tptr tint) 3) res resp;
         fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i 3 res));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) res);
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) locks);
         fold_right sepcon emp (map (fun j => lock_inv (if zlt j i then sh1 else Tsh) (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp (Znth j locks Vundef)
           resp (Znth j res Vundef))) (upto 3)))).
  { rewrite !sublist_same by auto; Exists Ews Tsh; go_lower; entailer'.
    apply prop_right, comp_join_top. }
  { (* second loop *)
    forward_call (sizeof tint).
    { simpl; computable. }
    Intros t sh'.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    simpl in *; assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh0 _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|????? Hj1 Hj2]; subst end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh3 & ? & Hj3).
    destruct (sepalg.join_assoc(c := Share.comp Ews)(e := sh') Hj3) as (sh3' & ? & Hj3'); auto.
    get_global_function'' _f; Intros.
    apply extract_exists_pre; intros f_.
    forward_spawn (share * share * list (val * val) * val * Z * val * val * val * val)%type
      (f_, t, (Znth i shs Ews, sh2, entries, m_entries, i, locksp, Znth i locks Vundef, resp, Znth i res Vundef),
    fun (x : (share * share * list (val * val) * val * Z * val * val * val * val)%type) (tid : val) =>
    let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
    fold_right sepcon emp
      [!!(0 <= t < 3 /\ isptr lockt /\ readable_share sh /\ readable_share tsh) && emp;
        data_at sh (tarray tentry size) entries p; atomic_entries sh entries empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res)]).
    { unfold spawn_pre; go_lower.
      Exists _arg (fun x : (share * share * list (val * val) * val * Z * val * val * val * val) =>
        let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
        [(_m_entries, p); (_thread_locks, locksp); (_results, resultsp)]).
      rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
      repeat (apply andp_right; [apply prop_right; repeat split; auto|]).
      { rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
        f_equal; f_equal; extensionality.
        destruct x0 as (?, x0); repeat destruct x0 as (x0, ?); simpl.
        extensionality; apply mpred_ext; entailer!. }
      rewrite (extract_nth_sepcon (map _ (upto 3)) i) by (rewrite Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      destruct (zlt i i); [omega|].
      rewrite lock_inv_isptr; Intros.
      assert (0 <= i < Zlength shs) by omega.
      apply andp_right.
      - apply prop_right; split; [omega|]; split; [omega|]; split; auto; split; auto.
        apply Forall_Znth; auto.
      - rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj3).
        rewrite <- (atomic_entries_join_nil _ _ _ _ Hj3'); auto.
        rewrite <- (lock_inv_share_join sh1 sh2) by auto.
        rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ m_entries)),
          !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
        fast_cancel.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ locksp)),
          !sepcon_assoc; apply sepcon_derives.
        { rewrite lock_struct_array; apply stronger_array_ext.
          - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
          - intros j ???; unfold unfold_reptype; simpl.
            destruct (eq_dec j i).
            + subst; rewrite upd_Znth_same; auto.
            + rewrite upd_Znth_diff by auto.
              rewrite Znth_repeat with (x1 := Vundef)(n0 := 3%nat); apply stronger_default_val. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ resp)),
          !sepcon_assoc; apply sepcon_derives.
        { apply stronger_array_ext.
          - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
          - intros j ???; unfold unfold_reptype; simpl.
            destruct (eq_dec j i).
            + subst; rewrite upd_Znth_same; auto.
            + rewrite upd_Znth_diff' by auto.
              rewrite Znth_repeat with (x1 := Vundef)(n0 := 3%nat); apply stronger_default_val. }
        erewrite sublist_next by (auto; omega); simpl; fast_cancel.
        { apply Forall_Znth; auto. }
        { eapply join_readable1, readable_share_list_join; eauto. } }
    go_lower.
    Exists sh3 sh3'; entailer'.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    fast_cancel.
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
    intros j ?; destruct (eq_dec j i).
    - subst; rewrite upd_Znth_same by auto.
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      if_tac; [auto | omega].
    - rewrite upd_Znth_diff' by auto.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      if_tac; if_tac; auto; omega. }
  Intros sh sh'.
  rewrite sublist_nil, <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, EX x : (share * (list (list (hist * hist) * list Z * list bool))),
    PROP (readable_share (fst x); sepalg_list.list_join (fst x) (sublist i 3 shs) Ews; Zlength (snd x) = i;
          Forall (fun p => let '(h, li, ls) := p in add_items_trace empty_hists (combine (combine (combine
            [1; 2; 3] [1; 1; 1]) li) ls) h) (snd x);
          Forall (fun h' => Zlength h' = Zlength empty_hists) (map fst (map fst (snd x))))
    LOCAL (let ls := map snd (snd x) in temp _total (vint (Zlength (filter id (concat ls))));
           lvar _values (tarray tint 16384) values; lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs (fst x) (tarray tentry size) entries m_entries;
         EX sh' : share, !!(readable_share sh' /\ sepalg_list.list_join sh' (sublist i 3 shs) Tsh) &&
           let h := map fst (map fst (snd x)) in atomic_entries sh' entries (fold_right join_hists empty_hists h);
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at (fst x) (tarray (tptr tint) 3) res resp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) (sublist i 3 res));
         data_at (fst x) (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) (sublist i 3 locks));
         fold_right sepcon emp (map (fun j => lock_inv sh1 (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp
              (Znth j locks Vundef) resp (Znth j res Vundef))) (sublist i 3 (upto 3))))).
  { rewrite !(sublist_same 0 3) by auto.
    Exists (sh, @nil (list (hist * hist) * list Z * list bool)) sh'; go_lower.
    match goal with H : sepalg_list.list_join _ (sublist _ _ _) _ |- _ => rewrite sublist_nil in H; inv H end.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    entailer'.
    apply prop_right; split.
    { eapply join_readable1; eauto. }
    eapply sepalg_list.list_join_assoc2 in Hshs; [|eapply sepalg.join_comm, comp_join_top].
    destruct Hshs as (shd & Hjoin' & ?).
    apply sepalg.join_comm in Hjoin'; exploit (sepalg.join_eq(x := sh)(y := Share.comp Ews)(z := shd)(z' := sh'));
      auto; intro; subst; auto. }
  { (* third loop *)
    destruct x as (sh3, lr); Intros sh3'; simpl in *.
    erewrite sublist_next with (l := upto 3), Znth_upto by (auto; rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite lock_inv_isptr; Intros.
    forward.
    forward_call (Znth i locks Vundef, sh1, f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp
      (Znth i locks Vundef) resp (Znth i res Vundef)).
    forward_call (Znth i locks Vundef, Tsh, sh2,
      |>f_lock_inv (Znth i shs Ews) entries m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef),
      |>f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef)).
    { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans;
         try (apply precise_weak_precise || apply positive_weak_positive || apply rec_inv_weak_rec_inv); auto |].
      { apply later_positive; auto. }
      { apply later_rec_lock, selflock_rec. }
      unfold f_lock_pred at 2.
      rewrite selflock_eq.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (lock_inv _ _ _)), !sepcon_assoc, <- sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      rewrite <- (lock_inv_share_join sh1 sh2 Tsh) by auto; unfold f_lock_pred; cancel.
      apply lock_inv_later. }
    erewrite sublist_next with (l := locks) by (auto; omega); simpl.
    forward_call (Znth i locks Vundef, sizeof (Tstruct _lock_t noattr)).
    { entailer!. }
    { apply sepcon_derives; [|cancel_frame].
      admit. (* lock size *) }
    unfold f_lock_inv at 1; Intros hi lii lsi.
    assert (0 <= i < Zlength shs) by omega.
    forward.
    { apply Forall_Znth; auto. }
    { entailer!.
      rewrite upd_Znth_same; auto. }
    rewrite upd_Znth_same by auto.
    forward.
    erewrite sublist_next with (l := res) by (auto; omega); simpl.
    forward_call (Znth i res Vundef, sizeof tint).
    { entailer!. }
    { rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ (Znth i res Vundef))), !sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      apply data_at_memory_block. }
    assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh3 _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1 ? Hj1]; subst end.
    match goal with H : sepalg_list.list_join sh3' _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1' ? Hj1']; subst end.
    gather_SEP 10 2.
    replace_SEP 0 (data_at w1 (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp).
    { go_lower.
      rewrite <- lock_struct_array.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join; eauto. }
    gather_SEP 8 3.
    replace_SEP 0 (data_at w1 (tarray (tptr tint) 3) res resp).
    { go_lower.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join; eauto. }
    forward.
    go_lower; Exists (w1, lr ++ [(hi, lii, lsi)]) w1'.
    rewrite sepcon_andp_prop', sepcon_andp_prop.
    apply andp_right; [|apply andp_right; [|apply andp_right]]; try apply prop_right.
    - simpl; split; [omega|].
      split; [eapply join_readable1; eauto|].
      split; auto.
      split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; auto|].
      split; [rewrite Forall_app; repeat constructor; auto|].
      rewrite !map_app, Forall_app; repeat (split; auto).
      simpl; constructor; [|constructor].
      eapply add_items_length; eauto.
    - repeat (split; auto).
      simpl; rewrite add_repr, map_app, concat_app, filter_app, Zlength_app; simpl; rewrite app_nil_r; auto.
    - split; auto.
      eapply join_readable1; eauto.
    - rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh3 _ _ m_entries)), (sepcon_comm _ (data_at _ _ _ m_entries)).
      erewrite <- !sepcon_assoc, data_at_share_join by eauto.
      rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_entries _ _ _)), (sepcon_comm _ (atomic_entries _ _ _)).
      erewrite <- !sepcon_assoc, atomic_entries_join; eauto.
      Intros.
      simpl; rewrite !map_app, fold_right_app; simpl.
      rewrite join_hists_base.
      rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at_ _ _ values)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at_ _ _ keys)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      fast_cancel.
      + erewrite add_items_length by eauto; apply Zlength_empty.
      + rewrite fold_join_hists_length, Zlength_empty; auto.
      + rewrite fold_join_hists_length by auto.
        symmetry; eapply add_items_length; eauto.
      + apply Forall_Znth; auto. }
      Opaque combine.
  Intros x sh''; destruct x as (?, lr); simpl in *.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  (*forward_call (0, 0, m_entries, sh, entries, fold_right join_hists empty_hists (map fst (map fst lr))).*)
  eapply semax_seq'.
  let Frame := fresh "Frame" in evar (Frame: list (mpred)).
  refine (modusponens (global_funspec Delta _freeze_table _ _ _ _ _ _ _ _) _ _ _);
  [eapply lookup_funspec;
    [check_function_name
    | lookup_spec_and_change_compspecs CS _freeze_table
    | find_spec_in_globals']|].
  intro Hf.
  eapply (@semax_call_id00_wow (rmaps.ConstType
          (share * val * list (val * val) * list (hist * hist) * val * val)) (Ews, m_entries, entries, fold_right join_hists empty_hists (map fst (map fst lr)), keys, values) Frame _ _ _ _ _ _ _ _ _ Hf);
 clear Hf; try clear Frame;
 [ check_result_type | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2
 | cbv beta iota zeta; extensionality rho;
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    repeat rewrite exp_unfold; reflexivity
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].
  { rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    apply sepcon_derives; [apply derives_refl|].
    simpl; fast_cancel. }
  { split; auto.
    rewrite fold_join_hists_length, Zlength_empty; auto. }
  after_forward_call.
  Intro x; destruct x as (lk, lv); simpl; Intros.
  (* Here's where we can prove that total is 3. *)
  assert (Zlength (filter id (concat (map snd lr))) = 3).
  { assert (map snd (map (fun '(h, li, ls) => (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls, h)) lr) =
      map fst (map fst lr)) as Hlr.
    { rewrite !map_map; apply map_ext.
      intros ((?, ?), ?); auto. }
    assert (Forall (fun '(la, h) => add_items_trace empty_hists la h)
      (map (fun '(h, li, ls) => (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls, h)) lr)) as Hadd.
    { rewrite Forall_map; eapply Forall_impl; [|eauto].
      intros ((?, ?), ?); auto. }
    assert (Forall2 full_hist' (map fst (fold_right join_hists empty_hists
      (map snd (map (fun '(h, li, ls) => (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls, h)) lr))))
      (map (fun x => vint x) lk)) as Hfullk.
    { apply Forall2_map2.
    pose proof (one_add_succeeds _ _ Hadd Hfullk) as Hone.
    lapply Hone.
    clear Hone; intro Hone; lapply Hone.
    clear Hone; intro Hone; lapply Hone.
    clear Hone; intro Hone; lapply Hone.
    clear Hone; intro Hone; lapply Hone.
    clear Hone; intro Hone.
  ) lk).
    { eapply Forall2_map2, Forall2_impl; [|eauto].
      
  admit. }
  forward.
  Exists values keys.
  rewrite !sepcon_assoc, (sepcon_comm (data_at _ _ _ keys)), (sepcon_comm (data_at _ _ _ values)).
  rewrite sepcon_assoc, (sepcon_comm (data_at _ _ _ values)), <- !sepcon_assoc; apply sepcon_derives; [apply sepcon_derives; auto|];
    apply andp_right, data_at_data_at_; apply prop_right; auto.
Admitted.

(* Given the relations on histories, what can we actually conclude about the maps? *)
Lemma make_map_eq : forall h h', Forall2 (fun a b => value_of_hist (fst a) = value_of_hist (fst b) /\
  value_of_hist (snd a) = value_of_hist (snd b)) h h' -> make_map h = make_map h'.
Proof.
  induction 1; auto; simpl.
  destruct x, y; simpl in *.
  destruct H as (-> & ->); rewrite IHForall2; auto.
Qed.

Lemma make_map_no_key : forall h k (Hout : Forall (fun x => make_int (value_of_hist (fst x)) <> k) h),
  Forall (fun x => fst x <> k) (make_map h).
Proof.
  induction h; simpl; auto; intros.
  destruct a.
  inv Hout.
  constructor; auto.
Qed.

(* It would be nice if we could maintain the invariant that the map has no duplicates and is well-chained,
   and indeed, the algorithm should maintain these properties. However, the per-slot histories do not obviously
   present a way to prove this: if a new key has "mysteriously appeared" (i.e., been added by another thread),
   we don't have a good way of knowing that it's well-chained. *)
(* We can, however, allow for the possibility that there is garbage in the map, and consider the abstract map
   to be those elements that can be successfully looked up, rather than all pairs in the map. In practice, this
   *should* come down to the same thing, but how could we prove it? *)
Lemma set_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = size)
  (Htrace : set_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ let m' := make_map (upd_Znth i h' (Znth i h ([], []))) in
    map_incl (make_map h) m' /\ set m' k v = Some (make_map h').
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & ((t & Ht & Hi1) & Hr0) & (tv & Htv & Hi2) & Hrest).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. } }
  assert (value_of_hist (fst (Znth i h' ([], []))) = vint k) as Hk'.
  { destruct Hi1 as [-> | (? & ? & [-> | (? & ? & ->)])].
    - rewrite value_of_hist_snoc; auto.
    - rewrite app_cons_assoc, value_of_hist_snoc; auto.
    - rewrite 2app_cons_assoc, value_of_hist_snoc; auto. }
  assert (wf_hists h') as Hwf'; [|split; auto; split].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst.
      split; [|rewrite Hi2, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto].
      destruct Hi1 as [-> | (? & ? & [-> | (? & ? & ->)])]; rewrite map_app, Forall_app;
        repeat constructor; auto; try (apply ordered_snoc; auto).
      * rewrite app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; auto|].
        apply newer_snoc; auto.
      * rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
          repeat apply newer_snoc; auto.
    + destruct Hrest as ((? & ? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      destruct Hcase as [-> | (? & ? & (? & ?) & ->)]; rewrite map_app, Forall_app; repeat constructor; auto.
      * apply ordered_snoc; auto.
      * rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
          repeat apply newer_snoc; auto.
    + destruct Hrest as (_ & ->); auto.
  - intros k0 v0 j Hk0 Hj.
    exploit (Znth_inbounds j (make_map h) (0, 0)).
    { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
    intro; unfold make_map in *; rewrite <- upd_Znth_map.
    rewrite Zlength_map in *.
    rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
    destruct (eq_dec j i); [subst; rewrite upd_Znth_same; auto | rewrite upd_Znth_diff'];
      rewrite ?Zlength_map in *; auto; try omega.
    rewrite Znth_map with (d' := ([], [])) by omega.
    specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i));
      [|destruct Hrest as (_ & ->); auto].
    destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [-> | (? & ? & (? & ?) & ->)].
    + rewrite value_of_hist_snoc, Heq; auto.
    + rewrite 2app_cons_assoc, value_of_hist_snoc, Heq; auto.
  - assert (0 <= i < Zlength h') by (rewrite Hlen; auto).
    unfold set.
    assert (lookup (make_map (upd_Znth i h' (Znth i h ([], [])))) k = Some i) as ->.
    + unfold lookup, make_map.
      assert (i = ((i - hash k) mod size + hash k) mod size) as Hmod.
      { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small by omega; auto. }
      pose proof (hash_range k).
      assert (Zlength (map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs))))
              (upd_Znth i h' (Znth i h ([], [])))) = size) as Hlen1.
      { rewrite Zlength_map, upd_Znth_Zlength; auto; omega. }
      erewrite index_of'_succeeds; simpl.
      f_equal; symmetry; apply Hmod.
      { rewrite Zlength_rebase; rewrite ?Zlength_map, ?upd_Znth_Zlength; auto;
          replace (Zlength h') with size; auto; try omega.
        apply Z_mod_lt, size_pos. }
      { rewrite Forall_forall; intros x Hin.
        apply In_Znth with (d := (0, 0)) in Hin; destruct Hin as (j & Hj & Hx).
        exploit (Z_mod_lt (i - hash k) size); [apply size_pos | intro].
        rewrite Zlength_sublist in Hj; rewrite ?Zlength_rebase; rewrite ?Hlen1; try (simpl in *; omega).
        rewrite Znth_sublist, Z.add_0_r in Hx by (auto; omega).
        rewrite Znth_rebase in Hx by (simpl in *; omega).
        rewrite Hlen1, Znth_map with (d' := ([], [])) in Hx.
        subst x; simpl.
        specialize (Hrest ((j + hash k) mod size)); destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        simpl in *; destruct Hcase as [-> | (? & ? & ? & ->)]; [|rewrite 2app_cons_assoc];
          rewrite value_of_hist_snoc; simpl.
        * split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
        * split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
        * intro X; rewrite <- X, Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hj; try omega.
          destruct Hj; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos.
        * rewrite upd_Znth_Zlength by auto.
          replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos. }
      { rewrite <- Hlen1, Znth_rebase', Znth_map with (d' := ([], [])); simpl;
          rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try (simpl in *; omega).
        rewrite upd_Znth_same by auto; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth i h ([], [])))) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto; simpl.
        rewrite Int.signed_repr; auto. }
    + simpl; unfold make_map; erewrite <- upd_Znth_map, upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map;
        auto.
      rewrite Znth_map', Hk', Hi2, value_of_hist_snoc; simpl.
      rewrite !Int.signed_repr; auto.
Qed.

Lemma get_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = size)
  (Htrace : get_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ match get (make_map h') k with
  | Some v' => v' = v /\ map_incl (upd_Znth i (make_map h) (k, v)) (make_map h')
  | None => v = 0 /\ map_incl (make_map h) (make_map h') end.
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  destruct Hi as (t & r & Ht & Hi1 & Hi2 & Hr0).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. }}
  assert (wf_hists h') as Hwf'; [|split; auto].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst; rewrite Hhi in *.
      split; [rewrite Hi1, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto|].
      destruct Hi2 as [(? & ? & ->) | (? & ? & ? & ->)]; auto.
      rewrite map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto.
    + destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      rewrite map_app, Forall_app; repeat constructor; auto.
      apply ordered_snoc; auto.
    + destruct Hrest as (_ & ->); auto.
  - unfold get, lookup.
    pose proof (index_of'_spec k (rebase (make_map h') (hash k))) as Hspec.
    destruct (index_of' (rebase (make_map h') (hash k)) k) eqn: Hindex; simpl.
    unfold make_map at 1; rewrite Znth_map with (d' := ([], [])).
    pose proof (hash_range k).
    assert ((z + hash k) mod size = i) as Hz.
    { destruct Hspec as (Hz & Hcase & Hall).
      assert (Zlength (make_map h') = Zlength h') as Hlenm by (unfold make_map; rewrite Zlength_map; auto).
      assert (z <= (i - hash k) mod Zlength (make_map h')) as Hle.
      { eapply Forall_sublist_le; try apply Hall; simpl.
        { apply Z_mod_lt; omega. }
        { simpl in *; omega. }
        rewrite Znth_rebase' by (simpl in *; omega).
        unfold make_map; rewrite Znth_map'.
        rewrite Hi1, value_of_hist_snoc; simpl.
        destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; [|rewrite Int.signed_repr by auto]; tauto. }
      rewrite Zlength_rebase in Hz by omega.
      rewrite Znth_rebase, Hlenm in Hcase by omega.
      unfold make_map in Hcase; rewrite Znth_map with (d' := ([], [])) in Hcase; simpl in Hcase.
      destruct (eq_dec ((z + hash k) mod size) i); auto.
      specialize (Hrest ((z + hash k) mod size)); destruct Hrest as ((? & r1 & ? & Hfst & ? & ? & ?) & _).
      { unfold indices.
        rewrite in_map_iff.
        exists z; split; [rewrite Z.add_comm; auto|].
        rewrite In_upto, Z2Nat.id.
        rewrite Hlenm in Hle; replace (Zlength h') with size in Hle by omega.
        destruct (eq_dec z ((i - hash k) mod size)); [|omega].
        contradiction n; rewrite e, Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto; omega.
        { apply Z_mod_lt, size_pos. } }
      replace (Zlength h') with size in Hcase by omega.
      simpl in *; rewrite Hfst, value_of_hist_snoc in Hcase; simpl in Hcase.
      destruct Hcase; [absurd (r1 = Int.repr k) | absurd (r1 = Int.zero)]; auto; apply signed_inj; auto.
      rewrite Int.signed_repr; auto.
      { apply Z_mod_lt; omega. } }
    simpl in *; rewrite Hz, Hi1.
    replace (value_of_hist (hk ++ _)) with (vint r) by (rewrite value_of_hist_snoc; auto); simpl.
    destruct Hi2 as [(? & ? & Hi2) | (? & ? & ? & Hi2)]; rewrite Hi2; clear dependent z; subst; simpl.
    + split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (make_map h) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite Zlength_map; intro;
        rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite Hhi in *; simpl in *; contradiction Hk0.
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto. }
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        rewrite value_of_hist_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + rewrite value_of_hist_snoc; simpl.
      rewrite !Int.signed_repr by auto.
      if_tac; [contradiction Hk; auto|].
      split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (upd_Znth i (make_map h) (k, v)) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite upd_Znth_Zlength; rewrite Zlength_map; auto.
      intro; rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite upd_Znth_same in Hj by (rewrite Zlength_map; auto).
        inv Hj; rewrite Hi1, Hi2.
        rewrite !value_of_hist_snoc; simpl.
        rewrite !Int.signed_repr; auto. }
      rewrite upd_Znth_diff' in Hj; rewrite ?Zlength_map; auto.
      rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        rewrite value_of_hist_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos.
    + assert (In r (map fst (rebase (make_map h') (hash k)))).
      { rewrite in_map_iff.
        unfold rebase, make_map; eexists; rewrite rotate_In, in_map_iff.
        split; [|do 2 eexists; eauto; apply Znth_In with (i0 := i); omega].
        rewrite Hi1, value_of_hist_snoc; simpl.
        apply Int.signed_repr; destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; auto.
        { pose proof (hash_range k).
          rewrite Zlength_map; omega. } }
      destruct Hspec as (Hnk & Hnz), Hi2 as [(? & ? & ?) | (? & ?)]; subst;
        [contradiction Hnz | contradiction Hnk].
Qed.
