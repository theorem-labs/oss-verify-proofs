(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Realloc MSucc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ev_len_ok (LENB : Z) (e : ev) : Prop :=
  match e with
  | EMmap _ len _ flags => map_fixed_b flags = true \/ len <= LENB
  | _ => True
  end.

Fixpoint lok {R} (LENB : Z) (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis e k => ev_len_ok LENB e /\ forall z, lok LENB P (k z)
  end.

Lemma lok_vis {R} LENB (P : R -> Prop) e k :
  ev_len_ok LENB e -> (forall z, lok LENB P (k z)) -> lok LENB P (SVis e k).
Proof. intros He H. destruct e; cbn; auto. Qed.

Lemma lok_vis_inv {R} LENB (P : R -> Prop) e k :
  lok LENB P (SVis e k) -> match e with EUndef _ => True | _ => ev_len_ok LENB e /\ forall z, lok LENB P (k z) end.
Proof. intros H. destruct e; cbn in *; auto. Qed.

Lemma lok_mono {R} LENB (P P' : R -> Prop) : (forall r, P r -> P' r) -> forall t, lok LENB P t -> lok LENB P' t.
Proof.
  intros HP t. induction t as [r | e k IH]; cbn; [apply HP|].
  destruct e; auto; intros [He H]; split; auto.
Qed.

Lemma lok_bind {R S} LENB (P : R -> Prop) (Q : S -> Prop) (t : M R) (f : R -> M S) :
  lok LENB P t -> (forall r, P r -> lok LENB Q (f r)) -> lok LENB Q (sbind t f).
Proof.
  induction t as [r | e k IH]; intros Ht Hf; cbn in *.
  - apply Hf. exact Ht.
  - destruct e; cbn in *; auto; destruct Ht as [He Ht]; split; auto.
Qed.


(* [comment removed for export] *)
Fixpoint lpath {R} (t : M R) (zs : list Z) (r : R) {struct t} : Prop :=
  match t, zs with
  | SRet r0, [] => r = r0
  | SVis (EUndef _) _, _ => False
  | SVis e k, z :: zs' => lpath (k z) zs' r
  | _, _ => False
  end.

(* [comment removed for export] *)
Fixpoint levents {R} (t : M R) (zs : list Z) {struct t} : list ev :=
  match t, zs with
  | SVis e k, z :: zs' => e :: levents (k z) zs'
  | _, _ => []
  end.

Lemma lok_follows {R} LENB (P : R -> Prop) (t : M R) : forall zs r,
  lok LENB P t -> lpath t zs r -> Forall (ev_len_ok LENB) (levents t zs) /\ P r.
Proof.
  induction t as [r0 | e k IH]; intros zs r Hl Hp; cbn in *.
  - destruct zs; [subst; split; [constructor| exact Hl] | destruct Hp].
  - destruct e; destruct zs as [|z zs]; try (exact (False_ind _ Hp));
      destruct Hl as [He Hl]; destruct (IH z zs r (Hl z) Hp) as [H1 H2]; (split; [constructor; assumption| exact H2]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kc (c : mctx) : Z * Z := (c_meta_alloc_shift c, c_avail_meta_count c).
Definition shf (st : mstate) : Z := c_meta_alloc_shift (ctx st).
Definition avc (st : mstate) : Z := c_avail_meta_count (ctx st).

Lemma kc_ctx st : kc (ctx st) = (shf st, avc st). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kc_set_secret v c : kc (set_secret v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_init_done v c : kc (set_init_done v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_mmap_counter v c : kc (set_mmap_counter v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_free_meta_head v c : kc (set_free_meta_head v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_avail_meta v c : kc (set_avail_meta v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_avail_meta_area_count v c : kc (set_avail_meta_area_count v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_meta_area_head v c : kc (set_meta_area_head v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_meta_area_tail v c : kc (set_meta_area_tail v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_avail_meta_areas v c : kc (set_avail_meta_areas v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_active_map v c : kc (set_active_map v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_usage_map v c : kc (set_usage_map v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_unmap_seq_map v c : kc (set_unmap_seq_map v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_bounces_map v c : kc (set_bounces_map v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_seq v c : kc (set_seq v c) = kc c. Proof. reflexivity. Qed.
Lemma kc_set_brk v c : kc (set_brk v c) = kc c. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma kc_set_avail_meta_count v c : kc (set_avail_meta_count v c) = (c_meta_alloc_shift c, v). Proof. reflexivity. Qed.
Lemma kc_set_meta_alloc_shift v c : kc (set_meta_alloc_shift v c) = (v, c_avail_meta_count c). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ctx_upd_ctx f st : ctx (upd_ctx f st) = f (ctx st). Proof. reflexivity. Qed.
Lemma ctx_set_regions v st : ctx (set_regions v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_shadow v st : ctx (set_shadow v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_next_rid v st : ctx (set_next_rid v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_metas v st : ctx (set_metas v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_areas v st : ctx (set_areas v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_groups v st : ctx (set_groups v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_slots v st : ctx (set_slots v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_tick v st : ctx (set_tick v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_put_meta m r st : ctx (put_meta m r st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_upd_meta m f st : ctx (upd_meta m f st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_put_group g m ai st : ctx (put_group g m ai st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_set_group_active_idx g ai st : ctx (set_group_active_idx g ai st) = ctx st.
Proof. unfold set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma ctx_new_region k b l st : ctx (fst (new_region k b l st)) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_drop_region rid st : ctx (drop_region rid st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_del_group g st : ctx (del_group g st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_upd_region rid f st : ctx (upd_region rid f st) = ctx st.
Proof. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.
Lemma ctx_upd_shadow rid f st : ctx (upd_shadow rid f st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_wr8 p v st : ctx (wr8 p v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_wr16 p v st : ctx (wr16 p v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_wr32 p v st : ctx (wr32 p v st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_havoc p n st : ctx (havoc p n st) = ctx st.
Proof. unfold havoc. destruct (n <=? 0); [reflexivity|]. apply ctx_upd_shadow. Qed.
Lemma ctx_add_slots m p stride cnt st : ctx (add_slots m p stride cnt st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_zero_hdrs p size : forall cnt i st, ctx (zero_hdrs p size i cnt st) = ctx st.
Proof. induction cnt as [|c IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ctx_set_size p e n b3 st : ctx (set_size p e n b3 st) = ctx st.
Proof.
  unfold set_size. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma ctx_enframe_at st g idx n off : ctx (fst (enframe_at st g idx n off)) = ctx st.
Proof.
  unfold enframe_at. cbv zeta. destruct (negb (off =? 0)); cbn [fst]; rewrite ctx_set_size; reflexivity.
Qed.
Lemma ctx_nest_layout st g idx j size cnt : ctx (nest_layout st g idx j size cnt) = ctx st.
Proof.
  unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
  rewrite ctx_zero_hdrs, ctx_wr8. pose proof (ctx_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H.
Qed.
Lemma ctx_hdr_havoc b st : ctx (hdr_havoc b st) = ctx st. Proof. reflexivity. Qed.
Lemma ctx_strip st : ctx (strip st) = ctx st. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kc_set_active sc v st : kc (ctx (set_active sc v st)) = kc (ctx st). Proof. reflexivity. Qed.
Lemma kc_set_usage sc v st : kc (ctx (set_usage sc v st)) = kc (ctx st). Proof. reflexivity. Qed.
Lemma kc_set_bounce i v st : kc (ctx (set_bounce i v st)) = kc (ctx st). Proof. reflexivity. Qed.
Lemma kc_step_seq st : kc (ctx (step_seq st)) = kc (ctx st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma kc_record_seq sc st : kc (ctx (record_seq sc st)) = kc (ctx st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma kc_account_bounce sc st : kc (ctx (account_bounce sc st)) = kc (ctx st).
Proof.
  unfold account_bounce.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma kc_decay_bounces sc st : kc (ctx (decay_bounces sc st)) = kc (ctx st).
Proof. unfold decay_bounces. match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity. Qed.
Lemma kc_set_head h v st : kc (ctx (set_head h v st)) = kc (ctx st).
Proof. unfold set_head. destruct h; reflexivity. Qed.
Lemma kc_dequeue h m st : kc (ctx (dequeue h m st)) = kc (ctx st).
Proof.
  unfold dequeue. cbv zeta. rewrite ctx_upd_meta.
  destruct (negb _); [| apply kc_set_head].
  set (st1 := match m_prev _ with Some pv => _ | None => st end).
  set (st2 := match m_next _ with Some nx => _ | None => st1 end).
  assert (E1 : ctx st1 = ctx st) by (subst st1; destruct (m_prev _); reflexivity).
  assert (E2 : ctx st2 = ctx st) by (subst st2; destruct (m_next _); rewrite ?ctx_upd_meta; exact E1).
  destruct (optr_eqb _ _); [rewrite kc_set_head|]; rewrite E2; reflexivity.
Qed.

Hint Rewrite kc_set_secret kc_set_init_done kc_set_mmap_counter kc_set_free_meta_head kc_set_avail_meta
  kc_set_avail_meta_area_count kc_set_meta_area_head kc_set_meta_area_tail kc_set_avail_meta_areas kc_set_active_map
  kc_set_usage_map kc_set_unmap_seq_map kc_set_bounces_map kc_set_seq kc_set_brk
  kc_set_avail_meta_count kc_set_meta_alloc_shift
  ctx_upd_ctx ctx_set_regions ctx_set_shadow ctx_set_next_rid ctx_set_metas ctx_set_areas ctx_set_groups ctx_set_slots
  ctx_set_tick ctx_put_meta ctx_upd_meta ctx_put_group ctx_set_group_active_idx ctx_new_region ctx_drop_region ctx_del_group
  ctx_upd_region ctx_upd_shadow ctx_wr8 ctx_wr16 ctx_wr32 ctx_havoc ctx_add_slots ctx_zero_hdrs ctx_set_size ctx_enframe_at ctx_nest_layout ctx_hdr_havoc ctx_strip
  kc_set_active kc_set_usage kc_set_bounce kc_step_seq kc_record_seq kc_account_bounce kc_decay_bounces kc_set_head kc_dequeue
  : mlkey.

Ltac kcx := autorewrite with mlkey; try reflexivity.
(* [comment removed for export] *)
Ltac new_region_ctx EN C :=
  pose proof (f_equal (fun x => ctx (fst x)) EN) as C; cbn [fst] in C; rewrite ctx_new_region in C.
Lemma shf_kc st : shf st = fst (kc (ctx st)). Proof. reflexivity. Qed.
Lemma avc_kc st : avc st = snd (kc (ctx st)). Proof. reflexivity. Qed.
(* [comment removed for export] *)
Ltac shx := rewrite ?shf_kc, ?avc_kc; autorewrite with mlkey; cbn [fst snd]; rewrite <- ?shf_kc, <- ?avc_kc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_class_range i : 0 <= size_class i <= 8191.
Proof.
  unfold size_class. generalize (Z.to_nat i) as n. intros n.
  do 48 (destruct n as [|n]; [cbn; lia|]). cbn. destruct n; cbn; lia.
Qed.

Lemma small_cnt_range sc i : 0 <= small_cnt sc i <= 31.
Proof.
  unfold small_cnt. generalize (Z.to_nat i) as a. generalize (Z.to_nat sc) as b. intros b a.
  do 9 (destruct b as [|b]; [cbn; do 3 (destruct a as [|a]; [cbn; lia|]); destruct a; cbn; lia|]).
  destruct b; destruct a; cbn; lia.
Qed.

Lemma med_cnt_range i : 0 <= med_cnt i <= 32.
Proof.
  unfold med_cnt. generalize (Z.to_nat i) as a. intros a.
  do 4 (destruct a as [|a]; [cbn; lia|]). cbn. destruct a; cbn; lia.
Qed.

Lemma small_cnt_pick_range sc u : 0 <= small_cnt_pick sc u <= 31.
Proof.
  unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma halve_even_range f : forall c u, 0 <= c -> 0 <= halve_even f c u <= c.
Proof.
  induction f as [|f IH]; intros c u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even c && (u <? 4 * c)); [| lia].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  specialize (IH (c / 2) u ltac:(lia)). lia.
Qed.

Lemma halve_big_range f : forall c sz, 0 <= c -> 0 <= halve_big f c sz <= c.
Proof.
  induction f as [|f IH]; intros c sz Hc; cbn [halve_big]; [lia|].
  destruct (65536 * UNIT <=? sz * c); [| lia].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  assert (0 <= c / 2 <= c) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  specialize (IH (c / 2) sz ltac:(lia)). lia.
Qed.

Lemma land_4095' x : Z.land x 4095 = x mod 4096.
Proof. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_le x : x <= round_up_pg x <= x + 4095.
Proof.
  unfold round_up_pg. change (PGSZ - 1) with 4095. rewrite land_4095'.
  pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma pair_fst_eq {A B} (a a' : A) (b b' : B) : (a, b) = (a', b') -> a' = a.
Proof. intros E. exact (eq_sym (f_equal fst E)). Qed.
Lemma triple_fst_eq {A B C} (a a' : A) (b b' : B) (c c' : C) : (a, b, c) = (a', b', c') -> a' = a.
Proof. intros E. exact (eq_sym (f_equal (fun t => fst (fst t)) E)). Qed.
Lemma some_pair_fst_eq {A B} (a a' : A) (b b' : B) : Some (a, b) = Some (a', b') -> a' = a.
Proof. intros E. exact (eq_sym (f_equal (fun o => match o with Some q => fst q | None => a end) E)). Qed.

Unset Implicit Arguments.

Section LOK.
Variable R : Type.
Variable LENB : Z.
Variable P : R -> Prop.
(* [comment removed for export] *)
Variable j : Z.
Hypothesis Hj : 0 <= j.
(* [comment removed for export] *)
Definition GLEN : Z := 2^23.
Definition RMAX : Z := 2^23 - 2^13.
Hypothesis HG : GLEN <= LENB.
Hypothesis HM : Z.shiftl 2 j * PGSZ <= LENB.

Local Notation LOK := (lok LENB P) (only parsing).

(* [comment removed for export] *)
Definition TH (f : Z) (st : mstate) : Prop :=
  shf st <= j \/ (shf st <= j + 1 /\ f <= avc st).

Lemma TH_mono f f' st : f' <= f -> TH f st -> TH f' st.
Proof. unfold TH. intros Hf [H|[H1 H2]]; [left; exact H| right; split; [exact H1| lia]]. Qed.

Lemma TH_key f st st' : kc (ctx st') = kc (ctx st) -> TH f st -> TH f st'.
Proof. unfold TH, shf, avc, kc. intros E. injection E as E1 E2. rewrite E1, E2. exact (fun H => H). Qed.

Lemma lok_guard tag c (k bail : M R) : LOK k -> LOK (guard tag c k bail).
Proof. intros Hk. unfold guard. destruct c; [exact Hk | exact I]. Qed.

Lemma lok_bad_answer (bail : M R) : LOK (bad_answer bail).
Proof. exact I. Qed.

(* [comment removed for export] *)
Local Notation SAMEK st := (fun st' => kc (ctx st') = kc (ctx st)).

Lemma lok_queue h m st (k : mstate -> M R) bail :
  (forall st', kc (ctx st') = kc (ctx st) -> LOK (k st')) -> LOK (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply lok_guard. apply lok_guard.
  destruct (get_head st h) as [hd|].
  - apply Hk. kcx. destruct (m_prev _); kcx.
  - apply Hk. kcx.
Qed.

Lemma lok_free_meta m st (k : mstate -> M R) bail :
  (forall st', kc (ctx st') = kc (ctx st) -> LOK (k st')) -> LOK (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply lok_queue. intros st' E. apply Hk. rewrite E. kcx. Qed.

Lemma lok_activate_group m st (k : mstate -> Z -> M R) bail :
  (forall st' z, kc (ctx st') = kc (ctx st) -> LOK (k st' z)) -> LOK (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply lok_guard. apply Hk. kcx. Qed.

Lemma lok_try_avail sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, kc (ctx st') = kc (ctx st) -> LOK (k st' z)) -> LOK (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail, ta_fin.
  destruct (active st sc) as [m|]; [| apply Hk; reflexivity].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply Hk; kcx|].
  match goal with |- lok _ _ (match ?s with _ => _ end) => destruct s as [[st1 m1]|] eqn:E1 end.
  2:{ destruct (m_freed (get_meta_rec st m) =? 0); [apply Hk; kcx | exact I]. }
  assert (K1 : kc (ctx st1) = kc (ctx st)).
  { destruct (m_freed (get_meta_rec st m) =? 0).
    - destruct (active (dequeue (LActive sc) m st) sc); [| discriminate]. apply some_pair_fst_eq in E1. subst st1. kcx.
    - destruct (m_next (get_meta_rec st m)); [| discriminate]. apply some_pair_fst_eq in E1. subst st1. kcx. }
  match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x as [[st2 m2] mask] eqn:E2 end.
  assert (K2 : kc (ctx st2) = kc (ctx st)).
  { revert E2. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end;
      try (destruct (m_next (get_meta_rec st1 m1))); intros E2; apply triple_fst_eq in E2; subst st2; kcx; exact K1. }
  match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x as [st3 m3] eqn:E3 end.
  assert (K3 : kc (ctx st3) = kc (ctx st)).
  { revert E3. repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end;
      try (destruct (m_next (get_meta_rec st2 m2))); try (destruct (m_mem (get_meta_rec st2 m2)));
      intros E3; apply pair_fst_eq in E3; subst st3; kcx; exact K2. }
  apply lok_activate_group. intros st4 mask4 K4. apply lok_guard. apply Hk. kcx. rewrite K4. exact K3.
Qed.

(* [comment removed for export] *)

Lemma lok_am_take st (k : mstate -> optr -> M R) bail :
  (forall st' m, shf st' = shf st -> avc st' = avc st - 1 -> LOK (k st' (Some m))) -> LOK (am_take st k bail).
Proof.
  intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [| exact I].
  apply Hk; reflexivity.
Qed.

Lemma lok_am_carve st p (k : mstate -> optr -> M R) bail :
  (forall st' m, shf st' = shf st -> avc st' = NSLOTS - 1 -> LOK (k st' (Some m))) -> LOK (am_carve st p k bail).
Proof.
  intros Hk. unfold am_carve. apply lok_am_take. intros st' m E1 E2. apply Hk.
  - rewrite E1. shx. destruct (c_meta_area_tail _); reflexivity.
  - rewrite E2. shx. reflexivity.
Qed.

Lemma lok_am_finish st nu (k : mstate -> optr -> M R) bail :
  (forall st' m, shf st' = shf st -> avc st' = NSLOTS - 1 -> LOK (k st' (Some m))) ->
  (forall st', LOK (k st' None)) ->
  LOK (am_finish st nu k bail).
Proof.
  intros Hk Hn. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [| exact I].
  match goal with |- lok _ _ (if ?c then _ else _) => destruct c end; [| apply lok_am_carve; exact Hk].
  apply lok_vis; [exact I|]. intros z. destruct (negb (mprotect_answer_ok z)); [apply lok_bad_answer|].
  destruct ((z =? 0) || _); [apply lok_am_carve; exact Hk | apply Hn].
Qed.

Lemma shiftl2_le s : s <= j -> Z.shiftl 2 s <= Z.shiftl 2 j.
Proof.
  intros Hs. destruct (Z.le_gt_cases 0 s) as [S0|S0].
  - rewrite !Z.shiftl_mul_pow2 by lia. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
  - rewrite (Z.shiftl_div_pow2 2 s) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 / 2 ^ (- s) <= 2) by (apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]; pose proof (Z.pow_pos_nonneg 2 (-s)); nia).
    pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj). nia.
Qed.

Lemma lok_am_after_brk st nu (k : mstate -> optr -> M R) bail :
  shf st <= j ->
  (forall st' m, shf st' <= j + 1 -> avc st' = NSLOTS - 1 -> LOK (k st' (Some m))) ->
  (forall st', LOK (k st' None)) ->
  LOK (am_after_brk st nu k bail).
Proof.
  intros Hs Hk Hn. unfold am_after_brk.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  2:{ apply lok_am_finish; [| exact Hn]. intros st' m E1 E2. apply Hk; [rewrite E1; lia| exact E2]. }
  apply lok_vis.
  { cbn. right. pose proof (shiftl2_le _ Hs) as SL. unfold shf in *. unfold PGSZ in *. nia. }
  intros z. destruct (negb (mmap_answer_ok _ _ z)); [apply lok_bad_answer|].
  destruct (is_err z); [apply Hn|].
  destruct (new_region _ _ _ _) as [st1 rid] eqn:EN.
  apply lok_am_finish; [| exact Hn]. intros st' m E1 E2. apply Hk; [| exact E2].
  rewrite E1. shx.
  new_region_ctx EN C. unfold shf in *. rewrite <- C. lia.
Qed.

Lemma lok_alloc_meta f st (k : mstate -> optr -> M R) bail :
  TH f st -> 1 <= f <= NSLOTS ->
  (forall st' m, TH (f - 1) st' -> LOK (k st' (Some m))) ->
  (forall st', LOK (k st' None)) ->
  LOK (alloc_meta st k bail).
Proof.
  intros HT Hf Hk Hn. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (K0 : kc (ctx st0) = kc (ctx st)) by (subst st0; destruct (c_init_done (ctx st) =? 0); kcx).
  assert (HT0 : TH f st0) by (eapply TH_key; [exact K0| exact HT]).
  clearbody st0. clear K0 HT st.
  destruct (c_free_meta_head (ctx st0)).
  { apply Hk. apply (TH_mono f); [lia|]. eapply TH_key; [| exact HT0]. kcx. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx st0)) 0) as [E0|NE]; cbn [negb].
  2:{ apply lok_am_take. intros st' m E1 E2. apply Hk. unfold TH in *. rewrite E1, E2. lia. }
  assert (Hs : shf st0 <= j) by (unfold TH, avc in HT0; rewrite E0 in HT0; lia).
  assert (AB : forall st1 nu, shf st1 <= j -> LOK (am_after_brk st1 nu k bail)).
  { intros st1 nu H1. apply lok_am_after_brk; [exact H1| | exact Hn].
    intros st' m E1 E2. apply Hk. unfold TH. right. rewrite E2. unfold NSLOTS in *. lia. }
  match goal with |- lok _ _ (if ?c then _ else _) => destruct c end; [| apply AB; exact Hs].
  destruct (c_brk (ctx st0)).
  - (* [comment removed for export] *)
    apply lok_vis; [exact I|]. intros cur. destruct (negb (brk0_answer_ok cur)); [apply lok_bad_answer|].
    apply lok_vis; [exact I|]. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply lok_bad_answer|].
    destruct (negb (r =? _)); [apply AB; shx; exact Hs|].
    destruct (negb (brk_pages_ok _ _ _)); [apply lok_bad_answer|].
    apply lok_vis; [cbn; left; reflexivity|]. intros rg. destruct (negb (mmap_fixed_answer_ok _ rg)); [apply lok_bad_answer|].
    destruct (new_region _ _ _ _) as [st1 rid] eqn:EN. apply AB.
    shx. new_region_ctx EN C. unfold shf in *. rewrite <- C. exact Hs.
  - (* [comment removed for export] *) apply AB. exact Hs.
  - (* [comment removed for export] *)
    apply lok_vis; [exact I|]. intros r. destruct (negb (brk_answer_ok _ _ r)); [apply lok_bad_answer|].
    destruct (negb (r =? _)); [apply AB; shx; exact Hs|].
    destruct (negb (brk_pages_ok _ _ _)); [apply lok_bad_answer|].
    apply AB. shx. exact Hs.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lay_ok (lay : layout_hook) : Prop :=
  (forall st p, ctx (lh_hdr lay st p) = ctx st)
  /\ (forall st g idx jj size cnt, ctx (lh_nest lay st g idx jj size cnt) = ctx st).

Lemma lay_ok_none : lay_ok lay_none.
Proof. split; intros; reflexivity. Qed.

Lemma lay_ok_full : lay_ok full_lay.
Proof. split; intros; cbn [lh_hdr lh_nest full_lay]; [apply ctx_hdr_havoc | apply ctx_nest_layout]. Qed.

Lemma lok_ag_tail lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  lay_ok lay ->
  (forall st', kc (ctx st') = kc (ctx st) -> LOK (k st' (Some m))) -> LOK (ag_tail lay st sc m p cnt ai k).
Proof.
  intros [HL _] Hk. unfold ag_tail, put_group. apply Hk. kcx. rewrite HL. reflexivity.
Qed.

Lemma lok_alloc_group (d f : Z) lay (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R)
      st sc req (k : mstate -> optr -> M R) bail :
  lay_ok lay ->
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1 f1,
     TH f1 st1 -> d <= f1 <= NSLOTS -> 0 <= req1 <= RMAX ->
     (forall st' idx, 0 <= idx -> TH (f1 - d) st' -> LOK (k1 st' idx)) ->
     (forall st' idx, idx < 0 -> LOK (k1 st' idx)) ->
     LOK (rec st1 sc1 req1 k1 bail1)) ->
  TH f st -> 0 <= d -> d + 1 <= f <= NSLOTS -> 0 <= req <= RMAX ->
  (forall st' m, TH (f - 1 - d) st' -> LOK (k st' (Some m))) ->
  (forall st', LOK (k st' None)) ->
  LOK (alloc_group R lay rec st sc req k bail).
Proof.
  intros HL Hrec HT Hd Hf Hreq Hk Hn. unfold alloc_group.
  eapply lok_alloc_meta with (f := f); [exact HT| lia | | exact Hn].
  intros st1 m HT1. cbv beta iota.
  pose proof (size_class_range sc) as SZ.
  set (size := UNIT * size_class sc) in *.
  set (c1 := if sc <? 9 then small_cnt_pick sc (usage st1 sc)
             else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size) in *.
  assert (C1 : 0 <= c1 <= 32).
  { subst c1. destruct (sc <? 9); [pose proof (small_cnt_pick_range sc (usage st1 sc)); lia|].
    pose proof (med_cnt_range (Z.land sc 3)) as M.
    pose proof (@halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st1 sc) ltac:(lia)) as HE.
    pose proof (@halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size ltac:(lia)) as HB. lia. }
  clearbody c1.
  set (c2 := if (c1 =? 1) && (size * c1 + UNIT <=? PGSZ / 2) then 2 else c1) in *.
  assert (C2 : 0 <= c2 <= 32) by (subst c2; destruct (_ && _); lia). clearbody c2.
  match goal with |- lok _ _ (if ?c then _ else _) => destruct c end.
  - (* [comment removed for export] *)
    set (ns := is_bouncing sc st1) in *. clearbody ns.
    set (st1' := step_seq (account_bounce sc st1)) in *.
    set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc) in *. clearbody u1.
    match goal with |- lok _ _ (match (if negb ns && (?c <=? 7) then _ else _) with _ => _ end) => set (c3 := c) in * end.
    assert (C3 : 0 <= c3 <= 32).
    { subst c3. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
    clearbody c3.
    match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x as [cnt needed] eqn:EX end.
    assert (HN : needed <= GLEN).
    { unfold GLEN. unfold RMAX in Hreq.
      assert (A : round_up_pg (req + IB + UNIT) <= 2 ^ 23) by (pose proof (round_up_pg_le (req + IB + UNIT)); unfold IB, UNIT in *; lia).
      assert (B : round_up_pg (size * c3 + UNIT) <= 2 ^ 23).
      { pose proof (round_up_pg_le (size * c3 + UNIT)). subst size. unfold UNIT in *. nia. }
      revert EX. repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end;
        intros EX; apply (f_equal snd) in EX; cbn [snd] in EX; subst needed; assumption. }
    apply lok_vis; [cbn; right; lia|].
    intros z. destruct (negb (mmap_answer_ok _ _ z)); [apply lok_bad_answer|].
    destruct (is_err z); [apply lok_free_meta; intros; apply Hn|].
    destruct (new_region _ _ _ _) as [st2 rid] eqn:EN.
    apply lok_ag_tail; [exact HL|]. intros st' K'. apply Hk.
    apply (TH_mono (f - 1)); [lia|]. apply (TH_key _ st1); [| exact HT1].
    rewrite K'. kcx. new_region_ctx EN C. rewrite <- C. subst st1'. kcx.
  - (* [comment removed for export] *)
    apply (Hrec _ _ _ _ _ (f - 1)); [exact HT1 | lia | | |].
    + unfold RMAX. subst size. unfold UNIT, IB. nia.
    + intros st' idx Hidx HT'. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (active st' _) as [g|]; [| exact I].
      apply lok_ag_tail; [exact HL|]. intros st'' K''. apply Hk.
      apply (TH_key _ st'); [| exact HT']. rewrite K''. kcx. destruct HL as [_ HL2]. rewrite HL2. reflexivity.
    + intros st' idx Hidx. replace (idx <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      apply lok_free_meta. intros; apply Hn.
Qed.

(* [comment removed for export] *)

Lemma ctz32_nonneg' z : 0 <= ctz32 z.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma lok_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail f,
  lay_ok lay ->
  TH f st -> Z.of_nat fuel <= f <= NSLOTS -> 0 <= req <= RMAX ->
  (forall st' idx, 0 <= idx -> TH (f - Z.of_nat fuel) st' -> LOK (k st' idx)) ->
  (forall st' idx, idx < 0 -> LOK (k st' idx)) ->
  LOK (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|fu IH]; intros st sc req k bail f HL HT Hf Hreq Hk Hn; cbn [alloc_slot]; [exact I|].
  apply lok_try_avail. intros st1 first K1.
  assert (HT1 : TH f st1) by (eapply TH_key; [exact K1| exact HT]).
  destruct (negb (first =? 0)).
  { apply Hk; [apply ctz32_nonneg'|]. apply (TH_mono f); [lia| exact HT1]. }
  eapply lok_alloc_group with (d := Z.of_nat fu) (f := f); [exact HL| | exact HT1 | lia | lia | exact Hreq | |].
  - intros st2 sc2 req2 k2 bail2 f2 HT2 Hf2 Hreq2 Hk2 Hn2.
    apply (IH st2 sc2 req2 k2 bail2 f2 HL HT2 ltac:(lia) Hreq2 Hk2 Hn2).
  - intros st' g HT'. apply lok_queue. intros st'' K''. apply Hk; [lia|].
    apply (TH_key _ st'); [rewrite K''; kcx|]. apply (TH_mono (f - 1 - Z.of_nat fu)); [lia| exact HT'].
  - intros st'. apply Hn. lia.
Qed.

(* [comment removed for export] *)

Lemma lok_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail f :
  lay_ok lay ->
  TH f st -> Z.of_nat FUEL <= f <= NSLOTS -> 0 <= n <= RMAX ->
  (forall st' g idx, TH (f - Z.of_nat FUEL) st' -> LOK (k st' (Some (g, idx)))) ->
  (forall st', LOK (k st' None)) ->
  LOK (malloc_small_ctrl lay st n k bail).
Proof.
  intros HL HT Hf Hn Hk Hkn. unfold malloc_small_ctrl. cbv zeta.
  match goal with |- lok _ _ (match active st ?c with _ => _ end) => set (sc := c); clearbody sc end.
  assert (Hslot : LOK (alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail)).
  { eapply lok_alloc_slot with (f := f); [exact HL| exact HT| exact Hf| exact Hn| |].
    - intros st' idx Hidx HT'. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (active st' sc); [apply Hk; exact HT' | exact I].
    - intros st' idx Hidx. replace (idx <? 0) with true by (symmetry; apply Z.ltb_lt; lia). apply Hkn. }
  destruct (active st sc) as [gp|]; [| exact Hslot].
  match goal with |- lok _ _ (if ?b then _ else _) => destruct b end; [| exact Hslot].
  apply Hk. apply (TH_mono f); [lia|]. eapply TH_key; [| exact HT]. kcx.
Qed.

End LOK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENTRY.
Variable LENB : Z.
(* [comment removed for export] *)
Variables NUSER' j : Z.
Hypothesis Hj : 0 <= j.
Hypothesis HG : GLEN <= LENB.
Hypothesis HM : Z.shiftl 2 j * PGSZ <= LENB.
Hypothesis HD : NUSER' + IB + UNIT <= LENB.

Definition TrueP {A : Type} (_ : A) : Prop := True.

Theorem malloc_core_lok lay st n :
  lay_ok lay -> shf st <= j -> 0 <= n <= NUSER' ->
  lok LENB TrueP (malloc_core lay st n).
Proof.
  intros HL Hs Hn. unfold malloc_core.
  destruct (size_overflows n); [exact I|].
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
  - apply lok_vis; [cbn; right; lia|].
    intros z. destruct (negb (mmap_answer_ok _ _ z)); [exact I|].
    destruct (is_err z); [exact I|].
    destruct (new_region _ _ _ _) as [st1 rid] eqn:EN.
    eapply (lok_alloc_meta _ _ _ j Hj HM) with (f := 1); [| unfold NSLOTS; lia | intros; exact I | ].
    2:{ intros st'. apply lok_vis; [exact I|]. intros ru. destruct (munmap_answer_ok ru); exact I. }
    left. shx. new_region_ctx EN C. unfold shf in *. rewrite <- C. exact Hs.
  - eapply (lok_malloc_small_ctrl _ _ _ j Hj HG HM) with (f := Z.of_nat FUEL);
      [exact HL| | unfold FUEL, NSLOTS; cbn; lia | unfold RMAX, MMAP_THRESHOLD, UNIT, IB in *; lia | intros; exact I | intros; exact I].
    left. shx. exact Hs.
Qed.

Theorem cmalloc_lok cs n :
  shf cs <= j -> 0 <= n <= NUSER' -> lok LENB TrueP (cmalloc cs n).
Proof.
  intros Hs Hn. unfold cmalloc. eapply lok_bind; [apply malloc_core_lok; [apply lay_ok_none| exact Hs| exact Hn]|].
  intros [st1 r] _. exact I.
Qed.

Lemma lok_rd8 {R} (P : R -> Prop) st a (k : Z -> M R) : (forall v, lok LENB P (k v)) -> lok LENB P (rd8 st a k).
Proof.
  intros Hk. unfold rd8. destruct (cell_read _ _); [apply Hk|]. cbn. split; [exact I|]. intros z.
  destruct (peek_answer_ok z); [apply Hk | exact I].
Qed.

Lemma lok_rd16 {R} (P : R -> Prop) st a (k : Z -> M R) : (forall v, lok LENB P (k v)) -> lok LENB P (rd16 st a k).
Proof. intros Hk. unfold rd16. apply lok_rd8. intros v0. apply lok_rd8. intros v1. apply Hk. Qed.

Lemma lok_rd32 {R} (P : R -> Prop) st a (k : Z -> M R) : (forall v, lok LENB P (k v)) -> lok LENB P (rd32 st a k).
Proof. intros Hk. unfold rd32. do 4 (apply lok_rd8; intros ?). apply Hk. Qed.

Theorem malloc_lok st n :
  shf st <= j -> 0 <= n <= NUSER' -> lok LENB TrueP (malloc st n).
Proof.
  intros Hs Hn. unfold malloc. eapply lok_bind.
  { apply malloc_core_lok; [apply lay_ok_full| shx; exact Hs| exact Hn]. }
  intros [st1 [[g idx]|]] _; [| exact I].
  unfold enframe_full, enframe_read_off. apply lok_rd8. intros b3.
  destruct (negb (b3 =? 0)).
  - apply lok_rd16. intros o16. destruct (enframe_at _ _ _ _ _). exact I.
  - destruct (enframe_at _ _ _ _ _). exact I.
Qed.

(* [comment removed for export] *)
Fixpoint xlok {R} (P : R -> Prop) (t : MX R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (XE (EUndef _)) _ => True
  | SVis (XE e) k => ev_len_ok LENB e /\ forall z, xlok P (k z)
  | SVis (XMremap _ _ _ _) k => forall z, xlok P (k z)
  end.

Lemma xlok_xlift {R} (P : R -> Prop) (t : M R) : lok LENB P t -> xlok P (xlift t).
Proof.
  induction t as [r | e k IH]; cbn; intros H; [exact H|].
  destruct e; cbn in *; try (destruct H as [He H]; split; [exact He|]); auto.
Qed.

Lemma xlok_bind {R S} (P : R -> Prop) (Q : S -> Prop) (t : MX R) (f : R -> MX S) :
  xlok P t -> (forall r, P r -> xlok Q (f r)) -> xlok Q (sbind t f).
Proof.
  induction t as [r | e k IH]; intros Ht Hf; cbn in *.
  - apply Hf. exact Ht.
  - destruct e as [e|a ol nl fl]; [destruct e|]; cbn in *; auto; destruct Ht as [He Ht]; split; auto.
Qed.

(* [comment removed for export] *)
Lemma xlok_xprun {O R} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O) (P : R -> Prop) :
  forall (t : MX R) o, xlok P t -> xlok (fun x => P (snd x)) (xprun pans pupd o t).
Proof.
  induction t as [r | e k IH]; intros o H; cbn in *; [exact H|].
  unfold xprun. cbn [eruns].
  destruct e as [e|a ol nl fl]; cbn [xpsel].
  - destruct e; cbn in H |- *; try (destruct H as [He H]; split; [exact He|]; intros z; apply IH; auto).
    + (* [comment removed for export] *) apply IH. apply H.
    + exact I.
  - intros z. apply IH. apply H.
Qed.

Lemma lok_get_meta {R} (P : R -> Prop) st p (k : aptr -> Z -> Z -> M R) bail :
  (forall m off idx, lok LENB P (k m off idx)) -> lok LENB P (get_meta st p k bail).
Proof.
  intros Hk. unfold get_meta.
  repeat first
    [ exact I
    | apply Hk
    | apply lok_guard
    | apply lok_rd8; intros ?
    | apply lok_rd16; intros ?
    | apply lok_rd32; intros ?
    | match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x end
    | progress (cbv zeta beta) ].
Qed.

Lemma lok_get_nominal_size {R} (P : R -> Prop) st p e (k : Z -> M R) bail :
  (forall sz, lok LENB P (k sz)) -> lok LENB P (get_nominal_size st p e k bail).
Proof.
  intros Hk. unfold get_nominal_size.
  repeat first
    [ exact I
    | apply Hk
    | apply lok_guard
    | apply lok_rd8; intros ?
    | apply lok_rd16; intros ?
    | apply lok_rd32; intros ?
    | match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x end
    | progress (cbv zeta beta) ].
Qed.

Lemma realloc_hdr_lok st p : lok LENB TrueP (realloc_hdr st p).
Proof.
  unfold realloc_hdr. apply lok_get_meta. intros m off idx.
  destruct (slot_start _ _); [| exact I].
  apply lok_get_nominal_size. intros sz. exact I.
Qed.

(* [comment removed for export] *)

Ltac lok_crush Hk :=
  repeat first
    [ exact I
    | apply Hk
    | apply lok_guard
    | apply lok_rd8; intros ?
    | apply lok_rd16; intros ?
    | apply lok_rd32; intros ?
    | match goal with |- lok _ _ (SVis _ _) => apply lok_vis; [exact I | intros ?] end
    | match goal with |- lok _ _ (match ?x with _ => _ end) => destruct x end
    | progress (cbv zeta beta) ].

Lemma lok_queue' {R} (P : R -> Prop) h m st (k : mstate -> M R) bail :
  (forall st', lok LENB P (k st')) -> lok LENB P (queue h m st k bail).
Proof. intros Hk. unfold queue. lok_crush Hk. Qed.

Lemma lok_free_group {R} (P : R -> Prop) dec ntf st g (k : mstate -> mapinfo -> M R) bail :
  (forall st1 p (k1 : aptr -> Z -> M R) bail1, (forall m idx, lok LENB P (k1 m idx)) -> lok LENB P (dec st1 p k1 bail1)) ->
  (forall st1 g1 i (k1 : mstate -> mapinfo -> M R) bail1, (forall st' mi, lok LENB P (k1 st' mi)) -> lok LENB P (ntf st1 g1 i k1 bail1)) ->
  (forall st' mi, lok LENB P (k st' mi)) ->
  lok LENB P (free_group R dec ntf st g k bail).
Proof.
  intros Hdec Hntf Hk. unfold free_group. cbv zeta.
  destruct (m_mem _) as [pp|]; [| exact I].
  destruct (negb _).
  - unfold free_meta. apply lok_queue'. intros st'. apply Hk.
  - apply Hdec. intros m idx. apply Hntf. intros st' mi. unfold free_meta. apply lok_queue'. intros st''. apply Hk.
Qed.

Lemma lok_dec_hdr {R} (P : R -> Prop) st1 p (k1 : aptr -> Z -> M R) bail1 :
  (forall m idx, lok LENB P (k1 m idx)) -> lok LENB P (dec_hdr st1 p k1 bail1).
Proof. intros Hk. unfold dec_hdr. apply lok_get_meta. intros; apply Hk. Qed.

Lemma lok_dec_slots {R} (P : R -> Prop) st1 p (k1 : aptr -> Z -> M R) bail1 :
  (forall m idx, lok LENB P (k1 m idx)) -> lok LENB P (dec_slots st1 p k1 bail1).
Proof. intros Hk. unfold dec_slots. destruct (_ !! p) as [[m idx]|]; [apply Hk| exact I]. Qed.

Lemma lok_nontrivial_free {R} (P : R -> Prop) dec fuel :
  (forall st1 p (k1 : aptr -> Z -> M R) bail1, (forall m idx, lok LENB P (k1 m idx)) -> lok LENB P (dec st1 p k1 bail1)) ->
  forall st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st' mi, lok LENB P (k st' mi)) -> lok LENB P (nontrivial_free dec fuel st g i k bail).
Proof.
  intros Hdec. induction fuel as [|fu IH]; intros st g i k bail Hk; cbn [nontrivial_free]; [exact I|].
  cbv zeta.
  match goal with |- lok _ _ (if ?c then _ else _) => destruct c end.
  - destruct (m_next _).
    + apply lok_guard. destruct (optr_eqb _ _); [destruct (active _ _)|];
        try (apply lok_free_group; [exact Hdec| intros; apply IH; assumption| exact Hk]).
      unfold activate_group. apply lok_guard. apply lok_free_group; [exact Hdec| intros; apply IH; assumption| exact Hk].
    + apply lok_free_group; [exact Hdec| intros; apply IH; assumption| exact Hk].
  - destruct (_ =? 0); [| apply Hk].
    apply lok_guard. destruct (negb _); [apply lok_queue'; intros; apply Hk| apply Hk].
Qed.

Lemma lok_free_tail dec st g idx :
  (forall st1 p (k1 : aptr -> Z -> M mstate) bail1, (forall m i, lok LENB TrueP (k1 m i)) -> lok LENB TrueP (dec st1 p k1 bail1)) ->
  lok LENB TrueP (free_tail dec st g idx).
Proof.
  intros Hdec. unfold free_tail. cbv zeta. apply lok_guard.
  destruct (negb _); [exact I|].
  apply (lok_nontrivial_free _ _ _ Hdec). intros st' [[base len]|]; [| exact I].
  destruct (negb _); [| exact I]. apply lok_vis; [exact I|]. intros ru. destruct (munmap_answer_ok ru); exact I.
Qed.

Lemma free_lok st p : lok LENB TrueP (free st p).
Proof.
  unfold free. destruct p as [p|]; [| exact I].
  eapply lok_bind with (P := TrueP).
  - unfold free_hdr. apply lok_get_meta. intros m off idx. destruct (slot_start _ _); [| exact I].
    apply lok_get_nominal_size. intros; exact I.
  - intros [[[st1 g] idx]|] _; [| exact I]. apply lok_free_tail. intros; apply lok_dec_hdr; assumption.
Qed.

Lemma cfree_lok cs p : lok LENB TrueP (cfree cs p).
Proof.
  unfold cfree. destruct p as [p|]; [| exact I].
  destruct (_ !! p) as [[m idx]|]; [| exact I].
  eapply lok_bind with (P := TrueP); [| intros; exact I].
  apply lok_free_tail. intros; apply lok_dec_slots; assumption.
Qed.

(* [comment removed for export] *)

Lemma realloc_move_xlok st p n :
  shf st <= j -> 0 <= n <= NUSER' -> xlok TrueP (realloc_move st p n).
Proof.
  intros Hs Hn. unfold realloc_move.
  eapply xlok_bind; [apply xlok_xlift; apply malloc_lok; [exact Hs| exact Hn]|].
  intros [st1 [q|]] _; [| exact I].
  eapply xlok_bind; [apply xlok_xlift; apply free_lok|]. intros; exact I.
Qed.

Theorem realloc_xlok st p n :
  shf st <= j -> 0 <= n <= NUSER' -> xlok TrueP (realloc st p n).
Proof.
  intros Hs Hn. unfold realloc. destruct p as [p|]; [| apply xlok_xlift; apply malloc_lok; [exact Hs| exact Hn]].
  destruct (size_overflows n); [exact I|].
  eapply xlok_bind; [apply xlok_xlift; apply realloc_hdr_lok|].
  intros [[[g idx] osz]|] _; [| exact I]. cbv beta zeta.
  assert (Hs' : shf (set_tick (N.succ (s_tick st)) st) <= j) by (shx; exact Hs).
  match goal with |- xlok _ (if ?c then _ else _) => destruct c end; [exact I|].
  match goal with |- xlok _ (if ?c then _ else _) => destruct c end; [| apply realloc_move_xlok; [exact Hs'| exact Hn]].
  unfold xguard. match goal with |- xlok _ (if ?c then _ else _) => destruct c end; [| exact I].
  match goal with |- xlok _ (if ?c then _ else _) => destruct c end; [exact I|].
  match goal with |- xlok _ (if ?c then _ else _) => destruct c end; [apply realloc_move_xlok; [exact Hs'| exact Hn]|].
  cbn. intros r. destruct (negb (mremap_answer_ok _ _ _ _ r)); [exact I|].
  destruct (is_err r); [apply realloc_move_xlok; [exact Hs'| exact Hn] | exact I].
Qed.


End ENTRY.

End RC__.
