(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition KTOP : nat := 16.
Definition CM : Z := 64.
Definition CMAX : Z := CM * Z.of_nat KTOP.
Definition NMAX : Z := 2^27.
Definition LMAX : Z := 2^28.
Definition LMETA : Z := 8 * PGSZ.
Definition GB : Z := 2^22 + PGSZ.
Definition AMB : Z := 11 * PGSZ.
Definition BB : Z := 2^29.
Definition BM : Z := 200.
Definition BP : Z := 128.

Definition Vs (s : Z) : Z := NSLOTS * (2^(s+1) - s - 2).

Definition cview (st : mstate) : Z * Z * Z :=
  (c_avail_meta_count (s_ctx st), c_avail_meta_area_count (s_ctx st), c_meta_alloc_shift (s_ctx st)).

Definition VIv (c : Z) (v : Z * Z * Z) : Prop :=
  let '(a, A, s) := v in 0 <= a /\ 0 <= A /\ 0 <= s /\ Vs s <= a + NSLOTS * A + c.
Definition VI (c : Z) (st : mstate) : Prop := VIv c (cview st).

Lemma VI_view c st st' : cview st' = cview st -> VI c st -> VI c st'.
Proof. unfold VI. intros ->. tauto. Qed.

Lemma VI_mono c c' st : c <= c' -> VI c st -> VI c' st.
Proof. unfold VI, VIv. destruct (cview st) as [[a A] s]. intros; lia. Qed.

Lemma cview_upd_meta m f st : cview (upd_meta m f st) = cview st. Proof. reflexivity. Qed.
Lemma cview_put_meta m r st : cview (put_meta m r st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_usage sc v st : cview (set_usage sc v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_active sc v st : cview (set_active sc v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_bounce i v st : cview (set_bounce i v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_put_group g m ai st : cview (put_group g m ai st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_group_active_idx g ai st : cview (set_group_active_idx g ai st) = cview st.
Proof. unfold set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma cview_set_areas v st : cview (set_areas v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_regions v st : cview (set_regions v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_slots v st : cview (set_slots v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_groups v st : cview (set_groups v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_set_next_rid v st : cview (set_next_rid v st) = cview st. Proof. reflexivity. Qed.
Lemma cview_step_seq st : cview (step_seq st) = cview st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma cview_record_seq sc st : cview (record_seq sc st) = cview st.
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma cview_account_bounce sc st : cview (account_bounce sc st) = cview st.
Proof. unfold account_bounce. repeat (destruct (_ : bool); try reflexivity). Qed.
Lemma cview_decay_bounces sc st : cview (decay_bounces sc st) = cview st.
Proof. unfold decay_bounces. destruct (_ && _); reflexivity. Qed.
Lemma cview_set_head h v st : cview (set_head h v st) = cview st.
Proof. destruct h; reflexivity. Qed.
Lemma cview_dequeue h m st : cview (dequeue h m st) = cview st.
Proof.
  unfold dequeue. rewrite cview_upd_meta.
  destruct (negb _); [| apply cview_set_head].
  match goal with |- cview (if ?c then _ else _) = _ => destruct c end.
  - rewrite cview_set_head. destruct (m_next _); [rewrite cview_upd_meta|]; (destruct (m_prev _); [rewrite cview_upd_meta|]); reflexivity.
  - destruct (m_next _); [rewrite cview_upd_meta|]; (destruct (m_prev _); [rewrite cview_upd_meta|]); reflexivity.
Qed.
Lemma cview_strip st : cview (strip st) = cview st. Proof. reflexivity. Qed.
Lemma cview_new_region kd b l st : cview (fst (new_region kd b l st)) = cview st.
Proof. reflexivity. Qed.
Lemma cview_drop_region rid st : cview (drop_region rid st) = cview st. Proof. reflexivity. Qed.
Lemma cview_upd_region rid f st : cview (upd_region rid f st) = cview st.
Proof. unfold upd_region. destruct (get_region st rid); reflexivity. Qed.
Lemma cview_add_slots m p stride cnt st : cview (add_slots m p stride cnt st) = cview st.
Proof. reflexivity. Qed.
Lemma cview_del_slots p stride cnt st : cview (del_slots p stride cnt st) = cview st.
Proof. reflexivity. Qed.
Lemma cview_del_group p st : cview (del_group p st) = cview st. Proof. reflexivity. Qed.
Lemma cview_bump_counter st : cview (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) = cview st.
Proof. reflexivity. Qed.

Definition ecost (e : ev) : Z * Z * Z :=
  match e with
  | EBrk req => if req =? 0 then (0, 0, 0) else (2 * PGSZ, 1, 2)
  | EMmap _ len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then (Z.max 0 (round_up_pg len), 1, 0) else (0, 0, 0)
  | EMprotect _ _ _ => (PGSZ, 0, 0)
  | _ => (0, 0, 0)
  end.

Definition elen_ok (e : ev) : Prop :=
  match e with
  | EMmap _ len prot flags =>
      (Z.land flags MAP_FIXED =? 0) = true -> 0 < len <= LMAX /\ (prot = PROT_NONE -> len <= LMETA)
  | _ => True
  end.

Fixpoint BT {R} (wb wm wp : Z) (t : M R) (Q : R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Q r
  | SVis (EUndef _) _ => True
  | SVis (EPeek _ _ _) _ => True
  | SVis e k =>
      let '(cb, cm, cp) := ecost e in
      cb <= wb /\ cm <= wm /\ cp <= wp /\ elen_ok e /\ forall z, BT (wb - cb) (wm - cm) (wp - cp) (k z) Q
  end.

Lemma ecost_nonneg e : let '(cb, cm, cp) := ecost e in 0 <= cb /\ 0 <= cm /\ 0 <= cp.
Proof.
  destruct e; cbn [ecost]; try lia.
  - destruct (addr =? 0); unfold PGSZ; lia.
  - destruct (Z.land flags MAP_FIXED =? 0); lia.
  - unfold PGSZ; lia.
Qed.

Lemma BT_mono {R} (Q Q' : R -> Prop) : (forall r, Q r -> Q' r) ->
  forall t wb wm wp wb' wm' wp', wb <= wb' -> wm <= wm' -> wp <= wp' -> BT wb wm wp t Q -> BT wb' wm' wp' t Q'.
Proof.
  intros HQ. fix IH 1. intros [r|e k] wb wm wp wb' wm' wp' Hb Hm Hp H; cbn in *; [auto|].
  destruct e; try exact I;
    match goal with |- (let '(_, _) := ?c in _) => destruct c as [[cb cm] cp] end;
    destruct H as (H1 & H2 & H3 & H4 & H5); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [exact H4|]);
    intros z; apply (IH _ (wb - cb) (wm - cm) (wp - cp)); try lia; apply H5.
Qed.

Lemma BT_weaken {R} (Q : R -> Prop) t wb wm wp wb' wm' wp' :
  wb <= wb' -> wm <= wm' -> wp <= wp' -> BT wb wm wp t Q -> BT wb' wm' wp' t Q.
Proof. intros. eapply BT_mono; eauto. Qed.

Lemma BT_post {R} (Q Q' : R -> Prop) t wb wm wp : (forall r, Q r -> Q' r) -> BT wb wm wp t Q -> BT wb wm wp t Q'.
Proof. intros. eapply BT_mono; eauto; lia. Qed.

Lemma BT_ret {R} (Q : R -> Prop) r wb wm wp : Q r -> BT wb wm wp (ret r) Q.
Proof. intros H. exact H. Qed.

Lemma BT_undef {R} (Q : R -> Prop) u k wb wm wp : BT wb wm wp (SVis (EUndef u) k : M R) Q.
Proof. exact I. Qed.

Lemma BT_bad_answer {R} (Q : R -> Prop) (b : M R) wb wm wp : BT wb wm wp (bad_answer b) Q.
Proof. exact I. Qed.

Lemma BT_guard {R} (Q : R -> Prop) tag c (k bail : M R) wb wm wp :
  BT wb wm wp k Q -> BT wb wm wp (guard tag c k bail) Q.
Proof. intros H. unfold guard. destruct c; [exact H| exact I]. Qed.

Lemma BT_bind {R S} (Q1 : R -> Prop) (Q : S -> Prop) (f : R -> M S) :
  forall t wb wm wp,
  BT wb wm wp t Q1 ->
  (forall r wb' wm' wp', Q1 r -> 0 <= wb' <= wb -> 0 <= wm' <= wm -> 0 <= wp' <= wp -> BT wb' wm' wp' (f r) Q) ->
  0 <= wb -> 0 <= wm -> 0 <= wp ->
  BT wb wm wp (sbind t f) Q.
Proof.
  fix IH 1. intros [r|e k] wb wm wp H Hf Hb Hm Hp; cbn in *.
  - apply Hf; auto; lia.
  - generalize (ecost_nonneg e). revert H.
    assert (GO : forall cb cm cp,
      (cb <= wb /\ cm <= wm /\ cp <= wp /\ elen_ok e /\ forall z, BT (wb - cb) (wm - cm) (wp - cp) (k z) Q1) ->
      (0 <= cb /\ 0 <= cm /\ 0 <= cp) ->
      cb <= wb /\ cm <= wm /\ cp <= wp /\ elen_ok e /\ forall z, BT (wb - cb) (wm - cm) (wp - cp) (sbind (k z) f) Q).
    { intros cb cm cp (H1 & H2 & H3 & H4 & H5) NN. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H4|].
      intros z; apply (IH _ (wb - cb) (wm - cm) (wp - cp)); try lia; [apply H5|].
      intros r wb' wm' wp' HQ B1 B2 B3; apply Hf; auto; lia. }
    destruct e; try (intros; exact I); cbn [ecost];
      try match goal with |- context [let '(_, _) := ?c in _] => destruct c as [[cb cm] cp] end; apply GO.
Qed.

Hint Rewrite cview_upd_meta cview_put_meta cview_set_usage cview_set_active cview_set_bounce cview_put_group
  cview_set_group_active_idx cview_set_areas cview_set_regions cview_set_slots cview_set_groups cview_set_next_rid
  cview_step_seq cview_record_seq cview_account_bounce cview_decay_bounces cview_set_head cview_dequeue cview_strip
  cview_new_region cview_drop_region cview_upd_region cview_add_slots cview_del_slots cview_del_group cview_bump_counter : cview.

Section CPS.
Context {R : Type} (Q : R -> Prop).

#[using="Type"] Lemma BT_queue h m st (k : mstate -> M R) bail wb wm wp :
  (forall st', cview st' = cview st -> BT wb wm wp (k st') Q) -> BT wb wm wp (queue h m st k bail) Q.
Proof.
  intros Hk. unfold queue. apply BT_guard. apply BT_guard.
  destruct (get_head st h) as [hd|].
  - apply Hk. destruct (m_prev _); reflexivity.
  - apply Hk. rewrite cview_set_head. reflexivity.
Qed.

#[using="Type"] Lemma BT_free_meta m st (k : mstate -> M R) bail wb wm wp :
  (forall st', cview st' = cview st -> BT wb wm wp (k st') Q) -> BT wb wm wp (free_meta m st k bail) Q.
Proof. intros Hk. unfold free_meta. apply BT_queue. intros st' E. apply Hk. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma BT_activate_group m st (k : mstate -> Z -> M R) bail wb wm wp :
  (forall st' x, cview st' = cview st -> BT wb wm wp (k st' x) Q) -> BT wb wm wp (activate_group m st k bail) Q.
Proof. intros Hk. unfold activate_group. apply BT_guard. apply Hk. reflexivity. Qed.

#[using="Type"] Lemma BT_try_avail sc st (k : mstate -> Z -> M R) bail wb wm wp :
  (forall st' x, cview st' = cview st -> BT wb wm wp (k st' x) Q) -> BT wb wm wp (try_avail sc st k bail) Q.
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk; reflexivity].
  cbv zeta. destruct (negb (m_avail _ =? 0)). { unfold ta_fin. apply Hk. reflexivity. }
  match goal with |- BT _ _ _ (match ?s1 with Some _ => _ | None => _ end) _ =>
    assert (H1 : forall st1 m1, s1 = Some (st1, m1) -> cview st1 = cview st);
    [| destruct s1 as [[st1 m1]|] eqn:E1; clear E1 ] end.
  { destruct (m_freed _ =? 0); [destruct (active _ sc)|destruct (m_next _)]; intros st1 m1 E; inversion E; subst;
      rewrite ?cview_dequeue, ?cview_set_active; reflexivity. }
  2:{ destruct (m_freed _ =? 0); [apply Hk; apply cview_dequeue| apply BT_undef]. }
  specialize (H1 st1 m1 eq_refl).
  destruct (_ && negb _); [destruct (m_next (get_meta_rec st1 m1))|]; cbv beta iota;
  (destruct (Z.land _ _ =? 0); [destruct (negb (optr_eqb _ _)); [destruct (m_next _)|destruct (m_mem _)]|]); cbv beta iota;
  apply BT_activate_group; intros st4 x E4; apply BT_guard; unfold ta_fin; apply Hk;
  rewrite cview_upd_meta, cview_decay_bounces, E4; autorewrite with cview; exact H1.
Qed.
End CPS.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma round_up_pg_ge x : x <= round_up_pg x.
Proof. rewrite round_up_pg_eq. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)). lia. Qed.
Lemma round_up_pg_le x : round_up_pg x <= x + 4095.
Proof. rewrite round_up_pg_eq. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)). lia. Qed.
Lemma round_up_pg_mod x : round_up_pg x mod PGSZ = 0.
Proof.
  rewrite round_up_pg_eq. unfold PGSZ. rewrite Zplus_mod_idemp_r. replace (x + - x) with 0 by lia. reflexivity.
Qed.
Lemma round_up_pg_id x : x mod PGSZ = 0 -> round_up_pg x = x.
Proof.
  intros H. rewrite round_up_pg_eq. unfold PGSZ in H. rewrite (Z.mod_opp_l_z x 4096) by lia. lia.
Qed.
Lemma round_up_pg_idem x : round_up_pg (round_up_pg x) = round_up_pg x.
Proof. apply round_up_pg_id, round_up_pg_mod. Qed.
Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof.
  intros H. destruct (Z.le_gt_cases (round_up_pg x) (round_up_pg y)) as [|C]; [assumption|]. exfalso.
  pose proof (round_up_pg_ge y). pose proof (round_up_pg_le x).
  pose proof (round_up_pg_mod x) as Mx. pose proof (round_up_pg_mod y) as My. unfold PGSZ in *.
  assert (E : round_up_pg x = 4096 * (round_up_pg x / 4096)) by (pose proof (Z.div_mod (round_up_pg x) 4096); lia).
  assert (E' : round_up_pg y = 4096 * (round_up_pg y / 4096)) by (pose proof (Z.div_mod (round_up_pg y) 4096); lia).
  nia.
Qed.
Lemma size_class_any i : 0 <= size_class i <= 8191.
Proof.
  unfold size_class. destruct (nth_in_or_default (Z.to_nat i) size_classes 0) as [H| ->]; [|lia].
  set (v := nth _ _ _) in *. clearbody v. pose proof (proj1 (List.Forall_forall _ _) size_classes_bounds _ H). cbn beta in *. lia.
Qed.
Lemma small_cnt_any sc i : 0 <= small_cnt sc i <= 31.
Proof.
  unfold small_cnt.
  destruct (nth_in_or_default (Z.to_nat sc) small_cnt_tab nil) as [H|E]; [|rewrite E; destruct (Z.to_nat i); cbn; lia].
  set (row := nth (Z.to_nat sc) small_cnt_tab nil) in *. clearbody row.
  destruct (nth_in_or_default (Z.to_nat i) row 0) as [H'| ->]; [|lia]. set (v := nth _ _ _) in *. clearbody v.
  assert (F : Forall (fun r => Forall (fun x => 0 <= x <= 31) r) small_cnt_tab).
  { unfold small_cnt_tab. repeat (constructor; [repeat (constructor; [lia|]); constructor|]). constructor. }
  pose proof (proj1 (List.Forall_forall _ _) F _ H) as Fr. pose proof (proj1 (List.Forall_forall _ _) Fr _ H'). cbn beta in *. lia.
Qed.
Lemma med_cnt_any i : 0 <= med_cnt i <= 32.
Proof.
  unfold med_cnt. destruct (nth_in_or_default (Z.to_nat i) med_cnt_tab 0) as [H| ->]; [|lia].
  set (v := nth _ _ _) in *. clearbody v. unfold med_cnt_tab in H. cbn in H. lia.
Qed.
Lemma halve_even_any f : forall c u, 0 <= c <= 32 -> 0 <= halve_even f c u <= 32.
Proof.
  induction f as [|f IH]; intros c u H; cbn; [lia|].
  destruct (_ && _); [|lia]. apply IH. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia.
Qed.
Lemma halve_big_any f : forall c s, 0 <= c <= 32 -> 0 <= halve_big f c s <= 32.
Proof.
  induction f as [|f IH]; intros c s H; cbn; [lia|].
  destruct (_ <=? _); [|lia]. apply IH. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia.
Qed.
Lemma small_cnt_pick_any sc u : 0 <= small_cnt_pick sc u <= 31.
Proof. unfold small_cnt_pick. repeat (destruct (negb _)); apply small_cnt_any. Qed.
Lemma Vs_nonneg s : 0 <= s -> 0 <= Vs s.
Proof.
  intros H. unfold Vs, NSLOTS. pose proof (Z.pow_gt_lin_r 2 (s + 1) ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma Vs_small s : 0 <= s -> Vs s <= CMAX -> s <= 2.
Proof.
  intros Hs H. unfold Vs, NSLOTS, CMAX, CM, KTOP in H. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  destruct (Z.le_gt_cases s 2) as [|C]; [assumption|]. exfalso.
  pose proof (Z.pow_gt_lin_r 2 (s - 3) ltac:(lia) ltac:(lia)) as P.
  replace (2 ^ (s + 1)) with (16 * 2 ^ (s - 3)) in H; [nia|].
  replace (s + 1) with (4 + (s - 3)) by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.
Lemma Vs_succ s : 0 <= s -> Vs (s + 1) = Vs s + NSLOTS * (2 ^ (s + 1) - 1).
Proof.
  intros H. unfold Vs. replace (s + 1 + 1) with (Z.succ (s + 1)) by lia. rewrite Z.pow_succ_r by lia. lia.
Qed.
Lemma shiftl_2 s : 0 <= s -> Z.shiftl 2 s = 2 ^ (s + 1).
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. change (2^1) with 2. lia. Qed.

Section NODES.
Context {R : Type} (Q : R -> Prop).

#[using="Type"] Lemma BT_brk0 (k : Z -> M R) wb wm wp : 0 <= wb -> 0 <= wm -> 0 <= wp ->
  (forall z, BT wb wm wp (k z) Q) -> BT wb wm wp (SVis (EBrk 0) k) Q.
Proof. intros B1 B2 B3 Hk. cbn [BT ecost elen_ok Z.eqb]. rewrite !Z.sub_0_r. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact I|]. exact Hk. Qed.

#[using="Type"] Lemma BT_brk req (k : Z -> M R) wb wm wp : req <> 0 -> 2 * PGSZ <= wb -> 1 <= wm -> 2 <= wp ->
  (forall z, BT (wb - 2 * PGSZ) (wm - 1) (wp - 2) (k z) Q) -> BT wb wm wp (SVis (EBrk req) k) Q.
Proof.
  intros Hr Hb Hm Hp Hk. cbn [BT ecost elen_ok]. destruct (Z.eqb_spec req 0); [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact I|]. exact Hk.
Qed.

#[using="Type"] Lemma BT_munmap a len (k : Z -> M R) wb wm wp : 0 <= wb -> 0 <= wm -> 0 <= wp ->
  (forall z, BT wb wm wp (k z) Q) -> BT wb wm wp (SVis (EMunmap a len) k) Q.
Proof. intros B1 B2 B3 Hk. cbn [BT ecost elen_ok]. rewrite !Z.sub_0_r. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact I|]. exact Hk. Qed.

#[using="Type"] Lemma BT_mprotect a len prot (k : Z -> M R) wb wm wp : PGSZ <= wb -> 0 <= wm -> 0 <= wp ->
  (forall z, BT (wb - PGSZ) wm wp (k z) Q) -> BT wb wm wp (SVis (EMprotect a len prot) k) Q.
Proof. intros Hb B2 B3 Hk. cbn [BT ecost elen_ok]. rewrite !Z.sub_0_r. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact I|]. exact Hk. Qed.

#[using="Type"] Lemma BT_mmap_fixed a len prot flags (k : Z -> M R) wb wm wp : (Z.land flags MAP_FIXED =? 0) = false ->
  0 <= wb -> 0 <= wm -> 0 <= wp ->
  (forall z, BT wb wm wp (k z) Q) -> BT wb wm wp (SVis (EMmap a len prot flags) k) Q.
Proof.
  intros Hf B1 B2 B3 Hk. cbn [BT ecost elen_ok]. rewrite Hf. rewrite !Z.sub_0_r.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact Hk]. discriminate.
Qed.

#[using="Type"] Lemma BT_mmap_none a len flags (k : Z -> M R) wb wm wp : (Z.land flags MAP_FIXED =? 0) = true ->
  0 < len <= LMETA -> round_up_pg len <= wb -> 1 <= wm -> 0 <= wp ->
  (forall z, BT (wb - round_up_pg len) (wm - 1) wp (k z) Q) -> BT wb wm wp (SVis (EMmap a len PROT_NONE flags) k) Q.
Proof.
  intros Hf Hl B1 Hm B3 Hk. cbn [BT ecost elen_ok]. rewrite Hf.
  pose proof (round_up_pg_ge len). rewrite Z.max_r by lia. rewrite !Z.sub_0_r.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact Hk]. intros _. unfold LMETA, LMAX, PGSZ in *. lia.
Qed.

#[using="Type"] Lemma BT_mmap_rw a len prot flags (k : Z -> M R) wb wm wp : (Z.land flags MAP_FIXED =? 0) = true -> prot <> PROT_NONE ->
  0 < len <= LMAX -> round_up_pg len <= wb -> 1 <= wm -> 0 <= wp ->
  (forall z, BT (wb - round_up_pg len) (wm - 1) wp (k z) Q) -> BT wb wm wp (SVis (EMmap a len prot flags) k) Q.
Proof.
  intros Hf Hp Hl Hb Hm B3 Hk. cbn [BT ecost elen_ok]. rewrite Hf.
  destruct (Z.eqb_spec prot PROT_NONE); [contradiction|].
  pose proof (round_up_pg_ge len). rewrite Z.max_r by lia. rewrite !Z.sub_0_r.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact Hk]. intros _. split; [lia|]. intros; contradiction.
Qed.
End NODES.

Section AM.
Context {R : Type} (Q : R -> Prop).

#[using="Type"] Lemma BT_am_take st (k : mstate -> optr -> M R) bail wb wm wp c :
  VI c st -> c_avail_meta_count (s_ctx st) <> 0 ->
  (forall st' r, VI (c + 1) st' -> BT wb wm wp (k st' r) Q) -> BT wb wm wp (am_take st k bail) Q.
Proof.
  intros HV Ha Hk. unfold am_take. destruct (c_avail_meta _) as [m|]; [|apply BT_undef].
  apply Hk. unfold VI, VIv, cview in *. cbn -[Z.add Z.sub Z.mul NSLOTS Vs]. lia.
Qed.

#[using="Type"] Lemma am_carve_view st p :
  exists st5, (forall (k : mstate -> optr -> M R) bail, am_carve st p k bail = am_take st5 k bail)
    /\ cview st5 = (NSLOTS, c_avail_meta_area_count (s_ctx st) - 1, c_meta_alloc_shift (s_ctx st)).
Proof.
  unfold am_carve. eexists. split; [reflexivity|].
  unfold cview. destruct (c_meta_area_tail _); cbn; reflexivity.
Qed.

#[using="Type"] Lemma BT_am_carve st p (k : mstate -> optr -> M R) bail wb wm wp c :
  VI c st -> c_avail_meta_count (s_ctx st) = 0 -> 1 <= c_avail_meta_area_count (s_ctx st) ->
  (forall st' r, VI (c + 1) st' -> BT wb wm wp (k st' r) Q) -> BT wb wm wp (am_carve st p k bail) Q.
Proof.
  intros HV Ha HA Hk. destruct (am_carve_view st p) as (st5 & E & V5). rewrite E.
  eapply BT_am_take; [| | exact Hk].
  - unfold VI in *. rewrite V5. unfold VIv, cview in *. rewrite Ha in HV. unfold NSLOTS in *. lia.
  - unfold cview in V5. injection V5 as E1 E2 E3. rewrite E1. unfold NSLOTS. lia.
Qed.

#[using="Type"] Lemma BT_am_finish st nu (k : mstate -> optr -> M R) bail wb wm wp c :
  VI c st -> c_avail_meta_count (s_ctx st) = 0 -> 1 <= c_avail_meta_area_count (s_ctx st) ->
  PGSZ <= wb -> 0 <= wm -> 0 <= wp ->
  (forall st' r, VI (c + 1) st' -> BT (wb - PGSZ) wm wp (k st' r) Q) -> BT wb wm wp (am_finish st nu k bail) Q.
Proof.
  intros HV Ha HA Hb Bm Bp Hk. assert (PG : PGSZ = 4096) by reflexivity. unfold am_finish.
  destruct (c_avail_meta_areas _) as [p|]; [|apply BT_undef]. cbv zeta.
  match goal with |- BT _ _ _ (if ?cnd then _ else _) _ => destruct cnd end.
  - apply BT_mprotect; [lia|lia|lia|].
    intros z. destruct (negb _); [apply BT_bad_answer|]. destruct (_ || _).
    + eapply BT_am_carve; eauto.
    + apply Hk. apply VI_mono with c; [lia| exact HV].
  - eapply BT_am_carve; eauto. intros st' r V'. eapply BT_weaken; [| | | apply Hk; exact V']; unfold PGSZ in *; lia.
Qed.

#[using="Type"] Lemma BT_am_after_brk st nu (k : mstate -> optr -> M R) bail wb wm wp c :
  VI c st -> c_avail_meta_count (s_ctx st) = 0 -> c <= CMAX ->
  9 * PGSZ <= wb -> 1 <= wm -> 0 <= wp ->
  (forall st' r, VI (c + 1) st' -> BT (wb - 9 * PGSZ) (wm - 1) wp (k st' r) Q) -> BT wb wm wp (am_after_brk st nu k bail) Q.
Proof.
  intros HV Ha Hc Hb Hm Bp Hk. assert (PG : PGSZ = 4096) by reflexivity. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HA|HA].
  - cbv zeta. unfold VI, VIv, cview in HV. unfold ctx in HA. rewrite Ha, HA in HV. destruct HV as (_ & _ & Hs & HVs).
    pose proof (Vs_small _ Hs ltac:(lia)) as S2.
    unfold ctx. rewrite (shiftl_2 _ Hs).
    assert (HP : 2 <= 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) <= 8).
    { split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia|]. change 8 with (2^3). apply Z.pow_le_mono_r; lia. }
    assert (RU : round_up_pg (2 ^ (c_meta_alloc_shift (s_ctx st) + 1) * PGSZ) = 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) * PGSZ).
    { apply round_up_pg_id. unfold PGSZ. apply Z_mod_mult. }
    apply BT_mmap_none; [reflexivity| unfold LMETA, PGSZ; lia| rewrite RU; lia| lia| lia|]. rewrite RU.
    intros z. destruct (negb _); [apply BT_bad_answer|]. destruct (is_err z).
    + eapply BT_weaken; [| | | apply Hk; unfold VI, VIv, cview; rewrite Ha, HA; repeat split; lia]; lia.
    + match goal with |- BT _ _ _ (let '(_, _) := ?nr in _) _ => destruct nr as [st1 rid] eqn:En end.
      assert (V1 : cview st1 = cview st) by (pose proof (cview_new_region RKMeta z (2 ^ (c_meta_alloc_shift (s_ctx st) + 1) * PGSZ) st) as X; rewrite En in X; exact X).
      apply BT_am_finish with c.
      * unfold VI, VIv, cview in *. cbn -[Z.add Z.sub Z.mul NSLOTS Vs Z.pow Z.le].
        injection V1 as E1 E2 E3. rewrite ?E1, ?E2, ?E3, Ha. rewrite Vs_succ by lia. split; [lia|]. split; [lia|]. split; [lia|]. nia.
      * cbn. injection V1 as E1 E2 E3. rewrite E1. exact Ha.
      * cbn -[Z.pow Z.sub Z.add]. lia.
      * lia. * lia. * lia.
      * intros st' r V'. eapply BT_weaken; [| | | apply Hk; exact V']; lia.
  - apply BT_am_finish with c; auto; [| lia| lia|].
    + unfold VI, VIv, cview in HV. unfold ctx in HA. lia.
    + intros st' r V'. eapply BT_weaken; [| | | apply Hk; exact V']; lia.
Qed.

#[using="Type"] Lemma BT_brk_any req (k : Z -> M R) wb wm wp : 2 * PGSZ <= wb -> 1 <= wm -> 2 <= wp ->
  (forall z, BT (wb - 2 * PGSZ) (wm - 1) (wp - 2) (k z) Q) -> BT wb wm wp (SVis (EBrk req) k) Q.
Proof.
  intros Hb Hm Hp Hk. assert (PG : PGSZ = 4096) by reflexivity. destruct (Z.eq_dec req 0) as [->|NE].
  - apply BT_brk0; [lia|lia|lia|]. intros z. eapply BT_weaken; [| | | apply Hk]; lia.
  - apply BT_brk; auto.
Qed.

#[using="Type"] Lemma BT_alloc_meta st (k : mstate -> optr -> M R) bail wb wm wp c :
  VI c st -> c <= CMAX -> AMB <= wb -> 2 <= wm -> 2 <= wp ->
  (forall st' r, VI (c + 1) st' -> BT (wb - AMB) (wm - 2) (wp - 2) (k st' r) Q) ->
  BT wb wm wp (alloc_meta st k bail) Q.
Proof.
  intros HV Hc Hb Hm Hp Hk. assert (PG : PGSZ = 4096) by reflexivity. unfold AMB in *. unfold alloc_meta.
  match goal with |- context [c_free_meta_head (ctx ?e)] => set (st0 := e) in * end.
  assert (V0 : cview st0 = cview st) by (subst st0; destruct (c_init_done _ =? 0); reflexivity).
  assert (HV0 : VI c st0) by (eapply VI_view; eauto). clearbody st0. clear V0 HV st. rename st0 into st.
  assert (KW : forall st' r wb' wm' wp', VI (c + 1) st' -> wb - 11 * PGSZ <= wb' -> wm - 2 <= wm' -> wp - 2 <= wp' -> BT wb' wm' wp' (k st' r) Q).
  { intros. eapply BT_weaken; [| | | apply Hk; assumption]; lia. }
  destruct (c_free_meta_head _) as [m|].
  { apply KW; [| lia| lia| lia]. apply VI_mono with c; [lia|]. eapply VI_view; [apply cview_dequeue| exact HV0]. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx st)) 0) as [Ha|Ha]; cbn [negb].
  2:{ eapply BT_am_take; [exact HV0| exact Ha|]. intros st' r V'. apply KW; auto; lia. }
  unfold ctx in Ha.
  assert (AFTER : forall st1 nu wb' wm' wp',
            cview st1 = cview st \/ (c_avail_meta_area_count (s_ctx st) = 0 /\ cview st1 = (0, 1, c_meta_alloc_shift (s_ctx st))) ->
            wb - 2 * PGSZ <= wb' -> wm - 1 <= wm' -> wp - 2 <= wp' -> BT wb' wm' wp' (am_after_brk st1 nu k bail) Q).
  { intros st1 nu wb' wm' wp' V1 B1 B2 B3.
    apply BT_am_after_brk with c; [| | exact Hc| lia| lia| lia|].
    - destruct V1 as [V1|[HA V1]]; [eapply VI_view; eauto|]. unfold VI. rewrite V1. unfold VI, VIv, cview in HV0. cbn -[Z.le Z.add Z.mul Vs NSLOTS].
      rewrite Ha, HA in HV0. unfold NSLOTS in *. lia.
    - destruct V1 as [V1|[_ V1]]; unfold cview in V1; injection V1 as E1 E2 E3; rewrite E1; [exact Ha| reflexivity].
    - intros st' r V'. apply KW; auto; lia. }
  destruct ((c_avail_meta_area_count (ctx st) =? 0) && negb _) eqn:EA; [| apply AFTER; [left; reflexivity| lia| lia| lia]].
  apply andb_prop in EA. destruct EA as [EA _]. apply Z.eqb_eq in EA. unfold ctx in EA.
  destruct (c_brk _) as [| |rid off]; [| apply AFTER; [left; reflexivity| lia| lia| lia]|].
  - apply BT_brk0; [lia|lia|lia|]. intros cur. destruct (negb _); [apply BT_bad_answer|]. cbv zeta.
    apply BT_brk_any; [lia|lia|lia|]. intros r. destruct (negb _); [apply BT_bad_answer|].
    destruct (negb (r =? _)). { apply AFTER; [left; reflexivity| lia| lia| lia]. }
    destruct (negb _); [apply BT_bad_answer|].
    apply BT_mmap_fixed; [reflexivity| lia| lia| lia|]. intros rg. destruct (negb _); [apply BT_bad_answer|].
    match goal with |- BT _ _ _ (let '(_, _) := ?nr in _) _ => destruct nr as [st1 rid] eqn:En end.
    apply AFTER; [| lia| lia| lia]. right. split; [exact EA|].
    pose proof (cview_new_region RKBrk (round_up_pg cur) (2 * PGSZ) st) as X. rewrite En in X. cbn [fst] in X.
    unfold cview in *. cbn. injection X as E1 E2 E3. rewrite E1, E3, Ha. reflexivity.
  - cbv zeta. apply BT_brk_any; [lia|lia|lia|]. intros r. destruct (negb _); [apply BT_bad_answer|].
    destruct (negb (r =? _)). { apply AFTER; [left; reflexivity| lia| lia| lia]. }
    destruct (negb _); [apply BT_bad_answer|].
    apply AFTER; [| lia| lia| lia]. right. split; [exact EA|].
    pose proof (cview_upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st) as X.
    unfold cview in *. cbn. injection X as E1 E2 E3. rewrite E1, E3, Ha. reflexivity.
Qed.
End AM.

Definition LV (req : Z) : Z := Z.max GB (round_up_pg (req + IB + UNIT)) + AMB.

Lemma LV_small req : 0 <= req <= 2048 -> LV req = GB + AMB.
Proof.
  intros H. unfold LV. rewrite Z.max_l; [reflexivity|].
  unfold GB. pose proof (round_up_pg_mono (req + IB + UNIT) PGSZ ltac:(unfold IB, UNIT, PGSZ; lia)).
  rewrite (round_up_pg_id PGSZ) in H0 by reflexivity. unfold PGSZ in *. lia.
Qed.

Lemma LV_ge req : GB + AMB <= LV req.
Proof. unfold LV. lia. Qed.

Section AG.
Context {R : Type} (Q : R -> Prop) (lay : layout_hook).
Hypothesis Hhdr : forall st b, cview (lh_hdr lay st b) = cview st.
Hypothesis Hnest : forall st g i j sz cnt, cview (lh_nest lay st g i j sz cnt) = cview st.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Variable f : nat.
Let Zf := Z.of_nat f.
Hypothesis REC : forall st j req k bail wb wm wp c,
  0 <= req <= 2048 -> VI c st -> c + Zf <= CMAX ->
  Zf * (GB + AMB) <= wb -> 3 * Zf <= wm -> 2 * Zf <= wp ->
  (forall st' x c', VI c' st' -> c' <= c + Zf -> BT (wb - Zf * (GB + AMB)) (wm - 3 * Zf) (wp - 2 * Zf) (k st' x) Q) ->
  BT wb wm wp (rec st j req k bail) Q.

#[using="Hhdr Hnest REC"] Lemma BT_alloc_group st sc req (k : mstate -> optr -> M R) bail wb wm wp c :
  0 <= req <= NMAX -> VI c st -> c + 1 + Zf <= CMAX ->
  LV req + Zf * (GB + AMB) <= wb -> 3 + 3 * Zf <= wm -> 2 + 2 * Zf <= wp ->
  (forall st' r c', VI c' st' -> c' <= c + 1 + Zf ->
     BT (wb - (LV req + Zf * (GB + AMB))) (wm - (3 + 3 * Zf)) (wp - (2 + 2 * Zf)) (k st' r) Q) ->
  BT wb wm wp (alloc_group R lay rec st sc req k bail) Q.
Proof.
  intros Hr HV Hc Hb Hm Hp Hk.
  assert (PG : PGSZ = 4096) by reflexivity. assert (Zf0 : 0 <= Zf) by (subst Zf; lia).
  pose proof (LV_ge req) as LVG. assert (GBv : GB = 2^22 + 4096) by reflexivity. assert (AMv : AMB = 45056) by reflexivity.
  assert (KW : forall st' r c' wb' wm' wp', VI c' st' -> c' <= c + 1 + Zf ->
     wb - (LV req + Zf * (GB + AMB)) <= wb' -> wm - (3 + 3 * Zf) <= wm' -> wp - (2 + 2 * Zf) <= wp' -> BT wb' wm' wp' (k st' r) Q).
  { intros. eapply BT_weaken; [| | | eapply Hk; eassumption]; lia. }
  unfold alloc_group. apply BT_alloc_meta with c; [exact HV| lia| nia| lia| lia|].
  intros st0 [m|] V0. 2:{ eapply KW; [exact V0| lia| nia| lia| lia]. }
  cbv zeta.
  set (cnt0 := if sc <? 9 then _ else _).
  assert (C0 : 0 <= cnt0 <= 32).
  { subst cnt0. destruct (sc <? 9); [pose proof (small_cnt_pick_any sc (usage st0 sc)); lia|].
    apply halve_big_any, halve_even_any, med_cnt_any. }
  clearbody cnt0.
  pose proof (size_class_any sc) as SC.
  set (cnt1 := if (cnt0 =? 1) && _ then 2 else cnt0).
  assert (C1 : 0 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia). clearbody cnt1.
  assert (VTAIL : forall stX stY p cnt ai wb' wm' wp' c', VI c' stY -> cview stX = cview stY -> c' <= c + 1 + Zf ->
     wb - (LV req + Zf * (GB + AMB)) <= wb' -> wm - (3 + 3 * Zf) <= wm' -> wp - (2 + 2 * Zf) <= wp' ->
     BT wb' wm' wp' (ag_tail lay stX sc m p cnt ai k) Q).
  { intros stX stY p cnt ai wb' wm' wp' c' VY VX H1 B1 B2 B3. unfold ag_tail. eapply (KW _ _ c'); [| lia| lia| lia| lia].
    eapply VI_view; [| exact VY]. autorewrite with cview. rewrite Hhdr. exact VX. }
  destruct (PGSZ / 2 <? _) eqn:BR.
  -
    set (st1 := step_seq (account_bounce sc st0)) in *.
    assert (V1 : cview st1 = cview st0) by (subst st1; rewrite cview_step_seq, cview_account_bounce; reflexivity). clearbody st1.
    set (cnt2 := if (_ <? 4 * cnt1) && negb _ then _ else cnt1).
    assert (C2 : 0 <= cnt2 <= 32). { subst cnt2. destruct (_ && negb _); [|lia]. repeat (destruct (_ && _); [lia|]). lia. } clearbody cnt2.
    assert (SZC : 0 <= UNIT * size_class sc * cnt2 /\ UNIT * size_class sc * cnt2 + UNIT <= 2^22) by (unfold UNIT; nia).
    assert (UNITv : UNIT = 16) by reflexivity. assert (IBv : IB = 4) by reflexivity.
    pose proof (round_up_pg_ge (UNIT * size_class sc * cnt2 + UNIT)) as RG1.
    pose proof (round_up_pg_mono _ _ (proj2 SZC)) as RM1. rewrite (round_up_pg_id (2^22)) in RM1 by reflexivity.
    pose proof (round_up_pg_ge (req + IB + UNIT)) as RG2.
    assert (LVQ : round_up_pg (req + IB + UNIT) + AMB <= LV req) by (unfold LV; lia).
    assert (LVG' : round_up_pg (UNIT * size_class sc * cnt2 + UNIT) + AMB <= LV req) by (unfold LV; lia).
    match goal with |- BT _ _ _ (let '(_, _) := ?pr in _) _ =>
      assert (PR : exists cnt needed, pr = (cnt, needed) /\ 0 < needed /\ needed <= LMAX /\ round_up_pg needed = needed /\ needed + AMB <= LV req);
      [| destruct PR as (cnt & needed & -> & N1 & N2 & N3 & N4)] end.
    { destruct (negb _ && (cnt2 <=? 7)); [destruct (_ || _)|].
      - eexists _, _. split; [reflexivity|]. rewrite round_up_pg_idem.
        pose proof (round_up_pg_le (req + IB + UNIT)). unfold LMAX, NMAX in *. lia.
      - eexists _, _. split; [reflexivity|]. rewrite round_up_pg_idem. unfold LMAX in *. lia.
      - eexists _, _. split; [reflexivity|]. rewrite round_up_pg_idem. unfold LMAX in *. lia. }
    apply BT_mmap_rw; [reflexivity| discriminate| lia| rewrite N3; nia| lia| lia|]. rewrite N3.
    intros r. destruct (negb _); [apply BT_bad_answer|]. destruct (is_err r).
    + apply BT_free_meta. intros st2 V2. eapply (KW _ _ (c + 1)); [| lia| nia| lia| lia].
      eapply VI_view; [| exact V0]. rewrite V2. exact V1.
    + destruct (new_region RKGroup r needed st1) as [st2 rid] eqn:En.
      pose proof (cview_new_region RKGroup r needed st1) as V2. rewrite En in V2. cbn [fst] in V2.
      eapply (VTAIL _ st0 _ _ _ _ _ _ (c + 1)); [exact V0| | lia| nia| lia| lia].
      transitivity (cview st2); [reflexivity| rewrite V2; exact V1].
  -
    apply Z.ltb_ge in BR.
    assert (UNITv : UNIT = 16) by reflexivity. assert (IBv : IB = 4) by reflexivity.
    assert (X0 : 0 <= UNIT * size_class sc * cnt1) by nia.
    change (PGSZ / 2) with 2048 in BR.
    apply REC with (c := c + 1); [rewrite (Z.mul_comm cnt1); lia| exact V0| lia| nia| lia| lia|].
    intros st1 idx c' V1 Hc'. destruct (idx <? 0).
    + apply BT_free_meta. intros st2 V2. eapply (KW _ _ c'); [| lia| nia| lia| lia]. eapply VI_view; [exact V2| exact V1].
    + destruct (active st1 _); [| apply BT_undef].
      eapply (VTAIL _ st1 _ _ _ _ _ _ c'); [exact V1| | lia| nia| lia| lia]. autorewrite with cview. apply Hnest.
Qed.
End AG.

Section AS.
Context {R : Type} (Q : R -> Prop) (lay : layout_hook).
Hypothesis Hhdr : forall st b, cview (lh_hdr lay st b) = cview st.
Hypothesis Hnest : forall st g i j sz cnt, cview (lh_nest lay st g i j sz cnt) = cview st.

#[using="Hhdr Hnest"] Lemma BT_alloc_slot f : forall st sc req (k : mstate -> Z -> M R) bail wb wm wp c,
  let ZF := Z.of_nat f in
  0 <= req <= NMAX -> VI c st -> c + ZF <= CMAX ->
  LV req + (ZF - 1) * (GB + AMB) <= wb -> 3 * ZF <= wm -> 2 * ZF <= wp ->
  (forall st' x c', VI c' st' -> c' <= c + ZF ->
     BT (wb - (LV req + (ZF - 1) * (GB + AMB))) (wm - 3 * ZF) (wp - 2 * ZF) (k st' x) Q) ->
  BT wb wm wp (alloc_slot lay f st sc req k bail) Q.
Proof.
  induction f as [|f IH]; intros st sc req k bail wb wm wp c ZF Hr HV Hc Hb Hm Hp Hk; [apply BT_undef|].
  assert (EZ : ZF = Z.of_nat f + 1) by (subst ZF; lia). set (Zf := Z.of_nat f) in *. assert (Zf0 : 0 <= Zf) by lia.
  pose proof (LV_ge req) as LVG. assert (GBv : GB = 2^22 + 4096) by reflexivity. assert (AMv : AMB = 45056) by reflexivity.
  cbn [alloc_slot]. apply BT_try_avail. intros st1 first V1.
  destruct (negb (first =? 0)).
  { eapply BT_weaken; [| | | eapply (Hk _ _ c); [eapply VI_view; eauto| lia]]; nia. }
  apply (BT_alloc_group Q lay Hhdr Hnest (alloc_slot lay f) f) with (c := c).
  - intros st0 j req0 k0 bail0 wb0 wm0 wp0 c0 Hr0 HV0 Hc0 Hb0 Hm0 Hp0 Hk0.
    apply (IH _ _ _ _ _ _ _ _ c0); [unfold NMAX; lia| exact HV0| lia| rewrite LV_small by lia; lia| lia| lia|].
    intros st' x c' V' Hc'. rewrite LV_small by lia. eapply BT_weaken; [| | | apply (Hk0 _ _ c' V' Hc')]; lia.
  - exact Hr.
  - eapply VI_view; eauto.
  - lia. - lia. - lia. - lia.
  - intros st2 [g|] c' V2 Hc'.
    + apply BT_queue. intros st4 V4. eapply BT_weaken; [| | | eapply (Hk _ _ c'); [| lia]]; [lia| lia| lia|].
      eapply VI_view; [| exact V2]. rewrite V4. apply cview_upd_meta.
    + eapply BT_weaken; [| | | eapply (Hk _ _ c'); [exact V2| lia]]; lia.
Qed.
End AS.

Section MC.
Context (lay : layout_hook).
Hypothesis Hhdr : forall st b, cview (lh_hdr lay st b) = cview st.
Hypothesis Hnest : forall st g i j sz cnt, cview (lh_nest lay st g i j sz cnt) = cview st.

Definition QV (c : Z) : mstate * option (aptr * Z) -> Prop := fun x => VI c (fst x).

#[using="Hhdr Hnest"] Lemma BT_malloc_small_ctrl st n wb wm wp c (k : mstate -> option (aptr * Z) -> M (mstate * option (aptr * Z))) bail :
  0 <= n <= NMAX -> VI c st -> c + CM <= CMAX ->
  LV n + 63 * (GB + AMB) <= wb -> 192 <= wm -> 128 <= wp ->
  (forall st' r c', VI c' st' -> c' <= c + CM -> BT 0 0 0 (k st' r) (QV (c + CM))) ->
  BT wb wm wp (malloc_small_ctrl lay st n k bail) (QV (c + CM)).
Proof.
  intros Hn HV Hc Hb Hm Hp Hk. pose proof (LV_ge n) as LVG. assert (GBv : GB = 2^22 + 4096) by reflexivity. assert (AMv : AMB = 45056) by reflexivity.
  unfold malloc_small_ctrl.
  match goal with |- context [alloc_slot lay FUEL st ?sc n] => set (sc2 := sc) in * end. clearbody sc2.
  destruct (active st sc2) as [gp|].
  - destruct (negb _).
    + eapply BT_weaken; [| | | apply (Hk _ _ c); [| unfold CM; lia]]; [lia|lia|lia|]. eapply VI_view; [apply cview_upd_meta| exact HV].
    + apply (BT_alloc_slot _ lay Hhdr Hnest FUEL) with (c := c); unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold CM in *; try lia; [exact HV|].
      intros st' x c' V' Hc'. destruct (x <? 0); [| destruct (active st' sc2); [| apply BT_undef]];
        (eapply BT_weaken; [| | | apply (Hk _ _ c'); [exact V'| lia]]; lia).
  - cbn [lowbit m_avail].
    apply (BT_alloc_slot _ lay Hhdr Hnest FUEL) with (c := c); unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold CM in *; try lia; [exact HV|].
    intros st' x c' V' Hc'. destruct (x <? 0); [| destruct (active st' sc2); [| apply BT_undef]];
      (eapply BT_weaken; [| | | apply (Hk _ _ c'); [exact V'| lia]]; lia).
Qed.

#[using="Hhdr Hnest"] Theorem BT_malloc_core st n c :
  0 <= n <= NMAX -> VI c st -> c + CM <= CMAX ->
  BT BB BM BP (malloc_core lay st n) (QV (c + CM)).
Proof.
  intros Hn HV Hc. pose proof (LV_ge n) as LVG.
  assert (GBv : GB = 2^22 + 4096) by reflexivity. assert (AMv : AMB = 45056) by reflexivity.
  assert (BBv : BB = 2^29) by reflexivity. assert (BMv : BM = 200) by reflexivity. assert (BPv : BP = 128) by reflexivity.
  assert (CMv : CM = 64) by reflexivity.
  assert (LVn : LV n <= 2^27 + 8192 + AMB).
  { unfold LV. pose proof (round_up_pg_le (n + IB + UNIT)). unfold NMAX in Hn. assert (IB + UNIT = 20) by reflexivity. lia. }
  unfold malloc_core. destruct (size_overflows n).
  { apply BT_ret. unfold QV. cbn [fst]. apply VI_mono with c; [lia| exact HV]. }
  destruct (MMAP_THRESHOLD <=? n).
  - cbv zeta. pose proof (round_up_pg_le (n + IB + UNIT)) as RL.
    apply BT_mmap_rw; [reflexivity| discriminate| unfold LMAX, NMAX, IB, UNIT in *; lia| unfold NMAX, IB, UNIT in *; lia| lia| lia|].
    intros r. destruct (negb _); [apply BT_bad_answer|]. destruct (is_err r).
    { apply BT_ret. unfold QV. cbn [fst]. apply VI_mono with c; [lia| exact HV]. }
    destruct (new_region RKGroup r (n + IB + UNIT) st) as [st1 rid] eqn:En.
    pose proof (cview_new_region RKGroup r (n + IB + UNIT) st) as V1. rewrite En in V1. cbn [fst] in V1.
    apply BT_alloc_meta with c; [| lia| unfold NMAX, IB, UNIT in *; lia| lia| lia|].
    { eapply VI_view; [| exact HV]. rewrite cview_step_seq. exact V1. }
    intros st3 [g|] V3.
    + apply BT_ret. unfold QV. cbn [fst]. apply VI_mono with (c + 1); [lia|]. eapply VI_view; [| exact V3].
      autorewrite with cview. rewrite Hhdr. autorewrite with cview. reflexivity.
    + apply BT_munmap; [unfold NMAX, IB, UNIT in *; lia| lia| lia|]. intros z. destruct (munmap_answer_ok z); [| apply BT_bad_answer].
      apply BT_ret. unfold QV. cbn [fst]. apply VI_mono with (c + 1); [lia|]. eapply VI_view; [apply cview_drop_region| exact V3].
  - apply (BT_malloc_small_ctrl st n BB BM BP c); auto; try lia.
    intros st' r c' V' Hc'. apply BT_ret. unfold QV. cbn [fst]. apply VI_mono with c'; [lia| exact V'].
Qed.
End MC.

Definition PHM (k : nat) (cs : mstate) : Prop := VI (CM * (Z.of_nat KTOP - Z.of_nat k)) cs.

Theorem cmalloc_BT cs n k : 0 <= n <= NMAX -> PHM (S k) cs ->
  BT BB BM BP (cmalloc cs n) (fun x => PHM k (fst x)).
Proof.
  intros Hn HP. unfold cmalloc. unfold PHM in *.
  apply (BT_bind (QV (CM * (Z.of_nat KTOP - Z.of_nat (S k)) + CM))).
  - apply BT_malloc_core; [intros; reflexivity| intros; reflexivity| exact Hn| exact HP|].
    unfold CMAX, CM. lia.
  - intros [st1 r] wb' wm' wp' HQ _ _ _. apply BT_ret. cbn [fst]. unfold QV in HQ. cbn [fst] in HQ.
    eapply VI_view; [apply cview_strip|]. replace (CM * (Z.of_nat KTOP - Z.of_nat k)) with (CM * (Z.of_nat KTOP - Z.of_nat (S k)) + CM) by lia. exact HQ.
  - unfold BB; lia. - unfold BM; lia. - unfold BP; lia.
Qed.

Section FG.
Context {R : Type} (Q : R -> Prop) (wb wm wp : Z).
Variable dec : decoder R.
Variable rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R.
Hypothesis DEC : forall st p k bail, (forall m idx, BT wb wm wp (k m idx) Q) -> BT wb wm wp (dec st p k bail) Q.
Hypothesis RECF : forall st g i k bail,
  (forall st' mi, cview st' = cview st -> BT wb wm wp (k st' mi) Q) -> BT wb wm wp (rec st g i k bail) Q.

#[using="DEC RECF"] Lemma BT_free_group st g (k : mstate -> mapinfo -> M R) bail :
  (forall st' mi, cview st' = cview st -> BT wb wm wp (k st' mi) Q) -> BT wb wm wp (free_group R dec rec st g k bail) Q.
Proof.
  intros Hk. unfold free_group.
  set (st1 := if _ <? 48 then _ else _) in *.
  assert (V1 : cview st1 = cview st) by (subst st1; destruct (_ <? 48); reflexivity). clearbody st1.
  destruct (m_mem _) as [p|]; [| apply BT_undef].
  destruct (negb _).
  - apply BT_free_meta. intros st3 V3. apply Hk. rewrite V3. autorewrite with cview. exact V1.
  - apply DEC. intros m idx. apply RECF. intros st3 mi V3. apply BT_free_meta. intros st4 V4. apply Hk.
    rewrite V4, V3. autorewrite with cview. exact V1.
Qed.
End FG.

Lemma BT_dec_slots {R} (Q : R -> Prop) wb wm wp st p (k : aptr -> Z -> M R) bail :
  (forall m idx, BT wb wm wp (k m idx) Q) -> BT wb wm wp (dec_slots st p k bail) Q.
Proof. intros Hk. unfold dec_slots. destruct (s_slots st !! p) as [[m idx]|]; [apply Hk| apply BT_undef]. Qed.

Lemma BT_nontrivial_free {R} (Q : R -> Prop) wb wm wp f : forall st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st' mi, cview st' = cview st -> BT wb wm wp (k st' mi) Q) -> BT wb wm wp (nontrivial_free dec_slots f st g i k bail) Q.
Proof.
  induction f as [|f IH]; intros st g i k bail Hk; [apply BT_undef|]. cbn [nontrivial_free].
  destruct (_ && okay_to_free st g).
  - assert (FGk : forall st1, cview st1 = cview st ->
      BT wb wm wp (free_group R dec_slots (nontrivial_free dec_slots f) st1 g k bail) Q).
    { intros st1 V1. apply BT_free_group; [intros; apply BT_dec_slots; auto| intros; apply IH; auto|].
      intros st' mi V'. apply Hk. rewrite V'. exact V1. }
    destruct (m_next _); [| apply FGk; reflexivity]. apply BT_guard.
    destruct (optr_eqb _ _); [destruct (active (dequeue _ g st) _)|];
      [apply BT_activate_group; intros st2 x V2; apply FGk; rewrite V2; apply cview_dequeue| apply FGk; apply cview_dequeue| apply FGk; apply cview_dequeue].
  - destruct (_ =? 0).
    + apply BT_guard. destruct (negb _).
      * apply BT_queue. intros st' V'. apply Hk. rewrite cview_upd_meta. exact V'.
      * apply Hk. apply cview_upd_meta.
    + apply Hk. apply cview_upd_meta.
Qed.

Lemma BT_free_tail st g idx : BT 0 0 0 (free_tail dec_slots st g idx) (fun st' => cview st' = cview st).
Proof.
  unfold free_tail. apply BT_guard. destruct (negb _).
  - apply BT_ret. apply cview_upd_meta.
  - apply BT_nontrivial_free. intros st2 [[base len]|] V2.
    + destruct (negb _); [| apply BT_ret; exact V2].
      apply BT_munmap; [lia|lia|lia|]. intros ru. destruct (munmap_answer_ok ru); [| apply BT_bad_answer].
      apply BT_ret. rewrite cview_drop_region. exact V2.
    + apply BT_ret. exact V2.
Qed.

Theorem cfree_BT cs p k : PHM k cs -> BT 0 0 0 (cfree cs (Some p)) (PHM k).
Proof.
  intros HP. unfold cfree. destruct (s_slots cs !! p) as [[g idx]|]; [| apply BT_undef].
  eapply BT_bind; [apply BT_free_tail| | lia| lia| lia].
  intros st1 wb' wm' wp' V1 _ _ _. apply BT_ret. unfold PHM in *. eapply VI_view; [| exact HP]. rewrite cview_strip. exact V1.
Qed.
