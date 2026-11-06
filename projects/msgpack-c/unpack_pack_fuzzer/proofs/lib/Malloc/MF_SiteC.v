(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv
  MI_Inv MI_Kit MI_List MI_Cnt MI_Ledger MI_WAMeta MI_WSlot2 MI_Contracts MF_Phi.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Notation MAPF' := (MAP_PRIVATE + MAP_ANON).

Definition clr_rec (r : meta) : meta := m_set_prev None (m_set_next None r).
Definition selfrec (m : aptr) : meta := mkMeta (Some m) (Some m) None 0 0 0 0 0 0.

Lemma try_avail_none {R} sc st (k : mstate -> Z -> M R) bail :
  active st sc = None -> try_avail sc st k bail = k st 0.
Proof. intros HA. unfold try_avail. rewrite HA. reflexivity. Qed.

Lemma dequeue_self h m st :
  m_next (get_meta_rec st m) = Some m ->
  dequeue h m st = upd_meta m clr_rec (set_head h None st).
Proof.
  intros Hn. unfold dequeue. rewrite Hn. change (optr_eqb (Some m) (Some m)) with (aptr_eqb m m). rewrite aptr_eqb_refl. reflexivity.
Qed.

Lemma try_avail_exhausted {R} sc st m (k : mstate -> Z -> M R) bail :
  active st sc = Some m -> exhausted_head (get_meta_rec st m) m ->
  try_avail sc st k bail = k (upd_meta m clr_rec (set_active sc None st)) 0.
Proof.
  intros HA (E1 & E2 & E3 & E4). unfold try_avail. rewrite HA. rewrite E1. cbn [Z.eqb negb].
  rewrite E2. cbn [Z.eqb].
  rewrite (dequeue_self (LActive sc) m st E3). cbn [set_head].
  rewrite active_upd_meta, active_set_active, Z.eqb_refl. reflexivity.
Qed.

Lemma alloc_meta_free {R} st f (k : mstate -> optr -> M R) bail :
  c_init_done (s_ctx st) = 1 -> c_free_meta_head (s_ctx st) = Some f -> m_next (get_meta_rec st f) = Some f ->
  alloc_meta st k bail = k (upd_meta f clr_rec (upd_ctx (set_free_meta_head None) st)) (Some f).
Proof.
  intros HI HF Hn. unfold alloc_meta, ctx. rewrite HI. cbn [Z.eqb]. rewrite HF.
  rewrite (dequeue_self LFree f st Hn). reflexivity.
Qed.

Lemma alloc_meta_take {R} st q (k : mstate -> optr -> M R) bail :
  c_init_done (s_ctx st) = 1 -> c_free_meta_head (s_ctx st) = None -> 0 < c_avail_meta_count (s_ctx st) ->
  c_avail_meta (s_ctx st) = Some q ->
  alloc_meta st k bail =
    k (upd_meta q clr_rec (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st)) (Some q).
Proof.
  intros HI HF HC HQ. unfold alloc_meta, ctx. rewrite HI. cbn [Z.eqb]. rewrite HF.
  replace (c_avail_meta_count (s_ctx st) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  unfold am_take, ctx. rewrite HQ. reflexivity.
Qed.

Definition agtN (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st1 := set_usage sc (usage st sc + cnt) st in
  let st2 := upd_meta m (MI_WCreate2.agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_none_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail lay_none st sc m p cnt ai k = k (agtN st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Definition fin_st (sc : Z) (m : aptr) (st : mstate) : mstate :=
  let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st in
  set_active sc (Some m) (upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st3).

Lemma slot_fin_eq {R} sc m st (k : mstate -> Z -> M R) bail :
  m_next (get_meta_rec st m) = None -> m_prev (get_meta_rec st m) = None -> active st sc = None ->
  queue (LActive sc) m (upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st) (fun st4 => k st4 0) bail
  = k (fin_st sc m st) 0.
Proof.
  intros Hn Hp HA. rewrite queue_eq by (rewrite get_meta_rec_upd_same; cbn; assumption).
  unfold queue_st. cbn [get_head]. rewrite active_upd_meta, HA. reflexivity.
Qed.

Lemma lookup_upd_meta st m f x :
  s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof.
  rewrite s_metas_upd_meta. destruct (aptr_eqb_spec x m) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

Lemma get_meta_rec_of_lookup st m r : s_metas st !! m = Some r -> get_meta_rec st m = r.
Proof. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

Lemma get_meta_rec_of_none st m : s_metas st !! m = None -> get_meta_rec st m = meta0.
Proof. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

Lemma clr_selfrec m : clr_rec (selfrec m) = meta0. Proof. reflexivity. Qed.
Lemma clr_meta0 : clr_rec meta0 = meta0. Proof. reflexivity. Qed.

Lemma mslot_inj a k k' : mslot a k = mslot a k' -> k = k'.
Proof. unfold mslot, aadd. intros H. injection H. unfold META_SIZE, AREA_HDR. lia. Qed.

Section SITEC.
Variable st0 : mstate.
Hypothesis CF0 : CF st0.
Hypothesis PHI0 : PHI st0.

Lemma H0_act sc m : active st0 sc = Some m ->
  exists r, s_metas st0 !! m = Some r /\ exhausted_head r m /\ 0 <= sc < 48 /\ m_sizeclass r = sc.
Proof.
  intros HA. destruct PHI0 as (_ & _ & PA & _ & _). pose proof (PA sc m HA) as EX.
  destruct (cf_active _ CF0 sc m HA) as (PR & Hsc & b & ai & Hb & SC).
  destruct (s_metas st0 !! m) as [r|] eqn:E; [| exfalso; apply PR; reflexivity].
  exists r. rewrite (get_meta_rec_of_lookup _ _ _ E) in EX, SC. auto.
Qed.

Lemma H0_act_inj sc sc' m : active st0 sc = Some m -> active st0 sc' = Some m -> sc = sc'.
Proof.
  intros H1 H2. destruct (H0_act sc m H1) as (r & E & _ & _ & S1). destruct (H0_act sc' m H2) as (r' & E' & _ & _ & S2).
  rewrite E in E'. injection E' as <-. lia.
Qed.

Lemma H0_free : c_free_meta_head (s_ctx st0) = None
  \/ exists f, c_free_meta_head (s_ctx st0) = Some f /\ s_metas st0 !! f = Some (selfrec f) /\ forall sc, active st0 sc <> Some f.
Proof.
  destruct PHI0 as (_ & _ & _ & [[HN _]|(f & HF & Hf)] & _); [left; exact HN| right].
  exists f. split; [exact HF|]. split; [exact Hf|]. intros sc HA.
  destruct (cf_active _ CF0 sc f HA) as (_ & _ & b & ai & Hb & _).
  exact (proj2 (cf_free _ CF0 f HF) b _ Hb eq_refl).
Qed.

Record QE (st : mstate) (j : Z) : Prop := mkQE {
  qe_init : c_init_done (s_ctx st) = 1;
  qe_cnt : 49 - j <= c_avail_meta_count (s_ctx st) <= NSLOTS;
  qe_avail : exists a, c_avail_meta (s_ctx st) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx st)))
     /\ forall k, NSLOTS - c_avail_meta_count (s_ctx st) <= k < NSLOTS ->
          s_metas st !! mslot a k = None /\ s_metas st0 !! mslot a k = None;
  qe_free : c_free_meta_head (s_ctx st) = None
     \/ exists f, c_free_meta_head (s_ctx st) = Some f /\ s_metas st !! f = Some (selfrec f)
          /\ s_metas st0 !! f <> None /\ forall sc, active st0 sc <> Some f;
  qe_act : forall sc, j <= sc -> active st sc = active st0 sc;
  qe_actm : forall sc m, j <= sc -> active st0 sc = Some m -> s_metas st !! m = s_metas st0 !! m;
  qe_keys : forall x, s_metas st0 !! x <> None -> s_metas st !! x <> None
}.

Record QX (st st' : mstate) (j : Z) (g : aptr) : Prop := mkQX {
  qx_lo : forall sc, sc < j -> active st' sc = active st sc;
  qx_j : active st' j = Some g;
  qx_frame : forall x, s_metas st !! x <> None -> (forall sc, j <= sc -> active st0 sc <> Some x) ->
     c_free_meta_head (s_ctx st) <> Some x -> s_metas st' !! x = s_metas st !! x;
  qx_keys : forall x, s_metas st !! x <> None -> s_metas st' !! x <> None
}.

Lemma QE_st0 : QE st0 0.
Proof.
  destruct PHI0 as (PI & PC & PA & PF & PG).
  constructor.
  - exact PI.
  - pose proof (cf_count _ CF0). lia.
  - destruct (cf_avail _ CF0 ltac:(lia)) as (a & Ea & _ & FREE). exists a. split; [exact Ea|]. intros k Hk. split; apply FREE; exact Hk.
  - destruct H0_free as [HN|(f & HF & Hf & NA)]; [left; exact HN| right]. exists f. repeat split; auto. rewrite Hf. discriminate.
  - intros; reflexivity.
  - intros; reflexivity.
  - auto.
Qed.

Definition after_try (st : mstate) (j : Z) : mstate :=
  match active st j with
  | None => st
  | Some m => upd_meta m clr_rec (set_active j None st)
  end.

Lemma step_try st j : QE st j -> 0 <= j < 48 ->
  (forall R (k : mstate -> Z -> M R) bail, try_avail j st k bail = k (after_try st j) 0)
  /\ active (after_try st j) j = None
  /\ (forall sc, sc <> j -> active (after_try st j) sc = active st sc)
  /\ s_ctx (after_try st j) = match active st j with None => s_ctx st | Some _ => s_ctx (set_active j None st) end
  /\ (forall x, active st0 j <> Some x -> s_metas (after_try st j) !! x = s_metas st !! x)
  /\ (forall x, s_metas st !! x <> None -> s_metas (after_try st j) !! x <> None)
  /\ s_regions (after_try st j) = s_regions st /\ s_reserved (after_try st j) = s_reserved st.
Proof.
  intros Q Hj. unfold after_try. destruct (active st j) as [m|] eqn:HA.
  - pose proof HA as HA0. rewrite (qe_act _ _ Q j ltac:(lia)) in HA0.
    destruct (H0_act j m HA0) as (r & E0 & EX & _ & _).
    assert (Em : s_metas st !! m = Some r) by (rewrite (qe_actm _ _ Q j m ltac:(lia) HA0); exact E0).
    split. { intros R k bail. apply (try_avail_exhausted j st m k bail HA). rewrite (get_meta_rec_of_lookup _ _ _ Em). exact EX. }
    split. { rewrite active_upd_meta, active_set_active, Z.eqb_refl. reflexivity. }
    split. { intros sc NE. rewrite active_upd_meta, active_set_active. replace (sc =? j) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. }
    split. { reflexivity. }
    split. { intros x NX. rewrite lookup_upd_meta. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; exact (NX HA0)|]. reflexivity. }
    split. { intros x PX. rewrite lookup_upd_meta. destruct (aptr_eqb_spec x m); [discriminate| exact PX]. }
    split; reflexivity.
  - split; [intros; apply try_avail_none; exact HA|]. split; [exact HA|]. repeat split; auto.
Qed.

Record QM (st : mstate) (j : Z) : Prop := mkQM {
  qm_init : c_init_done (s_ctx st) = 1;
  qm_cnt : 49 - j <= c_avail_meta_count (s_ctx st) <= NSLOTS;
  qm_avail : exists a, c_avail_meta (s_ctx st) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx st)))
     /\ forall k, NSLOTS - c_avail_meta_count (s_ctx st) <= k < NSLOTS ->
          s_metas st !! mslot a k = None /\ s_metas st0 !! mslot a k = None;
  qm_free : c_free_meta_head (s_ctx st) = None
     \/ exists f, c_free_meta_head (s_ctx st) = Some f /\ s_metas st !! f = Some (selfrec f)
          /\ s_metas st0 !! f <> None /\ forall sc, active st0 sc <> Some f;
  qm_actj : active st j = None;
  qm_act : forall sc, j < sc -> active st sc = active st0 sc;
  qm_actm : forall sc m, j < sc -> active st0 sc = Some m -> s_metas st !! m = s_metas st0 !! m;
  qm_keys : forall x, s_metas st0 !! x <> None -> s_metas st !! x <> None
}.

Lemma s_ctx_set_active_fields sc v st :
  c_init_done (s_ctx (set_active sc v st)) = c_init_done (s_ctx st)
  /\ c_avail_meta_count (s_ctx (set_active sc v st)) = c_avail_meta_count (s_ctx st)
  /\ c_avail_meta (s_ctx (set_active sc v st)) = c_avail_meta (s_ctx st)
  /\ c_free_meta_head (s_ctx (set_active sc v st)) = c_free_meta_head (s_ctx st).
Proof. repeat split; reflexivity. Qed.

Lemma QE_QM st j : QE st j -> 0 <= j < 48 -> QM (after_try st j) j.
Proof.
  intros Q Hj. destruct (step_try st j Q Hj) as (_ & A1 & A2 & CX & MX & KX & _).
  assert (CI : c_init_done (s_ctx (after_try st j)) = c_init_done (s_ctx st)
       /\ c_avail_meta_count (s_ctx (after_try st j)) = c_avail_meta_count (s_ctx st)
       /\ c_avail_meta (s_ctx (after_try st j)) = c_avail_meta (s_ctx st)
       /\ c_free_meta_head (s_ctx (after_try st j)) = c_free_meta_head (s_ctx st)).
  { rewrite CX. destruct (active st j); [apply s_ctx_set_active_fields| repeat split; reflexivity]. }
  destruct CI as (C1 & C2 & C3 & C4).
  constructor.
  - rewrite C1. exact (qe_init _ _ Q).
  - rewrite C2. exact (qe_cnt _ _ Q).
  - rewrite C2, C3. destruct (qe_avail _ _ Q) as (a & Ea & FREE). exists a. split; [exact Ea|].
    intros k Hk. destruct (FREE k Hk) as [F1 F2]. split; [| exact F2].
    rewrite MX; [exact F1|]. intros HA. destruct (H0_act j _ HA) as (r & E & _). rewrite F2 in E. discriminate.
  - rewrite C4. destruct (qe_free _ _ Q) as [HN|(f & HF & Hf & P0 & NA)]; [left; exact HN| right].
    exists f. split; [exact HF|]. split; [| split; [exact P0| exact NA]]. rewrite MX; [exact Hf|]. exact (NA j).
  - exact A1.
  - intros sc Hsc. rewrite A2 by lia. apply (qe_act _ _ Q). lia.
  - intros sc m Hsc HA. rewrite MX. { apply (qe_actm _ _ Q sc m ltac:(lia) HA). }
    intros HA'. pose proof (H0_act_inj sc j m HA HA'). lia.
  - intros x PX. apply KX. apply (qe_keys _ _ Q). exact PX.
Qed.

Definition take (st : mstate) : aptr * mstate :=
  match c_free_meta_head (s_ctx st) with
  | Some f => (f, upd_meta f clr_rec (upd_ctx (set_free_meta_head None) st))
  | None =>
      let q := default (0%N, 0) (c_avail_meta (s_ctx st)) in
      (q, upd_meta q clr_rec (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE))
                                            (set_avail_meta_count (c_avail_meta_count c - 1) c)) st))
  end.

Record QA (st : mstate) (j : Z) (mt : aptr) : Prop := mkQA {
  qa_init : c_init_done (s_ctx st) = 1;
  qa_cnt : 49 - j - 1 <= c_avail_meta_count (s_ctx st) <= NSLOTS;
  qa_avail : exists a, c_avail_meta (s_ctx st) = Some (mslot a (NSLOTS - c_avail_meta_count (s_ctx st)))
     /\ forall k, NSLOTS - c_avail_meta_count (s_ctx st) <= k < NSLOTS ->
          s_metas st !! mslot a k = None /\ s_metas st0 !! mslot a k = None;
  qa_free : c_free_meta_head (s_ctx st) = None;
  qa_actj : active st j = None;
  qa_act : forall sc, j < sc -> active st sc = active st0 sc;
  qa_actm : forall sc m, j < sc -> active st0 sc = Some m -> s_metas st !! m = s_metas st0 !! m;
  qa_keys : forall x, s_metas st0 !! x <> None -> s_metas st !! x <> None;
  qa_M : s_metas st !! mt = Some meta0;
  qa_M0 : forall sc, active st0 sc <> Some mt
}.

Lemma QM_QA st j : QM st j -> 0 <= j < 48 ->
  let (mt, st2) := take st in
  (forall R (k : mstate -> optr -> M R) bail, alloc_meta st k bail = k st2 (Some mt))
  /\ QA st2 j mt
  /\ (forall x, x <> mt -> s_metas st2 !! x = s_metas st !! x)
  /\ (forall sc, active st2 sc = active st sc)
  /\ (c_free_meta_head (s_ctx st) = Some mt \/ s_metas st !! mt = None)
  /\ s_regions st2 = s_regions st /\ s_reserved st2 = s_reserved st.
Proof.
  intros Q Hj. unfold take.
  destruct (qm_free _ _ Q) as [HN|(f & HF & Hf & P0 & NA)].
  -
    rewrite HN. destruct (qm_avail _ _ Q) as (a & Ea & FREE). rewrite Ea. cbn [default].
    set (k0 := NSLOTS - c_avail_meta_count (s_ctx st)) in *.
    pose proof (qm_cnt _ _ Q) as HC.
    destruct (FREE k0 ltac:(lia)) as [F1 F2].
    set (st2 := upd_meta _ _ _).
    assert (LK : forall x, s_metas st2 !! x = if aptr_eqb x (mslot a k0) then Some meta0 else s_metas st !! x).
    { intros x. unfold st2. rewrite lookup_upd_meta. autorewrite with mst. rewrite (get_meta_rec_of_none _ _ F1). reflexivity. }
    split. { intros R k bail. apply alloc_meta_take; [exact (qm_init _ _ Q)| exact HN| lia| exact Ea]. }
    split.
    + constructor; unfold st2; autorewrite with mst; cbn [c_init_done c_avail_meta_count c_avail_meta c_free_meta_head set_avail_meta set_avail_meta_count].
      * exact (qm_init _ _ Q).
      * lia.
      * exists a. rewrite mslot_succ. split; [f_equal; f_equal; lia|].
        intros k Hk. fold st2. rewrite LK. destruct (aptr_eqb_spec (mslot a k) (mslot a k0)) as [E|NE].
        { apply mslot_inj in E. lia. }
        apply FREE. lia.
      * exact HN.
      * exact (qm_actj _ _ Q).
      * exact (qm_act _ _ Q).
      * intros sc m Hsc HA. fold st2. rewrite LK. destruct (aptr_eqb_spec m (mslot a k0)) as [->|NE].
        { destruct (H0_act sc _ HA) as (r & E & _). rewrite F2 in E. discriminate. }
        exact (qm_actm _ _ Q sc m Hsc HA).
      * intros x PX. fold st2. rewrite LK. destruct (aptr_eqb_spec x (mslot a k0)); [discriminate| exact (qm_keys _ _ Q x PX)].
      * fold st2. rewrite LK, aptr_eqb_refl. reflexivity.
      * intros sc HA. destruct (H0_act sc _ HA) as (r & E & _). rewrite F2 in E. discriminate.
    + split. { intros x NE. rewrite LK. rewrite (aptr_eqb_neq _ _ NE). reflexivity. }
      split. { intros sc. unfold st2, active, ctx. autorewrite with mst. cbn. autorewrite with mst. reflexivity. }
      split; [right; exact F1|]. split; reflexivity.
  -
    rewrite HF.
    set (st2 := upd_meta _ _ _).
    assert (LK : forall x, s_metas st2 !! x = if aptr_eqb x f then Some meta0 else s_metas st !! x).
    { intros x. unfold st2. rewrite lookup_upd_meta. autorewrite with mst. rewrite (get_meta_rec_of_lookup _ _ _ Hf). reflexivity. }
    split. { intros R k bail. apply alloc_meta_free; [exact (qm_init _ _ Q)| exact HF| rewrite (get_meta_rec_of_lookup _ _ _ Hf); reflexivity]. }
    pose proof (qm_cnt _ _ Q) as HC.
    split.
    + constructor; unfold st2; autorewrite with mst; cbn [c_init_done c_avail_meta_count c_avail_meta c_free_meta_head set_free_meta_head].
      * exact (qm_init _ _ Q).
      * lia.
      * destruct (qm_avail _ _ Q) as (a & Ea & FREE). exists a. split; [exact Ea|].
        intros k Hk. fold st2. rewrite LK. destruct (FREE k Hk) as [F1 F2].
        destruct (aptr_eqb_spec (mslot a k) f) as [E|NE]; [exfalso; apply P0; rewrite <- E; exact F2|]. auto.
      * reflexivity.
      * exact (qm_actj _ _ Q).
      * exact (qm_act _ _ Q).
      * intros sc m Hsc HA. fold st2. rewrite LK. destruct (aptr_eqb_spec m f) as [->|NE]; [exfalso; exact (NA sc HA)|].
        exact (qm_actm _ _ Q sc m Hsc HA).
      * intros x PX. fold st2. rewrite LK. destruct (aptr_eqb_spec x f); [discriminate| exact (qm_keys _ _ Q x PX)].
      * fold st2. rewrite LK, aptr_eqb_refl. reflexivity.
      * exact NA.
    + split. { intros x NE. rewrite LK. rewrite (aptr_eqb_neq _ _ NE). reflexivity. }
      split. { intros sc. unfold st2, active, ctx. autorewrite with mst. cbn. autorewrite with mst. reflexivity. }
      split; [left; reflexivity|]. split; reflexivity.
Qed.

Lemma QA_QE st j mt j2 : QA st j mt -> j < j2 -> QE st j2.
Proof.
  intros Q Hj. constructor.
  - exact (qa_init _ _ _ Q).
  - pose proof (qa_cnt _ _ _ Q). lia.
  - exact (qa_avail _ _ _ Q).
  - left. exact (qa_free _ _ _ Q).
  - intros sc Hsc. apply (qa_act _ _ _ Q). lia.
  - intros sc m Hsc HA. apply (qa_actm _ _ _ Q sc m); [lia| exact HA].
  - exact (qa_keys _ _ _ Q).
Qed.

Lemma agtN_active st sc m p cnt ai sc' : active (agtN st sc m p cnt ai) sc' = active st sc'.
Proof. unfold agtN, active, ctx. autorewrite with mst. cbn. autorewrite with mst. reflexivity. Qed.

Lemma agtN_metas st sc m p cnt ai x :
  s_metas (agtN st sc m p cnt ai) !! x = if aptr_eqb x m then Some (MI_WCreate2.agG sc p cnt ai (get_meta_rec st m)) else s_metas st !! x.
Proof.
  unfold agtN. autorewrite with mst. destruct (aptr_eqb_spec x m) as [->|NE];
    [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; unfold get_meta_rec; autorewrite with mst; reflexivity.
Qed.

Lemma agtN_free st sc m p cnt ai : c_free_meta_head (s_ctx (agtN st sc m p cnt ai)) = c_free_meta_head (s_ctx st).
Proof. unfold agtN. autorewrite with mst. cbn. autorewrite with mst. reflexivity. Qed.

Lemma fin_active sc m st sc' : active (fin_st sc m st) sc' = if sc' =? sc then Some m else active st sc'.
Proof. unfold fin_st. rewrite active_set_active, !active_upd_meta. reflexivity. Qed.

Lemma fin_metas sc m st x : x <> m -> s_metas (fin_st sc m st) !! x = s_metas st !! x.
Proof. intros NE. unfold fin_st. autorewrite with mst. rewrite !lookup_insert_ne by congruence. reflexivity. Qed.

Lemma fin_metas_m sc m st : s_metas (fin_st sc m st) !! m <> None.
Proof. unfold fin_st. autorewrite with mst. rewrite lookup_insert_eq. discriminate. Qed.

Lemma agG_links sc p cnt ai r : m_next (MI_WCreate2.agG sc p cnt ai r) = m_next r /\ m_prev (MI_WCreate2.agG sc p cnt ai r) = m_prev r.
Proof. split; reflexivity. Qed.

Lemma live_ranges_ext st st' : s_regions st' = s_regions st -> s_reserved st' = s_reserved st -> live_ranges st' = live_ranges st.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma step_seq_account_fields sc st : let st' := step_seq (account_bounce sc st) in
  (forall sc', active st' sc' = active st sc') /\ s_metas st' = s_metas st /\ s_regions st' = s_regions st
  /\ s_reserved st' = s_reserved st /\ c_free_meta_head (s_ctx st') = c_free_meta_head (s_ctx st)
  /\ (forall sc', usage st' sc' = usage st sc').
Proof.
  destruct (account_bounce_fields sc st) as (_ & _ & A3 & A4 & _ & A6 & _ & A8).
  destruct (step_seq_fields (account_bounce sc st)) as (_ & _ & B3 & B4 & _ & B6 & _ & B8). cbn zeta.
  split; [intros sc'; rewrite B3, A3; reflexivity|]. split; [rewrite B6, A6; reflexivity|]. split; [rewrite B4, A4; reflexivity|].
  split.
  { unfold step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity. }
  split.
  { unfold step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity. }
  intros sc'; rewrite B8, A8; reflexivity.
Qed.

Lemma alloc_slot_shape (f : nat) : forall j st req R (k : mstate -> Z -> M R) bail,
  49 - j <= Z.of_nat f -> 0 <= j < 48 -> 0 <= req -> req + IB <= UNIT * size_class j -> QE st j ->
  exists len K, alloc_slot lay_none f st j req k bail = SVis (EMmap 0 len PROT_RW MAPF') K
    /\ 0 < len <= 2^20
    /\ forall z, exists stf sts g,
         K z = (if negb (mmap_answer_ok (live_ranges st) len z) then bad_answer bail
                else if is_err z then k stf (-1) else k sts 0)
         /\ (is_err z = false -> QX st sts j g).
Proof.
  induction f as [|f IH]; intros j st req R k bail Hf Hj Hreq Hfit Q.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot lay_none (S f) st j req k bail) with
    (try_avail j st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group R lay_none (alloc_slot lay_none f) st1 j req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive j) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (step_try st j Q Hj) as (TRY & A1 & A2 & CX & MX & KX & RG & RS). rewrite TRY. cbn beta.
  change (negb (0 =? 0)) with false. cbn iota.
  pose proof (QE_QM st j Q Hj) as Q1. set (st1 := after_try st j) in *.
  pose proof (QM_QA st1 j Q1 Hj) as STEP2. destruct (take st1) as [mt st2] eqn:ET.
  destruct STEP2 as (AM & Q2 & MX2 & AX2 & ORIG & RG2 & RS2).
  unfold alloc_group. rewrite AM. cbn beta iota zeta.
  change (if j <? 9 then small_cnt_pick j (usage st2 j) else halve_big 8 (halve_even 8 (med_cnt (Z.land j 3)) (usage st2 j)) (UNIT * size_class j))
    with (cnt0_of j (usage st2 j)).
  change (if (cnt0_of j (usage st2 j) =? 1) && (UNIT * size_class j * cnt0_of j (usage st2 j) + UNIT <=? PGSZ / 2) then 2 else cnt0_of j (usage st2 j))
    with (ag_cnt1 j (usage st2 j)).
  pose proof (ag_arith j req (usage st2 j)) as AR.
  set (c1 := ag_cnt1 j (usage st2 j)) in *.

  assert (LR2 : live_ranges st2 = live_ranges st) by (apply live_ranges_ext; congruence).
  assert (NOTMT : forall x, s_metas st !! x <> None -> c_free_meta_head (s_ctx st) <> Some x -> x <> mt).
  { intros x PX FX ->. destruct ORIG as [O|O].
    - apply FX. rewrite <- O, CX. destruct (active st j); [symmetry; apply (proj2 (proj2 (proj2 (s_ctx_set_active_fields j None st))))| reflexivity].
    - exact (KX mt PX O). }
  assert (MT0 : get_meta_rec st2 mt = meta0) by exact (get_meta_rec_of_lookup _ _ _ (qa_M _ _ _ Q2)).
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class j * c1 + UNIT)) as [HB|HB].
  -
    set (ns := is_bouncing j st2).
    set (st2' := step_seq (account_bounce j st2)).
    set (u1 := if Z.even j && (j <? 32) then usage st2 j + usage st2' (j + 1) else usage st2 j).
    change (if (u1 <? 4 * c1) && negb ns
            then if (Z.land j 3 =? 1) && (8 * PGSZ <? UNIT * size_class j * c1) then 2
                 else if (Z.land j 3 =? 2) && (4 * PGSZ <? UNIT * size_class j * c1) then 3
                 else if (Z.land j 3 =? 0) && (8 * PGSZ <? UNIT * size_class j * c1) then 3
                 else if (Z.land j 3 =? 0) && (2 * PGSZ <? UNIT * size_class j * c1) then 5
                 else c1
            else c1) with (ag_cnt2 j c1 u1 ns).
    set (c2 := ag_cnt2 j c1 u1 ns).
    specialize (AR u1 ns).
    destruct (step_seq_account_fields j st2) as (SA1 & SA2 & SA3 & SA4 & SA5 & _). fold st2' in SA1, SA2, SA3, SA4, SA5.
    assert (LR2' : live_ranges st2' = live_ranges st) by (rewrite <- LR2; apply live_ranges_ext; assumption).
    assert (GO : forall c3 n3, ag_cn3 j req c2 u1 ns = (c3, n3) ->
      exists len K,
        SVis (EMmap 0 n3 PROT_RW MAPF') (fun r =>
          if negb (mmap_answer_ok (live_ranges st2') n3 r) then bad_answer bail
          else if is_err r then free_meta mt st2' (fun st3 => k st3 (-1)) bail
          else let '(st3, rid) := new_region RKGroup r n3 st2' in
               ag_tail lay_none (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta mt (m_set_maplen (Z.shiftr n3 12)) st3)) j mt (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class j) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai)
                 (fun st4 go => match go with
                                | None => k st4 (-1)
                                | Some g => queue (LActive j) g (upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st4) (fun st5 => k st5 0) bail
                                end))
        = SVis (EMmap 0 len PROT_RW MAPF') K
        /\ 0 < len <= 2^20
        /\ forall z, exists stf sts g,
             K z = (if negb (mmap_answer_ok (live_ranges st) len z) then bad_answer bail
                    else if is_err z then k stf (-1) else k sts 0)
             /\ (is_err z = false -> QX st sts j g)).
    { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hj Hreq Hfit) HB E3) as [GRP RED].
      pose proof (grp_ok_sound j c3 n3 GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & _).
      eexists n3, _. split; [reflexivity|]. split; [lia|].
      intros z. rewrite LR2'.
      set (AI := let ai := (4096 - UNIT) / (UNIT * size_class j) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai).
      set (st3 := fst (new_region RKGroup z n3 st2')).
      set (st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta mt (m_set_maplen (Z.shiftr n3 12)) st3)).
      set (sts := fin_st j mt (agtN st4 j mt (s_next_rid st2', 0) c3 AI)).
      exists (fm_st st2' mt), sts, mt.
      split.
      { destruct (negb (mmap_answer_ok (live_ranges st) n3 z)); [reflexivity|].
        destruct (is_err z); [rewrite free_meta_eq; reflexivity|].
        change (new_region RKGroup z n3 st2') with (st3, s_next_rid st2'). cbv beta iota.
        fold st4. rewrite ag_tail_none_eq. cbv beta iota.
        apply slot_fin_eq.
        - rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
          rewrite (proj1 (agG_links _ _ _ _ _)). unfold st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same.
          unfold st3. unfold get_meta_rec. autorewrite with mst. rewrite (qa_M _ _ _ Q2). reflexivity.
        - rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
          rewrite (proj2 (agG_links _ _ _ _ _)). unfold st4. rewrite get_meta_rec_upd_ctx, get_meta_rec_upd_same.
          unfold st3. unfold get_meta_rec. autorewrite with mst. rewrite (qa_M _ _ _ Q2). reflexivity.
        - rewrite agtN_active. unfold st4, st3, active, ctx. autorewrite with mst. cbn. autorewrite with mst.
          exact (qa_actj _ _ _ Q2). }
      intros NE. constructor.
      - intros sc Hsc. unfold sts. rewrite fin_active. replace (sc =? j) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite agtN_active. unfold st4, st3, active, ctx. autorewrite with mst. cbn. autorewrite with mst.
        change (active st2 sc = active st sc). rewrite <- (A2 sc ltac:(lia)). apply AX2.
      - unfold sts. rewrite fin_active, Z.eqb_refl. reflexivity.
      - intros x PX NH FH. unfold sts. rewrite fin_metas by (apply NOTMT; assumption).
        rewrite agtN_metas, (aptr_eqb_neq _ _ (NOTMT x PX FH)). unfold st4, st3. autorewrite with mst.
        rewrite lookup_insert_ne by (apply not_eq_sym; apply NOTMT; assumption).
        rewrite MX2 by (apply NOTMT; assumption). rewrite MX by (apply NH; lia). reflexivity.
      - intros x PX. unfold sts. destruct (aptr_eqb_spec x mt) as [->|NEx]; [apply fin_metas_m|].
        rewrite fin_metas by exact NEx. rewrite agtN_metas, (aptr_eqb_neq _ _ NEx). unfold st4, st3. autorewrite with mst.
        rewrite lookup_insert_ne by congruence. rewrite MX2 by exact NEx. apply KX. exact PX. }
    unfold ag_cn3 in GO. cbn zeta in GO.
    destruct (negb ns && (c2 <=? 7)).
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class j + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
      * cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + cbn beta iota. exact (GO _ _ eq_refl).
  -
    pose proof (proj2 (AR 0 false 0 0 Hj Hreq Hfit) HB) as NEST.
    pose proof (nest_ok_sound j c1 NEST) as NS. cbn zeta in NS. destruct NS as (N1 & N2 & N3 & N4 & N5 & N6).
    lazymatch goal with |- exists len K, alloc_slot _ _ ?s ?jj ?rr ?kk ?bb = _ /\ _ =>
      destruct (IH jj s rr R kk bb) as (len & K' & EQ & LB & PROP) end.
    + rewrite Nat2Z.inj_succ in Hf. lia.
    + lia.
    + exact N5.
    + lia.
    + eapply QA_QE; [exact Q2| lia].
    + exists len, K'. split; [exact EQ|]. split; [exact LB|].
      intros z. destruct (PROP z) as (stf & sts & g2 & EK & QXI).
      set (size := UNIT * size_class j) in *.
      set (j2 := size_to_class (UNIT + c1 * size - IB)) in *.
      set (sts' := fin_st j mt (agtN (upd_meta mt (m_set_maplen 0) sts) j mt (slot_of sts g2 0) c1 (c1 - 1))).
      exists (fm_st stf mt), sts', mt.
      rewrite EK, LR2.
      split.
      { destruct (negb (mmap_answer_ok (live_ranges st) len z)); [reflexivity|].
        destruct (is_err z) eqn:EZ.
        - cbv beta. change (-1 <? 0) with true. cbv iota. rewrite free_meta_eq. reflexivity.
        - specialize (QXI eq_refl). cbv beta. change (0 <? 0) with false. cbv iota. rewrite (qx_j _ _ _ _ QXI).
          change (lh_nest lay_none) with (fun (st : mstate) (_ : aptr) (_ _ _ _ : Z) => st). cbv beta.
          rewrite ag_tail_none_eq. cbv beta iota.
          assert (MTS : s_metas sts !! mt = Some meta0).
          { rewrite (qx_frame _ _ _ _ QXI); [exact (qa_M _ _ _ Q2)| rewrite (qa_M _ _ _ Q2); discriminate| | rewrite (qa_free _ _ _ Q2); discriminate].
            intros sc Hsc. exact (qa_M0 _ _ _ Q2 sc). }
          apply slot_fin_eq.
          + rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
            rewrite (proj1 (agG_links _ _ _ _ _)). rewrite get_meta_rec_upd_same. rewrite (get_meta_rec_of_lookup _ _ _ MTS). reflexivity.
          + rewrite (get_meta_rec_of_lookup _ _ _ ltac:(rewrite agtN_metas, aptr_eqb_refl; reflexivity)).
            rewrite (proj2 (agG_links _ _ _ _ _)). rewrite get_meta_rec_upd_same. rewrite (get_meta_rec_of_lookup _ _ _ MTS). reflexivity.
          + rewrite agtN_active, active_upd_meta. rewrite (qx_lo _ _ _ _ QXI) by lia. exact (qa_actj _ _ _ Q2). }
      intros EZ. specialize (QXI EZ). constructor.
      * intros sc Hsc. unfold sts'. rewrite fin_active. replace (sc =? j) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite agtN_active, active_upd_meta. rewrite (qx_lo _ _ _ _ QXI) by lia. rewrite AX2. apply A2. lia.
      * unfold sts'. rewrite fin_active, Z.eqb_refl. reflexivity.
      * intros x PX NH FH. pose proof (NOTMT x PX FH) as NEx. unfold sts'. rewrite fin_metas by exact NEx.
        rewrite agtN_metas, (aptr_eqb_neq _ _ NEx). rewrite lookup_upd_meta, (aptr_eqb_neq _ _ NEx).
        rewrite (qx_frame _ _ _ _ QXI).
        -- rewrite MX2 by exact NEx. apply MX. apply NH. lia.
        -- rewrite MX2 by exact NEx. apply KX. exact PX.
        -- intros sc Hsc. apply NH. lia.
        -- rewrite (qa_free _ _ _ Q2). discriminate.
      * intros x PX. unfold sts'. destruct (aptr_eqb_spec x mt) as [->|NEx]; [apply fin_metas_m|].
        rewrite fin_metas by exact NEx. rewrite agtN_metas, (aptr_eqb_neq _ _ NEx). rewrite lookup_upd_meta, (aptr_eqb_neq _ _ NEx).
        apply (qx_keys _ _ _ _ QXI). rewrite MX2 by exact NEx. apply KX. exact PX.
Qed.

Lemma QE_st0_any j : 0 <= j -> QE st0 j.
Proof.
  intros Hj. destruct QE_st0 as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]. constructor; auto. lia.
Qed.

Lemma lowbit_0 : lowbit 0 = 0. Proof. reflexivity. Qed.

Theorem malloc_core_shape n : 0 < n < MMAP_THRESHOLD ->
  exists len K, malloc_core lay_none st0 n = SVis (EMmap 0 len PROT_RW MAPF') K
    /\ 0 < len <= 2^20
    /\ forall z, exists stf sts c,
         K z = (if negb (mmap_answer_ok (live_ranges st0) len z) then bad_answer (ret (st0, @None (aptr * Z)))
                else if is_err z then ret (stf, None) else ret (sts, Some (c, 0))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
  replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold malloc_small_ctrl.
  destruct (size_to_class_ok n ltac:(lia)) as [SC FIT].
  set (sc := size_to_class n) in *.
  set (sc' := match active st0 sc with
              | Some _ => sc
              | None => if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st0 sc =? 0)
                        then if (match active st0 (Z.lor sc 1) with
                                 | Some _ => let ar := get_meta_rec st0 (default (0%N, -1) (active st0 (Z.lor sc 1))) in
                                             if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st0 (Z.lor sc 1) + 3 else usage st0 (Z.lor sc 1)
                                 | None => usage st0 (Z.lor sc 1) + 3 end) <=? 12
                             then Z.lor sc 1 else sc
                        else sc
              end).
  assert (SC' : 0 <= sc' < 48 /\ n + IB <= UNIT * size_class sc').
  { subst sc'. destruct (active st0 sc); [auto|].
    destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st0 sc =? 0)) eqn:E; [|auto].
    destruct (_ <=? 12); [|auto].
    apply andb_true_iff in E as [E E5]. apply andb_true_iff in E as [E E4]. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc) by (lia || exact E4). split; [lia|].
    pose proof (size_class_le sc (sc + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  destruct SC' as [SC1 FIT1].
  assert (MASK : match active st0 sc' with Some gp => m_avail (get_meta_rec st0 gp) | None => 0 end = 0).
  { destruct (active st0 sc') as [gp|] eqn:HA; [| reflexivity].
    destruct (H0_act sc' gp HA) as (r & E & (EX & _) & _). rewrite (get_meta_rec_of_lookup _ _ _ E). exact EX. }
  change (match active st0 sc with
          | Some _ => sc
          | None => if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st0 sc =? 0)
                    then if (match active st0 (Z.lor sc 1) with
                             | Some _ => let ar := get_meta_rec st0 (default (0%N, -1) (active st0 (Z.lor sc 1))) in
                                         if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st0 (Z.lor sc 1) + 3 else usage st0 (Z.lor sc 1)
                             | None => usage st0 (Z.lor sc 1) + 3 end) <=? 12
                         then Z.lor sc 1 else sc
                    else sc
          end) with sc'.
  clearbody sc'. rewrite MASK. rewrite lowbit_0. change (negb (0 =? 0)) with false.
  match goal with |- exists len K, ?lhs = _ /\ _ =>
    match lhs with context [alloc_slot lay_none FUEL st0 sc' n ?kk ?bb] =>
      replace lhs with (alloc_slot lay_none FUEL st0 sc' n kk bb) by (destruct (active st0 sc'); reflexivity);
      destruct (alloc_slot_shape FUEL sc' st0 n _ kk bb) as (len & K & EQ & LB & PROP)
    end end.
  - unfold FUEL. cbn. lia.
  - exact SC1.
  - lia.
  - exact FIT1.
  - apply QE_st0_any. lia.
  - exists len, K. split; [exact EQ|]. split; [exact LB|].
    intros z. destruct (PROP z) as (stf & sts & g & EK & QXI). exists stf, sts, g. rewrite EK.
    destruct (negb (mmap_answer_ok (live_ranges st0) len z)); [reflexivity|].
    destruct (is_err z) eqn:EZ; cbv beta.
    + change (-1 <? 0) with true. reflexivity.
    + change (0 <? 0) with false. cbv iota. rewrite (qx_j _ _ _ _ (QXI eq_refl)). reflexivity.
Qed.
End SITEC.

Lemma sbind_vis {R S} e (k : Z -> M R) (f : R -> M S) : sbind (SVis e k) f = SVis e (fun z => sbind (k z) f).
Proof. reflexivity. Qed.

Lemma live_ranges_strip st : live_ranges (strip st) = live_ranges st.
Proof. reflexivity. Qed.

Theorem T2_C_sim : forall cs L n, PHI cs -> SIMREL cs L -> 0 < n < MMAP_THRESHOLD ->
  exists len kont, cmalloc cs n = SVis (EMmap 0 len PROT_RW MAPF') kont /\ 1 <= len <= 2 ^ 21
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF') a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Proof.
  intros cs L n HP CR Hn.
  destruct CR as (st & BL & LS & Ecs & INV & _).
  pose proof (CF_strip st (INVL_CF _ _ _ _ _ INV)) as CF0. rewrite Ecs in CF0.
  destruct (malloc_core_shape cs CF0 HP n Hn) as (len & K & EQ & LB & PROP).
  exists len, (fun z => sbind (K z) (fun x : mstate * option (aptr * Z) => let (st1, r) := x in
                 ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end))).
  split. { unfold cmalloc. rewrite EQ. reflexivity. }
  split; [lia|].
  assert (LR : live_ranges cs = live_ranges st) by (rewrite <- Ecs; apply live_ranges_strip).
  split.
  - intros z Hz. destruct (PROP z) as (stf & sts & c & EK). rewrite EK.
    replace (mmap_answer_ok (live_ranges cs) len z) with true by (symmetry; unfold mmap_answer_ok; rewrite Hz; reflexivity). cbn [negb].
    replace (is_err z) with true.
    2:{ symmetry. unfold is_err. unfold is_errno_form in Hz. apply andb_true_iff in Hz as [Hz _]. apply Z.leb_le in Hz. apply Z.ltb_lt. unfold TWO64 in *. lia. }
    exists (strip stf). reflexivity.
  - intros a Ha Hok. destruct (PROP a) as (stf & sts & c & EK). rewrite EK.
    unfold answer_ok in Hok. change (Z.land MAPF' MAP_FIXED =? 0) with true in Hok. cbv iota in Hok.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV)) in Hok. rewrite <- LR in Hok. rewrite Hok, Ha. cbn [negb].
    exists (strip sts), (slot_of sts c 0). reflexivity.
Qed.

Theorem T2_Cbig_sim : forall cs L n, PHI cs -> SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  exists len kont, cmalloc cs n = SVis (EMmap 0 len PROT_RW MAPF') kont /\ n + IB + UNIT <= len <= n + IB + UNIT
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF') a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Proof.
  intros cs L n HP CR Hn Hov.
  destruct CR as (st & BL & LS & Ecs & INV & _).
  pose proof (CF_strip st (INVL_CF _ _ _ _ _ INV)) as CF0. rewrite Ecs in CF0.
  assert (LR : live_ranges cs = live_ranges st) by (rewrite <- Ecs; apply live_ranges_strip).
  destruct HP as (PI & PC & PA & PF & PG).
  unfold cmalloc, malloc_core. rewrite Hov. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  rewrite sbind_vis. eexists (n + IB + UNIT), _. split; [reflexivity|]. split; [lia|].

  assert (AMQ : forall a R (k : mstate -> optr -> M R) bail,
            let st2 := step_seq (fst (new_region RKGroup a (n + IB + UNIT) cs)) in
            exists st3 g, alloc_meta st2 k bail = k st3 (Some g)).
  { intros a R k bail st2.
    assert (CI : c_init_done (s_ctx st2) = 1) by (unfold st2; autorewrite with mst; exact PI).
    assert (SM : s_metas st2 = s_metas cs) by (unfold st2; autorewrite with mst; reflexivity).
    destruct PF as [[HN _]|(f & HF & Hf)].
    - destruct (cf_avail _ CF0 ltac:(lia)) as (q & Eq & _ & _).
      eexists _, _. apply (alloc_meta_take st2 _ k bail CI); unfold st2; autorewrite with mst; [exact HN| lia| exact Eq].
    - eexists _, _. apply (alloc_meta_free st2 f k bail CI); [unfold st2; autorewrite with mst; exact HF|].
      rewrite (get_meta_rec_ext cs st2 f SM), (get_meta_rec_of_lookup _ _ _ Hf). reflexivity. }
  split.
  - intros z Hz. cbv beta.
    replace (mmap_answer_ok (live_ranges cs) (n + IB + UNIT) z) with true by (symmetry; unfold mmap_answer_ok; rewrite Hz; reflexivity). cbn [negb].
    replace (is_err z) with true.
    2:{ symmetry. unfold is_err. unfold is_errno_form in Hz. apply andb_true_iff in Hz as [Hz _]. apply Z.leb_le in Hz. apply Z.ltb_lt. unfold TWO64 in *. lia. }
    eexists. reflexivity.
  - intros a Ha Hok. cbv beta.
    unfold answer_ok in Hok. change (Z.land MAPF' MAP_FIXED =? 0) with true in Hok. cbv iota in Hok.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV)) in Hok. rewrite <- LR in Hok. rewrite Hok, Ha. cbn [negb].
    change (new_region RKGroup a (n + IB + UNIT) cs) with (fst (new_region RKGroup a (n + IB + UNIT) cs), s_next_rid cs). cbv beta iota.
    destruct (AMQ a _ (fun st3 go =>
          match go with
          | Some g =>
              let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                           (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (s_next_rid cs, 0)) mr))))))) st3 in
              let st5 := put_group (s_next_rid cs, 0) (Some g) (group_active_idx st4 (s_next_rid cs, 0)) (lh_hdr lay_none st4 (s_next_rid cs, 0)) in
              let st6 := add_slots g (s_next_rid cs, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
              let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
              ret (st7, Some (g, 0))
          | None => SVis (EMunmap a (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region (s_next_rid cs) st3, None) else bad_answer (ret (cs, @None (aptr * Z))))
          end) (ret (cs, @None (aptr * Z)))) as (st3 & g & EQ).
    cbv zeta in EQ. rewrite EQ. cbv beta iota zeta. eexists _, _. reflexivity.
Qed.

Theorem T2_C : forall cs L n, PHI cs -> creach cs L -> 0 < n < MMAP_THRESHOLD ->
  exists len kont, cmalloc cs n = SVis (EMmap 0 len PROT_RW MAPF') kont /\ 1 <= len <= 2 ^ 21
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF') a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Proof. intros cs L n HP CR Hn. exact (T2_C_sim cs L n HP (creach_sim cs L CR) Hn). Qed.

Theorem T2_Cbig : forall cs L n, PHI cs -> creach cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false ->
  exists len kont, cmalloc cs n = SVis (EMmap 0 len PROT_RW MAPF') kont /\ n + IB + UNIT <= len <= n + IB + UNIT
    /\ (forall z, is_errno_form z = true -> exists cs1, kont z = SRet (cs1, None))
    /\ (forall a, is_err a = false -> answer_ok L (EMmap 0 len PROT_RW MAPF') a = true -> exists cs2 c, kont a = SRet (cs2, Some c)).
Proof. intros cs L n HP CR Hn Hov. exact (T2_Cbig_sim cs L n HP (creach_sim cs L CR) Hn Hov). Qed.

End CEIL.

Notation MAPF' := (MAP_PRIVATE + MAP_ANON).
