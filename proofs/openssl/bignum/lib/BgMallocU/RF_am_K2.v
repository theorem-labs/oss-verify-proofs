(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K F_am_K2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A2 RF_am_K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmrep_agree_but_ctx : forall st st' m m',
  rmrep st m ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
  A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 -> A2.agree_on m m' RVMLOCK 4 ->
  (forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep_ctx st' m' ->
  rmrep st' m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGV AGA AGG AGR CX'.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - destruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
  - destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G6|]. eapply A2.agree_on_sub; [exact AGV| lia| cbn; lia].
  - intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
    unfold rarea_rep. rewrite !Hconc.
    assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
    assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
    rewrite PW. split; [|split].
    + eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
    + eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
    unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
    + eapply RA2.rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

Lemma rmrep_ctx_mid_agree : forall st st' m m',
  rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
                               /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
  s_regions st' = s_regions st ->
  A2.agree_on m m' (RCTX + 80) 832 ->
  u64arr bgusegs m' (RCTX + 80) (actives st') /\ u64arr bgusegs m' (RCTX + 464) (usages st')
  /\ u8arr bgusegs m' (RCTX + 848) (unmap_seqs st') /\ u8arr bgusegs m' (RCTX + 880) (bouncess st').
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
  assert (E3 : usages st' = usages st).
  { unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st).
  { unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
  assert (E5 : bouncess st' = bouncess st).
  { unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
  rewrite E2, E3, E4, E5.
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold RCTX in *.
  split; [|split; [|split]].
  - eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
  conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
  0x10000 <= x < 0x353000 -> ~ (lo <= x < lo + n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.
Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma rgr_conc q : conc st' q = conc st q.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, rgr_lookup_new, Hr. reflexivity.
  - rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma rgr_regions_wf : rregions_wf st'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
    cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
    apply ranges_free_intro. intros b n HI.
    pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
    assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
    destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
  - intros q1 r1 q2 r2 H1 H2 NE.
    assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
              r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
    { intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
      replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
      - left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
        pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
        destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
      - right. exact D. }
    destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + exact (OLD q2 r2 H2' NE2).
    + destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
    destruct (decide (fst a = rid)) as [E|NE].
    + exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
      cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      rewrite LEN in A1. repeat split; try assumption; lia.
    + exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
  - intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
    assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
    exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

Lemma rmrep_grow_region : rmrep st' m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
  assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
  split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    replace (rctx_head_cells st') with (rctx_head_cells st) by (unfold rctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
    replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
    replace (ctx_tail_cells st') with (ctx_tail_cells st).
    2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
  - intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
    unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
    split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
  - intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
    exists w8. rewrite rgr_conc, PW. split; assumption.
  - intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
    destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + exfalso. apply NK. exact Hk.
    + exact (SH q rq H Hk).
Qed.

End GROW.

Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl bgusegs (at_node bgusegs) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl bgusegs (at_node bgusegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.
End WithCeiling0.
