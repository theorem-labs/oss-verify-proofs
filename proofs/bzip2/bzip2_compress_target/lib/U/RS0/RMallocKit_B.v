(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep Arr SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Export MallocKit_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require Import RMallocRep RMallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.



(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rrepfoot (st : mstate) (a : Z) : Prop :=
  (RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
  \/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).

Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a. Proof. intros; left; assumption. Qed.
Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a. Proof. intros; right; left; assumption. Qed.
Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
Lemma rrepfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> rrepfoot st a.
Proof. intros; do 6 right; left. exists rid, r, v. auto. Qed.
Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a. Proof. intros; do 7 right; left; assumption. Qed.
Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a. Proof. intros; do 8 right; assumption. Qed.

Lemma rbytes_at_agree : forall m m' A bs,
  bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  (intros m m' A bs; cps_intros (H0 & H1 & HB); intros AG). split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rrw_cells_agree : forall m m' A cs,
  rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono rsegs m m' -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_transport; eauto.
Qed.

Lemma ru64arr_agree : forall m m' A ws,
  u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono rsegs m m' -> u64arr rsegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
  eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

Lemma ru8arr_agree : forall m m' A bs,
  u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono rsegs m m' -> u8arr rsegs m' A bs.
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_unowned : forall st m m' W,
  rmrep st m -> munch W m m' -> wmono rsegs m m' -> ivs_avoid W (rrepfoot st) -> rmrep st m'.
Proof.
  (intros st m m' W; cps_intros (WF & CX & GL & AR & GR & SH); intros MU WM HW).
  cps_pose WF as (Hres & WR & DJ & WA & WG).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - cps_destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - cps_destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. cps_destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. cps_destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      cps_pose Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma rmrep_put_meta_frame : forall st m m' g mr',
  rmrep st m -> meta_slot st g ->
  munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' (conc st g) (meta_cells st mr') ->
  rmrep (put_meta g mr' st) m'.
Proof.
  (intros st m m' g mr' MR; cps_intros (a & ar & k & Ha & Hk & Eg); intros MU WM CH).
  cps_pose MR as (WF & CX & GL & AR & GR & SH).
  cps_destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). bz_ceil.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  cps_pose WF as (Hres & WR & DJ & WA & WG).
  cps_destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
  pose proof (round_up_pg_ge (r_len ra)) as RU.
  (* [comment removed for export] *)
  assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
  assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  assert (TC : forall A cs, rw_cells rsegs m A cs ->
            (A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
    cps_destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. unfold RCTX in *.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | cbn; lia].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
    + apply TC; [exact C6 | cbn; lia].
  - cps_destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros a' ar' Ha'. cbn in Ha'.
    cps_destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    destruct (decide (a' = a)) as [->|NEa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'.
      cps_destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
      split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k' Hk'. rewrite Hmc, get_meta_rec_put.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
      * apply TC; [exact PD| cbn; lia].
    + assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
      cps_destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
      * apply TC; [exact PD| cbn; lia].
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    cps_destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    cps_destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
    destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
    destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [|exact I].
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
    rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_ctx_frame' : forall st st' m m',
  rmrep st m -> munch [(RCTX, RCTX + 928)] m m' -> wmono rsegs m m' ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
  rmrep_ctx st' m' -> rmrep st' m'.
Proof.
  (intros st st' m m'; cps_intros (WF & CX & GL & AR & GR & SH); intros MU WM ER EM EA EG ES ERs CX').
  cps_pose WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
  assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  unfold RCTX in *.
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - cps_destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
    cps_destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    cps_destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len ra)).
    cps_destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
    + apply TC; [exact A1| cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
    + apply TC; [exact A3| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    cps_destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    cps_destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len rb)).
    cps_destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
    cps_destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof.
  (intros st m p; cps_intros (WF & CX & GL & AR & GR & SH)). cps_pose WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
    eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof.
  (intros st m v; cps_intros (WF & CX & GL & AR & GR & SH)).
  assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 80 + 8 * sc) ->
  ov_read_bytes rsegs m a 8 = Some (le8 (pw st (active st sc))).
Proof.
  (intros st m sc a; cps_intros (_ & (_ & C2 & _) & _); intros Hsc ->).
  eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 464 + 8 * sc) ->
  ov_read_bytes rsegs m a 8 = Some (le8 (wz (usage st sc))).
Proof.
  (intros st m sc a; cps_intros (_ & (_ & _ & C3 & _) & _); intros Hsc ->).
  eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa (RCTX + 880 + i) ->
  ov_read_bytes rsegs m a 1 = Some [b8 (bounces st i)].
Proof.
  (intros st m i a; cps_intros (_ & (_ & _ & _ & _ & C5 & _) & _); intros Hi ->).
  eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.

Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa (RCTX + 912) ->
  ov_read_bytes rsegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof.
  (intros st m a; cps_intros (_ & (_ & _ & _ & _ & _ & C6) & _); intros ->).
  apply (rw_cells_read_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rmeta_slot_bounds : forall st m g, rmrep st m -> meta_slot st g ->
  0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ (conc st g + 40 <= 0x10000 \/ 0x66000 <= conc st g) /\ conc st g mod 4 = 0
  /\ conc st g mod 4096 >= 24.
Proof.
  (intros st m g MR; cps_intros (a & ar & k & Ha & Hk & Eg)). pose proof MR as (WF & _). cps_pose WF as (_ & WR & _).
  cps_destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  cps_destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  bz_ceil; unfold AREA_HDR, META_SIZE, NSLOTS in *. pose proof (round_up_pg_ge (r_len ra)).
  rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.

Lemma rgroup_bounds : forall st m b gh, rmrep st m -> (s_groups st) !! b = Some gh ->
  0 <= conc st b /\ conc st b + 16 <= alloc_ceiling /\ (conc st b + 16 <= 0x10000 \/ 0x66000 <= conc st b) /\ conc st b mod 16 = 0.
Proof.
  intros st m b gh MR Hb. pose proof MR as (WF & _). cps_pose WF as (_ & WR & _).
  cps_destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
  cps_destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  bz_ceil. pose proof (round_up_pg_ge (r_len r)).
  rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  (lo <= a < sp
   \/ RCTX <= a < RCTX + 928
   \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
Lemma rfree_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> rfree_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

Lemma rfree_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
  conc st q <= a < conc st q + 40 -> rfree_fp st lo sp a.
Proof.
  (intros st m lo sp q a MR; cps_intros (ar & arr & k & Har & Hk & Eq); intros Ha). pose proof MR as (WF & _).
  cps_destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.

(* [comment removed for export] *)
Lemma rfree_fp_mono : forall st st' lo sp sp' a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
  (forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
  sp' <= sp ->
  rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. cps_destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
  - right; left. cps_destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
  - right; right. cps_destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

Lemma rpres_except_of_munch' : forall C W m m',
  munch W m m' -> wmono rsegs m m' ->
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
  rpres_except C m m'.
Proof.
  intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
  intros a _ HC. eapply outside_of_cover; eauto.
Qed.

Lemma rpres_except_of_munch_cov : forall C W m m',
  munch W m m' -> wmono rsegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

Lemma rctxW_avoid : forall A n, (A + n <= RCTX \/ RCTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
  0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
  intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

Lemma rmrep_ctx_frameW :
  (rw_cells rsegs m' RCTX (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 80 <= lo \/ hi <= RCTX)) ->
  (u64arr rsegs m' (RCTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> RCTX + 464 <= lo \/ hi <= RCTX + 80)) ->
  (u64arr rsegs m' (RCTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> RCTX + 848 <= lo \/ hi <= RCTX + 464)) ->
  (u8arr rsegs m' (RCTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> RCTX + 880 <= lo \/ hi <= RCTX + 848)) ->
  (u8arr rsegs m' (RCTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> RCTX + 912 <= lo \/ hi <= RCTX + 880)) ->
  (rw_cells rsegs m' (RCTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 928 <= lo \/ hi <= RCTX + 912)) ->
  rmrep st' m'.
Proof.
  intros H1 H2 H3 H4 H5 H6.
  cps_pose MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
  assert (CX' : rmrep_ctx st' m').
  { unfold rmrep_ctx. split; [|split; [|split; [|split; [|split]]]].
    - destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
  eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
  clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.

(* [comment removed for export] *)
Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rmrep st' m'.

End ACeilS1.
