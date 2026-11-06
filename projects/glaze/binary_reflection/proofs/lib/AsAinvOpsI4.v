(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3e.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Section I4.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  Definition foot_ialloc4 (a : Z) : Prop :=
    (IA_FLAG bt <= a < IA_FLAG bt + 4) \/ (IA_INST bt <= a < IA_INST bt + IASZ) \/ CEIL <= a.
  Definition OPS_REP_ialloc_init4 : Prop := forall st Lc FF M M' mdl,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> a_ialloc st = false ->
    agrees_off foot_ialloc4 M M' ->
    byteZ SG M' (IA_FLAG bt) 1 -> byteZ SG M' (IA_FLAG bt + 1) 0 ->
    fillZ SG M' (IA_INST bt + 8) (IA_INST bt + 8 + 0x40000) 0 ->
    cellZ SG M' (IA_INST bt + 0x40dc0) 8 PG -> cellZ SG M' (IA_INST bt + 0x40dc8) 8 (IA_INST bt + 0x40dd0) ->
    Rep bt (op_ialloc_init st) Lc FF M' mdl.

  Theorem OPS_REP_ialloc_init4_pf : OPS_REP_ialloc_init4.
  Proof.
    intros st Lc FF M M' mdl W R HF AGR B1 B2 FZ0 C1 C2.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & (LV1 & LV2 & LV3) & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & PR & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & CC & U1 & U2 & U3 & U4 & DC & DT & DR & DJ).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10.
    (* [comment removed for export] *)
    assert (AGZ : forall i, 0 <= i < 2 ^ 64 -> ~ (IA_FLAG bt <= i < IA_FLAG bt + 8) -> ~ (IA_INST bt <= i < IA_INST bt + IASZ) -> i < CEIL -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr N1 N2 N3. apply AGF; [| exact Hr]. intros Hf. unfold foot_ialloc4 in Hf. uilia. }
    (* [comment removed for export] *)
    assert (FH : ia_img_lo IA <= IA_FLAG bt /\ IA_FLAG bt + 8 <= ia_img_hi IA /\ ia_img_lo IA <= IA_INST bt /\ IA_INST bt + IASZ <= ia_img_hi IA).
    { destruct Q4 as (plo & phi & Hin & H1 & H2). destruct (PR plo phi (or_introl Hin)).
      destruct Q5 as (plo' & phi' & Hin' & H1' & H2'). destruct (PR plo' phi' (or_introl Hin')). (lazymatch goal with |- ?G => let G' := eval unfold IA_FLAG, IA_INST in G in change_no_check G' end). lia. }
    assert (HEAPfree : forall i, 0 <= i -> i < CEIL -> ~ (ia_img_lo IA <= i < ia_img_hi IA) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi0 Hi1 NH. destruct FH as (FH1 & FH2 & FH3 & FH4). apply AGZ; uilia. }
    assert (DYNK : forall i, dyn_kind bt st i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hd. destruct (dyn_kind_facts bt st Lc FF W i Hd) as (D1 & D2 & D3 & _). apply HEAPfree; [lia | exact D2 | exact D3]. }
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    (* [comment removed for export] *)
    pose proof (img_pw bt st Lc FF W) as PWI. unfold img_ranges in PWI. cbn [AsAinvDefs3.PW seps fst snd] in PWI.
    destruct PWI as ((_ & _ & S03 & S04 & _ & _ & _ & _) & (_ & S13 & S14 & _ & _ & _ & _) & (S23 & S24 & _ & _ & _ & _) & (_ & S35 & S36 & S37 & _) & (S45 & S46 & S47 & _) & _).
    assert (IMGR : forall i, 0 <= i < AS_LO ->
              (ia_instance IA + 112 <= i < ia_instance IA + 992) \/ (ia_depot_tab IA <= i < ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15)
              \/ (ia_stackstore IA <= i < ia_stackstore IA + 16 + 16 * 2 ^ 12) \/ (bt_tls_fs bt <= i < bt_tls_fs bt + 16)
              \/ (ia_rtc_sb IA <= i < ia_rtc_sb IA + 8) \/ (ia_rtc_uar IA <= i < ia_rtc_uar IA + 4) ->
              M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi Hr. unfold IA_FLAG, IA_INST in AGZ. apply AGZ; [clear -Hi; uilia | | | clear -Hi; uilia]; intros X;
      (destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]; [clear -Hi Hr X S03 S04 | clear -Hi Hr X S13 S14 | clear -Hi Hr X S23 S24
                                                 | clear -Hi Hr X S35 S45 | clear -Hi Hr X S36 S46 | clear -Hi Hr X S37 S47]; lia). }
    clear S03 S04 S13 S14 S23 S24 S35 S36 S37 S45 S46 S47.
    (* [comment removed for export] *)
    assert (CONSTfree : forall c i, In c (bt_consts bt) -> fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c i Hc Hi. rewrite Forall_forall in DC, YC, CC. pose proof (DC c Hc i Hi) as ND. destruct (YC c Hc) as [R0 R1].
      unfold img_dyn, IA_FLAG, IA_INST in ND, AGZ. apply AGZ; [clear -R0 R1 Hi; lia | | |]; [intros X; apply ND | intros X; apply ND |]; [do 6 right; left; exact X | do 7 right; exact X |].
      destruct (CC c Hc) as [CV|CV]; [destruct (priv_cover_wins bt st Lc FF W _ _ i CV Hi) as [_ LT] | destruct (const_cover_wins bt st Lc FF W _ _ i CV Hi) as [_ LT]]; clear -LT I2; uilia. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    (lazymatch goal with |- ?G => let G' := eval unfold op_ialloc_init in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. exact (CONSTfree c0 i Hc0 Hi). }
    split. { change (rep_instance bt st M'). pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
             eapply rep_instance_frame; [exact DEF | exact R2 | uilia | uilia | uilia | uilia | exact S1 |].
             intros i Hi Hr. unfold instance_cells, IB in Hi.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]].
             7: apply DYNK; apply (dyn_kind_fixed bt st _ _ i IN8); uilia.
             all: apply IMGR; uilia. }
    split. { change (rep_thread bt st M'). eapply rep_thread_frame; [exact DEF | exact R3 | uilia | uilia | uilia | uilia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in Hi. apply DYNK.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]]; first [apply (dyn_kind_fixed bt st _ _ i INT); uilia | apply (dyn_kind_fixed bt st _ _ i INC); uilia]. }
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg (set_ialloc st) c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | uilia | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. unfold foot_region in Hi. apply DYNK. apply (dyn_kind_space bt st Lc FF W). uilia. }
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). uilia. }
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3). apply DYNK. apply (dyn_kind_space bt st Lc FF W). uilia. }
    split. { change (a_tq (set_ialloc st)) with (a_tq st). eapply rep_batches_frame; [exact DEF | exact R5 | intros b0 Hb0; apply BR; apply in_app_iff; left; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; left; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (a_gq (set_ialloc st)) with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). uilia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply DYNK. apply (dyn_kind_dyn bt st _ _ i (sec_dyn st sc Hs)). uilia. }
    split. { change (rep_headers bt st Lc M'). eapply rep_headers_frame; [exact DEF | exact R8 | | |].
             - intros p' n' Hin. destruct (live_range bt st Lc FF W p' n' Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n'). uilia.
             - intros m n' Hin. destruct (quar_item_range bt st Lc FF W m n' Hin) as (A1 & A2 & A3). pose proof (rz_range n'). uilia.
             - intros p' n' i Hown Hfh Hr.
               destruct (hdr_zone bt st Lc FF W p' n' i Hown Hfh) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [apply DYNK; apply (dyn_kind_space bt st Lc FF W); uilia|].
               destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply DYNK. apply (dyn_kind_dyn bt st _ _ i (sec_dyn st sc' Hs')). uilia. }
    split. { change (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). uilia.
             - intros i Hi Hr. unfold foot_depot_static, DEPOT_NIDS, DEPOT_MAP1, DEPOT_TAB, SSOBJ in Hi.
               destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               all: apply IMGR; uilia.
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               apply DYNK. destruct HIn as [Eb | Hnb]; [apply (dyn_kind_fixed bt st _ _ i INN); rewrite Eb; uilia | apply (dyn_kind_dyn bt st _ _ i (node_dyn st bb Hnb)); uilia]. }
    split. { change (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2].
             eapply rep_fake_frame; [exact DEF | exact R10 | uilia | uilia | uilia | uilia | uilia | uilia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). uilia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply DYNK; apply (dyn_kind_fixed bt st _ _ i INFS); uilia.
               + apply IMGR; uilia.
               + apply DYNK; apply (dyn_kind_fixed bt st _ _ i (dtls_member bt st Lc FF W)); uilia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). apply DYNK. apply (dyn_kind_fixed bt st _ _ i INFS). uilia. }
    (* [comment removed for export] *)
    split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_ialloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_ialloc set_ialloc] in G in change_no_check G' end). split; [exact B1|]. split; [exact B2|]. split; [exact FZ0|]. intros _. split; [exact C1 | exact C2]. }
    split. { change (rep_shadow bt st Lc M'). eapply (rep_shadow_frame_grow bt st Lc Lc); [exact DEF | exact R12 | intros g Hg; exact Hg | | | |].
             - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _). uilia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
             - intros c0 i Hc0 Hi Hr. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
               unfold foot_shreg, sh_lo in Hi. apply HEAPfree; clear -Hi E1 E2 E5 E6 E8 SBH I2 X15; Zlia.
             - intros sc i Hs Hi Hr. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). unfold foot_shsec, sh_lo in Hi. apply HEAPfree; clear -Hi A1 A2 I2; Zlia. }
    split; [exact R13|].
    split. { destruct R14 as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & Bu6 & Bu7 & Bu8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa a_reg a_sec a_dep a_shsec set_ialloc] in G in change_no_check G' end).
             repeat (split; [assumption|]).
             change (prim_charge (set_ialloc st)) with (prim_charge st). change (sec_charge (set_ialloc st)) with (sec_charge st).
             change (depot_charge (set_ialloc st)) with (depot_charge st). exact Bu8. }
    split. { intros p' n' Hin'. destruct (R15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f' k' Hin'. frW DEF (R16 f' k' Hin'). }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R17); [uilia | uilia |]. intros i Hi. apply IMGR; uilia. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R18); [uilia | uilia |]. intros i Hi. apply IMGR; uilia. }
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.
End I4.
