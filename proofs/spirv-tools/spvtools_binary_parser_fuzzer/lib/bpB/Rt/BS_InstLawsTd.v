(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSymDrive BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX BLFrame BMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BakeStackRep BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BecLazy BsDepotInv BsDepotHash BG_Malloc2 BG_MallocLarge3 BG_MallocAll BS_InstDefs RtB_Iface BS_InstLaws3.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition TDLOC : Z := 0x6c5828.

Section LawsTd.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Lemma td_window_bridge : forall (s : ast) (LB : list (Z * Z)), BllocRep.aclient_write_ok s LB (TDLOC, TDLOC + 8).
  Proof.
    intros s LB. right; right; right; left. cbn [fst snd]. unfold TDLOC, ARW_LO, AIMG_TOP.
    split; [lia|]. split; [lia|]. intros a Ha.
    unfold astatic, AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT,
      AHOOKS, AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2. lia.
  Qed.

  Lemma td_protected0 : forall x LB m a,
    as_RHEAP (KHp p) x LB m -> TDLOC <= a < TDLOC + 8 -> iprotected0 p x a -> False.
  Proof.
    intros x LB m a R Ha PR.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    destruct HA as (AR & ND & EQ). pose proof (proj1 AR) as OK.
    pose proof (proj1 OK) as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; lia)) as [FE1 FE2]. acb.
    destruct TH as (_ & _ & DB0 & DB8 & DB32 & DKO). unfold kPageSize in DKO.
    pose proof T2 as TKO. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, kPageSize in TKO. unfold kPageSize in T3.
    pose proof DPL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & QSEC & QA1 & QA2 & QA3 & QA4).
    pose proof (aapp_env _ _ QA1 ltac:(lia)) as [NB1 NB2]. pose proof (aapp_env _ _ QA3 ltac:(lia)) as [SB1 SB2].
    unfold iprotected0, ALIBCPGSZ, AGOT_SSP, ACFLAGS, BsIface.ATP in PR. unfold TDLOC in Ha.
    unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in DKO.
    clear - Ha PR DKO NB1 SB1 TKO. lia.
  Qed.

  Lemma td_ahm : forall x LB m a,
    as_RHEAP (KHp p) x LB m -> TDLOC <= a < TDLOC + 8 ->
    (AIMM_OBJ <= a < AIMM_OBJ + 8) \/ (ip_TB p <= a < ip_TB p + AHM_SIZE) -> False.
  Proof.
    intros x LB m a R Ha PR.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM).
    pose proof AHM as (AH1 & AH2 & AH3 & AHP & AHA & AHK & AHC & AT1 & AT2 & AT3 & AT4 & AT5 & AT6 & AT7 & ATS).
    acb.
    assert (TKO : 4096 <= ip_TB p /\ (ip_TB p + AHM_SIZE <= AIMG_LO \/ AIMG_TOP <= ip_TB p) /\ ~ (ALOWSH_LO <= ip_TB p + AHM_SIZE - 1 /\ ip_TB p < AHI_LO)).
    { clear - AHK AHC ACEILB. unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, AHM_SIZE in *. lia. }
    unfold AIMM_OBJ, AHM_SIZE in PR. unfold AHM_SIZE in TKO. unfold TDLOC in Ha.
    unfold AIMG_LO, AIMG_TOP in TKO. clear - Ha PR TKO. lia.
  Qed.

  Lemma td_protected : forall x LB m a,
    as_RHEAP (KHp p) x LB m -> TDLOC <= a < TDLOC + 8 -> iprotected p x a -> False.
  Proof.
    intros x LB m a R Ha [PR|PR]; [exact (td_protected0 x LB m a R Ha PR) | exact (td_ahm x LB m a R Ha PR)].
  Qed.

  Theorem inst_RHEAP_td : forall x LB m m',
    as_RHEAP (KHp p) x LB m -> munch [(TDLOC, TDLOC + 8)] m m' -> wmono asegs m m' -> as_RHEAP (KHp p) x LB m'.
  Proof.
    intros x LB m m' R MU WM.
    pose proof R as (HA & IDS & LEN & AWV & FLX & DEP0 & DPL & DTR & DJ1 & DJ2 & EF & MF & DJD & TH & TLS & ASV & DAP & DSEC & PINV & AHM). pose proof (proj1 DAP) as DSB.
    assert (AG : agree_on (iprotected p x) m m').
    { intros a Pa Ha. apply MU. rewrite wa_unsigned by lia. cbn. split; [| exact I].
      intros K. exact (td_protected x LB m a R K Pa). }
    cbn [as_RHEAP KHp]. unfold IRHEAP. cbv zeta.
    split.
    {   eapply (ARHEAP_frame_ok _ _ _ _ _ HA MU WM). apply Forall_cons; [| apply Forall_nil].
      exact (td_window_bridge (i_s x) (lbp LB)). }
    split; [exact IDS|]. split; [exact LEN|].
    split; [exact (awin_vis_wmono _ _ _ AWV WM)|].
    split.
    {   destruct FLX as (F1 & F2 & (g & F3) & F4 & (b & F5)).
      split; [| split; [| split; [| split]]].
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F1|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F2|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - exact (sspguard_rw_any m').
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F4|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia.
      - exists b. eapply (rw_cells_transport_pt _ _ _ AG WM); [exact F5|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia. }
    split.
    {   destruct DEP0 as [DWF DM]. split; [exact DWF|]. exact (depot_mem_frame p x _ m m' DWF DM AG WM eq_refl eq_refl). }
    split; [exact DPL|]. split; [exact DTR|]. split; [exact DJ1|]. split; [exact DJ2|]. split; [exact EF|]. split; [exact MF|]. split; [exact DJD|].
    split.
    {   destruct TH as (A1 & A2 & A3). split; [| split; [| exact A3]].
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact A1|]. intros a Ha. unfold iprotected, iprotected0, BsIface.ATP, BllocRep.ATP in *. cbn in Ha. lia.
      - eapply (rw_cells_transport_pt _ _ _ AG WM); [exact A2|]. intros a Ha. unfold iprotected, iprotected0, BsIface.ATP, BllocRep.ATP in *. cbn in Ha. lia. }
    split.
    {   destruct TLS as (tb & te & T48). exists tb, te.
      eapply (rw_cells_transport_pt _ _ _ AG WM); [exact T48|]. intros a Ha. unfold iprotected, iprotected0. cbn in Ha. lia. }
    split; [exact ASV|]. split; [exact DAP|]. split; [exact DSEC|]. split; [exact PINV|].
    {
      pose proof AHM as (AH1 & AH2 & AH3 & AHREST).
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH1|]; intros a Ha; unfold iprotected; cbn in Ha; right; left; exact Ha|].
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH2|]; intros a Ha; unfold iprotected; cbn in Ha; right; right; unfold AHM_SIZE, AHM_B1 in *; lia|].
      split; [eapply (rw_cells_transport_pt _ _ _ AG WM); [exact AH3|]; intros a Ha; unfold iprotected; cbn in Ha; right; right; unfold AHM_SIZE, AHM_B2 in *; lia|].
      exact AHREST. }
  Qed.

  Theorem inst_RFS_td : forall LF m m',
    as_RFS (KHp p) LF m -> munch [(TDLOC, TDLOC + 8)] m m' -> wmono asegs m m' -> as_RFS (KHp p) LF m'.
  Proof.
    intros LF m m' R MU WM. cbn [as_RFS KHp] in R |- *.
    destruct R as (G & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS).
    pose proof G as (G1 & G2 & G3 & G4).
    assert (FW : Forall (fun iv : Z * Z => snd iv <= TDLOC + 8) [(TDLOC, TDLOC + 8)]) by (apply Forall_cons; [cbn; lia | apply Forall_nil]).
    split; [exact G|]. split.
    { eapply rw_cells_out; [exact TLS| exact MU| exact WM| exact FW|]. intros lo hi P. cbn in P |- *. unfold TDLOC, BsIface.ATP, BllocRep.ATP in *. lia. }
    split.
    { exists h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10. eapply rw_cells_out; [exact HDR| exact MU| exact WM| exact FW|]. intros lo hi P. cbn in P |- *. unfold TDLOC, AIMG_TOP in *. lia. }
    split; [exact SL|]. split; [exact ND|]. split.
    { intros k pos S. eapply rw_cells_out; [exact (FL k pos S)| exact MU| exact WM| exact FW|]. intros lo hi P. cbn in P |- *.
      pose proof (flag_addr_range (ip_fsb p) k pos S). unfold AFS_FLAGS, TDLOC, AIMG_TOP in *. lia. }
    split.
    { eapply stk_high_transport; [exact STF| exact WM|]. unfold AIMG_TOP, AFS_HDR in *. lia. }
    eapply stk_high_transport; [exact STS| exact WM|]. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val. lia.
  Qed.

  Theorem inst_td_law : forall s LB LF B m m',
    munch [(TDLOC, TDLOC + 8)] m m' -> wmono asegs m m' ->
    (as_RHEAP (KHp p) s LB m -> as_RHEAP (KHp p) s LB m')
    /\ (as_RFS (KHp p) LF m -> as_RFS (KHp p) LF m')
    /\ (as_rauxv_ok (KHp p) m B -> as_rauxv_ok (KHp p) m' B).
  Proof.
    intros s LB LF B m m' MU WM.
    split; [intros R; exact (inst_RHEAP_td s LB m m' R MU WM)|].
    split; [intros R; exact (inst_RFS_td LF m m' R MU WM)|].
    intros R. exact R.
  Qed.
End LawsTd.
