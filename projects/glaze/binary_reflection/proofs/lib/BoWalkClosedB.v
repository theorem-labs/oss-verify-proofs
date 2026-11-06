(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRc4V.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6h OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6m.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFKeep0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section K6N.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable TSDP : Z.
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem rc_bfree_full_map_pf : rc_bfree_stmt bt FXOK arm_full24_map.
  Proof using QHDR_CONST PCELLS CELLSM HTPm BOOTG CELLSPIN RCF RCC CELLNB BT_ia BT_segs MIDENDm FLm PGPm TSDPm TPm TSDP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_bfree_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba rest HFX HH MW W RX EGQ (FULL & NFAR) XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R12 R13r R4 S16 Slo Shi SOK QRK.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    unfold arm_full24 in FULL.
    assert (Hnth : nth_error (a_gq st) 0 = Some (BATCH ba [])) by (rewrite EGQ; reflexivity).
    assert (Hb : In (BATCH ba []) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    destruct (batch_facts bt st Lc FF W _ Hb) as (CV & _ & B1' & B2'). cbn [ba_addr] in CV, B1', B2'.
    assert (Hc : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W BATCHCLASS Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & _).
    destruct CV as (j & Hj0 & Hj1 & Eab). change (csize BATCHCLASS) with 8192 in Hj1, Eab.
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & _ & SB0 & SB1 & SBH & SB16).
    unfold chunk_addr, fa_beg, region_beg, KREGION, KFAOFF in *. change (csize BATCHCLASS) with 8192 in *.
    set (e := j * 8192).
    assert (He : 0 <= e < 2 ^ 32 /\ ba = SBEG + 24 * 2 ^ 32 + e) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); change BATCHCLASS with 24 in *; clear - Hj0 Hj1 Q3 Q2 Eab; lia).
    assert (Ek : compact_of SBEG 24 ba = e / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - He. lia. }
    eapply katD_conseq.
    { apply (dfull_map_katD bt TSDP TPm TSDPm PGPm FLm MIDENDm BT_segs BT_ia CELLNB RCC RCF CELLSPIN BOOTG HTPm CELLSM PCELLS QHDR_CONST
               fx X (fun _ => False) Xd Xdec_false qt qg st Lc FF M mdl R S ret 24 e HH MW W QRK).
      - apply (RepX_mono bt X); [intros z Hz; left; exact Hz | exact RX].
      - exact Hc.
      - exact FULL.
      - exact NFAR.
      - exact CINIT.
      - exact (proj1 He).
      - exact XSUB.
      - intros z [].
      - exact R1.
      - exact RET.
      - exact R2.
      - rewrite R10. (lazymatch goal with |- ?G => let G' := eval unfold T_PC in G in change_no_check G' end). reflexivity.
      - rewrite R11. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. reflexivity.
      - rewrite R12. reflexivity.
      - rewrite R13r. f_equal. clear - He. lia.
      - exact R4.
      - exact Slo.
      - exact Shi.
      - exact SOK. }
    intros c' POST. cbv zeta in POST.
    set (lo := fa_beg SBEG 24 + r_mapped_fa (a_reg st 24)) in *.
    set (st' := add_meter (op_famap st 24) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0) in *.
    destruct POST as (Mi & MF & mdlF & RF & -> & HHF & MWF & MIF & W' & FAR' & RXa & FOOTMi & DEFMi & CHG & KEEP & PCNT & PSLOT & LZF & SEVF & RKF).
    change (cache_max 24) with 2 in *. change (2 / 2) with 1 in *. change (2 - 1) with 1 in *.
    assert (Hc24 : 1 <= 24 <= 30) by (clear; lia).
    assert (CA' : a_cache st' 24 = a_cache st 24) by reflexivity.
    assert (REG' : a_reg st' 24 = REG (r_mapped_user (a_reg st 24)) (r_alloc_user (a_reg st 24)) (r_mapped_fa (a_reg st 24) + KFAMAP) (r_free (a_reg st 24)) (r_uhole (a_reg st 24)) false).
    { (lazymatch goal with |- ?G => let G' := eval unfold st', op_famap, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    pose proof W as (_ & WC & _). destruct (WC 24 Hc24) as (CLEN & _). clear WC. change (cache_max 24) with 2 in CLEN.
    assert (LEN : Z.of_nat (length (a_cache st 24)) = 2) by (change BATCHCLASS with 24 in FULL; change (cache_max 24) with 2 in FULL; clear - FULL CLEN; lia).
    set (st1 := op_drain_top st' 24 1) in *.
    assert (W1 : WFq bt st1 Lc FF qt qg) by (apply (OPS_WFq_drain_top_pf bt st' Lc FF 24 1 qt qg W' Hc24); [rewrite CA'; clear - LEN; lia | exact FAR']).
    assert (GQ1 : a_gq st1 = a_gq st) by reflexivity.
    assert (CA1 : a_cache st1 24 = firstn (Z.to_nat (Z.of_nat (length (a_cache st' 24)) - 1)) (a_cache st' 24)).
    { (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    assert (LEN1 : Z.of_nat (length (a_cache st1 24)) = 1) by (rewrite CA1, CA', length_firstn; clear - LEN; lia).
    assert (Hnth1 : nth_error (a_gq st1) 0 = Some (BATCH ba [])) by (rewrite GQ1; exact Hnth).
    assert (XSUB1 : forall z, X z -> XB bt st1 z) by (intros z Hz; apply XB_drain_top; apply XB_famap_meter; exact (XSUB z Hz)).
    assert (ROOM1 : Z.of_nat (length (a_cache st1 BATCHCLASS)) < cache_max BATCHCLASS) by (change BATCHCLASS with 24; rewrite LEN1; change (cache_max 24) with 2; clear; lia).
    assert (GRF : mem_grows M MF).
    { intros a Ha. destruct (decide (MF a = M a)) as [E | N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]. }
    pose proof RX as (M0 & RP & DX).
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    pose proof RP as (_ & _ & Rt & _). destruct Rt as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _). rewrite BT_segs in TW.
    assert (MDEFT : forall a : word, T <= U a < T + 4096 -> M a <> None).
    { intros a Ha. apply GR0. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (writableZ_def M0 _ _ _ TW). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Ha. }
    assert (RX1 : RepX bt X (op_qbatch_free SBEG st1 0) Lc FF MF mdlF).
    { apply (OPS_REPX_qbatch_free_pf bt X Xd st1 Lc FF (mid_mem bt st' 24 1 Mi MF) MF mdlF mdlF 0%nat ba qt qg W1 RXa Hnth1 ROOM1 XSUB1 XQ).
      - intros i' bp E. discriminate E.
      - intros a Ha. apply GRF. exact (QDEF a Ha).
      - intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold foot_qbatch_free, T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1.
        assert (DEFa : MF a <> None -> (T + 208 + 80 * 24 <= U a < T + 208 + 80 * 24 + 4 \/ T + 208 + 80 * 24 + 16 + 4 * 1 <= U a < T + 208 + 80 * 24 + 16 + 4 * 1 + 4 \/ T + 2768 <= U a < T + 3168 \/ CEIL <= U a) ->
                       ((T + 208 + 80 * 24 <= U a < T + 208 + 80 * 24 + 4 \/ T + 208 + 80 * 24 + 16 + 4 * 1 <= U a < T + 208 + 80 * 24 + 16 + 4 * 1 + 4 \/ T + 2768 <= U a < T + 3168 \/ CEIL <= U a) \/ X (U a)) /\ MF a <> None) by (intros D F; exact (conj (or_introl F) D)).
        destruct (mid_mem_diff bt st' Lc FF qt qg 24 1 W' Hc24 ltac:(clear; lia) FAR' Mi MF a NE) as [I | [NE' NFd]].
        + unfold T_PC, PC_SZ in I. apply DEFa; [apply GRF; apply MDEFT; clear - I; lia | left; exact I].
        + assert (DM : MF a <> None) by exact (DEFMi a NE').
          apply DEFa; [exact DM|].
          destruct (FOOTMi a NE') as [F | []]. unfold FOOTC in F. cbv zeta in F. change (cache_max 24) with 2 in F. change (2 / 2) with 1 in F. change (2 - 1) with 1 in F.
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]];
            [ do 3 right; clear - F Slo; lia | left; clear - F; lia | right; left; clear - F; lia | right; right; left; clear - F; lia
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); left; exact F
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); right; left; exact F
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end); right; right; left; clear - F; lia
            | exfalso; apply NFd; (lazymatch goal with |- ?G => let G' := eval unfold Fdr, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); rewrite REG'; (lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end); do 3 right; clear - F; lia ].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1. exact PCNT.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). change BATCHCLASS with 24. rewrite LEN1, Ek. exact PSLOT.
      - apply same_but_materialized_refl.
      - exact MIF. }
    idtac "PROGRESS K6n: RX1".
    (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_qbatch_free SBEG st1 0), MF, mdlF, RF.
    split; [reflexivity|]. split; [exact HFX|]. split; [exact HHF|]. split; [exact MWF|].
    split; [exact (OPS_WFq_qbatch_free_pf bt st1 Lc FF 0%nat ba qt qg W1 Hnth1 ROOM1)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_cache set_gq] in G in change_no_check G' end); rewrite GQ1, EGQ; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end); rewrite Hnth1; (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top, st', add_meter in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_kact set_cache set_gq set_reg] in G in change_no_check G' end); apply Z.add_0_r|].
    split.
    { split.
      - intros h HL. unfold holes_le in *. (lazymatch goal with |- ?G => let G' := eval unfold op_qbatch_free in G in change_no_check G' end). rewrite Hnth1. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_cache set_gq] in G in change_no_check G' end). intros c' Hc'. apply HL.
        unfold st1, op_drain_top, st', add_meter, op_famap in Hc'. cbn [a_reg set_cache set_reg] in Hc'. unfold fupdZ in Hc'.
        destruct (Z.eqb c' 24) eqn:E; [apply Z.eqb_eq in E; subst c'; cbn [r_uhole r_fhole] in Hc'; destruct Hc' as [H | H]; [left; exact H | discriminate H] | exact Hc'].
      - apply (fk_trans _ st'); [apply (fk_famap_meter bt); left; reflexivity|].
        exact (fk_trans _ _ _ (fk_drain_top bt st' BATCHCLASS 1 (or_introl eq_refl)) (fk_qbatch_free SBEG st1 0)). }
    split; [intros z Hz; exact (XB_qbatch_free bt st1 Lc FF qt qg 0%nat ba z W1 Hnth1 (XSUB1 z Hz))|].
    split.
    { intros a Ha. apply KEEP. destruct Ha as [Ha | Ha]; [left; left; exact Ha | right; exact Ha]. }
    split.
    { intros a NE. destruct (CHG a NE) as [C D]. split; [exact C | left; exact D]. }
    split; [exact LZF|]. split; [exact SEVF | exact RKF].
  Qed.
End K6N.
End BoAllocFRcK6n.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTopMp.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFRcK2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFRcK3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFRcMK5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW8 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutBg OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW10.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopBg OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocFRefillG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Ls.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopRf OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp BoAllocFRcK6n OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.




Section W14.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  (* [comment removed for export] *)
  Hypothesis BF : AsKSys10.AsAinvBootF3.boot_facts bt.
  Hypothesis BTOT : AsKSys10.AsKSys11.boot_totals bt.
  Hypothesis DC1 : BoDepotTop3.BoDepotTop1.depot_cells bt.
  Hypothesis DC2 : BoDepotTopN1b.BoDepotTopN1a.depot_cells2 bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x10ab58 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  (* [comment removed for export] *)
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  (* [comment removed for export] *)



  (* [comment removed for export] *)
  Lemma HYP_ITEM_FULL_MAP_PF : rc_item_stmt bt FXOK arm_prim_full_map.
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN BOOTG RCF RCC HTP CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (rc_item_full_map_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC RCF HTP TPm TSDPm PGPm FLm MIDENDm CELLSPIN BOOTG HTPm CELLSM PCELLS QHDR_CONST). Qed.
  Lemma HYP_BFREE_FULL_MAP_PF : rc_bfree_stmt bt FXOK arm_full24_map.
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN BOOTG RCF RCC CELLNB BT_ia BT_segs TSDP. exact (rc_bfree_full_map_pf bt FXOK TSDP TPm TSDPm PGPm FLm MIDENDm BT_segs BT_ia CELLNB RCC RCF CELLSPIN BOOTG HTPm CELLSM PCELLS QHDR_CONST). Qed.

  Theorem free_kat_W14 : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_W13 bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14 : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13 bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_thunk : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_thunk bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_opdel : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_opdel bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_opdel_sz : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_opdel_sz bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
End W14.
End BoAllocFTopMp.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMTopP3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocMHoleN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP3.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : BoAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation AAINVH := (AAINV_HS bt).
  #[local] Abbreviation MOK := (malloc_ok BSEGS FXOK both_addrs AAINVH MSTK_A).
  #[local] Abbreviation MNULL := (malloc_null BSEGS FXOK both_addrs AAINVH MSTK_A).


  (* [comment removed for export] *)
  Definition miss_null_stmt : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st st' : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_lsopt h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = [] ->
      refill_fail_st bt st (class_of (needed n)) st' -> at_refill_ret bt fx R M mdl Lc FF n st' 0 c' ->
      katD BSEGS c' (MNULL R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Lemma miss_conts : partB_stmt bt FXOK ->
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> bounds st Lc B C K -> holes_lsopt h st -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = [] ->
      (forall st' c', refill_ok_st bt (op_meter st EVT [] 0) (class_of (needed n)) st' -> a_cache st' (class_of (needed n)) <> [] ->
                      at_refill_ret bt fx R M mdl Lc FF n st' 1 c' -> katwD BSEGS c' (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True))
      /\ (forall st' c', refill_fail_st bt (op_meter st EVT [] 0) (class_of (needed n)) st' -> at_refill_ret bt fx R M mdl Lc FF n st' 0 c' ->
                         katD BSEGS c' (fun _ => True)).
  Proof using HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0.
    pose proof (holes_ls_of_opt h n st HL HO) as HS.
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply (WF_meter bt st Lc FF EVT [] 0 W); (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
    assert (HS1 : holes_ls n st1) by (exact (holes_ls_same_regcache n st st1 eq_refl eq_refl HS)).
    assert (HC01 : a_cache st1 (class_of (needed n)) = []) by exact HC0.
    pose proof (depot_room_meter bt st Lc FF EVT [] 0 W (Z.le_refl _)) as DR1. fold st1 in DR1.
    split; [| intros st' c' _ _; apply katD_refl; exact I].
    intros st' c' EST CNE AR. apply katwD_of_katD.
    destruct AR as (rq & Mq & mdlq & x18 & x19 & sz & bsz & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & Wq & RPq & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q4 & Q3
                    & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & STKq & ACC & SEVq & LKq).
    subst c'.
    pose proof (app_removelast_last 0 CNE) as E.
    set (ks := removelast (a_cache st' (class_of (needed n)))) in E. set (kk := last (a_cache st' (class_of (needed n))) 0) in E.
    pose proof CP as (_ & _ & _ & CP2 & _).
    pose proof (refill_ok_st_frame bt st1 (class_of (needed n)) st' EST) as (_ & _ & _ & ED' & _ & EK' & _).
    cbn [st1 op_meter add_meter a_dep a_kact] in ED', EK'.
    apply (katD_bind BSEGS _ (runA_post bt FXOK (uncharge st') ks kk Lc FF R M mdl n)).
    + apply (malloc_suffix bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT fx R M mdl Lc FF ret sp n st' ks kk rq Mq mdlq x18 x19 sz bsz
               HFX HLq MWq Wq RPq CP Hn' E); try assumption.
      * intros a Ha. apply STKq. rewrite CP2. exact Ha.
      * intros a NE. destruct (ACC a NE) as [F D]. split; [| exact (D eq_refl)].
        destruct F as [F | F]; [| right; right; left; exact F].
        destruct (Z_lt_le_dec (U a) (U (getr R 2) - 2480)) as [L | L]; [right; left; lia | left; (lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); left; lia].
      * rewrite EK'. destruct BD as (_ & _ & BK). unfold kcost_malloc, EVT in HK |- *. clear - BK HK Hn'. lia.
      * unfold depot_room in DR1 |- *. cbn [st1 op_meter add_meter a_dep a_kact] in DR1. rewrite ED', EK'. exact DR1.
      * exists h. exact (refill_ok_st_holes bt st1 (class_of (needed n)) st' EST h (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st st1 eq_refl (holes_lsopt_le _ _ HL))).
    + intros c' PC.
      eapply (PB h fx R M mdl Lc FF B C K ret n sp (uncharge st') ks kk c'); try eassumption.
      * unfold bounds in BD |- *. (lazymatch goal with |- ?G => let G' := eval unfold uncharge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact] in G in change_no_check G' end). rewrite EK'. clear - BD. unfold EVT in *. lia.
      * apply (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st' (uncharge st') eq_refl).
        exact (refill_ok_st_holes bt st1 (class_of (needed n)) st' EST h (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st st1 eq_refl (holes_lsopt_le _ _ HL))).
      * (lazymatch goal with |- ?G => let G' := eval unfold hole_flags, uncharge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). destruct (holes_closed_ok bt n st1 Lc FF st' Hn' W1 HS1 HC01 EST (class_of (needed n))) as [F1 F2].
        rewrite F1, F2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma miss_charge : forall (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K n : Z) (st : ast),
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> 1 <= n -> K + kcost_malloc n <= KCAP ->
      WF bt (op_meter st EVT [] 0) Lc FF /\ Rep bt (op_meter st EVT [] 0) Lc FF M mdl /\ a_kact (op_meter st EVT [] 0) <= KCAP
      /\ mu_room (op_meter st EVT [] 0).
  Proof using.
    intros M mdl Lc FF B C K n st W RP BD Hn HK. clear HYP_DEPOT G_KD GEOM BOOTG PCELLS CELLS HTP.
    split; [apply (WF_meter bt st Lc FF EVT [] 0 W); (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia|].
    split.
    - pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA' & _) & (Bw1 & Bw2 & _) & _).
      apply (OPS_REP_meter_pf bt st Lc FF M mdl mdl EVT [] 0 RP eq_refl); [intros a; tauto | exact FA' | | | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      + rewrite app_nil_r. exact Bw1.
      + rewrite app_nil_r. exact Bw2.
    - split; [| apply (AsAinvRoom3.mu_room_charged bt st Lc FF); [exact W | reflexivity | reflexivity]].
      (lazymatch goal with |- ?G => let G' := eval cbn [a_kact op_meter add_meter] in G in change_no_check G' end). destruct BD as (_ & _ & BK). unfold kcost_malloc, EVT in HK |- *. clear - BK HK Hn. lia.
  Qed.

  Theorem case_miss : partB_stmt bt FXOK -> miss_null_stmt -> MCASE bt FXOK (ia_malloc both_addrs) P_miss.
  Proof using HTP HYP_DEPOT G_KD BOOTG GEOM PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB _ h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK (Hp & HC0).
    assert (Hn' : 1 <= n <= 64512) by lia.
    destruct (miss_charge M mdl Lc FF B C K n st W RP BD (proj1 Hn') HK) as (W1 & RP1 & KC1 & MUR1).
    destruct (miss_conts PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0) as [C1 C0].
    apply katwD_of_katD. apply (katwD_ok_only BSEGS _ _ (fun _ => True)).
    exact (malloc_to_refill_ret bt TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS GEOM BOOTG HTP fx R M mdl Lc FF ret sp n (op_meter st EVT [] 0)
             (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True) HLT MW W1 RP1 KC1 MUR1 CP HR10 Hn' FPC HC0 C1 C0).
  Qed.

  (* [comment removed for export] *)
  Definition MCASE_S (entry : Z) (P : Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_lsopt h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      P n st ->
      katsD BSEGS (cfg BSEGS fx R entry M mdl) (MOK R M mdl Lc FF B C K ret n sp) (MNULL R M mdl Lc FF B C K ret n sp).
  Definition P_fresh_prim (n : Z) (st : ast) : Prop :=
    n <= 64512 /\ a_cache st (class_of (needed n)) = []
    /\ Z.of_nat (length (r_free (a_reg st (class_of (needed n))))) < cache_hint (class_of (needed n))
    /\ utest_x st (class_of (needed n)).

  Theorem case_miss_alt : partB_stmt bt FXOK -> miss_null_stmt -> MCASE_S (ia_malloc both_addrs) P_fresh_prim.
  Proof using HTP HYP_DEPOT G_KD BOOTG GEOM PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB _ h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK (Hp & HC0 & ENF & EUX).
    assert (Hn' : 1 <= n <= 64512) by lia.
    destruct (miss_charge M mdl Lc FF B C K n st W RP BD (proj1 Hn') HK) as (W1 & RP1 & KC1 & MUR1).
    destruct (miss_conts PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0) as [C1 C0].
    apply katsD_of_katwD. apply katwD_of_katD. apply (katsD_ok_only BSEGS _ _ (fun _ => True)).
    exact (malloc_to_refill_ret_s bt TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS GEOM BOOTG HTP fx R M mdl Lc FF ret sp n (op_meter st EVT [] 0)
             (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True) HLT MW W1 RP1 KC1 MUR1 CP HR10 Hn' FPC HC0 ENF EUX C1 C0).
  Qed.
End TOPP3.
End WithCeil.
End BoAllocMTopP3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMTopS4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs.BoAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecDefs.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_t : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defT : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPS4.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).                       (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp both_addrs.
  (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.

  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Lemma errno_wins_ok : as_wins_ok both_addrs [(ia_errno both_addrs, ia_errno both_addrs + 4)].
  Proof using.
    intros a (lo & hi & Hin & Ha). cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
    unfold ia_errno in Ha. cbn [ia_tp both_addrs] in Ha.
    split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end); lia|].
    split; [| split].
    - intros (lo' & hi' & Hin & Hr). cbn [ia_priv both_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - (lazymatch goal with |- ?G => let G' := eval unfold in_rtc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_rtc_sb ia_rtc_uar both_addrs] in G in change_no_check G' end). lia.
    - intros (lo' & hi' & Hin & Hr). cbn [ia_const both_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  Definition sec_null_stmt (HPf : option Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HPf (Some n) st -> BackingAlgebra.model_ivs_wf mdl ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      at_sec_null bt fx R M mdl Lc FF n st c' ->
      katD BSEGS c' (malloc_null BSEGS FXOK both_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).

  Theorem sec_null : forall HPf, sec_null_stmt HPf.
  Proof using OOM_NOT_REP NCELL CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros HPf h fx R M mdl Lc FF B C K ret n sp st c' HLT HFX W RP BD HPN MW CP HR10 Hn FPC HB HC HK AR.
    destruct AR as (rq & Mq & mdlq & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & RPq & Q10 & SF & ACC0 & SEVq & LKq).
    destruct SF as (x18 & x19 & sz & bsz & SF). cbv zeta in SF.
    destruct SF as (PRL & Q21 & Q4 & Q3 & Q26 & Q27 & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & FLA & STKq).
    pose proof W as Wq.
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (destruct BD as ((BP & BP2) & _); unfold GBUDGET, MBLK in HB; lia).
    subst c'.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (tp := getr R 4) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2. fold tp in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & _).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    pose proof (thread_dyn bt st Lc FF Wq) as (GT0 & GTC & GTI & GTB & TPG & _).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof RPq as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG in *.
    assert (GTS : TSIDE T) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact (conj GTI GTB)). hidehyp GTB.
    assert (Etp : tp = Z_to_bv 64 (ia_tp both_addrs)) by exact CP4.
    assert (Utp : U tp = ia_tp both_addrs) by (rewrite Etp; reflexivity).
    (* [comment removed for export] *)
    set (Hd := HID st mdlq).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdlq z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    destruct R14 as (Bw1 & Bw2 & _).
    set (Mr := mrestrict Hd Mq).
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30)) by konst Hd Mq R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by konst Hd Mq R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_inited.
    assert (K_mrn : rdn BSEGS Mr (Z_to_bv 64 0x190421) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs NCELL.
    assert (STKr : forall x : word, U S - 3584 <= U x < U S -> Mr x = Mq x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia|]. left. rewrite CP2 in Hx. lia. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS Mq (at_ S k) w = Some bs -> rdn BSEGS Mr (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STKr. lia. }
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply (proj2 (STKq x ltac:(lia))). }
    assert (SOKoom : store_ok BSEGS Mr (Z_to_bv 64 0x190420) 1 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOKerr : store_ok BSEGS Mr (at_ tp (-164)) 4 = true).
    { rewrite Etp. replace (at_ (Z_to_bv 64 (ia_tp both_addrs)) (-164)) with (Z_to_bv 64 (ia_errno both_addrs) : word) by (apply bv_eq; reflexivity).
      apply store_ok_wseg. vm_cast_no_check (eq_refl true). }
    assert (FCr : forall (o : Z) (v : word),
              In (o, v) [(-8, at_ ARB 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
              rdn BSEGS Mr (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. apply FC.
      replace (at_ ARB 0x4c834) with (Z_to_bv 64 0x4c834 : word) in Hin by (symmetry; apply ARB_litNs; lia). exact Hin. }
    assert (FLr : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
              rdn BSEGS Mr (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FLA o v Hin). }
    assert (FAr : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn BSEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k v Hin) as [Hk1 Hk2]. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA k v Hin)]. }
    assert (FIr : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (Hk : -56 <= k /\ k + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI k v Hin)]. }
    assert (RETR : ret_ok (getr R 1)) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    (* [comment removed for export] *)
    destruct (run_mS_null Mr (seg_rom BSEGS) rq R S tp T n x18 x19 PRL Q4 Q3 Q10 RETR)
      as (r3 & RUN & X10 & X1 & X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
    all: try assumption.
    all: try (rewrite ?CP2; split; [split; [exact GT4 | exact GTS] | lia]).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); lia).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); repeat split; lia).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    set (MC := mn_mem Mr S tp) in RUN.
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF Mq mdlq BT_ia RPq) asanF_segs_wx (a_aa st)
             (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS)) (@mkst fx r3 (getr R 1) MC (seg_rom BSEGS)) mdlq).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HLq. }
    { rewrite restrict_mkst_t. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS))) with Mq by reflexivity.
    set (MDin := munrestrict Hd Mq MC).
    apply katD_refl.
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gtpm : AIMGLO + 164 <= U tp /\ U tp <= AIMGHI) by (rewrite Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); lia).
    assert (GRin : mem_grows Mq MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply (mn_mem_grows Mr S tp). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (DIFF : forall a : word, MDin a <> Mq a ->
              U a = 0x190420 \/ (U S - 2152 <= U a < U S - 2144) \/ (ia_errno both_addrs <= U a < ia_errno both_addrs + 4)).
    { intros a NE. unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = Mq a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z.eq_dec (U a) 0x190420) as [E|N1]; [left; exact E|].
      destruct (Z_lt_le_dec (U a) (U S - 2152)) as [L1|L1]; [| destruct (Z_lt_le_dec (U a) (U S - 2144)) as [L2|L2]; [right; left; lia|]].
      all: destruct (Z_lt_le_dec (U a) (U tp - 164)) as [L3|L3]; [| destruct (Z_lt_le_dec (U a) (U tp - 160)) as [L4|L4]; [right; right; (lazymatch goal with |- ?G => let G' := eval unfold ia_errno in G in change_no_check G' end); rewrite <- Utp; lia|]].
      all: exfalso; apply NE; rewrite <- EMr; apply (mn_mem_outside Mr S tp GSm Gtpm); lia. }
    assert (DEF : forall a : word, MDin a <> Mq a -> MDin a <> None).
    { intros a NE. destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (Mq a) eqn:E2; [|reflexivity].
      exfalso. assert (X : Mq a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    (* [comment removed for export] *)
    assert (RPf : Rep bt st Lc FF MDin mdl1).
    { apply (Rep_frame bt st Lc FF Mq MDin mdl1 Wq (Rep_sbm bt st Lc FF Mq mdlq mdl1 RPq MI1 SBM1)).
      intros a NE. split; [| exact (DEF a NE)]. intros RCa.
      destruct (DIFF a NE) as [E | [E | E]].
      - rewrite E in RCa. exact (OOM_NOT_REP st Lc FF Wq RCa).
      - pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) Wq RCa). rewrite CP2 in E. lia.
      - refine (win_vs_rep bt st Lc FF Wq [(ia_errno both_addrs, ia_errno both_addrs + 4)] (U a) _ _ RCa).
        + rewrite BT_ia. exact errno_wins_ok.
        + exists (ia_errno both_addrs), (ia_errno both_addrs + 4). split; [left; reflexivity | exact E]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold malloc_null in G in change_no_check G' end). exists fx, r3, MDin, mdl1.
    split; [(lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end); rewrite CP1; reflexivity|]. split; [exact HFX|].
    split.
    { (* [comment removed for export] *)
      intros r Hr. unfold as_callee_saved in Hr. cbn [In] in Hr.
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity); rewrite X2; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 3) with (3%bv : reg) by (apply bv_eq; reflexivity); rewrite X3; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 4) with (4%bv : reg) by (apply bv_eq; reflexivity); rewrite X4; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 8) with (8%bv : reg) by (apply bv_eq; reflexivity); rewrite X8; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 9) with (9%bv : reg) by (apply bv_eq; reflexivity); rewrite X9; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 18) with (18%bv : reg) by (apply bv_eq; reflexivity); rewrite X18; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 19) with (19%bv : reg) by (apply bv_eq; reflexivity); rewrite X19; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 20) with (20%bv : reg) by (apply bv_eq; reflexivity); rewrite X20; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 21) with (21%bv : reg) by (apply bv_eq; reflexivity); rewrite X21; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 22) with (22%bv : reg) by (apply bv_eq; reflexivity); rewrite X22; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 23) with (23%bv : reg) by (apply bv_eq; reflexivity); rewrite X23; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 24) with (24%bv : reg) by (apply bv_eq; reflexivity); rewrite X24; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 25) with (25%bv : reg) by (apply bv_eq; reflexivity); rewrite X25; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 26) with (26%bv : reg) by (apply bv_eq; reflexivity); rewrite X26; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 27) with (27%bv : reg) by (apply bv_eq; reflexivity); rewrite X27; reflexivity|].
      destruct Hr. }
    split; [exact X10|].
    split.
    { (* [comment removed for export] *) intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite ?BT_ia.
      destruct (decide (MDin a = Mq a)) as [E | N].
      - rewrite E in NE. pose proof (ACC0 a NE) as F. left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
      - destruct (DIFF a N) as [E | [E | E]].
        + right; right; left. exists 0x10ee9a, 0x19fce8. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv both_addrs In] in G in change_no_check G' end); tauto | lia].
        + left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
        + right; right; right. exact E. }
    split.
    { (* [comment removed for export] *) intros a Ha Dm. unfold in_errno, ia_errno in Ha. cbn [ia_tp both_addrs] in Ha.
      (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end). rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [pose proof (u64_range a); lia | right; lia]).
      apply (mn_mem_errno Mr S tp Gtpm). rewrite Utp. (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end). lia. }
    split.
    { (* [comment removed for export] *) intros a Ha. assert (D : MDin a <> None) by (apply GRin; apply (proj1 (STKq a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); rewrite CP2; exact Ha)))).
      split; [exact D | exact (store_ok1_defT MDin a D)]. }
    split.
    { (* [comment removed for export] *)
      exists st. split; [exact Wq|]. split; [exact RPf|]. split; [| exact (model_ivs_wf_sbm mdlq mdl1 SBM1 MWq)].
      split; [exact BD | exact HPN]. }
    split; [eapply same_except_vm_trans; [exact SEVq | apply same_but_materialized_except_vm; exact SBM1]|].
    split; [| exact (halted_sbm mdlq mdl1 SBM1 HLq)].
    intros a Ha. pose proof (lazy_kept_sbm bt Lc FF mdlq mdl1 SBM1 a) as L1. rewrite ?BT_ia in L1. rewrite (L1 Ha). pose proof (LKq a) as L2. rewrite ?BT_ia in L2. exact (L2 Ha).
  Qed.
End TOPS4.
End WithCeil.
End BoAllocMTopS4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSbAsm.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecK OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSa BoAllocMTopS4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbTop.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.

Section ASM.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis SCELLS : sec_cells bt.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).                 (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis HTP : TP = ia_tp both_addrs.

  (* [comment removed for export] *)
  Definition sec_granted_stmt : Prop :=
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (c' : config) (Qok : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 64512 < n <= NMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      at_sec_grant bt fx R M mdl Lc FF n st c' ->
      (forall c'', runS_post bt FXOK st Lc FF R M mdl n c'' -> katD BSEGS c'' Qok) ->
      katD BSEGS c' Qok.
  Hypothesis SEC_GRANTED : sec_granted_stmt.

  (* [comment removed for export] *)
  Theorem malloc_sec_gen : forall (HPf : option Z -> ast -> Prop)
      (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> HPf h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      holes_le h st ->                                                           (* [comment removed for export] *)
      HPf (Some n) st ->                                                         (* [comment removed for export] *)
      (forall st', (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) ->
                   a_kact st' = a_kact st + kcost_malloc n -> HPf None st') ->   (* [comment removed for export] *)
      katsD BSEGS (cfg BSEGS fx R (ia_malloc both_addrs) M mdl)
            (malloc_ok BSEGS FXOK both_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp)
            (malloc_null BSEGS FXOK both_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros HPf h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HP MW HO CP HR10 Hn FPC HB HC HK HLE HPN HCL.
    apply (malloc_sec_to_mmap bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS SCELLS GEOM BOOTG BOK BTOT HTP
             fx R M mdl Lc FF B C K ret sp n st h _ _ HFX HLT MW W RP BD HLE HO CP HR10 Hn FPC HB HC HK).
    - (* [comment removed for export] *)
      intros c' AG. apply katwD_of_katD.
      apply (SEC_GRANTED fx R M mdl Lc FF B C K ret sp n st h c' _ HFX HLT MW W RP BD HLE HO CP HR10 Hn HB HC HK AG).
      intros c'' RPOST.
      exact (malloc_partBs bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS (proj1 SCELLS) HTP HPf
               h fx R M mdl Lc FF B C K ret n sp st c'' HLT HFX W BD HP HO CP HR10 Hn FPC HB HC HK HCL RPOST).
    - (* [comment removed for export] *)
      intros c' AN.
      exact (sec_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP HPf
               h fx R M mdl Lc FF B C K ret n sp st c' HLT HFX W RP BD HPN MW CP HR10 Hn FPC HB HC HK AN).
  Qed.

  (* [comment removed for export] *)
  Lemma sec_holes_ls : forall h n st, holes_le h st -> hole_ok h n -> 64512 < n -> holes_ls n st.
  Proof using.
    intros h n st HL HO Hn c F. exfalso. destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2].
    destruct F as [F | F]; [rewrite F1 in F | rewrite F2 in F]; discriminate F.
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_sec_S : MCASE_S bt FXOK (ia_malloc both_addrs) P_sec.
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP. unfold P_sec in HP.
    pose proof (holes_lsopt_le h st HL) as HLE.
    exact (malloc_sec_gen holes_lsopt h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 (conj HP (proj2 Hn)) FPC HB HC HK HLE
             (sec_holes_ls h n st HLE HO HP)
             (fun st' E _ => sec_holes_none h n st st' HLE HO HP (fun c => proj1 (E c)))).
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_sec_DR : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true.
  Proof using SEC_GRANTED HTP BTOT BOK BOOTG GEOM OOM_NOT_REP NCELL SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret n sp PRE Hbig.
    destruct PRE as (HLT & HFX & AI & HO & CP & HR10 & Hn & FPC & HB & HC & HK).
    destruct AI as (st & W & RP & (BD & HP) & MW).
    pose proof HP as (HL & DH). pose proof (holes_lsopt_le None st HL) as HLE.
    assert (K0 : 0 <= a_kact st) by (destruct BD as (_ & _ & BK); exact (proj1 BK)).
    exact (malloc_sec_gen (HP_q drv_hist) None fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HP MW HO CP HR10 (conj Hbig (proj2 Hn)) (FPC eq_refl) HB HC HK HLE
             (sec_holes_ls None n st HLE HO Hbig)
             (fun st' E EK => conj (sec_holes_none None n st st' HLE HO Hbig (fun c => proj1 (E c)))
                                   (drv_hist_malloc_sec st st' n DH Hbig K0 E ltac:(rewrite EK; apply Z.le_refl)))).
  Qed.
End ASM.
End WithCeil.
End BoAllocMSbAsm.
Module BoAllocMTopP4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs.BoAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunNs.BoAllocMRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocMHoleN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1 BoAllocMTopP3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_n : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defQ : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP4.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).                       (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp both_addrs.
  (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation AAINVH := (AAINV_HS bt).
  #[local] Abbreviation MNULL := (malloc_null BSEGS FXOK both_addrs AAINVH MSTK_A).

  (* [comment removed for export] *)
  Lemma errno_wins_ok : as_wins_ok both_addrs [(ia_errno both_addrs, ia_errno both_addrs + 4)].
  Proof using.
    intros a (lo & hi & Hin & Ha). cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
    unfold ia_errno in Ha. cbn [ia_tp both_addrs] in Ha.
    split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end); lia|].
    split; [| split].
    - intros (lo' & hi' & Hin & Hr). cbn [ia_priv both_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - (lazymatch goal with |- ?G => let G' := eval unfold in_rtc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_rtc_sb ia_rtc_uar both_addrs] in G in change_no_check G' end). lia.
    - intros (lo' & hi' & Hin & Hr). cbn [ia_const both_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  Theorem miss_null : miss_null_stmt bt FXOK.
  Proof using OOM_NOT_REP NCELL CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret n sp st st' c' HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HC0 EST AR.
    destruct AR as (rq & Mq & mdlq & x18 & x19 & sz & bsz & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & Wq & RPq & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q4 & Q3
                    & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & STKq & ACC & SEVq & LKq).
    subst c'.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (tp := getr R 4) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2. fold tp in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & _).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    pose proof (thread_dyn bt st' Lc FF Wq) as (GT0 & GTC & GTI & GTB & TPG & _).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof RPq as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG in *.
    assert (GTS : TSIDE T) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact (conj GTI GTB)). hidehyp GTB.
    assert (Etp : tp = Z_to_bv 64 (ia_tp both_addrs)) by exact CP4.
    assert (Utp : U tp = ia_tp both_addrs) by (rewrite Etp; reflexivity).
    (* [comment removed for export] *)
    set (Hd := HID st' mdlq).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdlq z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    destruct R14 as (Bw1 & Bw2 & _).
    set (Mr := mrestrict Hd Mq).
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30)) by konst Hd Mq R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by konst Hd Mq R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_inited.
    assert (K_mrn : rdn BSEGS Mr (Z_to_bv 64 0x190421) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs NCELL.
    assert (STKr : forall x : word, U S - 3584 <= U x < U S -> Mr x = Mq x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia|]. left. rewrite CP2 in Hx. lia. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS Mq (at_ S k) w = Some bs -> rdn BSEGS Mr (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STKr. lia. }
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply (proj2 (STKq x ltac:(lia))). }
    assert (SOKoom : store_ok BSEGS Mr (Z_to_bv 64 0x190420) 1 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOKerr : store_ok BSEGS Mr (at_ tp (-164)) 4 = true).
    { rewrite Etp. replace (at_ (Z_to_bv 64 (ia_tp both_addrs)) (-164)) with (Z_to_bv 64 (ia_errno both_addrs) : word) by (apply bv_eq; reflexivity).
      apply store_ok_wseg. vm_cast_no_check (eq_refl true). }
    assert (FCr : forall (o : Z) (v : word),
              In (o, v) [(-8, at_ ARB 0x4c834); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
              rdn BSEGS Mr (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    assert (FAr : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn BSEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k v Hin) as [Hk1 Hk2]. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA k v Hin)]. }
    assert (FIr : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (Hk : -56 <= k /\ k + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI k v Hin)]. }
    assert (Q2' : getr rq 2 = at_ (at_ S (-2272)) (-48)) by (rewrite at_at; exact Q2).
    assert (RETR : ret_ok (getr R 1)) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    (* [comment removed for export] *)
    destruct (run_mA_null Mr (seg_rom BSEGS) rq R S tp T n x18 x19 Q2' Q4 Q3 Q10 Q18 RETR)
      as (r3 & RUN & X10 & X1 & X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
    all: try assumption.
    all: try (rewrite ?CP2; split; [split; [exact GT4 | exact GTS] | lia]).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); lia).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); repeat split; lia).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    set (MC := mn_mem Mr S tp) in RUN.
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF Mq mdlq BT_ia RPq) asanF_segs_wx (a_aa st')
             (@mkst fx rq (Z_to_bv 64 0x50f9c) Mq (seg_rom BSEGS)) (@mkst fx r3 (getr R 1) MC (seg_rom BSEGS)) mdlq).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HLq. }
    { rewrite restrict_mkst_n. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x50f9c) Mq (seg_rom BSEGS))) with Mq by reflexivity.
    set (MDin := munrestrict Hd Mq MC).
    apply katD_refl.
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gtpm : AIMGLO + 164 <= U tp /\ U tp <= AIMGHI) by (rewrite Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end); lia).
    assert (GRin : mem_grows Mq MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply (mn_mem_grows Mr S tp). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (DIFF : forall a : word, MDin a <> Mq a ->
              U a = 0x190420 \/ (U S - 2152 <= U a < U S - 2144) \/ (ia_errno both_addrs <= U a < ia_errno both_addrs + 4)).
    { intros a NE. unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = Mq a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z.eq_dec (U a) 0x190420) as [E|N1]; [left; exact E|].
      destruct (Z_lt_le_dec (U a) (U S - 2152)) as [L1|L1]; [| destruct (Z_lt_le_dec (U a) (U S - 2144)) as [L2|L2]; [right; left; lia|]].
      all: destruct (Z_lt_le_dec (U a) (U tp - 164)) as [L3|L3]; [| destruct (Z_lt_le_dec (U a) (U tp - 160)) as [L4|L4]; [right; right; (lazymatch goal with |- ?G => let G' := eval unfold ia_errno in G in change_no_check G' end); rewrite <- Utp; lia|]].
      all: exfalso; apply NE; rewrite <- EMr; apply (mn_mem_outside Mr S tp GSm Gtpm); lia. }
    assert (DEF : forall a : word, MDin a <> Mq a -> MDin a <> None).
    { intros a NE. destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (Mq a) eqn:E2; [|reflexivity].
      exfalso. assert (X : Mq a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    (* [comment removed for export] *)
    assert (RPf : Rep bt st' Lc FF MDin mdl1).
    { apply (Rep_frame bt st' Lc FF Mq MDin mdl1 Wq (Rep_sbm bt st' Lc FF Mq mdlq mdl1 RPq MI1 SBM1)).
      intros a NE. split; [| exact (DEF a NE)]. intros RCa.
      destruct (DIFF a NE) as [E | [E | E]].
      - rewrite E in RCa. exact (OOM_NOT_REP st' Lc FF Wq RCa).
      - pose proof (rep_cells_lt_ceil bt BT_ia st' Lc FF (U a) Wq RCa). rewrite CP2 in E. lia.
      - refine (win_vs_rep bt st' Lc FF Wq [(ia_errno both_addrs, ia_errno both_addrs + 4)] (U a) _ _ RCa).
        + rewrite BT_ia. exact errno_wins_ok.
        + exists (ia_errno both_addrs), (ia_errno both_addrs + 4). split; [left; reflexivity | exact E]. }
    (* [comment removed for export] *)
    pose proof (holes_ls_fail bt n st st' Hn (holes_ls_of_opt h n st HL HO) HC0 EST) as HLS.
    pose proof (refill_fail_st_frame bt st (class_of (needed n)) st' EST) as (_ & _ & _ & _ & _ & EK & _).
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold malloc_null in G in change_no_check G' end). exists fx, r3, MDin, mdl1.
    split; [(lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end); rewrite CP1; reflexivity|]. split; [exact HFX|].
    split.
    { (* [comment removed for export] *)
      intros r Hr. unfold as_callee_saved in Hr. cbn [In] in Hr.
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity); rewrite X2; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 3) with (3%bv : reg) by (apply bv_eq; reflexivity); rewrite X3; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 4) with (4%bv : reg) by (apply bv_eq; reflexivity); rewrite X4; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 8) with (8%bv : reg) by (apply bv_eq; reflexivity); rewrite X8; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 9) with (9%bv : reg) by (apply bv_eq; reflexivity); rewrite X9; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 18) with (18%bv : reg) by (apply bv_eq; reflexivity); rewrite X18; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 19) with (19%bv : reg) by (apply bv_eq; reflexivity); rewrite X19; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 20) with (20%bv : reg) by (apply bv_eq; reflexivity); rewrite X20; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 21) with (21%bv : reg) by (apply bv_eq; reflexivity); rewrite X21; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 22) with (22%bv : reg) by (apply bv_eq; reflexivity); rewrite X22; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 23) with (23%bv : reg) by (apply bv_eq; reflexivity); rewrite X23; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 24) with (24%bv : reg) by (apply bv_eq; reflexivity); rewrite X24; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 25) with (25%bv : reg) by (apply bv_eq; reflexivity); rewrite X25; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 26) with (26%bv : reg) by (apply bv_eq; reflexivity); rewrite X26; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 27) with (27%bv : reg) by (apply bv_eq; reflexivity); rewrite X27; reflexivity|].
      destruct Hr. }
    split; [exact X10|].
    split.
    { (* [comment removed for export] *) intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite ?BT_ia.
      destruct (decide (MDin a = Mq a)) as [E | N].
      - rewrite E in NE. destruct (ACC a NE) as [[F | F] _]; [left; rewrite <- CP2; fold S; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); lia | right; left; rewrite ?BT_ia in F; exact F].
      - destruct (DIFF a N) as [E | [E | E]].
        + right; right; left. exists 0x10ee9a, 0x19fce8. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv both_addrs In] in G in change_no_check G' end); tauto | lia].
        + left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
        + right; right; right. exact E. }
    split.
    { (* [comment removed for export] *) intros a Ha Dm. unfold in_errno, ia_errno in Ha. cbn [ia_tp both_addrs] in Ha.
      (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end). rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [pose proof (u64_range a); lia | right; lia]).
      apply (mn_mem_errno Mr S tp Gtpm). rewrite Utp. (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp both_addrs] in G in change_no_check G' end). lia. }
    split.
    { (* [comment removed for export] *) intros a Ha. assert (D : MDin a <> None) by (apply GRin; apply (proj1 (STKq a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); rewrite CP2; exact Ha)))).
      split; [exact D | exact (store_ok1_defQ MDin a D)]. }
    split.
    { (* [comment removed for export] *)
      exists st'. split; [exact Wq|]. split; [exact RPf|]. split; [| exact (model_ivs_wf_sbm mdlq mdl1 SBM1 MWq)].
      split; [unfold bounds in BD |- *; rewrite EK; exact BD | exact HLS]. }
    split; [eapply same_except_vm_trans; [exact SEVq | apply same_but_materialized_except_vm; exact SBM1]|].
    split; [| exact (halted_sbm mdlq mdl1 SBM1 HLq)].
    intros a Ha. pose proof (lazy_kept_sbm bt Lc FF mdlq mdl1 SBM1 a) as L1. rewrite ?BT_ia in L1. rewrite (L1 Ha). pose proof (LKq a) as L2. rewrite ?BT_ia in L2. exact (L2 Ha).
  Qed.
End TOPP4.
End WithCeil.
End BoAllocMTopP4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMW1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopB.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : BoAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.

  Theorem malloc_case_hit : MCASE bt FXOK (ia_malloc both_addrs) P_hit.
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    eapply (case_hit bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
  Qed.
End W1.
End BoAllocMW1.
Module BoAllocMW3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopB BoAllocMTopP3 BoAllocMTopP4.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : BoAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.

  Theorem malloc_case_miss : MCASE bt FXOK (ia_malloc both_addrs) P_miss.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    apply (case_miss bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS GEOM BOOTG G_KD HYP_DEPOT HTP).
    - eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    - exact (miss_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP).
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_case_miss_alt : MCASE_S bt FXOK (ia_malloc both_addrs) P_fresh_prim.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    apply (case_miss_alt bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS GEOM BOOTG G_KD HYP_DEPOT HTP).
    - eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    - exact (miss_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP).
  Qed.
End W3.
End BoAllocMW3.
Module BoAllocMW4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopB BoAllocMTopP3 BoAllocMTopP4 BoAllocMW1 BoAllocMW3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W4.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : BoAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.

  Theorem malloc_katw_of_sec :
    MCASE bt FXOK (ia_malloc both_addrs) P_sec ->
    MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros HS. apply (malloc_katw_of_cases bt FXOK (ia_malloc both_addrs)).
    - exact (malloc_case_hit bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT HTP).
    - exact (malloc_case_miss bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS NCELL GEOM BOOTG G_KD HYP_DEPOT HTP OOM_NOT_REP).
    - exact HS.
  Qed.
End W4.
End BoAllocMW4.
Module BoAllocMW5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMW4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section W5.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x190421, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis DC : depot_cells bt.
  Hypothesis DC2 : depot_cells2 bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.

  Theorem malloc_katw_of_sec5 :
    MCASE bt FXOK (ia_malloc both_addrs) P_sec ->
    MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true.
  Proof using OOM_NOT_REP HTP DC2 DC BTOT BF GEOM NCELL PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    exact (malloc_katw_of_sec bt FXOK TP TSDP PGP FL MIDEND 1312 BT_segs BT_ia CELLS PCELLS NCELL GEOM (boot_facts_geom bt BF) ltac:(lia)
             (hyp_depot_closed bt FXOK BF BTOT BT_segs BT_ia DC DC2 1312 ltac:(lia)) HTP OOM_NOT_REP).
  Qed.
End W5.
End BoAllocMW5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoContractsMallocB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP1.BoAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMTopP3 BoAllocMW3 BoAllocMW4 BoAllocMW5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation U := bv_unsigned.

Section MallocAt.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (both_bt hv).
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite both_bt_consts; unfold both_consts; cbv zeta; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].

  #[local] Notation TP := (ia_tp both_addrs).
  Definition TSDP_M : Z := 0x662728.
  Definition PGP_M : Z := 0x19dc60.
  Definition FL_M : Z := 0x10b9b8.

  Lemma MCELLS_at : malloc_cells bt TP TSDP_M PGP_M FL_M 0.
  Proof. unfold malloc_cells, TSDP_M, PGP_M, FL_M. repeat (split; [in_consts|]). cbn. lia. Qed.
  Lemma PCELLS_at : pop_cells bt.
  Proof. unfold pop_cells. repeat (split; [in_consts|]). in_consts. Qed.
  Lemma DCELLS_at : depot_cells bt /\ depot_cells2 bt.
  Proof. exact (depot_cells_both bt _ _ _ _ (both_bt_consts hv)). Qed.
  Lemma OOM_at : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.
  Proof. intros st Lc FF W. exact (oom_not_rep_B hv st Lc FF _ _ W). Qed.

  (* [comment removed for export] *)
  Lemma HYP_DEPOT_at : BoAllocFHyp.HYP_DEPOT_stmt bt FXOK 1312.
  Proof. apply (hyp_depot_closed bt FXOK BF BTOT eq_refl eq_refl (proj1 DCELLS_at) (proj2 DCELLS_at) 1312). lia. Qed.
  Lemma case_fresh_prim_at : MCASE_S bt FXOK (ia_malloc both_addrs) P_fresh_prim.
  Proof.
    exact (malloc_case_miss_alt bt FXOK TP TSDP_M PGP_M FL_M 0 1312 eq_refl eq_refl MCELLS_at PCELLS_at (may_return_null_row_B hv)
             (boot_facts_stack bt BF) (boot_facts_geom bt BF) ltac:(lia) HYP_DEPOT_at eq_refl OOM_at).
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_SEC_S : MCASE_S bt FXOK (ia_malloc both_addrs) P_sec.

  Lemma case_sec_at : MCASE bt FXOK (ia_malloc both_addrs) P_sec.
  Proof.
    intros h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP.
    apply katsD_katwD. exact (H_SEC_S h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP).
  Qed.

  Theorem malloc_katw_at : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true.
  Proof.
    exact (malloc_katw_of_sec5 bt FXOK TP TSDP_M PGP_M FL_M 0 eq_refl eq_refl MCELLS_at PCELLS_at (may_return_null_row_B hv)
             (boot_facts_stack bt BF) BF BTOT (proj1 DCELLS_at) (proj2 DCELLS_at) eq_refl OOM_at case_sec_at).
  Qed.
  Theorem malloc_katw_thunk_at : MALLOC_KATW BSEGS FXOK both_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Proof. exact (malloc_katw_thunk bt FXOK eq_refl MSTK_A true malloc_katw_at). Qed.

  (* [comment removed for export] *)
  Theorem malloc_alt_at : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc both_addrs) true.
  Proof.
    intros h fx R M mdl Lc FF B C K ret n sp PRE FR.
    destruct PRE as (HLT & HFX & AI & HO & CP & HR10 & Hn & FPC & HB & HC & HK).
    destruct AI as (st & W & RP & [BD HL] & MW).
    destruct (FRESH_at bt Lc FF B C K M mdl n st FR W RP) as [Hs | [Hp (F1 & F2 & F3)]].
    - exact (H_SEC_S h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK Hs).
    - exact (case_fresh_prim_at h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK
               (conj Hp (conj F1 (conj F2 F3)))).
  Qed.
  Theorem malloc_alt_thunk_at : MALLOC_ALT BSEGS FXOK both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Proof. exact (malloc_alt_thunk bt FXOK eq_refl (FRESH_bt bt) (FRESH_sbm bt) MSTK_A true malloc_alt_at). Qed.

  (* [comment removed for export] *)
  Hypothesis H_SEC_DR : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true.

  (* [comment removed for export] *)
  Theorem malloc_alt_sec_thunk_drx : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk both_addrs) true.
  Proof.
    intros fx R M mdl Lc FF B C K ret n sp PRE Hbig.
    pose proof PRE as (HH & HFX & AI & REST).
    destruct AI as (st & W & RP & BH & MW).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    unfold cfg.
    apply (katsD_step_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl eq_refl RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 (ia_malloc_thunk both_addrs)) M (seg_rom BSEGS))
             (@mkst fx R (Z_to_bv 64 (ia_malloc both_addrs)) (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - reflexivity.
    - exact (jstep_malloc_thunk fx R (mrestrict (HID st mdl) M)).
    - intros mdl1 MI1 SBM1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx R (Z_to_bv 64 (ia_malloc_thunk both_addrs)) M (seg_rom BSEGS))) with M by reflexivity.
      rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      assert (PRE1 : malloc_pre BSEGS FXOK both_addrs (AAINV_DRX bt) None MSTK_A true fx R M mdl1 Lc FF B C K ret n sp).
      { split; [rewrite Ehl; exact HH|]. split; [exact HFX|]. split; [| exact REST].
        exists st. split; [exact W|]. split; [exact (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1)|].
        split; [exact BH | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]. }
      apply (katsD_conseq BSEGS _ _ _ _ _ (H_SEC_DR fx R M mdl1 Lc FF B C K ret n sp PRE1 Hbig)).
      + intros c' (fx' & R' & M' & mdl' & p & Ec & HFX' & RK & E10 & P16 & PBLK & PSEC & PLC & PFF & PDEF & SH1 & SH2 & SH3 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl', p. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | unfold lzb; rewrite Elz; reflexivity].
      + intros c' (fx' & R' & M' & mdl' & Ec & HFX' & RK & E10 & CH & EK & SCR & AI' & SEV & LZK & HH').
        exists fx', R', M', mdl'. repeat (split; [assumption|]).
        split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
        split; [| exact HH']. intros a Ha. transitivity (lzb mdl1 a); [exact (LZK a Ha) | unfold lzb; rewrite Elz; reflexivity].
  Qed.
End MallocAt.
End BoContractsMallocB.
Module BoContractsFreeB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys5q OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp.BoAllocFTopW10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMThunk.BoAllocFThunk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTopDp BoAllocFTopMp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK6p.BoAllocMQhdr OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a BoContractsMallocB.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FreeAt.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (both_bt hv).
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite both_bt_consts; unfold both_consts; cbv zeta; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].

  #[local] Notation TP := (ia_tp both_addrs).
  Definition TSDP_B : Z := 0x662728.
  Definition PGP_B : Z := 0x19dc60.
  Definition FL_B : Z := 0x10b9b8.
  Definition MINSZ_B : Z := 0xe666661.

  Lemma CELLS_at : free_cells bt TP TSDP_B PGP_B FL_B 0 1.
  Proof. unfold free_cells, TSDP_B, PGP_B, FL_B. repeat (split; [in_consts|]). cbn. lia. Qed.
  Lemma CELLNB_at : free_cells_nb bt.  Proof. unfold free_cells_nb, IB. cbn [bt_ia both_bt ia_instance both_addrs bt_spacebeg]. in_consts. Qed.
  Lemma CELL_min_at : In (0x10ab58 + 800, 8%nat, MINSZ_B) (bt_consts bt).  Proof. unfold MINSZ_B. in_consts. Qed.
  Lemma RCC_at : rc_cells bt TSDP_B.
  Proof. unfold rc_cells, IB, TSDP_B. cbn [bt_ia both_bt ia_instance both_addrs bt_spacebeg]. split; [in_consts|]. split; [in_consts | lia]. Qed.
  Lemma RCF_at : rc_cells_full bt.  Proof. unfold rc_cells_full. repeat (split; [in_consts|]). in_consts. Qed.
  Lemma SECC_at : sec_cells bt TSDP_B.
  Proof. unfold sec_cells, IB, TSDP_B. cbn [bt_ia both_bt ia_instance both_addrs bt_ptrarr]. repeat (split; [in_consts|]). lia. Qed.
  Lemma CELLSPIN_at : free_cells_spin bt.  Proof. unfold free_cells_spin. repeat (split; [in_consts|]). in_consts. Qed.

  (* [comment removed for export] *)
  Lemma QHDR_CONST_at : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  Proof. exact (qhdr_const_both bt _ _ _ _ eq_refl (both_bt_consts hv)). Qed.

  Lemma G_min_at : 0 <= MINSZ_B <= 2 ^ 28.  Proof. unfold MINSZ_B. lia. Qed.

  Theorem free_kat_at : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs).
  Proof.
    exact (free_kat_W14 bt FXOK TP TSDP_B PGP_B FL_B 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_B CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_thunk_at : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_free_thunk both_addrs).
  Proof. exact (free_kat_thunk bt FXOK eq_refl MSTK_A free_kat_at). Qed.
  Theorem free_kat_opdel_at : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_opdel both_addrs).
  Proof. exact (free_kat_opdel bt FXOK eq_refl MSTK_A free_kat_at). Qed.
  Theorem free_kat_opdel_sz_at : FREE_KAT BSEGS FXOK both_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof. exact (free_kat_opdel_sz bt FXOK eq_refl MSTK_A free_kat_at). Qed.

  (* [comment removed for export] *)
  Theorem free_kat_n_drx_at : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs).
  Proof.
    exact (free_kat_n_drx14 bt FXOK TP TSDP_B PGP_B FL_B 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_B CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_thunk_at : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs).
  Proof.
    exact (free_kat_n_drx14_thunk bt FXOK TP TSDP_B PGP_B FL_B 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_B CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_opdel_at : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs).
  Proof.
    exact (free_kat_n_drx14_opdel bt FXOK TP TSDP_B PGP_B FL_B 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_B CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_opdel_sz_at : FREE_KAT_N BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).
  Proof.
    exact (free_kat_n_drx14_opdel_sz bt FXOK TP TSDP_B PGP_B FL_B 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_B CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
End FreeAt.
End BoContractsFreeB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoWalkRowsB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMTopP3 BoContractsMallocB BoContractsFreeB.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition WALK_ROWS_B {RC : run_ceil} (hv : AsAinvOomCell3.BoAinvBoot3.bvars) : Prop :=
  let bt := both_bt hv in
  MALLOC_KATW BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_KATW BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ MALLOC_ALT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_ALT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_free both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_free_thunk both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_opdel both_addrs)
  /\ FREE_KAT BSEGS AzSymStepR.fx_ok both_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz both_addrs)
  /\ MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true
  /\ MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk both_addrs) true
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_free both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel both_addrs)
  /\ FREE_KAT_N BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz both_addrs).

(* [comment removed for export] *)
Definition WALK_RESIDUAL_B {RC : run_ceil} (hv : AsAinvOomCell3.BoAinvBoot3.bvars) : Prop :=
  let bt := both_bt hv in
  MCASE_S bt AzSymStepR.fx_ok (ia_malloc both_addrs) P_sec
  /\ MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true.

Theorem walk_rows_of_residual_B : forall (RC : run_ceil) (hv : AsAinvOomCell3.BoAinvBoot3.bvars),
  boot_facts (both_bt hv) -> boot_totals (both_bt hv) -> WALK_RESIDUAL_B hv -> WALK_ROWS_B hv.
Proof.
  intros RC hv BF BTOT (HS & HD). unfold WALK_ROWS_B. cbv zeta.
  split; [exact (malloc_katw_at AzSymStepR.fx_ok hv BF BTOT HS)|].
  split; [exact (malloc_katw_thunk_at AzSymStepR.fx_ok hv BF BTOT HS)|].
  split; [exact (malloc_alt_at AzSymStepR.fx_ok hv BF BTOT HS)|].
  split; [exact (malloc_alt_thunk_at AzSymStepR.fx_ok hv BF BTOT HS)|].
  split; [exact (free_kat_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact (free_kat_thunk_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact (free_kat_opdel_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact (free_kat_opdel_sz_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact HD|].
  split; [exact (malloc_alt_sec_thunk_drx AzSymStepR.fx_ok hv HD)|].
  split; [exact (free_kat_n_drx_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact (free_kat_n_drx_thunk_at AzSymStepR.fx_ok hv BF BTOT)|].
  split; [exact (free_kat_n_drx_opdel_at AzSymStepR.fx_ok hv BF BTOT)|].
  exact (free_kat_n_drx_opdel_sz_at AzSymStepR.fx_ok hv BF BTOT).
Qed.

(* [comment removed for export] *)
Section Final.
  Hypothesis H_SEC_S : forall (RC : run_ceil) hv, boot_facts (both_bt hv) -> boot_totals (both_bt hv) ->
    MCASE_S (both_bt hv) AzSymStepR.fx_ok (ia_malloc both_addrs) P_sec.
  Hypothesis H_SEC_DR : forall (RC : run_ceil) hv, boot_facts (both_bt hv) -> boot_totals (both_bt hv) ->
    MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX (both_bt hv)) MSTK_A (ia_malloc both_addrs) true.

  Theorem WALK_all_B : forall (RC : run_ceil) (hv : AsAinvOomCell3.BoAinvBoot3.bvars),
    boot_facts (both_bt hv) -> boot_totals (both_bt hv) -> WALK_ROWS_B hv.
  Proof.
    intros RC hv BF BTOT. apply (walk_rows_of_residual_B RC hv BF BTOT).
    exact (conj (H_SEC_S RC hv BF BTOT) (H_SEC_DR RC hv BF BTOT)).
  Qed.
End Final.
End BoWalkRowsB.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoGrowDie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSbFin.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvDepotObl3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6.BoDepotGrantEx OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoGrowDie BoAllocMSbAsm.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Theorem hyp_depot9_closed : forall {RC : run_ceil} (bt : as_boot) (FXOK : FPState -> Prop),
  boot_facts bt -> boot_totals bt -> bt_segs bt = BSEGS -> bt_ia bt = both_addrs -> depot_cells bt -> depot_cells2 bt ->
  forall KD, 576 <= KD -> BoDepotTop3.BoDepotHyp9.HYP_DEPOT9_stmt bt FXOK KD.
Proof.
  intros RC bt FXOK BF BTOT BT_segs BT_ia DC DC2 KD HKD.
  pose proof (boot_facts_ok bt BF) as BOK. pose proof (boot_facts_geom bt BF) as BG.
  destruct (dep0_bounds bt BOK) as [DEP0 [_ DFR0]].
  apply (hyp_depot9_pf bt FXOK BT_segs BT_ia DC DC2 (depot_obls_pf bt)).
  - intros st Lc FF W ROOM KC. exact (depot_frames_room bt st Lc FF W ROOM KC DFR0).
  - exact DEP0.
  - exact BG.
  - exact (grant_ex_pf bt BOK BTOT).
  - exact (grant_nr_ex_pf bt BOK BTOT).
  - exact HKD.
Qed.

Section FinAt.
  Context {RC : run_ceil}.
  Variable hv : bvars.
  #[local] Abbreviation bt := (both_bt hv).
  #[local] Abbreviation FXOK := AzSymStepR.fx_ok.
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite both_bt_consts; (lazymatch goal with |- ?G => let G' := eval unfold both_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Ltac in_consts_nat i := lazymatch i with O => idtac | S ?j => in_consts_nat j end.
  Ltac in_consts_fast :=
    let G := match goal with |- ?G => eval cbv beta in G end in
    lazymatch G with In (?a, ?n, ?v) ?L =>
      let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                                if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
      in_consts_nat i; exact (nth_error_In L i eq_refl)
    end.
  Ltac in_consts := first [in_consts_fast | in_consts_old].
  #[local] Abbreviation TP := (ia_tp both_addrs).

  (* [comment removed for export] *)
  Lemma MCELLS_s : malloc_cells bt TP 0x662728 0x19dc60 0x10b9b8 0.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold malloc_cells in G in change_no_check G' end). repeat (split; [in_consts|]). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. Qed.
  Lemma PCELLS_s : pop_cells bt.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold pop_cells in G in change_no_check G' end). repeat (split; [in_consts|]). in_consts. Qed.
  Lemma SCELLS_s : sec_cells bt.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold sec_cells in G in change_no_check G' end). repeat (split; [in_consts|]). in_consts. Qed.
  Lemma DCELLS_s : depot_cells bt /\ depot_cells2 bt.
  Proof using. exact (depot_cells_both bt _ _ _ _ (both_bt_consts hv)). Qed.
  Lemma OOM_s : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x190420.
  Proof using. intros st Lc FF W. exact (oom_not_rep_B hv st Lc FF _ _ W). Qed.
  Lemma GEOM_s : free_boot_geom bt.  Proof using BF RC. exact (boot_facts_stack bt BF). Qed.
  Lemma BOOTG_s : boot_geom bt.  Proof using BF RC. exact (boot_facts_geom bt BF). Qed.
  Lemma HYP_DEPOT9_s : BoDepotTop3.BoDepotHyp9.HYP_DEPOT9_stmt bt FXOK 1312.
  Proof using BTOT BF. apply (hyp_depot9_closed bt FXOK BF BTOT eq_refl eq_refl (proj1 DCELLS_s) (proj2 DCELLS_s) 1312). lia. Qed.

  (* [comment removed for export] *)
  Lemma GROW_DIE_s :
    forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
      FXOK fx -> getr regs 2 = sp -> getr regs 18 = addr ->
      2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 -> 4096 <= U addr < 2 ^ 47 ->
      store_ok BSEGS M (at_ sp (-1072)) 1168 = true -> rdn BSEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1d5) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1dd) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e5) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      rdn BSEGS M (Z_to_bv 64 0x22730) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x613e0)) ->
      rdn BSEGS M (Z_to_bv 64 0x104a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
      rdn BSEGS M (Z_to_bv 64 0x105f58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
      rdn BSEGS M (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
      exists fx' r M', msteps BSEGS (@mkst fx regs (0x82fe8%bv : word) M rom) (@mkst fx' r (0x7ca24%bv : word) M' rom).
  Proof using. exact GD.grow_die_w. Qed.

  (* [comment removed for export] *)
  Hypothesis SEC_GRANTED_at : sec_granted_stmt bt FXOK.

  Theorem H_SEC_S_at : MCASE_S bt FXOK (ia_malloc both_addrs) P_sec.
  Proof using SEC_GRANTED_at BTOT BF.
    exact (malloc_sec_S bt FXOK TP 0x662728 0x19dc60 0x10b9b8 0 eq_refl eq_refl MCELLS_s PCELLS_s SCELLS_s (may_return_null_row_B hv) OOM_s
             GEOM_s BOOTG_s (boot_facts_ok bt BF) BTOT eq_refl SEC_GRANTED_at).
  Qed.
  Theorem H_SEC_DR_at : MALLOC_ALT_SEC BSEGS FXOK both_addrs (AAINV_DRX bt) MSTK_A (ia_malloc both_addrs) true.
  Proof using SEC_GRANTED_at BTOT BF.
    exact (malloc_sec_DR bt FXOK TP 0x662728 0x19dc60 0x10b9b8 0 eq_refl eq_refl MCELLS_s PCELLS_s SCELLS_s (may_return_null_row_B hv) OOM_s
             GEOM_s BOOTG_s (boot_facts_ok bt BF) BTOT eq_refl SEC_GRANTED_at).
  Qed.
End FinAt.
End BoAllocMSbFin.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSbFin2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvDepotObl3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop BoAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSg BoAllocMSbAsm BoAllocMSbFin.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section Fin2.
  Context {RC : run_ceil}.
  Variable hv : bvars.
  Hypothesis BF : boot_facts (both_bt hv).
  Hypothesis BTOT : boot_totals (both_bt hv).

  Theorem SEC_GRANTED_at : sec_granted_stmt (both_bt hv) AzSymStepR.fx_ok.
  Proof using BTOT BF.
    exact (sec_granted (both_bt hv) AzSymStepR.fx_ok (ia_tp both_addrs) 0x662728 0x19dc60 0x10b9b8 0 1312 eq_refl eq_refl
             (MCELLS_s hv) (PCELLS_s hv) (SCELLS_s hv) BF eq_refl ltac:(lia) ltac:(right; lia) (HYP_DEPOT9_s hv BF BTOT) (GROW_DIE_s)).
  Qed.

  Theorem H_SEC_S : MCASE_S (both_bt hv) AzSymStepR.fx_ok (ia_malloc both_addrs) P_sec.
  Proof using BTOT BF. exact (H_SEC_S_at hv BF BTOT SEC_GRANTED_at). Qed.

  Theorem H_SEC_DR : MALLOC_ALT_SEC BSEGS AzSymStepR.fx_ok both_addrs (AAINV_DRX (both_bt hv)) MSTK_A (ia_malloc both_addrs) true.
  Proof using BTOT BF. exact (H_SEC_DR_at hv BF BTOT SEC_GRANTED_at). Qed.
End Fin2.
End BoAllocMSbFin2.
(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.BoAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 BoWalkRowsB BoAllocMSbFin2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem WALK_all_B_closed : forall (RC : run_ceil) (hv : AsAinvOomCell3.BoAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (both_bt hv) -> AsKSys10.AsKSys11.boot_totals (both_bt hv) -> @BoWalkRowsB.WALK_ROWS_B RC hv.
Proof.
  exact (BoWalkRowsB.WALK_all_B
           (fun RC hv BF BT => @BoAllocMSbFin2.H_SEC_S RC hv BF BT)
           (fun RC hv BF BT => @BoAllocMSbFin2.H_SEC_DR RC hv BF BT)).
Qed.
