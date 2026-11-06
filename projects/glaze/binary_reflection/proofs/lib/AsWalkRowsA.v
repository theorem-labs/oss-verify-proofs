(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRcK6n.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.AsAllocFRc4V.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.AsAllocFRcK6g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcK6h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.AsAllocFRcK6m.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFKeep0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3.
Import OSSVerify.glaze.binary_reflection.images.Asan.
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
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis HTPm : TPm = ia_tp asan_addrs.
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
End AsAllocFRcK6n.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFPutBg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFTopMp.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS.AsAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFRcK2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFRcK3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFRcK5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFRcK6b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.AsAllocFRcK6c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFRcMK5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW9.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFThunk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFPutBg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW10.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopBg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocFRefillG OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Ls.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopRf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp AsAllocFRcK6n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.




Section W14.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  (* [comment removed for export] *)
  Hypothesis BF : AsKSys10.AsAinvBootF3.boot_facts bt.
  Hypothesis BTOT : AsKSys10.AsKSys11.boot_totals bt.
  Hypothesis DC1 : AsDepotTop3.AsDepotTop1.depot_cells bt.
  Hypothesis DC2 : AsDepotTopN1b.AsDepotTopN1a.depot_cells2 bt.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Variable MINSZ : Z.
  Hypothesis CELL_min : In (0x103f18 + 800, 8%nat, MINSZ) (bt_consts bt).     (* [comment removed for export] *)
  Hypothesis G_min : 0 <= MINSZ <= 2 ^ 28.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis HTPm : TPm = ia_tp asan_addrs.
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

  Theorem free_kat_W14 : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_free asan_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_W13 bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14 : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free asan_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13 bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_thunk : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk asan_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_thunk bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_opdel : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel asan_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_opdel bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
  Theorem free_kat_n_drx14_opdel_sz : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz asan_addrs).
  Proof using QHDR_CONST PCELLS CELLSM HTPm MIDENDm FLm PGPm TSDPm TPm CELLSPIN SHGATE BOOTG SECC RCF RCC G_min CELL_min MINSZ HTP DC2 DC1 BTOT BF GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP. exact (free_kat_n_drx13_opdel_sz bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB GEOM BF BTOT DC1 DC2 HTP MINSZ CELL_min G_min RCC RCF SECC BOOTG SHGATE CELLSPIN TPm TSDPm PGPm FLm MIDENDm HTPm CELLSM PCELLS HYP_ITEM_FULL_MAP_PF HYP_BFREE_FULL_MAP_PF). Qed.
End W14.
End AsAllocFTopMp.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMW1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.Asan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  Theorem malloc_case_hit : MCASE bt FXOK (ia_malloc asan_addrs) P_hit.
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    eapply (case_hit bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
  Qed.
End W1.
End AsAllocMW1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMW3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.Asan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.

  Theorem malloc_case_miss : MCASE bt FXOK (ia_malloc asan_addrs) P_miss.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    apply (case_miss bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS GEOM BOOTG G_KD HYP_DEPOT HTP).
    - eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    - exact (miss_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP).
  Qed.

  (* [comment removed for export] *)
  Theorem malloc_case_miss_alt : MCASE_S bt FXOK (ia_malloc asan_addrs) P_fresh_prim.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    apply (case_miss_alt bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS GEOM BOOTG G_KD HYP_DEPOT HTP).
    - eapply (malloc_partB bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption.
    - exact (miss_null bt FXOK TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS NCELL OOM_NOT_REP).
  Qed.
End W3.
End AsAllocMW3.
Module AsAllocMW4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4 AsAllocMW1 AsAllocMW3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.Asan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W4.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.

  Theorem malloc_katw_of_sec :
    MCASE bt FXOK (ia_malloc asan_addrs) P_sec ->
    MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof using OOM_NOT_REP HTP HYP_DEPOT G_KD BOOTG GEOM NCELL PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros HS. apply (malloc_katw_of_cases bt FXOK (ia_malloc asan_addrs)).
    - exact (malloc_case_hit bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT HTP).
    - exact (malloc_case_miss bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS PCELLS NCELL GEOM BOOTG G_KD HYP_DEPOT HTP OOM_NOT_REP).
    - exact HS.
  Qed.
End W4.
End AsAllocMW4.
Module AsAllocMW5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop AsAllocMW4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section W5.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis DC : depot_cells bt.
  Hypothesis DC2 : depot_cells2 bt.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.

  Theorem malloc_katw_of_sec5 :
    MCASE bt FXOK (ia_malloc asan_addrs) P_sec ->
    MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof using OOM_NOT_REP HTP DC2 DC BTOT BF GEOM NCELL PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    exact (malloc_katw_of_sec bt FXOK TP TSDP PGP FL MIDEND 1312 BT_segs BT_ia CELLS PCELLS NCELL GEOM (boot_facts_geom bt BF) ltac:(lia)
             (hyp_depot_closed bt FXOK BF BTOT BT_segs BT_ia DC DC2 1312 ltac:(lia)) HTP OOM_NOT_REP).
  Qed.
End W5.
End AsAllocMW5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsContractsMallocA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOomCell3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 AsAllocMW3 AsAllocMW4 AsAllocMW5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocMThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation U := bv_unsigned.

Section MallocAt.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (asan_bt hv).
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite asan_bt_consts; unfold asan_consts; cbv zeta; repeat (first [left; reflexivity | right]).
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

  #[local] Notation TP := (ia_tp asan_addrs).
  Definition TSDP_M : Z := 0x65bae8.
  Definition PGP_M : Z := 0x197020.
  Definition FL_M : Z := 0x104d78.

  Lemma MCELLS_at : malloc_cells bt TP TSDP_M PGP_M FL_M 0.
  Proof. unfold malloc_cells, TSDP_M, PGP_M, FL_M. repeat (split; [in_consts|]). cbn. lia. Qed.
  Lemma PCELLS_at : pop_cells bt.
  Proof. unfold pop_cells. repeat (split; [in_consts|]). in_consts. Qed.
  Lemma DCELLS_at : depot_cells bt /\ depot_cells2 bt.
  Proof. exact (depot_cells_asan bt _ _ _ _ (asan_bt_consts hv)). Qed.
  Lemma OOM_at : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.
  Proof. intros st Lc FF W. exact (oom_not_rep_A hv st Lc FF _ _ W). Qed.

  (* [comment removed for export] *)
  Lemma HYP_DEPOT_at : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK 1312.
  Proof. apply (hyp_depot_closed bt FXOK BF BTOT eq_refl eq_refl (proj1 DCELLS_at) (proj2 DCELLS_at) 1312). lia. Qed.
  Lemma case_fresh_prim_at : MCASE_S bt FXOK (ia_malloc asan_addrs) P_fresh_prim.
  Proof.
    exact (malloc_case_miss_alt bt FXOK TP TSDP_M PGP_M FL_M 0 1312 eq_refl eq_refl MCELLS_at PCELLS_at (may_return_null_row_A hv)
             (boot_facts_stack bt BF) (boot_facts_geom bt BF) ltac:(lia) HYP_DEPOT_at eq_refl OOM_at).
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_SEC_S : MCASE_S bt FXOK (ia_malloc asan_addrs) P_sec.

  Lemma case_sec_at : MCASE bt FXOK (ia_malloc asan_addrs) P_sec.
  Proof.
    intros h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP.
    apply katsD_katwD. exact (H_SEC_S h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HP).
  Qed.

  Theorem malloc_katw_at : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof.
    exact (malloc_katw_of_sec5 bt FXOK TP TSDP_M PGP_M FL_M 0 eq_refl eq_refl MCELLS_at PCELLS_at (may_return_null_row_A hv)
             (boot_facts_stack bt BF) BF BTOT (proj1 DCELLS_at) (proj2 DCELLS_at) eq_refl OOM_at case_sec_at).
  Qed.
  Theorem malloc_katw_thunk_at : MALLOC_KATW ASEGS FXOK asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Proof. exact (malloc_katw_thunk bt FXOK eq_refl MSTK_A true malloc_katw_at). Qed.

  (* [comment removed for export] *)
  Theorem malloc_alt_at : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc asan_addrs) true.
  Proof.
    intros h fx R M mdl Lc FF B C K ret n sp PRE FR.
    destruct PRE as (HLT & HFX & AI & HO & CP & HR10 & Hn & FPC & HB & HC & HK).
    destruct AI as (st & W & RP & [BD HL] & MW).
    destruct (FRESH_at bt Lc FF B C K M mdl n st FR W RP) as [Hs | [Hp (F1 & F2 & F3)]].
    - exact (H_SEC_S h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK Hs).
    - exact (case_fresh_prim_at h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK
               (conj Hp (conj F1 (conj F2 F3)))).
  Qed.
  Theorem malloc_alt_thunk_at : MALLOC_ALT ASEGS FXOK asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Proof. exact (malloc_alt_thunk bt FXOK eq_refl (FRESH_bt bt) (FRESH_sbm bt) MSTK_A true malloc_alt_at). Qed.

  (* [comment removed for export] *)
  Hypothesis H_SEC_DR : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true.

  (* [comment removed for export] *)
  Theorem malloc_alt_sec_thunk_drx : MALLOC_ALT_SEC ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk asan_addrs) true.
  Proof.
    intros fx R M mdl Lc FF B C K ret n sp PRE Hbig.
    pose proof PRE as (HH & HFX & AI & REST).
    destruct AI as (st & W & RP & BH & MW).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    unfold cfg.
    apply (katsD_step_acct ASEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl eq_refl RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 (ia_malloc_thunk asan_addrs)) M (seg_rom ASEGS))
             (@mkst fx R (Z_to_bv 64 (ia_malloc asan_addrs)) (mrestrict (HID st mdl) M) (seg_rom ASEGS)) mdl).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - reflexivity.
    - exact (jstep_malloc_thunk fx R (mrestrict (HID st mdl) M)).
    - intros mdl1 MI1 SBM1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx R (Z_to_bv 64 (ia_malloc_thunk asan_addrs)) M (seg_rom ASEGS))) with M by reflexivity.
      rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      assert (PRE1 : malloc_pre ASEGS FXOK asan_addrs (AAINV_DRX bt) None MSTK_A true fx R M mdl1 Lc FF B C K ret n sp).
      { split; [rewrite Ehl; exact HH|]. split; [exact HFX|]. split; [| exact REST].
        exists st. split; [exact W|]. split; [exact (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1)|].
        split; [exact BH | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]. }
      apply (katsD_conseq ASEGS _ _ _ _ _ (H_SEC_DR fx R M mdl1 Lc FF B C K ret n sp PRE1 Hbig)).
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
End AsContractsMallocA.
Module AsContractsFreeA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys5q OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS.AsAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFTopW10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp.AsAllocFThunk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTopDp AsAllocFTopMp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK6p.AsAllocMQhdr OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a AsContractsMallocA.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FreeAt.
  Context {RC : run_ceil}.
  Variable FXOK : FPState -> Prop.
  Variable hv : bvars.
  #[local] Notation bt := (asan_bt hv).
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.

  Ltac in_consts_old := rewrite asan_bt_consts; unfold asan_consts; cbv zeta; repeat (first [left; reflexivity | right]).
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

  #[local] Notation TP := (ia_tp asan_addrs).
  Definition TSDP_A : Z := 0x65bae8.
  Definition PGP_A : Z := 0x197020.
  Definition FL_A : Z := 0x104d78.
  Definition MINSZ_A : Z := 0xe666661.

  Lemma CELLS_at : free_cells bt TP TSDP_A PGP_A FL_A 0 1.
  Proof. unfold free_cells, TSDP_A, PGP_A, FL_A. repeat (split; [in_consts|]). cbn. lia. Qed.
  Lemma CELLNB_at : free_cells_nb bt.  Proof. unfold free_cells_nb, IB. cbn [bt_ia asan_bt ia_instance asan_addrs bt_spacebeg]. in_consts. Qed.
  Lemma CELL_min_at : In (0x103f18 + 800, 8%nat, MINSZ_A) (bt_consts bt).  Proof. unfold MINSZ_A. in_consts. Qed.
  Lemma RCC_at : rc_cells bt TSDP_A.
  Proof. unfold rc_cells, IB, TSDP_A. cbn [bt_ia asan_bt ia_instance asan_addrs bt_spacebeg]. split; [in_consts|]. split; [in_consts | lia]. Qed.
  Lemma RCF_at : rc_cells_full bt.  Proof. unfold rc_cells_full. repeat (split; [in_consts|]). in_consts. Qed.
  Lemma SECC_at : sec_cells bt TSDP_A.
  Proof. unfold sec_cells, IB, TSDP_A. cbn [bt_ia asan_bt ia_instance asan_addrs bt_ptrarr]. repeat (split; [in_consts|]). lia. Qed.
  Lemma CELLSPIN_at : free_cells_spin bt.  Proof. unfold free_cells_spin. repeat (split; [in_consts|]). in_consts. Qed.

  (* [comment removed for export] *)
  Lemma QHDR_CONST_at : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  Proof. exact (qhdr_const_asan bt _ _ _ _ eq_refl (asan_bt_consts hv)). Qed.

  Lemma G_min_at : 0 <= MINSZ_A <= 2 ^ 28.  Proof. unfold MINSZ_A. lia. Qed.

  Theorem free_kat_at : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_free asan_addrs).
  Proof.
    exact (free_kat_W14 bt FXOK TP TSDP_A PGP_A FL_A 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_A CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_thunk_at : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_free_thunk asan_addrs).
  Proof. exact (free_kat_thunk bt FXOK eq_refl MSTK_A free_kat_at). Qed.
  Theorem free_kat_opdel_at : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_opdel asan_addrs).
  Proof. exact (free_kat_opdel bt FXOK eq_refl MSTK_A free_kat_at). Qed.
  Theorem free_kat_opdel_sz_at : FREE_KAT ASEGS FXOK asan_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz asan_addrs).
  Proof. exact (free_kat_opdel_sz bt FXOK eq_refl MSTK_A free_kat_at). Qed.

  (* [comment removed for export] *)
  Theorem free_kat_n_drx_at : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free asan_addrs).
  Proof.
    exact (free_kat_n_drx14 bt FXOK TP TSDP_A PGP_A FL_A 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_A CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_thunk_at : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk asan_addrs).
  Proof.
    exact (free_kat_n_drx14_thunk bt FXOK TP TSDP_A PGP_A FL_A 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_A CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_opdel_at : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel asan_addrs).
  Proof.
    exact (free_kat_n_drx14_opdel bt FXOK TP TSDP_A PGP_A FL_A 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_A CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
  Theorem free_kat_n_drx_opdel_sz_at : FREE_KAT_N ASEGS FXOK asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz asan_addrs).
  Proof.
    exact (free_kat_n_drx14_opdel_sz bt FXOK TP TSDP_A PGP_A FL_A 0 1 eq_refl eq_refl CELLS_at CELLNB_at (boot_facts_stack bt BF) BF BTOT
             (proj1 (DCELLS_at hv)) (proj2 (DCELLS_at hv)) eq_refl MINSZ_A CELL_min_at G_min_at RCC_at RCF_at SECC_at (boot_facts_geom bt BF) (boot_facts_gate bt BF) CELLSPIN_at
             TP TSDP_M PGP_M FL_M 0 eq_refl (MCELLS_at hv) (PCELLS_at hv) QHDR_CONST_at).
  Qed.
End FreeAt.
End AsContractsFreeA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFArms OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcKS.AsAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFRcK6a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP4.AsAllocMTopP3 AsContractsMallocA AsContractsFreeA.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition WALK_ROWS_A {RC : run_ceil} (hv : AsAinvBoot3.bvars) : Prop :=
  let bt := asan_bt hv in
  MALLOC_KATW ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_KATW ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ MALLOC_ALT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_ALT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_HS bt) (FRESH_bt bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_free asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_free_thunk asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_opdel asan_addrs)
  /\ FREE_KAT ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_H bt) MSTK_A (ia_opdel_sz asan_addrs)
  /\ MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true
  /\ MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc_thunk asan_addrs) true
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_free asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_free_thunk asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel asan_addrs)
  /\ FREE_KAT_N ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_opdel_sz asan_addrs).

(* [comment removed for export] *)
Definition WALK_RESIDUAL_A {RC : run_ceil} (hv : AsAinvBoot3.bvars) : Prop :=
  let bt := asan_bt hv in
  MCASE_S bt AzSymStepR.fx_ok (ia_malloc asan_addrs) P_sec
  /\ MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX bt) MSTK_A (ia_malloc asan_addrs) true.

Theorem walk_rows_of_residual_A : forall (RC : run_ceil) (hv : AsAinvBoot3.bvars),
  boot_facts (asan_bt hv) -> boot_totals (asan_bt hv) -> WALK_RESIDUAL_A hv -> WALK_ROWS_A hv.
Proof.
  intros RC hv BF BTOT (HS & HD). unfold WALK_ROWS_A. cbv zeta.
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
  Hypothesis H_SEC_S : forall (RC : run_ceil) hv, boot_facts (asan_bt hv) -> boot_totals (asan_bt hv) ->
    MCASE_S (asan_bt hv) AzSymStepR.fx_ok (ia_malloc asan_addrs) P_sec.
  Hypothesis H_SEC_DR : forall (RC : run_ceil) hv, boot_facts (asan_bt hv) -> boot_totals (asan_bt hv) ->
    MALLOC_ALT_SEC ASEGS AzSymStepR.fx_ok asan_addrs (AAINV_DRX (asan_bt hv)) MSTK_A (ia_malloc asan_addrs) true.

  Theorem WALK_all_A : forall (RC : run_ceil) (hv : AsAinvBoot3.bvars),
    boot_facts (asan_bt hv) -> boot_totals (asan_bt hv) -> WALK_ROWS_A hv.
  Proof.
    intros RC hv BF BTOT. apply (walk_rows_of_residual_A RC hv BF BTOT).
    exact (conj (H_SEC_S RC hv BF BTOT) (H_SEC_DR RC hv BF BTOT)).
  Qed.
End Final.
