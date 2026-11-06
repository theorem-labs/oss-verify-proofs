(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame AKit AKit2 AModelFacts ASec AFreeModel AFreeRep AFreeGeo. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_afree_iseg F_afree_tail F_afree_icpt. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_afree_tailR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.F_afreeC_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_afree_arep ARecGeo F_adorec AQrecP AFrameD AFreeC_kit_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFreeBack ADeallocC_kit_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Theorem afree_back_D : forall DI AFK CI, afree_back_stmt_D DI AFK CI.
Proof.
  intros DI AFK CI. unfold afree_back_stmt_D. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP RIMG RSTK RET QL0 QLB0.
  destruct RET as (t0 & t1 & t2 & a0 & a1 & a2 & a3' & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & R1 & -> & FPLE1 & ARNG1 & T1 & PB1 & PE1 & LOC1
                   & AR1 & BL1 & AF1 & MI1 & ST & MU1 & CP1 & ELIVE & ENEXT & EQLOC & EQLB & ENRES & EPA & ESB & GB1).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.

  assert (D : forall A n, bv_unsigned sp - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  clear FRP.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x41168)) with (Z_to_bv 64 0x41168 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).

  do 8 step.
  zstep.
  step.
  try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp).

  apply evtF_done. unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -80) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  -
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    pose proof AR1 as (A1 & A2 & A3 & A4 & A5 & HQ & HS & HD & A9 & A10 & A11 & A12).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    +
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    +
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB AKitQ.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB ARep.TwinB ARepQ.TwinB ARepQP.TwinB ARepQR.TwinB ARepQD.TwinB ALayout.TwinB AHeapP.TwinB ARepKit.TwinB ARepFrame.TwinB AKit.TwinB AKit2.TwinB AModelFacts.TwinB ASec.TwinB AFreeModel.TwinB AFreeRep.TwinB AFreeGeo.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import F_afree_iseg.TwinB F_afree_tail.TwinB F_afree_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_afree_tailR.TwinB.F_afreeC_iface. Import F_afree_arep.TwinB ARecGeo.TwinB F_adorec.TwinB AQrecP.TwinB AFrameD.TwinB AFreeC_kit_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import AFreeBack.TwinB ADeallocC_kit_iface.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Theorem afree_back_D : forall DI AFK CI, afree_back_stmt_D DI AFK CI.
Proof.
  intros DI AFK CI. unfold afree_back_stmt_D. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP RIMG RSTK RET QL0 QLB0.
  destruct RET as (t0 & t1 & t2 & a0 & a1 & a2 & a3' & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & R1 & -> & FPLE1 & ARNG1 & T1 & PB1 & PE1 & LOC1
                   & AR1 & BL1 & AF1 & MI1 & ST & MU1 & CP1 & ELIVE & ENEXT & EQLOC & EQLB & ENRES & EPA & ESB & GB1).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = bv_unsigned sp - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.

  assert (D : forall A n, bv_unsigned sp - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  clear FRP.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x41af8)) with (Z_to_bv 64 0x41af8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).

  do 8 step.
  zstep.
  step.
  try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp).

  apply evtF_done. unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -80) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  -
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    pose proof AR1 as (A1 & A2 & A3 & A4 & A5 & HQ & HS & HD & A9 & A10 & A11 & A12).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    +
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    +
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC2.
End TwinB.
