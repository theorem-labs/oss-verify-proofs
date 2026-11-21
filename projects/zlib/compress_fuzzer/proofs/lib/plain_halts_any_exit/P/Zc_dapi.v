(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr ITree Nodes MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Malloc Monad ZApi ZHarness ZInst ZTarget ZApiC ZHarnessC ZInstC ZTargetC Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Drv_kit Zlib_iface Zh_kit Z_kit Z_dview Z_drep Z_zrd Zg_defl_path2 Zg_defl_pathi2 Zg_dinit_modelG Zg_dinit_ifaceG Zg_dend2 Zc_zrd Zc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState ZApiInst ZApiInstC ZTaint ZTaintC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Local Transparent the_zapi the_zapiC.

Lemma deflate_initC_progG : deflate_initC lops the_zapiC = dinit_progG.
Proof. reflexivity. Qed.

Lemma deflate_endC_end : forall b, deflate_endC lops b = ZTarget.deflate_end lops b.
Proof. intros [[[[? ?] ?] ?] ?]. reflexivity. Qed.

Lemma blk5_zd_blocks : forall (b : bptr * bptr * bptr * bptr * bptr) S As Aw Ap Ah Ab ni no,
  blk5_blocks b As Aw Ap Ah Ab = zd_blocks b (Z_drep.mkDL S As Aw Ap Ah Ab ni no).
Proof. intros [[[[sp wp] pp] hp] bp] S As Aw Ap Ah Ab ni no. reflexivity. Qed.

Lemma zd_blocks_inj : forall (b b' : bptr * bptr * bptr * bptr * bptr) As Aw Ap Ah Ab L,
  blk5_blocks b As Aw Ap Ah Ab = zd_blocks b' L -> b = b' /\ As = dl_As L /\ Aw = dl_Aw L /\ Ap = dl_Ap L /\ Ah = dl_Ah L /\ Ab = dl_Ab L.
Proof.
  intros [[[[sp wp] pp] hp] bp] [[[[sp' wp'] pp'] hp'] bp'] As Aw Ap Ah Ab L H.
  unfold blk5_blocks, zd_blocks in H. cbn [z_dpend z_dhead z_dprev z_dwin z_dstate the_zapi zinst] in H.
  injection H as -> -> -> -> -> -> -> -> -> ->. repeat split; reflexivity.
Qed.

Section DINIT.
  Hypothesis DINITG : forall lv, 0 <= lv <= 9 -> deflateInit_stmtG lv.

  Theorem deflateInit_proofC : forall R : zreps, Zlib_iface.zr_d R = zr_dC -> forall lv, 0 <= lv <= 9 -> deflateInit_stmtC R lv.
  Proof.
    intros R RD lv Hlv. unfold deflateInit_stmtC. intros until canary. intros ENV ZS SIF LOSP SP16 FRM -> -> -> ->.
    rewrite deflate_initC_progG.
    eapply implM_mono.
    { eapply (DINITG lv Hlv); [exact ENV| exact ZS| exact SIF| exact LOSP| exact SP16| exact FRM| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros r s' ms' PO. unfold deflateInit_postG in PO. unfold deflateInit_postC.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & -> & PO).
    do 15 eexists. exists F', fc', m'. split; [reflexivity|].
    destruct r as [b|].
    - destruct PO as (As & Aw & Ap & Ah & Ab & G & LPE & HA0 & PUB & DQ & DCL). exists As, Aw, Ap, Ah, Ab.
      split; [exact LPE|]. split; [exact HA0|]. split; [exact PUB|].
      split; [unfold dsc_tin; cbn [dc_init zinstC]; rewrite (dzC_init_scalars lv Hlv); reflexivity|].
      split; [unfold dsc_tout; cbn [dc_init zinstC]; rewrite (dzC_init_scalars lv Hlv); reflexivity|].
      rewrite RD. rewrite (blk5_zd_blocks b S As Aw Ap Ah Ab 0 0).
      set (L0 := Z_drep.mkDL S As Aw Ap Ah Ab 0 0) in *.
      replace S with (dl_S L0) by reflexivity.
      cbn [dc_init zinstC]. apply (zr_dC_init m' L0 b G lv Hlv); [| exact DCL].
      unfold dinitG_of, zsG in DQ. unfold dinitC_of. exact DQ.
    - exact PO.
  Qed.
End DINIT.

Section DEND.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.

  Theorem deflateEnd_proofC : forall R : zreps, Zlib_iface.zr_d R = zr_dC -> deflateEnd_stmtC R.
  Proof.
    intros R RD. unfold deflateEnd_stmtC. intros until canary. intros ENV PUB ZR SIF LOSP SP16 FRM ->.
    rewrite RD in ZR. destruct ZR as (L & sa & b' & ELB & ES & DQ & DR & PT & DCL & ZOK).
    destruct (zd_blocks_inj b b' As Aw Ap Ah Ab L ELB) as (<- & -> & -> & -> & -> & ->).
    rewrite ELB in ENV. subst S.
    rewrite deflate_endC_end.
    eapply implM_mono.
    { eapply (deflateEnd_drep2 FREE HND HBR HFRAME L sa (dz_z ds));
        [exact ENV| exact PUB| exact DQ| exact (zr_dC_check sa PT)| exact SIF| exact LOSP| exact SP16| exact FRM| unfold Z_DEFLATEEND_A; reflexivity]. }
    cbv beta. intros [] s' ms' PO. unfold deflateEnd_post2 in PO. unfold deflateEnd_postC.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & -> & LPE & HA0 & RAW).
    do 15 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact LPE|]. split; [| exact RAW].
    rewrite HA0. rewrite (zr_dC_dend2 sa ds DR PT). reflexivity.
  Qed.
End DEND.
End WithCeiling0.
