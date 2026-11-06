(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceANull ArtMem ArtRuns ArtBridge EarInv EarFsInv EarFsInvLaws
     EarInvFreePure EarInvRepX EarFsInvLaws4 EarWrapFree EarWrapFreeNull EarIfaceInst.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarInvFreePure EarWrapFreeR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x675a80.

#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_free : afree_spec art_L (rn_ar rn) scfg HI.
Proof.
  apply (art_wrap_free art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
  - symmetry. exact Htp.
  - exact art_L_statics.
  - exact art_fsinv_frame_law_proved.
  - intros rn0 D g FF LK M FS. exact FS.
  - intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
  - intros rn0 D g FF LK M FS. exact FS.
  - exact (art_fsinv_frame_law2_proved rn).
Qed.

#[using="Hwx Htp"] Theorem art_inst_free_null : afree_null_spec art_L (rn_ar rn) scfg HI.
Proof.
  apply (art_wrap_free_null art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Hwx); try reflexivity.
  - symmetry. exact Htp.
  - exact art_L_statics.
  - exact art_fsinv_frame_law_proved.
  - intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
Qed.
End Inst.
