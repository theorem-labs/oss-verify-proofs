(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr HeapIfaceANull IcptIfaceA
     ArtMem ArtRuns ArtBridge EatLift EarDep EarUkey EarInv EarInvFreePure EarFsInv EarFsInvLaws EarFsInvLaws4 EarWrapKit EarWrapFreeR
     EarWrapMallocAll EarWrapFree EarWrapMemI EarWrapSmallocI EarIfaceLaws EarIfaceInst EarIfaceInstFree EarIfaceInstAnn EarIfaceInstSfree EarIfaceLayoutPM
     EarIcptInst EarIcptLawsGap EarFam.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import StrictOfB L5Defs PeSpecsAa PeACxa PeAImgGap PeCTopAsmA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FamTop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable IL : icpt_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x675a80.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x696f38.
Hypothesis Hloff : rn_loff rn = 0x10.
Hypothesis ILY : as0_icpt_layout IL.

#[local] Abbreviation HIk := (art_HIk MAPS0 RESV0 NOACC0 BASE BUDGET rn).

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_inst : forall D, @PECASMA.inst_ok (MkScfgP scfg) art_L art_C IL (rn_ar rn) (HIk D).
Proof.
  intros D. set (rnD := art_rn_k rn D).
  assert (SM : forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIk D) k) by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
  pose proof (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff
                (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Halloc Hwx STATIC Htp) SM) as OKR.
  split; [exact OKR|]. split; [exact (art_icpt_ok scfg IL BUDGET Hwx ILY MAPS0 RESV0 NOACC0 BASE rnD Htp Hkey0 Htsd Hloff)|]. split.
  - apply HAJ.AEXT.
    + exact (art_inst_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
    + exact (@PMACXA.cxa_atexit_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIk D) art_pma_layout OKR (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rnD Htp Hkey0 Htsd Hloff)).
    + exact (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rnD Htp Hkey0 Htsd Hloff).
    + exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
    + exact (art_inst_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rnD scfg Hwx Htp).
  - exact (art_law_img_gap MAPS0 RESV0 NOACC0 BASE BUDGET rnD).
Qed.

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_top : @PECASMA.fam_ok (MkScfgP scfg) art_L art_C IL art_LR (rn_ar rn) HIk.
Proof.
  split; [exact (art_fam_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff)|].
  exact art_fam_inst.
Qed.
End FamTop.
