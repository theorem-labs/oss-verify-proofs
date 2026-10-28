(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b BatHandoffRi_b BatIfaceInst_b BatIfaceInstFree_b BatIfaceLayout_b
  BatWrapSmallocI_b BatIcptInst_b Ba0DefsK_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0MainPhaseA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx StrictOfB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatIfaceInstAnn_b Ba0InstA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAa_b BatIfaceLayoutPM_b PnACxa_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Theorem as0_ext_ok_pma : forall scfg BUDGET, sc_alloc scfg = false -> ext_ok_stmt scfg art_L PMA.EXT BUDGET.
Proof.
  intros scfg BUDGET Halloc.
  apply (as0_ext_ok scfg BUDGET PMA.EXT eq_refl eq_refl eq_refl eq_refl).
  intros MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  assert (SM : forall k, In k [0; 1; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) k)
    by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
  pose proof (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
                (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp) SM) as OKR.
  exact (@PMACXA.cxa_atexit_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) art_pma_layout OKR
           (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn Htp Hkey Htsd Hloff)).
Qed.
