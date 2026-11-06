(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull IcptIfaceA LibIface LibIfaceAB ArtRuns ArtBridge BatInv BatFsInv BatHandoffRi BatIfaceInst BatIfaceInstFree BatIfaceLayout
  BatWrapSmallocI BatIcptInst Ba0DefsK Ba0Drv_defs Ba0DrvLib Ba0DrvRead Ba0MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx StrictOfB BatIfaceInstAnn Ba0InstA L5Defs PnSpecsAa BatIfaceLayoutPM PnACxa.
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
