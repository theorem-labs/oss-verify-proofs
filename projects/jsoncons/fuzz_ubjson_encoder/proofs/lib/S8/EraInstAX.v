(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceANull IcptIfaceA LibIface LibIfaceAB ArtRuns ArtBridge EarInv EarFsInv EarHandoffRi EarIfaceInst EarIfaceInstFree EarIfaceLayout
  EarWrapSmallocI EarIcptInst Ea0DefsK Ea0Drv_defs Ea0DrvLib Ea0DrvRead EraMainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIfaceAEx StrictOfB EarIfaceInstAnn EraInstA L5Defs PeSpecsAa EarIfaceLayoutPM PeACxa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem as0_ext_ok_pma : forall scfg BUDGET, sc_alloc scfg = false -> ext_ok_stmt scfg art_L PMA.EXT BUDGET.
Proof.
  intros scfg BUDGET Halloc.
  apply (as0_ext_ok scfg BUDGET PMA.EXT eq_refl eq_refl eq_refl eq_refl).
  intros MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  assert (SM : forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) k)
    by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
  pose proof (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
                (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp) SM) as OKR.
  exact (@PMACXA.cxa_atexit_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) art_pma_layout OKR
           (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn Htp Hkey Htsd Hloff)).
Qed.
