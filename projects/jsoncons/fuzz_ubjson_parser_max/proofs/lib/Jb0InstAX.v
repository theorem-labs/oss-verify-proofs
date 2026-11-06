(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceANull IcptIfaceAB0 LibIface LibIfaceAJ ArtRuns ArtBridge JbtInv JbtFsInv JbtHandoffRi JbtIfaceInst JbtIfaceInstFree JbtIfaceLayout
JbtWrapSmallocI JbtIcptInst Jb0DefsK Jb0Drv_defs Jb0DrvLib Jb0DrvRead Jb0MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx StrictOfJ JbtIfaceInstAnn Jb0InstA L5Defs PmSpecsAb JbtIfaceLayoutPM PmBCxa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem as0_ext_ok_pma : forall scfg BUDGET, sc_alloc scfg = false -> ext_ok_stmt scfg art_L PMB.EXT BUDGET.
Proof.
intros scfg BUDGET Halloc.
apply (as0_ext_ok scfg BUDGET PMB.EXT eq_refl eq_refl).
intros MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
assert (SM : forall k, In k [0; 1; 2; 3; 4] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) k)
by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
pose proof (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
(art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp) SM) as OKR.
exact (@PMBCXA.cxa_atexit_ok (MkScfgP scfg) art_L (rn_ar rn) art_C (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) art_pma_layout OKR
(art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn Htp Hkey Htsd Hloff)).
Qed.
