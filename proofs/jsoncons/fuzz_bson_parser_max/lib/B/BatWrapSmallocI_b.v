(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b BatIfaceInst_b BatWrapSmalloc_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_inst_smalloc : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> rn_tp rn = 0x673d00 ->
  forall k, In k [0; 1; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) k.      (* [comment removed for export] *)
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx Htp k Hk.
  apply (art_asmalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity; [symmetry; exact Htp | exact Htp | exact Hk].
Qed.
