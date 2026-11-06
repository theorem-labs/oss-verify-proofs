(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx EbrInv EbrFsInv EbrIfaceInst EbrWrapSmalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_inst_smalloc : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> rn_tp rn = 0x67a180 ->
  forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) k.
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx Htp k Hk.
  apply (art_asmalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity; [symmetry; exact Htp | exact Htp | exact Hk].
Qed.
