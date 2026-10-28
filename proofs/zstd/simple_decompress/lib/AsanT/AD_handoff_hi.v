(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image Mem Cells Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AD_handoff0 AZ_globals AD_handoff_ro AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Lemma harness_invA_init : forall V m, Forall (mfact_ok bsegs V m) both_mem_facts -> harness_invA m.
Proof.
  intros V m HM. split.
  - unfold APDCTX. aimg V m HM 0x602380 [C8 (Z_to_bv 64 0)] H. exact H.
  - exact (aro_clientM_init V m HM).
Qed.
End CANSEC1.
