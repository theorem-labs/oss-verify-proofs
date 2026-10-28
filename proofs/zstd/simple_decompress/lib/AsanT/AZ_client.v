(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstanceM AInstanceF AFreeAll
     AZ_kit AZ_fake_heap AZ_frame_iface AZ_dframe_iface AZ_dctx_iface AZ_dctx_iface_m AZ_prod_iface AZ_harness.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition lib_stmtsA : Prop :=
  forall rc : runConstT,
    zd_reserve_stmtA /\ zd_u32r_stmtA /\ zd_createdctx_stmtA (AI_of (@AHI_free rc)) /\
    zd_ddctx_stmtA (AI_of (@AHI_free rc)) AFake_iface.afake_rng /\ zd_iserror_stmtA /\
    zd_finddsize_stmtA (AI_of (@AHI_free rc)) AFake_iface.afake_rng /\ zd_freedctx_stmtA (AI_of (@AHI_free rc)).

(* [comment removed for export] *)
Definition client_stmtZ : Prop := forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) AFake_iface.afake_rng.
Theorem zd_fuzz_one_clientA : lib_stmtsA -> client_stmtZ.
Proof.
  intros LIB rc. destruct (LIB rc) as (R & U & C & DD & IE & FD & FR).
  apply (zd_fuzz_one_proofA (AI_of (@AHI_free rc)) AFake_iface.afake_rng).
  - exact afake_rng_mono.
  - apply fake_heap_AI_of.
  - intros iv Hiv. cbn [aci AI_of]. unfold aci_I. apply in_or_app. right. exact Hiv.
  - intros iv Hiv. cbn [aci AI_of]. unfold aci_I. apply in_or_app. left. exact Hiv.
  - exact R.
  - exact U.
  - exact C.
  - exact DD.
  - exact IE.
  - exact FD.
  - exact FR.
Qed.

(* [comment removed for export] *)
