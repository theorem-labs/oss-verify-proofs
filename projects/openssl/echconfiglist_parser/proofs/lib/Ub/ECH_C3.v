(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_C3_stmt ECH_C3_ready ECH_C3_newex ECH_C3_phase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem C3_spec : heap_sr_hyps_x H -> getdefctx_fresh_stmt H -> C3_stmts H.
  Proof.
    intros HX CERTA. unfold C3_stmts.
    split; [exact getdefctx_ready_spec|].
    split; [exact (getdefctx_spec H HX CERTA)|].
    split; [exact getglobal_ready_spec|].
    split; [exact (getglobal_spec H HX CERTA)|].
    split; [exact getandlock_spec|].
    split; [exact cnewex_ready_spec|].
    split; [exact (cnewex_spec H HX CERTA)|].
    exact cfreeex_spec.
  Qed.
End W.

Print Assumptions C3_spec.
