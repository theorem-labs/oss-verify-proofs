(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AXRep AXRep_leafP AXImg_leafP.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8_P_tok_stmt X8_P_tok3_stmt X8_P_tok X8_P_tok_incr X8_P_tok3d X8_F_insert4 X8_F_lookup2 X8_F_lookup2a X8_F_lookup2b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

Lemma token_list_exists_c : token_list_exists_stmt H.
Proof.
  apply (token_list_exists_spec H HH).
  - exact (tokit_ctor_spec (ah_memset H HH) img_tchar_ok).
  - exact (tokit_incr_spec (ah_memset H HH) img_tchar_ok).
  - exact (ah_memcpy H HH).
Qed.

Lemma otf_segA_c : stack_malloc_stmt H 0 P_A_FS_MALLOC_0 -> otf_segA_stmt H.
Proof. intros FS0. exact (otf_segA H HH FS0 token_list_exists_c). Qed.

Theorem otf_spec_c : stack_malloc_stmt H 0 P_A_FS_MALLOC_0 -> otf_stmt H.
Proof. intros FS0. exact (otf_spec H HH FS0 token_list_exists_c). Qed.

End HCW.
