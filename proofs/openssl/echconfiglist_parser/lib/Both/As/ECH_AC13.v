(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsIface ECH_ARep ECH_AStmt_C5 ECH_AStmt_C13
     ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC13_store.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC13_spec : asan_rt_hyps H -> C13_stmts H.
  Proof.
    intros HH. unfold C13_stmts.
    split; [exact (astorenew_spec H HH)|].
    split; [exact (aextfree_spec H HH)|].
    split; [exact (aentryfree_spec H HH)|].
    split; [exact (astorefree_spec H HH)|].
    split; [exact (apopfree_exts_spec H HH)|].
    split; [exact (apopfree_entries_spec H HH)|].
    split; [exact (EXTobj_frame_law H)|].
    split; [exact (ENTRYobj_frame_law H)|].
    split; [exact (EXT_shad_frame_law H)|].
    split; [exact (ENTRY_shad_frame_law H)|].
    split; [exact aentryfree_null_spec|].
    split; [exact apkeyfree_null_spec|].
    split; [exact athunk_ext_spec|].
    split; [exact athunk_entry_spec|].
    exact athunk_xbuf_spec.
  Qed.

  (* [comment removed for export] *)
  Definition STOREobj_frame : EP_frame H storerep STOREobj blocks_STORE := STOREobj_frame_law H.
  Definition STOREobj_owned : EP_owned storerep STOREobj blocks_STORE := STOREobj_owned_law.
  Definition STORE_shad_frame : eshad_frame H storerep blocks_STORE STORE_shad := STORE_shad_frame_law H.
  Definition store_cost_nonneg (HH : asan_rt_hyps H) : ecost_pos storerep (store_cost H) := store_cost_pos H HH.
  Definition entry_cost_nonneg (HH : asan_rt_hyps H) : ecost_pos entrep (entry_cost H) := entry_cost_pos H HH.
End W.

Print Assumptions AC13_spec.
