(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Lept_chain Gq_numa LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tr_numaCreate_2 : In [0x91ab4] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.   (* [comment removed for export] *)
Lemma tr_numaDestroy_1 : In [0x91d4c] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.  (* [comment removed for export] *)
Lemma tr_numaDestroy_2 : In [0x91d54] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.  (* [comment removed for export] *)

Lemma tr_numaCreate_1 : In [0x91aa4] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma chain_ok_lower : forall ras (m : mem) lo lo' f, ras <> [] -> lo' <= lo -> chain_ok m lo f ras -> chain_ok m lo' f ras.
Proof.
  intros [|ra1 ras] m lo lo' f NE LE H; [exfalso; exact (NE eq_refl)|].
  cbn [chain_ok] in *. destruct H as (H1 & H2 & H3 & H4 & fp1 & H5 & H6 & H7).
  split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists fp1. exact (conj H5 (conj H6 H7)).
Qed.

(* [comment removed for export] *)
Lemma numaCreate_ra_range : forall r l, numaCreate_trace_ok (r :: l) -> 4096 <= r < 2^64.
Proof. intros r l H. unfold numaCreate_trace_ok in H. exact (Forall_inv H). Qed.
