(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcDefs.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 4c6b0aaa171e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; F1 row R3): new file. rule 24: no function proved here (kind: a
   definition moved out of DMrc.v, unchanged).
   [rc_split_t]: the model's ARM SPLIT of H4's read record, i.e. the recycled chunk is a primary chunk or a live
   secondary with its slot (cgif: wf_chunks + wf_secondary, DGif1drMr.rchunk_secRm / rchunkRm).  The text and the
   Section variables are DMrc.v's; DMrc.rc_split_t is this definition at DMrc's Section variable DRq, so a consumer of
   the split field (DMrcRhOk) needs neither DMrc nor DMrcPrim. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD RMAXD : Z.
Definition rc_split_t : Prop :=
forall X k ks zs, DRq X (k :: ks) zs ->
(exists off, ck_beg k = PPrim off) \/
(exists r o sm i, ck_beg k = PSec r o /\ nth_error (st_secs X) r = Some sm /\ nth_error (st_sec_arr X) i = Some r).
End h.
End d.
