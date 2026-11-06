(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the bcmp interceptor's contract at fuzz_reply.asan's trampoline 0x421ac, in the
   site form the W walks take (Reusable/YG0d.v abcmp_realizes at `SIGMA WS_bcmp`: lib/A/W_list_find.v ABCMP,
   lib/A/W_has_prefix.v ABCMP).  The proof is cgif_file_fuzzer's released bcmp_icpt_contract (lib/A/AE2s.v:710 at
   origin/ossv/recipes c8557374ad2e) and its chain lib/A/AE3b.v AE6z.v AE70.v AE2z.v, relocated onto this image by
   port_core.py (sha256 718254b3f4dd; internal record) with five --override rows (bcmp's REAL is musl `bcmp`, 0x963cc, a `j` to the
   memcmp trampoline 0x421a8, so the chain carries the memcmp interceptor's contract too).  PB_fr's segments are the
   image's (W_tbl.v frsegs = Asan.M.loaded_segments = AB1v.v tfibsegs), so the site form is the relocated
   contract by conversion; the words below tie the chain to the pinned build. *)
(* Modified by Theorem Labs, 2026-10: made generic in place over AE2y.v's icpt_laws_x (any allocator invariant ARx;
   ghost head set Hpx threaded unchanged), as SitesCf did for AE2t / AE6y / AE7e: each walk lemma is stated over ARx
   (<name>_x, and POSTr_x / POSTC_x for the section posts); every theorem or lemma that took AR_laws keeps its
   statement byte for byte (its post definition too) and is re-proved from its _x at ARx := AR_x B
   (AE2y.icpt_laws_x_AR), in a section named <section>A. Contract texts over ARx: lib/A/IcptRealizesX.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1w AF0m AE2k AE2z AE2s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_tbl W_place W_kit W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2y IcptRealizesX.
Import ListNotations.
Open Scope Z_scope.

(* Build identity, on the pinned fuzz_reply.asan (sha256 42c58610e125...): the trampoline, the interceptor, the first
   words of main and LLVMFuzzerTestOneInput, and the image's ofl_head (the sink head the walks are stated over). *)
Lemma bcmp_id_trampoline : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x421ac)) = Some 0x2e00206f.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_interceptor : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x4448c)) = Some 0xfd010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_main : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x81e4c)) = Some 0xfb010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_llvmf : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x840b0)) = Some 0xec010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_ofl_head : A_ofl_head = 0x5f9b68.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bcmp_id_sigma : @pa_sigma _ fr_prog_listing PB_fr WS_bcmp = 0x421ac.
Proof. reflexivity. Qed.
Lemma bcmp_id_segs : @pa_segs _ fr_prog_listing PB_fr = tfibsegs.
Proof. reflexivity. Qed.
(* the site form: what W_list_find.v / W_has_prefix.v take as `Hypothesis ABCMP` *)
(* over a generic allocator invariant ARx (AE2y.v icpt_laws_x; IcptRealizesX.v abcmp_realizes_x, at tfibsegs =
   pa_segs PB_fr, bcmp_id_segs) *)
Corollary bcmp_site_realizes_x : forall B ARx,
  icpt_laws_x B ARx -> TfibSyms B -> abcmp_realizes_x B ARx (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B ARx WL TB. exact (bcmp_icpt_contract_x B ARx WL TB). Qed.
Corollary bcmp_site_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  abcmp_realizes (@pa_segs _ fr_prog_listing PB_fr) B (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B LAWS TB. exact (abcmp_realizes_of_x B _ (bcmp_site_realizes_x B (AR_x B) (icpt_laws_x_AR B LAWS) TB)). Qed.
End b.
