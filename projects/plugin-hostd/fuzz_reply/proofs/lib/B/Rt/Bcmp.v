(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the bcmp interceptor's contract at fuzz_reply.asan-ubsan's trampoline 0x42204, in
   the site form the image-B W walks take (abcmp_realizes at `SIGMA WS_bcmp`, the twin of lib/A/Rt/Bcmp.v).  The proof
   is cgif_file_fuzzer's released bcmp_icpt_contract (lib/YE2s.v:710, the asan-ubsan twin of A/AE2s.v, at
   origin/ossv/recipes c8557374ad2e) and its chain YE3b.v YE6z.v YE70.v YE2z.v, relocated onto this image by pg-tools
   port_core.py (sha256 718254b3f4dd; internal record) with five --override rows keyed by code bytes.  fuzz_reply's musl `bcmp` (0x9694c) is a
   `j` to the memcmp trampoline 0x42200, so the chain carries the memcmp interceptor's contract too (YE2z.v).  PB_fr's
   segments are the image's (W_tbl.v frsegs = AsanUbsan.M.loaded_segments = YB1v.v tfibsegs), so the site form is the
   relocated contract by conversion; the words below tie the chain to the pinned build. *)
(* Modified by Theorem Labs, 2026-10: made generic in place over YE2y.v's icpt_laws_x (any allocator invariant ARx;
   ghost head set Hpx threaded unchanged), hunk for hunk as image A's twin lib/A/Rt/Bcmp.v was
   (a working branch 6b4f6082575): bcmp_site_realizes_x states the site form over ARx; bcmp_site_realizes
   keeps its statement byte for byte and is re-proved from it at ARx := AR_x B (YE2y.icpt_laws_x_AR). Contract texts
   over ARx: lib/B/IcptRealizesX.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1w YF0m YE2k YE2z YE2s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_tbl W_place W_kit W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2y IcptRealizesX.
Import ListNotations.
Open Scope Z_scope.

(* Build identity, on the pinned fuzz_reply.asan-ubsan (sha256 10ffb5f9202a...): the trampoline, the interceptor, the
   first words of main and LLVMFuzzerTestOneInput, and the image's ofl_head. *)
Lemma bcmp_id_trampoline : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x42204)) = Some 0x2e00206f.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_interceptor : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x444e4)) = Some 0xfd010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_main : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x81ea4)) = Some 0xfb010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_llvmf : option_map bv_unsigned (fetch_word tfibsegs (Z_to_bv 64 0x84408)) = Some 0xec010113.
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_id_ofl_head : A_ofl_head = 0x5fa0e8.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bcmp_id_sigma : @pa_sigma _ fr_prog_listing PB_fr WS_bcmp = 0x42204.
Proof. reflexivity. Qed.
Lemma bcmp_id_segs : @pa_segs _ fr_prog_listing PB_fr = tfibsegs.
Proof. reflexivity. Qed.
(* the site form an image-B walk takes as `Hypothesis ABCMP` *)
(* over a generic allocator invariant ARx (YE2y.v icpt_laws_x; IcptRealizesX.v abcmp_realizes_x, at tfibsegs =
   pa_segs PB_fr, bcmp_id_segs) *)
Corollary bcmp_site_realizes_x : forall B ARx,
  icpt_laws_x B ARx -> TfibSyms B -> abcmp_realizes_x B ARx (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B ARx WL TB. exact (bcmp_icpt_contract_x B ARx WL TB). Qed.
Corollary bcmp_site_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  abcmp_realizes (@pa_segs _ fr_prog_listing PB_fr) B (@pa_sigma _ fr_prog_listing PB_fr WS_bcmp).
Proof. intros B LAWS TB. exact (abcmp_realizes_of_x B _ (bcmp_site_realizes_x B (AR_x B) (icpt_laws_x_AR B LAWS) TB)). Qed.
End b.
