(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs (for the cf layer at plugin-hostd/fuzz_reply; row img-constapart-A, its IMG_QAPART half).
   rule 24: no function proved (kind: image row; a closed computation over reply image A's symbol table,
   fuzz_reply.asan, pin 42c58610e125).

   IMG_QAPART at image A.  The cf layer's Definition IMG_QAPART
   (proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:65-68 @ 8b12df2b772) is stated over the image class under
   [Context {IM : AImg}].  The reply tree does not carry that layer file, so the Lemma below states IMG_QAPART's body at
   reply's instance IM := AImg_reply (proofs/plugin-hostd/fuzz_reply/lib/A/AGif2reply.v:23 @ d2bd679271c,
   im_syms := lib/A/AF0m.v's TfibSyms), with qhdr_inst (YGcfInstDrainX.v:62-63 @ 8b12df2b772) UNFOLDED.
   The quarantine header words TFIB_INST 0xa2a58 + o_quar + 152 .. 156 and + 160 .. 192 ([0xa2dc8, 0xa2dcc),
   [0xa2dd0, 0xa2df0)) lie below the internal allocator 0xa72c0, the flag 0x135b48, the store 0x177f88 and the depot
   0x187f98 (proofs/plugin-hostd/fuzz_reply/lib/A/AF0m.v:17-20 @ d2bd679271c).  cgif's discharge pattern: by the
   numerals (proofs/cgif/cgif_file_fuzzer/lib/YFey.v:578 / :585 / :638).  The error-message buffer's object is the
   separate row ERRB_QAPART (lib/A/ReplyImg_errbqapart.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
Open Scope Z_scope.

(* IMG_QAPART at image A: proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainX.v:65-68 @ 8b12df2b772, with qhdr_inst
   (:62-63) unfolded. *)
Lemma IMG_QAPART_A : forall B, @im_syms AImg_reply B -> forall a,
  ((as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192)) ->
  ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
  ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS.
rewrite (ts_inst B TS) in Ha.
rewrite (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, o_quar in *. lia.
Qed.
