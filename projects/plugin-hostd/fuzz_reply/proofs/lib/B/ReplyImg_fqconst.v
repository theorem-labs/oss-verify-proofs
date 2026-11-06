(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs: reply image row img-fqconst-B of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the constant-cell table of reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   FQ_CONST, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstFreeView.v:56-58 @ 587da63d252, with const_at
   (YGcfInstFreeView.v:54-55 @ 587da63d252) unfolded: const_at ly a w v := exists e, In (ACell e w (AV (ANum v)))
   (as_const B ly) /\
   aeval B ly e = a.  The layer states both over its Section's Variable B; its consumers hold TS : im_syms B.  Reply
   does not carry YGcfInstFreeView.v, so the Lemma states FQ_CONST's body, const_at unfolded, at a B with image B's
   symbol facts (im_syms of AImg_reply, B/AGif2reply.v:24, which is YF0m.TfibSyms).
   Proof: each cell is found in Tfib_const by cell_lookup, computed by vm_compute (cgif's pattern: YF0x.v:206
   tfib_const_lookup; YFev.v:111 / :121 / :131).  At image B the four cells are inst + o_q_max, inst + o_q_maxcache,
   inst + o_q_min (8 bytes each) and inst + o_q_cmutex + 2 (2 bytes), TFIB_INST = 0xa2fd8 (B/YF0m.v:16). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Open Scope Z_scope.

(* FQ_CONST at image B: YGcfInstFreeView.v:57-58 @ 587da63d252, const_at unfolded. *)
Lemma FQ_CONST_B : forall B, @im_syms AImg_reply B -> forall ly,
  (exists e, In (ACell e 8 (AV (ANum kQuarantineMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_max) /\
  (exists e, In (ACell e 8 (AV (ANum kQuarantineCacheMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_maxcache) /\
  (exists e, In (ACell e 8 (AV (ANum kQuarantineMin))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_min) /\
  (exists e, In (ACell e 2 (AV (ANum 0))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_cmutex + 2).
Proof.
intros B TS ly. change (TfibSyms B) in TS. rewrite (ts_const B TS ly), (ts_inst B TS).
split; [|split; [|split]].
- exists (ANum (TFIB_INST + o_q_max)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_max))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_maxcache)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_maxcache))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_min)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_min))). vm_compute. reflexivity.
- exists (ANum (TFIB_INST + o_q_cmutex + 2)). split; [|reflexivity].
  apply (cell_lookup_In _ (ANum (TFIB_INST + o_q_cmutex + 2))). vm_compute. reflexivity.
Qed.
