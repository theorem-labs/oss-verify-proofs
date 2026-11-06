(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_hoom.v, with its module paths changed; 2 of its 19 lines of code are new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hoom-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a symbol-table fact at reply's image A, fuzz_reply.asan, pin
   42c58610e125). Reuse search: proof-index HOOM / as_oom_byte / ts_oom (index built 2026-10-30T04:38:19Z) and a
   grep of every working-branch ref for `as_oom_byte B = im_oom`: no discharge at any unit.

   HOOM is the cf layer's unit premise `Hypothesis HOOM : as_oom_byte B = im_oom` (YGcfInstMiss.v:251, commit
   f7a76d48d021; CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row 31), taken under the symbol facts `Hypothesis TS : im_syms B`. Reply has not
   taken the layer files, so hoom_A states that hypothesis's text VERBATIM at reply's image class instance AImg_reply
   (A/AGif2reply.v:23, im_oom := TFIB_OOM and im_syms := TfibSyms), with TS as its premise; a consumer closes HOOM with
   `exact (hoom_A B TS)`. The discharge is cgif's (AGif2cgif.v:26 `im_oom := TFIB_OOM` + YF0m.v:304 `ts_oom`): reply A's
   TfibSyms field ts_oom (A/AF0m.v:882) with TFIB_OOM = 0x128320 (A/AF0m.v:20). *)
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

(* HOOM at image A: the out-of-memory byte of the symbol table is the image class's cell (TFIB_OOM = 0x128320). *)
Lemma hoom_A : forall B, @im_syms AImg_reply B -> as_oom_byte B = @im_oom AImg_reply.
Proof. intros B TS. exact (ts_oom B TS). Qed.

(* The image class's OOM cell at reply A is the literal 0x128320 (A/AF0m.v:20). *)
Lemma hoom_A_value : @im_oom AImg_reply = 0x128320.
Proof. reflexivity. Qed.
