(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-herr-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of reply's image A, fuzz_reply.asan).
   HERR is the cf layer's unit premise `Hypothesis HERR : as_errno B = im_errno.` (YGcfInstMiss.v:244 at 692f71ce28c,
   :242 at 1ad1106e381), in the Section where `TS : im_syms B`.  Reply has not taken the layer files, so the lemma below
   states that text at reply's image instance (ImgBase.AImg at AImg_reply, A/AGif2reply.v:23, whose im_errno is
   TFIB_ERRNO 0x5d93cc, A/AF0m.v:22) over the same premise TS; a consumer closes the layer's HERR with `exact`.
   Discharge pattern: cgif's AGif2cgif.v:26 `im_errno := TFIB_ERRNO` + YF0m.v:297 `ts_errno`; here the TfibSyms field
   ts_errno (A/AF0m.v:875). *)
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

(* HERR at image A: the symbol table's errno cell is the image class's errno cell. *)
Lemma herr_A : forall B, @im_syms AImg_reply B -> as_errno B = @im_errno AImg_reply.
Proof. intros B TS. change (TfibSyms B) in TS. exact (ts_errno B TS). Qed.

(* The cell's value, for a reader that needs the number: TFIB_ERRNO = 0x5d93cc (A/AF0m.v:22). *)
Lemma herr_A_val : @im_errno AImg_reply = 0x5d93cc.
Proof. reflexivity. Qed.

Print Assumptions herr_A.
Print Assumptions herr_A_val.
About herr_A.
