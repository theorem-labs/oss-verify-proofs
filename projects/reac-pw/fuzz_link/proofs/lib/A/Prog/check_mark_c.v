(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Stdio/PSourceMeter.v, with its module paths and module names changed; 5 of its 15 lines of code are new or changed and 25 lines of the source are left out. *)
(* check_mark (fuzz_link.c:595-606) on image A (fuzz_link.asan 0x88450, 60 bytes; listing
   (internal path) (internal record, sha256 02dda35ead16)). Its instruction words are
   check_write's at every offset but the two jal at +0x34 / +0x38, which resolve to the same targets (before_abort
   0x5b318, abort 0x90ac4), so its contract is check_write_c.v's `check_rc_acontract` at this entry: the header there
   gives the instruction behind each premise, K = 16, the empty write set, and the plain conjunct (`unchanged`) that
   does not carry over. The plain twin is lib/Prog/check_write_c.v's check_mark_contract.
   Satisfiability witness (op_refused in LLVMFuzzerTestOneInput, check_mark(rc, -EINVAL)): a0 = a1 = w64 (-22), the
   -EINVAL mark_quietly answers for a NULL marks block or a NULL name; the closed lemma of `check_rc_apre` is in
   lib/A/Prog/help_witness.v.
   Released proofs (rule 24): none of check_mark (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem check_write_c.
Local Open Scope Z_scope.

Definition CHECK_MARK_A : Z := 0x88450.
Lemma CHECK_MARK_A_is_entry : CHECK_MARK_A = LA_check_mark. Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_mark_acontract : Prop := check_rc_acontract SK segs rlo rhi B CHECK_MARK_A.

End c.
