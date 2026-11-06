(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of __asan_stack_free_5 (0x40190) of plugin-hostd/fuzz_command's ASan build against astack_free_cls_realizes, built from cgif_rgb_fuzzer's lib/YF3h.v (entry state, frame and flag regions, closing through astack_free_law_ok) and cgif_file_fuzzer's lib/A/AF0r.v and AF0s.v (a second symbolic phase over a fresh shadow-pointer atom and the read-out of its stores), over the asan-state definitions of the cgif_file_fuzzer proof as plugin-hostd/fuzz_command holds them: one image; class 5; the 32 stores of the .rodata word 0x10340 in place of the memset tail; module names; TfxSyms becomes CmdBSyms. *)
(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport's asan image by this unit's provenance/evidence/class5/run.sh (alreloc with the resolve lines of class5cmp.py); CmdBSyms becomes TransportSyms. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Rt/RtSF5.v; 5 of its 31 lines of code are new or changed and 347 lines of the source are left out. *)
(* RtSF5Cg: the class-5 release contract of fuzz_transport.asan, stated over the callee text of lib/A/Prog/TransportRtCg.v
   that the image-A program-walk statements assume. RtSF5.cmd_stack_free5_contract proves RtStack.astack_free_cls_realizes
   at the release entry __asan_stack_free_5 (0x3df10); TransportRtCg.astack_free_cls_realizes has the same text, so the
   proof is the same term. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require Import RtStack.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require RtSM1T.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require RtSF5.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportRtCg.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem stack_free5_realizes : forall (B : asyms), AR_laws tfibsegs B -> TransportSyms B ->
  TransportRtCg.astack_free_cls_realizes tfibsegs B 0x3df10 5.
Proof. intros B LAWS TB. exact (RtSF5.cmd_stack_free5_contract B LAWS TB). Qed.
End c.
