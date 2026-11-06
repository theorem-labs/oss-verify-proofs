(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC9s.v, with its module paths and module names changed; 14 of its 33 lines of code are new or changed and 250 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the piece lemma of ent_build's case 0 up to
   the parts, HPgSeg.hsu_piece_W7a_stmt at headamp_himg_B / headamp_bld_B, from the three block lemmas of the piece.
   Proves no function (kind: segment lemma).

   The piece runs from the jump table's case-0 target D = 0x8194c, and from D0E = 0x819c0 when no input byte is
   left, to G = 0x81afc. Its blocks are the head (both entries to the two arms, lib/AU/HPgE0Hd.v), the digits arm
   DIG 0x81a1c (lib/AU/HPgE0Dig.v) and the table arm ODD 0x82318 (lib/AU/HPgE0Odd.v); their statements, the two
   inner cuts and their composition (e0_piece_of_blocks) are lib/AU/HPgE0Def.v. Nothing is restated here.

   The two hypotheses are the runtime contracts the table arm calls: the strlen wrapper's at its trampoline 0x41c18
   (lib/A/Rt/StrlenDef.v astrlen_realizes) and __asan_memcpy's at 0x51d8c (the kernel's aintrin_realizes,
   lib/Reusable/YG0d.v). The allocator invariant's laws are the kernel theorem AR_laws_ok, not a hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgE0Base HPgE0Def.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgE0Hd HPgE0Dig HPgE0Odd.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : astrlen_realizes rsegs B E0_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy E0_MEMCPY.

Theorem e0_piece_W7a : hsu_piece_W7a_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using ASTRLEN AMEMCPY.
exact (e0_piece_of_blocks B MT (HPgE0Hd.e0_head B MT) (HPgE0Dig.e0_dig B MT)
        (HPgE0Odd.e0_odd B MT ASTRLEN AMEMCPY)).
Qed.

End d.
End b.

Print Assumptions e0_piece_W7a.
