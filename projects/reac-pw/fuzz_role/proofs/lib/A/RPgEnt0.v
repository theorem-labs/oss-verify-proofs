(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC9s.v, with its module paths and module names changed; 16 of its 35 lines of code are new or changed and 250 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the piece lemma of ent_build's case 0 up to
   the parts loop, RPgSeg.rs_piece_W7a_stmt, from the three block lemmas of the piece.
   Proves no function (kind: segment lemma).

   The piece runs from the jump table's case-0 target D = 0x80b40, and from D0E = 0x80bac when no input byte is
   left, to G = 0x80d14. Its blocks are the head (both entries to the two arms, lib/A/RPgEnt0Hd.v), the digits arm
   DIG 0x80c00 (lib/A/RPgEnt0Dig.v) and the table arm ODD 0x813a8 (lib/A/RPgEnt0Odd.v); their statements and the
   two inner cuts are lib/A/RPgEnt0Def.v. Nothing is restated here: the piece is the three in a row.

   The two hypotheses are the runtime contracts the table arm calls: the strlen wrapper's (its text
   lib/A/Rt/StrlenDef.v:37; its proof lib/A/Rt/Strlen.v:27 strlen_icpt_contract needs the relocated frame) and
   __asan_memcpy's (the kernel's aintrin_realizes, lib/Reusable/YG0d.v:328). The allocator invariant's laws are the
   kernel theorem AR_laws_ok, not a hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgEnt0Def.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgEnt0Dig RPgEnt0Odd RPgEnt0Hd.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : astrlen_realizes rsegs B STRLEN_ENTRY.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x510d4.

Theorem r7_piece_W7a : rs_piece_W7a_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
intros cx POST rest i k kd HST Hkd HG.
exact (RPgEnt0Hd.r7_head B MT cx POST rest i k kd HST Hkd
        (RPgEnt0Dig.r7_dig B MT (AR_laws_ok rsegs B) cx POST rest i k HST HG)
        (RPgEnt0Odd.r7_odd B MT (AR_laws_ok rsegs B) ASTRLEN AMEMCPY cx POST rest i k HST HG)).
Qed.

End d.
End b.

Print Assumptions r7_piece_W7a.
