(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its block A (hd_c3 / hd_c3_of, hd_bounds, hd_A: the start facts, the bounds and
   the run from C3 through the __asan_memcpy call) and its helpers hd_getr_z, hd_reg_atom, hd_reg_is,
   hd_frame_nil, hd_frame_ro, hd_aview_some, renamed to the h2_ prefix and moved to headamp's addresses,
   registers, real-frame cells and cut lists; the call is taken through lib/A/HPgIntrin.v hd_memcpy_at in place
   of the donor's own hd_memcpy; the donor's blocks B and C (the parse and its exits) are not taken; the run from
   the call's return to C4 and the segment's post are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM02.v, with its module paths and module names changed; 16 of its 35 lines of code are new or changed and 425 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0.v at 97ea9c9eafa; for reac-pw/fuzz_headamp image A: module paths, the rs_ / rl_ / rm_ / RS_ / RM_ prefixes renamed to hs_ / hd_ / hm_ / HS_ / HM_; __asan_memcpy 0x510d4 -> 0x51d0c. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47): the piece lemma of ent_build's case 0 up to
   the parts loop, HPgSeg.hs_piece_W7a_stmt, from the three block lemmas of the piece.
   Proves no function (kind: segment lemma).

   The piece runs from the jump table's case-0 target D = 0x81860, and from D0E = 0x818cc when no input byte is
   left, to G = 0x81a34. Its blocks are the head (both entries to the two arms, lib/A/HPgEnt0Hd.v), the digits arm
   DIG 0x81920 (lib/A/HPgEnt0Dig.v) and the table arm ODD 0x820c8 (lib/A/HPgEnt0Odd.v); their statements and the
   two inner cuts are lib/A/HPgEnt0Def.v. Nothing is restated here: the piece is the three in a row.

   The two hypotheses are the runtime contracts the table arm calls: the strlen wrapper's at its image-A
   trampoline STRLEN_ENTRY_A 0x41b98 (its text lib/A/Rt/StrlenDef.v:40 astrlen_realizes) and
   __asan_memcpy's (the kernel's aintrin_realizes, lib/Reusable/YG0d.v:328). The allocator invariant's laws are the
   kernel theorem AR_laws_ok, not a hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgEnt0Def.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgEnt0Dig HPgEnt0Odd HPgEnt0Hd.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : astrlen_realizes rsegs B STRLEN_ENTRY_A.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x51d0c.

Theorem r7_piece_W7a : hs_piece_W7a_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
intros cx POST rest i k kd HST Hkd HG.
exact (HPgEnt0Hd.r7_head B MT cx POST rest i k kd HST Hkd
        (HPgEnt0Dig.r7_dig B MT (AR_laws_ok rsegs B) cx POST rest i k HST HG)
        (HPgEnt0Odd.r7_odd B MT (AR_laws_ok rsegs B) ASTRLEN AMEMCPY cx POST rest i k HST HG)).
Qed.

End d.
End b.

Print Assumptions r7_piece_W7a.
