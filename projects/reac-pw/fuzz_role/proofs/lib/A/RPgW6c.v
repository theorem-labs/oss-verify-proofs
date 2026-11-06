(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v; 9 of its 29 lines of code are new or changed and 497 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x7ff88), ent_build's cases 6, 7 and 8 from their switch entries to the join J
   0x8165c, as lib/A/RPgSeg.v states it (rs_piece_W6c_stmt). Proves no function (kind: segment lemma). The two
   callees are the kernel's contracts of __asan_memcpy (0x510d4) and __asan_memset (0x51570), YG0d.aintrin_realizes,
   hypotheses of the theorem. The three cases are lib/A/RPgW6c6.v, RPgW6c7.v, RPgW6c8.v; the bridge to the cuts is
   lib/A/RPgW6cGlue.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgSeg RPgW6cTail RPgW6cBase RPgW6cGlue.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgW6c6 RPgW6c7 RPgW6c8.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

Theorem w6c_piece : rs_piece_W6c_stmt rsegs B MT.
Proof.
apply w6c_piece_of.
- exact (RPgW6c6.w6c_case6 B AMEMCPY).
- exact (RPgW6c7.w6c_case7 B AMEMCPY).
- exact (RPgW6c8.w6c_case8 B AMEMSET).
Qed.
End b.

Print Assumptions w6c_piece.
