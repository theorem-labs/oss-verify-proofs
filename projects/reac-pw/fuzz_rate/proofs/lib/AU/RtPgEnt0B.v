(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module names changed; 11 of its 33 lines of code are new or changed and 568 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): the piece is RtPgSegB.rsb_piece_W7a_stmt at image B's loaded segments, from lib/AU/RtPgEnt0DefB.v's rt7b_piece and the three blocks of lib/AU/RtPgEnt0HdB.v, RtPgEnt0DigB.v and RtPgEnt0OddB.v; the two call contracts are image B's (the strlen wrapper 0x421ec in lib/AU/RtPgW7bCallB.v's form, __asan_memcpy 0x518b8). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the piece of lane W7a,
   RtPgSegB.rsb_piece_W7a_stmt, ent_build's case 0 from its two entries D0 = 0x81460 and D0E = 0x814d0 to G = 0x8160c
   (pod.h:224-249). Proves no function (kind: segment lemma).

   HOW. lib/AU/RtPgEnt0DefB.v rt7b_piece reduces the piece to three block statements, each proved in its own file:
   the head (lib/AU/RtPgEnt0HdB.v rt7b_head: D0 / D0E to the arms DIG 0x8152c and ODD 0x81de0), the digits arm
   (lib/AU/RtPgEnt0DigB.v rt7b_dig: DIG to G) and the odd_ch arm (lib/AU/RtPgEnt0OddB.v rt7b_odd: ODD to G). Only the
   odd_ch arm calls out of the program: the strlen wrapper at 0x421ec and __asan_memcpy at 0x518b8, whose contracts
   are the two hypotheses below (lib/AU/RtPgW7bCallB.v w7b_astrlen_realizes, the verbatim body of image A's
   astrlen_realizes until image B's own runtime file is in the tree; the kit's YG0d.v aintrin_realizes). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgStepsB RtPgW7bBaseB RtPgW7bCallB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgEnt0DefB RtPgEnt0HdB RtPgEnt0DigB RtPgEnt0OddB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RTSB_MEMCPY.

Lemma rt7b_W7a : rsb_piece_W7a_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
apply rt7b_piece.
- apply rt7b_head.
- apply rt7b_dig.
- apply rt7b_odd; assumption.
Qed.
End d.
End b.

Print Assumptions rt7b_W7a.
