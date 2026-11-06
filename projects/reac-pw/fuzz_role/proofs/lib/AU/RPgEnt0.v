(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 129 of its 184 lines of code are new or changed and 906 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; RPgEnt0Def / RPgSeg / RPgMem / RPgImgA are lib/A/RtPgEnt0Def.v (rt7_odd_stmt, rt7_cut_ODD, rt7_L_arm, rt7_g_of_cp, rt7_PG_sh), RtPgSeg.v, RtPgMem.v and RtPgImgA.v; the shadow offset is in s2, &ch in s6, and the cursor stays in s9 (no `s9 := s8`: s8 is the one callee-saved register the block changes, and no location of rs_cut_G names it); G is 0x8150c; rate's rt_seg_pre holds no frame shadow; the strlen wrapper's hypothesis is this unit's lib/A/Rt/StrlenDef.v astrlen_realizes STRLEN_ENTRY and __asan_memcpy is 0x51860; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Odd.v at 21da95a5fcd3; image B (images.AsanUbsan): lib/AU/RtPgEnt0DefB.v (rt7b_odd_stmt, rt7b_cut_ODD, rt7b_L_arm, rt7b_g_of_cp), RtPgSegB.v, RtPgMemB.v and RtPgImgB.v for the A files; c is in a3, the shadow offset in s4, &ch in s2, t1 what is left (saved in s8 across the two calls and put back), so the block changes the callee-saved s6 and s8, which no location of rsb_cut_G names (its list is rt7b_L_arm without s8 = -8); the frame for locals is of class 4; G is 0x8160c; the strlen wrapper's hypothesis is lib/AU/RtPgW7bCallB.v w7b_astrlen_realizes at W7B_STRLEN 0x421ec and __asan_memcpy is RtPgStepsB.RTSB_MEMCPY 0x518b8; names oa_ -> oab_, rt7_ -> rt7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; lib/AU/RPgEnt0Def.v (r7b_odd_stmt, r7b_cut_ODD, r7b_L_arm, r7b_g_of_cp), RPgSeg.v (no header cells), RPgMem.v and RPgImgA.v for the rate files; the shadow offset is in s11 and t1 is saved in s4 across the two calls and put back, so the block changes the callee-saved s4 and s6, which no location of rs_cut_G names (its list is r7b_L_arm without s10 = -8 and s4 = 1); the real frame is 0x200 bytes; G is 0x80dc8; the strlen wrapper's hypothesis is lib/AU/RPgW7bCall.v w7b_astrlen_realizes at W7B_STRLEN 0x41b60 and checked_memcpy is RPgSteps.RL_MEMCPY 0x5116c; names rt7b_ -> r7b_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/AU/RPgEnt0Odd.v, with its module paths and module names changed; 6 of its 32 lines of code are new or changed and 158 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): the piece is RtPgSegB.rsb_piece_W7a_stmt at image B's loaded segments, from lib/AU/RtPgEnt0DefB.v's rt7b_piece and the three blocks of lib/AU/RtPgEnt0HdB.v, RtPgEnt0DigB.v and RtPgEnt0OddB.v; the two call contracts are image B's (the strlen wrapper 0x421ec in lib/AU/RtPgW7bCallB.v's form, __asan_memcpy 0x518b8). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0B.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; the piece is lib/AU/RPgSeg.v rs_piece_W7a_stmt, from lib/AU/RPgEnt0Def.v r7b_piece and the three blocks of lib/AU/RPgEnt0Hd.v, RPgEnt0Dig.v and RPgEnt0Odd.v; the two call contracts are role B's (the strlen wrapper 0x41b60, __asan_memcpy 0x5116c); names rt7b_ -> r7b_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the piece
   RPgSeg.rs_piece_W7a_stmt, ent_build's case 0 from its two entries D0 = 0x80c14 and D0E = 0x80c88 to G = 0x80dc8
   (pod.h:224-249). Proves no function (kind: segment lemma).

   HOW. lib/AU/RPgEnt0Def.v r7b_piece reduces the piece to three block statements, each proved in its own file:
   the head (lib/AU/RPgEnt0Hd.v r7b_head: D0 / D0E to the arms DIG 0x80ce8 and ODD 0x815e0), the digits arm
   (lib/AU/RPgEnt0Dig.v r7b_dig: DIG to G) and the odd_ch arm (lib/AU/RPgEnt0Odd.v r7b_odd: ODD to G). Only the
   odd_ch arm calls out of the program: the strlen wrapper at 0x41b60 and __asan_memcpy at 0x5116c, whose contracts
   are the two hypotheses below (lib/AU/RPgW7bCall.v w7b_astrlen_realizes, the body of lib/AU/Rt/StrlenDef.v
   astrlen_realizes; YG0d.v aintrin_realizes). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSeg RPgSteps RPgW7bBase RPgW7bCall.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0Def RPgEnt0Hd RPgEnt0Dig RPgEnt0Odd.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Open Scope Z_scope.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy RL_MEMCPY.

Lemma r7b_W7a : rs_piece_W7a_stmt rsegs B MT.
Proof using ASTRLEN AMEMCPY.
apply r7b_piece.
- apply r7b_head.
- apply r7b_dig.
- apply r7b_odd; assumption.
Qed.
End d.
End b.

Print Assumptions r7b_W7a.
