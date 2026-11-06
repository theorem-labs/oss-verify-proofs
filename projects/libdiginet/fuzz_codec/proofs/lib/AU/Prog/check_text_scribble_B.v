(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths and module names changed; 28 of its 57 lines of code are new or changed and 364 lines of the source are left out. *)
(* check_text_scribble at image B (fuzz_codec.asan-ubsan 0x83dbc, 227 instructions, real frame 128, a side-stack frame of
   class 0): lib/AU/Prog/CPgChkU.v's cdcU_check_text_scribble_specX, from the seven segments of
   check_text_scribble_B_inv.v (S0 check_text_scribble_B_s0.v, L _l.v, E _e.v, P _p.v, M _m1.v _m2.v _m3.v, F _f.v,
   R _r.v) and bs_now (check_text_scribble_B_now.v).
   Every UBSan check of the function is a branch to the trap at 0x8412c (bltu) and none is taken: q + i + 1 (0x83efc),
   want + o (0x83f24, 0x83f4c, 0x83fc0), q + i (0x83f80; the unconditional jump at 0x83f84 to the trap is on its taken
   side only), ch + n (0x84030), (ch + n) + j (0x84098): each compares the complement of a pointer held below 2 ^ 47
   with an index of at most 24 (segments L, P, M, F). The error path of every instrumented check is not reached (the
   shadow entries of the text, the record, want and the frame). The aborts at 0x84130 are not reached: the bytes the
   callee used are the owed ones and its text equals want (the contract's premise owed = scribble_text_spec), and the
   record's bytes [n, 24) hold 0xa5 (the memset). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_now check_text_scribble_B_s0a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0 check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_e check_text_scribble_B_p.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_mi check_text_scribble_B_m1.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_m2 check_text_scribble_B_m3.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_r.
Import ListNotations.
Open Scope Z_scope.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.

Theorem check_text_scribble_B_holds :
  astack_malloc_realizes tfibsegs B 0 -> astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
  aintrin_realizes tfibsegs B OSet B_MEMSET -> abcmp_realizes tfibsegs B B_BCMP ->
  cdcU_scribble_text_specX tfibsegs B MT B_SCRT ->
  cdcU_check_text_scribble_specX tfibsegs B MT B_CTS.
Proof.
intros ASM0 ASF FFL MSET ABCMP SCRT.
apply (bs_spec_of_segs B MT).
- apply bs_s0_holds; assumption.
- apply bs_l_holds; assumption.
- apply bs_e_holds; assumption.
- apply bs_p_holds; assumption.
- unfold bs_seg_M. intros g pos W2 c2 Hpre Hnow Hc.
  eapply SRr_bind; [eapply bsm1_holds; eassumption|]. intros W3 c3 _ H3.
  eapply SRr_bind; [eapply bsm2_holds; eassumption|]. intros W4 c4 _ H4.
  eapply bsm3_holds; eassumption.
- apply bs_f_holds; assumption.
- apply bs_r_holds; assumption.
- intros g Hpre. apply bs_now_of; assumption.
Qed.
End f.
