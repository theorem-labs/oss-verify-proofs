(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 665 of its 733 lines of code are new or changed and 4985 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b_c.v, with its module paths and module names changed; 11 of its 34 lines of code are new or changed and 710 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_5 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): J4 0x88440 -> K5 0x88570, the unquote
   of reac_segconf.c:78-86 (SegModel.r_unquote). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_5 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_d.v (A9's stretch SA9_C, K3 -> K5, whose file
   pf_a9_s3.v had not landed: written new on image B's code) with the forms of lib/B/Prog/trim_l.v / trim_f.v,
   pf_seg_B5_r2.v (the B5 segment lane) and pf_seg_B9_s1.v (the B9 segment lane).
   b9_s5 chains the pieces of the stretch, each from a cut to the next (continuation form):
     pf_seg_B9_s5m.v b9s5_j4_ok    J4 -> K5 (|v0| < 2, or v0[0] neither quote), B9S5_SQ, B9S5_DQ
                                   check B#10, traps T12, T14
     pf_seg_B9_s5a.v b9s5_dq_ok    B9S5_DQ 0x88480 -> B9S5_ST or K5        check B#11, trap T15
     pf_seg_B9_s5a.v b9s5_sq_ok    B9S5_SQ 0x88530 -> B9S5_ST or K5        check B#13, trap T15
     pf_seg_B9_s5s.v b9s5_strip_ok B9S5_ST 0x88554 -> K5 (the NUL store)   check B#14, trap T16
   The cut predicates and K5's rebuild are pf_seg_B9_s5k.v's. Instructions walked: 0x88440 .. 0x8849c (24),
   0x884c4 .. 0x884c8 (2), 0x88520 .. 0x8856c (20): 46 of the stretch's 63 (the other 17 are the slow arms and
   error calls of B#10, B#11, B#13, B#14, 0x88f9c .. 0x88fa4, 0x88fec .. 0x8900c, 0x89274 .. 0x89278,
   0x89290 .. 0x89298, which the token executor shows are not reached). Checks B#10, B#11, B#13, B#14; traps T12,
   T14, T15, T16. No call. No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B9_d pf_seg_B9_s5k pf_seg_B9_s5s pf_seg_B9_s5a
  pf_seg_B9_s5m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.

Lemma b9_s5 : SB9_5 B.
Proof.
intros n HK5.
pose proof (b9s5_strip_ok B n HK5) as HS5.
exact (b9s5_j4_ok B n HK5 (b9s5_dq_ok B n HK5 HS5) (b9s5_sq_ok B n HK5 HS5)).
Qed.

End x.
End d.
