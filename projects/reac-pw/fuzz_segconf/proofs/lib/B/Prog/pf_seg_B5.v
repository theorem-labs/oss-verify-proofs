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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 135 of its 172 lines of code are new or changed and 5016 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b_r.v, with its module paths and module names changed; 16 of its 45 lines of code are new or changed and 143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b.v, with its module names changed; 32 of its 60 lines of code are new or changed and 17 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file
   (the line driver, 116 instructions; the B5 segment lane of the image-B G3 walk owner, 2026-10-30): S_B5 = S_B5h /\ S_B5t of
   lib/B/Prog/pf_pieces.v (the image-B piece-statement lane, 80a6c9c97a8b), proved from the eleven pieces below.
   proves function reac_segconf_parse_file (segment B5; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; verdict none released).
   ADAPTED from a working branch (the image-A G3 walk owner's image-A segment A5: pf_a5_k.v, pf_a5_d.v and its pieces
   pf_a5_h.v, pf_a5_r3.v, pf_a5_tl.v) + the unit owner's UBSan piece walk lib/U/Prog/pf_p2.v (the trap arithmetic),
   re-derived on image B's code; closed against G3 FINAL at 6f783602b5e3 (contract lib/B/Prog/
   reac_segconf_parse_file_c.v, the B-kit copies at 694f3575dda2).

   The head half S_B5h (HEAD 0x881f8 -> LONG 0x88258 / HDR 0x883b4 / KEY 0x883f8 / TAIL 0x88600), backwards from the
   exits through the internal points of pf_seg_B5_d.v:
     R5 0x88390 (pf_seg_B5_r5.v)  check B#7, `*line` 0 -> TAIL, '[' -> HDR, else KEY
     C  0x88388 (pf_seg_B5_c.v)   trim(buf) (C11)
     L k 0x882f8 (pf_seg_B5_lp.v) strip_comment: checks B#4, B#5, B#6, traps T08, T09, the cut store; every k
     R4 0x882cc (pf_seg_B5_r4.v)  trap T07, buf[LEN] = 0, the loop's constants
     R3 0x88250 (pf_seg_B5_r3.v)  LEN >= 512 -> LONG; checked_memcpy(buf, at, LEN) (C10)
     Q3 0x88238 (pf_seg_B5_q3.v)  lineno++ (trap T05), meta_fill_00 (C7): buf in scope
     R2 0x88224 (pf_seg_B5_r2.v)  trap T04, len and p'
     R1 0x88204 (pf_seg_B5_r1.v)  trap T03 (nl found), or strlen (C6)
     HEAD 0x881f8 (pf_seg_B5_hd.v) strchr(p, '\n') (C5)
   The tail half S_B5t (TAIL 0x88600 -> HEAD 0x881f8 at pred n / DONE 0x89114):
     TAIL (pf_seg_B5_tl.v)        meta_fill_f8 (C24): buf out of scope
     R6 0x8860c (pf_seg_B5_r6.v)  check B#15, `*p` <> 0 -> HEAD, else DONE
   Every point holds at the ambient FP state f0: B5 calls no printf, so no step changes it, and the exits are taken
   from the HA_ cuts at f0.
   SECTION HYPOTHESES (each is pf_pieces.v's for B5, at every FP state; TL and SIGP are the listing's records):
     TL      PALib B: the runtime record (the errno cell aj_art_at needs)                 hd, r1
     SIGP    seg_sig_prog: the program call target pa_sigma SS_trim = BASE + AF_trim         c
     ASTRCHR RtSeg.astrchr_realizes at pa_sigma SS___interceptor_trampoline_strchr            hd
     ASTRLEN RtString.astrlen_realizes at pa_sigma SS___interceptor_trampoline_strlen         r1
     AMEMCPY aintrin_realizes OCpy at pa_sigma SS___asan_memcpy                              r3
     ASH00   aset_shadow_realizes at pa_sigma SS___asan_set_shadow_00, 0x00                   q3
     ASHF8   aset_shadow_realizes at pa_sigma SS___asan_set_shadow_f8, 0xf8                   tl
     TRIM    trim_contract at BASE + AF_trim, STK_trim, RLO_A, RHI_A                          c *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegObj SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B5_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B5_hd pf_seg_B5_r1 pf_seg_B5_r2
  pf_seg_B5_q3 pf_seg_B5_r3 pf_seg_B5_r4 pf_seg_B5_lp pf_seg_B5_c pf_seg_B5_r5 pf_seg_B5_tl pf_seg_B5_r6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f8) 0xf8.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.

(* the head half: HEAD -> LONG / HDR / KEY / TAIL *)
Theorem pf_seg_B5h_holds : S_B5h B.
Proof.
intros f0 n HLONG HHDR HKEY HTAIL.
pose proof (pf_seg_B5_r5.b5_r5_ok (fx := f0) B n (HTAIL f0) (HHDR f0) (HKEY f0)) as HR5.
pose proof (pf_seg_B5_c.b5_c_ok (fx := f0) B SIGP TRIM n HR5) as HC.
pose proof (pf_seg_B5_lp.b5_lp_ok (fx := f0) B n HC 0%nat) as HL0.
pose proof (pf_seg_B5_r4.b5_r4_ok (fx := f0) B n HL0) as HR4.
pose proof (pf_seg_B5_r3.b5_r3_ok (fx := f0) B AMEMCPY n (HLONG f0) HR4) as HR3.
pose proof (pf_seg_B5_q3.b5_q3_ok (fx := f0) B ASH00 n HR3) as HQ3.
pose proof (pf_seg_B5_r2.b5_r2_ok (fx := f0) B n HQ3) as HR2.
pose proof (pf_seg_B5_r1.b5_r1_ok (fx := f0) B TL ASTRLEN n HQ3 HR2) as HR1.
exact (pf_seg_B5_hd.b5_hd_ok (fx := f0) B TL ASTRCHR n HR1).
Qed.

(* the tail half: TAIL -> HEAD (pred n) / DONE *)
Theorem pf_seg_B5t_holds : S_B5t B.
Proof.
intros f0 n HHEAD HDONE.
exact (pf_seg_B5_tl.b5_tl_ok (fx := f0) B ASHF8 n (pf_seg_B5_r6.b5_r6_ok (fx := f0) B n (HHEAD f0) (HDONE f0))).
Qed.

(* the segment statement of pf_pieces.v *)
Theorem pf_seg_B5_holds : S_B5 B.
Proof. exact (conj pf_seg_B5h_holds pf_seg_B5t_holds). Qed.
End d.
