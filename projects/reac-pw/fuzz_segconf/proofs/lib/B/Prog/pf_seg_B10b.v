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
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B10b of
   reac_segconf_parse_file's walk, S_B10b_holds : S_B10b B (lib/B/Prog/pf_pieces.v: HA_TAIL n -> H_INTENT n,
   INTENT 0x888e4 -> TAIL 0x88600). The B10b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B10b; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; verdict none released;
   ADAPTED from the image-A G3 walk owner's image-A segment walk A10b (a working branch's lib/A/Prog/pf_a10b_k.v,
   pf_a10b_f.v, pf_a10b_j.v, pf_a10b_b2.v, pf_a10b_b3.v) and the unit owner's UBSan piece walks (a working branch's
    lib/U/Prog/pf_p6.v; another working branch's pfC_facts.v), re-derived on image B's code; closed against G3 FINAL at 6f783602b5e3).

   THE SEGMENT (89 instructions; PLAN-pf-asanubsan.md section 5.2 row B10b: 89 / 2 checks / 1 trap):
     0x888e4 .. 0x8895c (31) + arms 0x88980-0x88984, 0x88a48-0x88a4c, 0x88c80-0x88c84, 0x88d68 (7)
                              the five bcmp calls of reac_role_intent_parse      pf_seg_B10b_c.v  (38 walked)
     0x88960 .. 0x8897c (8)   the bad-role refusal, refuse(c, ln + 1, F_badrole, cur_name, val)
                                                                                 pf_seg_B10b_r.v  (8 walked)
     0x88d6c .. 0x88dc4 (23)  T30 (cur & 3, 0x88d74), B#31 (cur + 16, 0x88d7c-0x88d8c), sw role, B#32 (cur + 20,
                              0x88d94-0x88da4), sw role_set, snprintf(&cur->role_file, 96, "%s", c->reading)
                                                                                 pf_seg_B10b_s.v  (23 walked)
     0x88dc8 .. 0x88dec (10)  low's eight shadow cells out of scope, `j` TAIL     pf_seg_B10b_j.v  (10 walked)
     cold 0x88fcc .. 0x88fe8 (8, the two checks' partial-granule arms) and the stubs 0x89288 / 0x8928c (2): never
     reached (both checks' shadow bytes are 0: the token run takes the fast path), so 79 of the 89 are walked and
     the other 10 are shown unreachable.
   CHECKS (2 of 2): B#31 and B#32 (store4 at cur + 16 / cur + 20 inside the block c) by one shadow entry from
     pf_obj's sa_addr c SEG_C_SIZE (gi < 32). TRAPS (1 of 1): T30 0x88d74 `bnez (cur & 3)` not taken: cur =
     c + 356 gi, c mod 16 = 0 (pf_tf, F1), 356 = 4 * 89.
   The kit pf_seg_B10b_k.v fixes the inner cuts BAD 0x88960, ROLEV 0x88d6c, JOIN 0x88dc8 and proves pb10_compose
   (PB10_C -> PB10_R -> PB10_S -> PB10_J -> S_B10b); the pure facts are pf_seg_B10b_f.v.

   SECTION HYPOTHESES (pf_pieces.v's callee list for B10b and the listing's walk facts; each at every FP state
   where it is a runtime or program contract):
     ABCMP  the kit's abcmp_realizes at pa_sigma SS___interceptor_trampoline_bcmp (lib/B/YG0d.v)   piece C
     ASNP   RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA   piece S
     REF    refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA   piece R
     SIGP   seg_sig_prog (B's SegObj.v: the call target SS_refuse is BASE + AF_refuse)                   piece R
     OBJ    seg_val_objs (B's SegObj.v: the literal atoms A_OBJ 35, 55 .. 60)                           pieces C, R, S
     VRO    seg_val_relro (B's SegObj.v: the read-only range, arodata_okP after refuse)                 piece R
     SSPX   the stack-protector cells at every AR state (the image-A owner's route A, sa_ssp after refuse)      piece R *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B10b_k pf_seg_B10b_c pf_seg_B10b_r
  pf_seg_B10b_s pf_seg_B10b_j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the runtime entries and the program callee of B10b's calls, at image B's numbers, at every FP state *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_bcmp).
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (B's SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A; image B's stage-2 SegRecCells gives it) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Theorem S_B10b_holds : S_B10b B.
Proof.
apply pb10_compose; [apply pb10_c_ok | apply pb10_r_ok | apply pb10_s_ok | apply pb10_j_ok]; assumption.
Qed.
End d.
