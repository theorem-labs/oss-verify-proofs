(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 16 of its 40 lines of code are new or changed and 429 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_longp.v, with its module paths and module names changed; 33 of its 57 lines of code are new or changed and 16 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3): the segment S_MF_FRONT of lib/B/Prog/m_file_m.v
   (HEAD 0x86378 -> LONG 0x863d4, HDR 0x864f4, KEY 0x8661c, TAIL 0x86820; the image-B m_file segment table section 2), proved at
   every FP state from its seven pieces by mf_front_m.v's fr_chain. A walk lane of the image-B m_file-family owner's G2B (on
   a working branch). The segment reaches no snprintf, so each piece works at the one FP state fx0.
   THE PIECES (mf_front_m.v's points; each file is one piece lemma):
     mf_front_1.v fr_hd : FR_SC -> HEAD (S n)                  0x86378-0x86380, the strchr call (RtSeg.astrchr_realizes)
     mf_front_2.v fr_sc : FR_E -> FR_SL -> FR_SC              0x86384-0x863a8, the trap 0x86398, the strlen call
     mf_front_3.v fr_sl : FR_E -> FR_SL                       0x863ac-0x863c0, the trap 0x863b4
     mf_front_4.v fr_e  : LONG -> FR_ST -> FR_CL * -> FR_E    0x863c4-0x863d0, 0x86420-0x8642c, the trap 0x863c8
     mf_front_5.v fr_cl : FR_ST -> FR_CL i                    0x86430-0x864b0, the checks 0x86438 / 0x8646c, the trap 0x8645c
     mf_front_6.v fr_st : FR_SR -> FR_ST                      0x864b4-0x864c0, the strip call (strip_contract)
     mf_front_7.v fr_sr : TAIL -> HDR -> KEY -> FR_SR          0x864c4-0x864f0, 0x867e0-0x867e8, the trap 0x864d0, the check
                                                              0x864dc
   Section hypotheses: VOBJS (the listing's objects), SIGP (the listing's program call targets) and the three callee rows of the image-B m_file segment table the segment calls
   (strchr, strlen at their trampolines; strip at BASE + AF_strip with SegInstB.STK_strip). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require
  mf_front_1 mf_front_2 mf_front_3 mf_front_4 mf_front_5 mf_front_6 mf_front_7.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
(* the listing's program call targets (the jal 0x864c0 is the slot `PCall SS_strip 1`; its target pa_sigma SS_strip is
   BASE + AF_strip only by this fact, as lib/B/Prog/m_file_rf.v takes it for m_refuse) *)
Hypothesis SIGP : seg_sig_prog.
(* the callees of the segment (the image-B m_file segment table: wrapper_strchr 0x43ab4, wrapper_strlen 0x43a98, strip 0x879cc) *)
Hypothesis STRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis STRIP : forall fx0 : YK11.FPState,
  @strip_contract fx0 rc SK SEGS B (BASE + AF_strip) SegInstB.STK_strip.

Lemma S_MF_FRONT_ok : S_MF_FRONT (rc := rc) (SK := SK) (PI := PI) B.
Proof.
unfold S_MF_FRONT, MF_TAIL_F, MF_LONG_F, MF_HDR_F, MF_KEY_F, MF_HEAD_F.
intros n HT HL HH HK fx0.
apply (fr_chain (fx := fx0) B n (HT fx0) (HL fx0) (HH fx0) (HK fx0)).
- intros T H K. eapply (mf_front_7.fr_sr (fx := fx0)); eassumption.
- intros SR. eapply (mf_front_6.fr_st (fx := fx0)); eassumption.
- intros ST. eapply (mf_front_5.fr_cl (fx := fx0)); eassumption.
- intros L ST CL. eapply (mf_front_4.fr_e (fx := fx0)); eassumption.
- intros E. eapply (mf_front_3.fr_sl (fx := fx0)); eassumption.
- intros E SL. eapply (mf_front_2.fr_sc (fx := fx0)); eassumption.
- intros SC. eapply (mf_front_1.fr_hd (fx := fx0)); eassumption.
Qed.
End e.
End f.
End d.

About S_MF_FRONT_ok.
Print Assumptions S_MF_FRONT_ok.
