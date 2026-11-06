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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_longp.v, with its module paths and module names changed; 44 of its 64 lines of code are new or changed and 20 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: segment A5 of reac_segconf_parse_file (the line driver; segment A5's proof,
   2026-10-30). proves function reac_segconf_parse_file, its segment S_A5 (lib/A/Prog/pf_pieces.v); the function's
   rule-24 record (reuse verdict none: written new; the rule-24 check's CONFIRM 2026-10-30T15:42:08Z) is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md.

   S_A5: HEAD 0x87ddc -> LONG / HDR / KEY / TAIL, and TAIL 0x88068 -> HEAD (pred n) / DONE; 111 instructions
   (0x87ddc-0x87fac's line driver and 0x88068-0x88090's tail), checks 4-7 and 12, calls strchr, strlen, meta_fill_00,
   the checked memcpy, trim, meta_fill_f8. The walk goes through the internal points of lib/A/Prog/pf_a5_d.v; each
   piece proves one point's H from the H of the points (or exit cuts) it reaches:
     pf_a5_h.v   a5_head_ok  HEAD -> R1 (strchr)          a5_r1_ok  R1 -> Q3 / R2 (strlen)    a5_r2_ok  R2 -> Q3
     pf_a5_r3.v  a5_q3_ok    Q3 -> R3 (meta_fill_00)      a5_r3_ok  R3 -> LONG / R4 (memcpy)  a5_r4_ok  R4 -> L 0
     pf_a5_lp.v  a5_loop_ok  L k -> L (k + 1) / C (strip_comment, checks 4-6)
     pf_a5_tr.v  a5_c_ok     C -> R5 (trim, its closed site lemma a5_trim_site_ok)
                 a5_r5_ok    R5 -> TAIL / HDR / KEY (check 7)
     pf_a5_tl.v  a5_tail_ok  TAIL -> R6 (meta_fill_f8)    a5_r6_ok  R6 -> HEAD (pred n) / DONE (check 12)
   This file chains them at each FP state f0. The Section hypotheses are the callee texts of pf_pieces.v's list for
   A5, at listing terms, plus the runtime record TL (pal_env, which aj_art_at asks at the interceptor calls). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj trim_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a5_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_h pf_a5_r3 pf_a5_lp pf_a5_tr pf_a5_tl.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
(* the callee texts of pf_pieces.v's list for A5, each at every FP state, at listing terms *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strlen).
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_00) 0.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis ASHF8 : forall fx0 : YK11.FPState,
  @aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_f8) 0xf8.
(* the listing's runtime record (pal_env: aj_art_at at the strchr / strlen calls) and the program call target
   pa_sigma SS_trim = BASE + AF_trim *)
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).

Theorem pf_a5_holds : S_A5 B.
Proof.
unfold S_A5. intros f0 n. split.
- intros HL HH HK HT.
  assert (R5 : H_R5 (fx := f0) B n).
  { eapply pf_a5_tr.a5_r5_ok; eauto. }
  assert (C : H_C (fx := f0) B n).
  { eapply pf_a5_tr.a5_c_ok; eauto. }
  assert (L0 : H_L (fx := f0) B 0 n).
  { eapply pf_a5_lp.a5_loop_ok; eauto. }
  assert (R4 : H_R4 (fx := f0) B n).
  { eapply pf_a5_r3.a5_r4_ok; eauto. }
  assert (R3 : H_R3 (fx := f0) B n).
  { eapply pf_a5_r3.a5_r3_ok; eauto. }
  assert (Q3 : H_Q3 (fx := f0) B n).
  { eapply pf_a5_r3.a5_q3_ok; eauto. }
  assert (R2 : H_R2 (fx := f0) B n).
  { eapply pf_a5_h.a5_r2_ok; eauto. }
  assert (R1 : H_R1 (fx := f0) B n).
  { eapply pf_a5_h.a5_r1_ok; eauto. }
  eapply pf_a5_h.a5_head_ok; eauto.
- intros HH HD.
  assert (R6 : H_R6 (fx := f0) B n).
  { eapply pf_a5_tl.a5_r6_ok; eauto. }
  eapply pf_a5_tl.a5_tail_ok; eauto.
Qed.
End e.
End f.
End d.
