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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/mf_longp.v, with its module paths and module names changed; 38 of its 58 lines of code are new or changed and 20 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): SEGMENT A11b of reac_segconf_parse_file's walk, assembled.
   Segment A11b's proof, by the G3 walk owner, 2026-10-30.

   proves function reac_segconf_parse_file (segment A11b; reuse search and CONFIRM: the unit's internal record,
   commit dfb49d6ad789, path records/segp/g3-lookup.md, the rule-24 check 2026-10-30T15:42:08Z;
   reuse verdict none: written new).

   A11b is MISS 0x885a8 and LOWOUT 0x88774 -> TAIL 0x88068, 119 instructions, inline check 28 (the catalogue
   row's shadow byte), and the calls reac_box_catalogue (0x88634), snprintf (0x88698, eleven passes) and refuse
   (0x886e8). Its statement is pf_pieces.v's S_A11b (:772-774), never edited here:

     S_A11b := forall f0 n, (HA_TAIL n -> H_MISS (fx := f0) B n) /\ (HA_TAIL n -> H_LOWOUT (fx := f0) B n).

   The walk is cut at the two points pf_a11b_d.v states (KLOOP 0x8865c, the head of the join loop, once per
   pass ti; KEXIT 0x886c8, the F_badmodel refusal), and proved in these files:

     pf_a11b_x.v   pfx_lowout_ok : HA_TAIL B n -> H_LOWOUT B n       LOWOUT 0x88774 .. TAIL, 4 instructions
                                                                     (low146 out of scope, `j`)
     pf_a11b_x1.v  x1_refuse_site_ok_886e8                           the closed refuse site lemma (rule 1j-bis)
     pf_a11b_x2.v  pfx_kexit_ok  : HA_LOWOUT B n -> H_KEXIT B n      KEXIT 0x886c8 .. LOWOUT, 43 instructions
                                                                     (refuse, known and ntok out of scope)
     pf_a11b_js.v, pf_a11b_jsite.v, pf_a11b_jk.v                     the snprintf family at "%s%s", the closed
                                                                     snprintf site lemma, one pass of the loop
     pf_a11b_j.v   pfj_kloop_ok  : HA_KEXIT B n -> forall ti, ti < 11 -> H_KLOOP B n ti
                                                                     KLOOP 0x8865c .. 0x886c4, 27 instructions,
                                                                     eleven passes, by induction on those left
     pf_a11b_m1.v  reac_box_catalogue_site_ok                        the closed catalogue site lemma (rule 1j-bis)
     pf_a11b_m.v   pfm_miss_ok   : HA_KLOOP B n 0 -> H_MISS B n      MISS 0x885a8 .. KLOOP, 45 instructions
                                                                     (known and ntok in scope, the catalogue)

   (4 + 43 + 27 + 45 = 119 pcs, every pc of 0x885a8 .. 0x88780 once; the 121 of the segment table is that
   table's count. Check 28's error arm 0x88cc8 is never entered: its bnez is decided not taken.) The functional
   facts of the loop are pf_a11b_f.v's (the eleven prefix lengths, one pass's step, that no pass is cut by the
   240-byte bound, pf_J 11 = SegModel.known, the literal addresses).

   The chaining: LOWOUT at every FP state gives KEXIT at every FP state, which gives KLOOP at pass 0 at every FP
   state, which gives MISS; LOWOUT at the ambient FP state is the second half of S_A11b outright. Each HA_ step
   is `intros f1` and the matching lemma at (fx := f1), because the snprintf and refuse calls return at FP states
   of their own.

   Section hypotheses: the union of the three pieces', each named by the piece that uses it.
     SNP   pf_a11b_j     the snprintf interceptor (the interceptor owner's row 4, released form)
     REF   pf_a11b_x2    refuse's contract at its listing entry
     CAT   pf_a11b_m     reac_box_catalogue's contract at its listing entry
     SIGP  pf_a11b_m, pf_a11b_x2   the two call targets are BASE + AF_<callee>
     OBJ   pf_a11b_j, pf_a11b_x2   the literal atoms "%s%s", "|", "" and F_badmodel
     VRO, SSPX  pf_a11b_x2 ONLY, at pf_a6_k.a6_base_move after the refuse call: refuse's post gives only its
           journal, which keeps an image byte only when it is not an owned static; whether the GOT word and the
           guard are owned statics is a record fact of listing stage 2 (SegRecCells.seg_rec_cells), and
           arodata_okP after refuse needs pa_relro_img. Route A of the image-A owner, the shape of
           lib/A/Prog/reac_segconf_parse.v.
   No piece takes TL (PALib). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0s YK15 YP09 YI00 YI04 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib
  SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA
  refuse_c reac_box_catalogue_c reac_segconf_parse_file_c pf_pieces pf_a11b_d pf_a11b_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a11b_x pf_a11b_x2 pf_a11b_j
  pf_a11b_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
(* the interceptor owner's interface row 4: snprintf at the listing's trampoline *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
(* the program callees, at the listing's entries and image A's numbers *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis CAT : forall fx0 : YK11.FPState,
  @reac_box_catalogue_contract fx0 rc SK SEGS B (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
(* the listing's facts over the abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.

Theorem pf_a11b_holds : S_A11b B.
Proof.
unfold S_A11b. intros f0 n. split; intros HT.
- (* the miss path: LOWOUT, then KEXIT, then the eleven passes from pass 0, then MISS *)
  assert (LOW : HA_LOWOUT B n).
  { intros f1. eapply (pfx_lowout_ok (fx := f1) B); eassumption. }
  assert (EX : HA_KEXIT B n).
  { intros f1. eapply (pfx_kexit_ok (fx := f1) B); eassumption. }
  assert (LP : HA_KLOOP B n 0).
  { (* pf_a11b_j.v takes its FP state after its hypotheses (Section w), so SNP and OBJ come first *)
    intros f1. exact (pfj_kloop_ok B SNP OBJ (fx := f1) n EX 0%nat ltac:(lia)). }
  eapply (pfm_miss_ok (fx := f0) B); eassumption.
- (* the hit path's exit: LOWOUT at the ambient FP state *)
  eapply (pfx_lowout_ok (fx := f0) B); eassumption.
Qed.

End e.
End f.
End d.
