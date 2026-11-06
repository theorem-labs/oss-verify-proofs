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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 527 of its 576 lines of code are new or changed and 404 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a11b_x2.v, with its module paths and module names changed; 19 of its 40 lines of code are new or changed and 555 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B8b of
   reac_segconf_parse_file's walk, the theorem S_B8b_holds : S_B8b B of lib/B/Prog/pf_pieces.v (the image-B piece statements at
   80a6c9c97a8b), composed from its four sub-walks. The B8b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b, 98 of its 1328 instructions; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none
   released). ADAPTED from a working branch (the image-A twin lane: pf_a8b_d / k / m / t.v) and the unit owner's
   UBSan piece walks, re-derived on image B's code; closed against G3 FINAL at 6f783602b5e3.

   THE SEGMENT (pf_seg_B8b_d.v's head comment has every pc): PROV2 0x88e4c, NEW 0x88e54 and FOUND 0x88eb0 to TAIL
   0x88600, through the walk-internal cut JOIN 0x88f00 (pf_seg_B8b_d.v):
     pf_seg_B8b_p.v  pb8b_prov2_holds : HA_TAIL n -> H_PROV2 n          (snprintf 0x88e4c, j TAIL)
     pf_seg_B8b_j.v  pb8b_join_holds  : HA_TAIL n -> H_B8B_JOIN n       (T34, B#38, B#39, seen_gen, snprintf cur_name)
     pf_seg_B8b_n.v  pb8b_new_holds   : HA_B8B_JOIN n -> H_NEW n        (B#35, T32, T33, memset, snprintf name)
     pf_seg_B8b_f.v  pb8b_found_holds : HA_B8B_JOIN n -> H_FOUND n      (B#36, B#37, F_twice refuse)
   JOIN is taken at every FP state (HA_B8B_JOIN), which pb8b_join_holds gives at every FP state from HA_TAIL.
   Counts against the plan's row (PLAN-pf-asanubsan section 5.2, B8b: 98 instructions, checks B#35-39, traps
   T32 T33 T34): the 66 instructions of 0x88e4c-0x88f50 are walked by the symbolic executor (PROV2 2, NEW 23 and
   0x88efc, FOUND 19 and 0x88efc, JOIN 21; the snprintf pair 0x88e4c / 0x88e50 again from JOIN); the 23 slow-arm
   instructions (0x89090-0x890b0, 0x890c0-0x890f4) and the 9 error-call instructions (0x892cc-0x892d4,
   0x892dc-0x892f0) are unreachable: every check's shadow byte is 0 (the block c is addressable, pf_obj's
   sa_addr c SEG_C_SIZE), so each `bnez` to a slow arm is decided not taken; 5 of 5 checks and 3 of 3 traps
   discharged.
   SECTION HYPOTHESES (pf_pieces.v's callee list for B8b, each at every FP state, and the listing / record facts the
   walks share): SNP (snprintf, RtFormat.asnprintf_realizes at the trampoline, gotwA / guardA), MEMSET
   (aintrin_realizes OSet at __asan_memset), REF (refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A,
   seg_litA_rc, gotwA, guardA), SIGP, OBJ and VRO (SegObj's seg_sig_prog / seg_val_objs / seg_val_relro), SSPX (the
   stack-protector cells at every AR state, as B6, B9, B10b, B11c take it: the cells after the refuse call). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YG00 YG0a YG01 YG0v YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegObj SegGlob SegPgBase SegABase refuse_c reac_segconf_parse_file_c SegInstB pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B8b_d pf_seg_B8b_p pf_seg_B8b_j
  pf_seg_B8b_n pf_seg_B8b_f.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis MEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (pa_sigma SS___asan_memset).
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.

(* JOIN at every FP state from TAIL at every FP state *)
Lemma pb8b_join_all : forall n, HA_TAIL B n -> HA_B8B_JOIN B n.
Proof. intros n HT f1. exact (pb8b_join_holds (fx := f1) B SNP OBJ n HT). Qed.

(* the segment statement of pf_pieces.v at every ambient FP state *)
Theorem S_B8b_holds : S_B8b B.
Proof.
intros f0 n. split; [|split].
- intros HT. pose proof (pb8b_join_all n HT) as HJ.
  exact (pb8b_new_holds (fx := f0) B SNP MEMSET OBJ n HJ).
- intros HT. pose proof (pb8b_join_all n HT) as HJ.
  exact (pb8b_found_holds (fx := f0) B REF SIGP OBJ VRO SSPX n HJ).
- intros HT. exact (pb8b_prov2_holds (fx := f0) B SNP n HT).
Qed.
End d.
