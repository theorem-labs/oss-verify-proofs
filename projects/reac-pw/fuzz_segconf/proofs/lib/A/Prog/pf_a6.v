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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 193 of its 226 lines of code are new or changed and 420 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_r.v, with its module paths and module names changed; 19 of its 40 lines of code are new or changed and 205 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A6 of reac_segconf_parse_file's walk,
   pf_a6_holds : pf_pieces.S_A6 B (lib/A/Prog/pf_pieces.v:736-739: LONG 0x87e2c -> TAIL and REF3 0x87e74 -> TAIL,
   24 instructions, check #3, calls strspn 0x87e34 and refuse 0x87e74). Segment A6's proof, 2026-10-30.
   The two halves: pf_a6_r.v (pf_a6_ref3 : HA_TAIL B n -> H_REF3 B n, the refuse call and the jump to TAIL) and
   pf_a6_l.v (pf_a6_long : H_REF3 B n -> H_LONG B n, strspn, check #3 and the '[' mask, at the same FP state:
   strspn's post is art_post); the helpers are pf_a6_k.v's.
   Section hypotheses (pf_pieces.v's list for A6, :669 and :683, plus the listing facts the walks use):
     REF     refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
     STRSPN  RtString.astrspn_realizes at pa_sigma SS___interceptor_trampoline_strspn, gotwA, guardA
     TL      PALib B, the listing's walk record (the strspn step's errno cell, pal_env)
     SIGP    seg_sig_prog, the listing's program call targets (refuse's entry)
     VRO, SSPX  FORCED by pf_a6_k.a6_base_move after the refuse call (pf_a6_r.v's head comment); discharged
             from listing stage 2 (SegObj's pinned instance / SegRecCells.seg_rec_cells). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj
SegPaLib SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c SegInstA pf_pieces pf_a6_r
pf_a6_l.
Import ListNotations.
Open Scope Z_scope.

Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis STRSPN : forall fx0 : YK11.FPState, @RtString.astrspn_realizes fx0 rc SEGS B
  (pa_sigma SS___interceptor_trampoline_strspn) gotwA guardA.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Theorem pf_a6_holds : S_A6 B.
Proof.
intros f0 n.
assert (R3 : HA_TAIL B n -> H_REF3 (fx := f0) B n) by (intros HT; apply (pf_a6_ref3 (fx := f0)); assumption).
split.
- intros HT. apply (pf_a6_long (fx := f0)); try assumption. exact (R3 HT).
- exact R3.
Qed.
End s.
