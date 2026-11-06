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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 824 of its 867 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_b.v, with its module paths and module names changed; 11 of its 36 lines of code are new or changed and 842 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: segment A10b of reac_segconf_parse_file's walk, assembled.

   proves function reac_segconf_parse_file (segment A10b; reuse search: origin/main, origin/ossv/recipes,
   origin/ossv/candidates, origin/release/pau-projects-recipes, the unreleased proof delivery, cold/* heads,
   image-A address 0x87a78 / the released-proof index on reac_segconf_parse_file; output and the G3 walk owner's
   CONFIRM of 2026-10-30T15:42:08Z in the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md;
   reuse verdict none: written new).

   pf_a10b_holds : S_A10b B  (lib/A/Prog/pf_pieces.v:765), INTENT 0x88450 -> TAIL 0x88068, 87 instructions
   (0x88450-0x884f8 42, 0x885a0-0x885a8 2, 0x8879c-0x887a4 2, 0x8883c-0x888b8 31, 0x88a70-0x88a90 8,
   0x88d28-0x88d30 2), checks 31 and 32, five bcmp calls, one refuse call, one snprintf call.

   The segment is cut at two inner cuts, ROLEV 0x88840 and JOIN 0x8888c (lib/A/Prog/pf_a10b_k.v), into three
   pieces, composed by pf_a10b_k.pa10_compose:
     pf_a10b_b.v (+ b2, b3, b4)  pa10_b_ok : PA10_B B   INTENT -> ROLEV (five match arms) / JOIN (refuse)
     pf_a10b_s.v                 pa10_s_ok : PA10_S B   ROLEV -> JOIN (checks 31, 32, two stores, snprintf)
     pf_a10b_j.v                 pa10_j_ok : PA10_J B   JOIN -> TAIL (s3 reload, low out of scope)
   with the pure facts of pf_a10b_f.v (the reader form of O1's bcmp half, the role chain, the two step shapes,
   sa_rconf after the role stores).

   SECTION HYPOTHESES, each a callee text pf_pieces.v's list names for A10b (its comment before Section s)
   or a listing fact over the abstract instance, at listing terms (the image-A owner's ruling 16:54Z):
     ABCMP      the kit's abcmp_realizes at pa_sigma SS___interceptor_trampoline_bcmp (pf_pieces.v:674)
     ASNPRINTF  RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA
                (row 4, pf_pieces.v:672-673; the site prints "%s", a piece FR_cmd has)
     REFUSE     refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
                (pf_pieces.v:683-684)
     SIGP, OBJ  SegObj's seg_sig_prog (refuse's call target) and seg_val_objs (the literal atoms A_OBJ 35,
                55 .. 60)
     SSPX, VRO  the stack-protector cells at every AR state, and seg_val_relro: FORCED, and only, where the
                JOIN cut is re-established after the refuse call (pf_a10b_b4.b_join through
                pf_a6_k.a6_base_move): refuse's post gives only its journal, the journal keeps an image byte
                only off as_owned_static B (lib/Reusable/YCbq.v:479), and whether the GOT word 0xa36d8 and the
                guard 0x5ff078 are owned statics is a record fact of listing stage 2
                (SegRecCells.seg_rec_cells); arodata_okP after refuse needs pa_relro_img. The G3 walk owner's
                accepted exception (2026-10-30, route A); discharged from stage 2.
   Segment A10b's proof, by the G3 walk owner, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YP09 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegInstA SegObj refuse_c pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
pf_a10b_k pf_a10b_b pf_a10b_s pf_a10b_j.
Open Scope Z_scope.

Section a.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* forced only by pf_a6_k.a6_base_move after the refuse call (pf_a10b_b4.b_join); see the head comment *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis VRO : seg_val_relro (PI := PI).

Theorem pf_a10b_holds : S_A10b B.
Proof.
exact (pa10_compose B (pa10_b_ok B ABCMP REFUSE SIGP OBJ SSPX VRO) (pa10_s_ok B ASNPRINTF OBJ) (pa10_j_ok B)).
Qed.
End a.
