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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 302 of its 349 lines of code are new or changed and 406 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a12_k.v, with its module paths and module names changed; 16 of its 44 lines of code are new or changed and 321 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B6 of
   reac_segconf_parse_file's walk, S_B6 of lib/B/Prog/pf_pieces.v (the B6 segment lane of the image-B G3 walk owner, 2026-10-30).
   proves no function on its own (kind: segment of reac_segconf_parse_file's walk; the composition lane joins the
   16 segments into the function's proof).
   ADAPTED from a working branch + U piece walks: the image-A G3 walk owner's image-A segment walks (pf_a5_k.v,
   pf_a2.v, pf_a7_s.v) and the unit owner's UBSan piece walks (lib/U/Prog/pf_p3.v, whose p3_in_set / p3_spn and the
   branchless-mask arithmetic are re-derived here on image B's code), re-derived on image B's numbers.
   S_B6 is the pair of walks that leave B6's two entries (plan section 5.2 row B6, 0x88258-0x882bc plus the cold
   0x88f78-0x88f84 and the stub 0x89260; 29 instructions, 1 UBSan trap site T06, 1 ASan check B#3):
     LONG 0x88258 -> TAIL, through the strspn call at 0x88260 and the shared refuse call at 0x882b4
     REF3 0x882b4 -> TAIL, the shared refuse call itself (B9's `j 0x882b4` at 0x884c0 enters here too)
   The two halves are pf_seg_B6_l.v (b6_long_ok, LONG to the REF3 cut) and pf_seg_B6_r2.v (b6_ref3, REF3 to
   TAIL); this file only joins them: the LONG half consumes HA_REF3, which the REF3 half gives from HA_TAIL at
   every FP state, so both halves of S_B6 follow from HA_TAIL alone. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YK04 YA0i YG0v YG00 YG0a YG01 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s YA0n YA0o YCbm YA0q YG0f YG0n YG0d YCbq YG0d_tail YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow
PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun
PaArt PaFx SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B6_k pf_seg_B6_a pf_seg_B6_r pf_seg_B6_r2 pf_seg_B6_l.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the one interceptor B6 calls (pf_pieces.v:849): strspn at the listing's trampoline, at every FP state *)
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strspn) gotwA guardA.
(* the one program callee B6 calls: refuse, at image B's entry and window, at every FP state *)
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance, and its runtime record (aj_art_at's errno cell) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis TL : PALib B.
(* the stack-protector cells at every AR state: refuse's journal does not keep the guard's shadow, so the walk
   re-derives them from the record (stage 2's SegRecCells discharges this; the image-B G3 walk owner, 2026-10-30) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* REF3 -> TAIL at every FP state, which is what the LONG half consumes *)
Lemma b6_ref3_all : forall n : nat, HA_TAIL B n -> HA_REF3 B n.
Proof. intros n HT f1. exact (b6_ref3 B REFUSE SIGP VRO SSPX (fx := f1) n HT). Qed.

Theorem pf_seg_B6_holds : S_B6 B.
Proof.
intros f0 n. split.
- intros HT. exact (b6_long_ok B STRSPN TL f0 n (b6_ref3_all n HT)).
- intros HT. exact (b6_ref3 B REFUSE SIGP VRO SSPX (fx := f0) n HT).
Qed.
End d.
