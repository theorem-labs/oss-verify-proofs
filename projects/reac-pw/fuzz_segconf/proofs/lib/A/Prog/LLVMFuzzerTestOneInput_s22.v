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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 622 of its 662 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s22a.v; 25 of its 58 lines of code are new or changed and 629 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S14 of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84d34), the body of the inlined m_declared loop at turn
   i: 0x858f4 .. 0x85ac0 with the continue join 0x859c4 .. 0x859f8 (141 instructions, checks 30-35, one call of
   the strrchr wrapper, one checked memcpy, two inner loops without calls). Lane 22 of the harness walk.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s47.v (origin/ossv/recipes
   501c0d516c69): a segment cut at inner points whose statements live in a kit (_s22k.v, as _s40.v), each piece
   proved in its own file (_s22a .. _s22f, as _s41 .. _s48), and the segment lemma composed from them.

   The cut (LLVMFuzzerTestOneInput_s22k.v):
     P1 _s22a  0x858f4 .. 0x8592c  v in scope, the ignore test (check 30), the strrchr call        -> JOIN | VR
     P2 _s22b  0x85930 .. 0x85970  no '.', '.' first, NUL after it (check 31)                     -> JOIN | VD
     P3 _s22c  the digit loop 0x85974 <- 0x859a8 (check 32) and its exit 0x859fc .. 0x85a14      -> JOIN | VP
     P4 _s22d  the parent loop 0x85a18 <- 0x85a78 (check 34) and its failure exit 0x85b88         -> JOIN | VM
     P5 _s22e  0x85a8c .. 0x85ac0  88(s1) := tab, memcpy(v, name, di), the NUL (check 35), vid   -> K85ac4 i
     P6 _s22f  the join 0x859c4 .. 0x859f8  v out of scope, m->n (check 33), the latch  -> K858f4 (S i) | K85bd0
   and s22_compose chains them into lt_seg_S14_stmt. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
LLVMFuzzerTestOneInput_s22a LLVMFuzzerTestOneInput_s22b LLVMFuzzerTestOneInput_s22c
LLVMFuzzerTestOneInput_s22d LLVMFuzzerTestOneInput_s22e LLVMFuzzerTestOneInput_s22f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Local Open Scope Z_scope.

Module P1 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22a.
Module P2 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22b.
Module P3 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22c.
Module P4 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22d.
Module P5 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22e.
Module P6 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.LLVMFuzzerTestOneInput_s22f.

(* a premise of a piece lemma is a walk hypothesis of this section, possibly at another FP state
   (fuzz_command lib/A/Prog/LLVMFuzzerTestOneInput.v:42) *)
Ltac s22_close := solve [ assumption | match goal with H : forall fx0 : YK11.FPState, _ |- _ => exact (H _) end ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's hypotheses: the listing record of the runtime cells and wrappers (PALib, PALibF), the image facts
   lt_img needs at a later reader (_s10's s10_img) and the record's symbols (BSYM, AR's stack-protector cells),
   the model and meter laws, and the two runtime rows the segment calls, each at every FP state *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strrchr).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).

Theorem lt_seg_S14 : lt_seg_S14_stmt B MT.
Proof using All.
apply (s22_compose B MT).
- eapply P1.s22_p1; s22_close.
- eapply P2.s22_p2; s22_close.
- eapply P3.s22_p3; s22_close.
- eapply P4.s22_p4; s22_close.
- eapply P5.s22_p5; s22_close.
- eapply P6.s22_p6; s22_close.
Qed.

End e.
End f.
End d.
About lt_seg_S14.
Print Assumptions lt_seg_S14.
