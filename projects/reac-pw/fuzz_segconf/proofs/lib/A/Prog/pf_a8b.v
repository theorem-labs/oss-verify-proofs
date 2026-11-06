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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 38 of its 69 lines of code are new or changed and 422 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan): segment A8b of reac_segconf_parse_file's walk.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk); the lane's rule-24 record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md (reuse
   verdict: none, written new).

   S_A8b (lib/A/Prog/pf_pieces.v:752-755) is
     forall f0 n, (HA_TAIL n -> H_NEW B n) /\ (HA_TAIL n -> H_FOUND B n) /\ (HA_TAIL n -> H_PROV2 B n).

   THE CODE (the unit's internal record, commit dfb49d6ad789,
   path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s; 91 instructions:
   0x8890c-0x889f8 main, 0x88b34-0x88b58 and 0x88b64-0x88b9c the five checks' slow blocks,
   0x88d78-0x88d84 and 0x88d88-0x88da0 their error stubs):

     NEW 0x8890c  ld a0,0xb0(s1); lb a0,0(a0); bnez -> 0x88b64      check #35, store4 of c->n
                  addi a0,s3,1; addi a1,zero,0x164; mul a1,s3,a1
                  ld a2,0x80(s1); sw a0,0(a2)                        c->n = n + 1
                  ld s8,0x90(s1); add s4,s8,a1                       s4 = &c->seg[n]
                  addi a2,zero,0x164; mv a0,s4; mv a1,zero
                  jal 0x55d7c <checked_memset>                       memset(&seg[n], 0, 356)
                  auipc/addi a2 = 0x21340 "%s"; addi a1,zero,0x10; mv a0,s4; mv a3,s9
                  jal 0x43a64 <wrapper_snprintf>                     snprintf(seg[n].name, 16, "%s", np)
                  ld s3,0x98(s1); j 0x889b0
     FOUND 0x88964 srli a0,s7,3; add a0,a0,s6; lb a0,0(a0); bnez -> 0x88b78   check #36, load4 seen_gen
                  ld a3,0x38(s1); lb a1,0(a3)                        check #37, load4 c->gen
                  lw a0,0x160(s4); ld s8,0x90(s1); ld s3,0x98(s1)
                  bnez a1 -> 0x88b88
                  ld a1,0x40(s1); lw a1,0(a1)                        a1 = c->gen
                  bne a0,a1 -> 0x889b4                               seen_gen <> gen: no refusal
                  a2 = 0x21620 F_twice; a0 = s8 = c; a1 = s10 = lineno; a3 = s9 = name
                  jal 0x88da4 <refuse>
            0x889b0 ld a3,0x38(s1)                                   (refuse clobbered a3)
     JOIN 0x889b4 lb a0,0(a3); bnez -> 0x88b34                       check #38, load4 c->gen
                  addi a0,s4,0x160; srli a1,a0,3; add a1,a1,s6; lb a2,0(a1)   check #39, store4 seen_gen
                  ld a1,0x40(s1); lw a1,0(a1); bnez a2 -> 0x88b48
                  sw a1,0(a0)                                        seg[i].seen_gen = c->gen
                  a2 = 0x21340 "%s"; a1 = 0x10; a0 = slot 0x50 = cur_name; a3 = s9 = np
     PROV2 0x889f0 jal 0x43a64 <wrapper_snprintf>                    snprintf(cur_name, 16, "%s", np), or, when
                  j 0x88068 (TAIL)                                   entered from A12 at 0x88908 with a0 =
                                                                     &seg[gi].ignore_file, a1 = 0x60, a3 = c->reading

   THE SHAPE OF THE PROOF. NEW and FOUND both reach the pc 0x889b4, which this file cuts as the walk-internal
   point JOIN (PF_A8B_JOIN): FOUND's `bne` arm jumps straight to it and both the refuse-return path (through
   0x889b0) and NEW's `j 0x889b0` reach it after one `ld a3,0x38(s1)`. JOIN's own work -- the seen_gen store and
   the cur_name snprintf -- is the common tail, and the pc 0x889f0 it ends at is PROV2's cut, so H_PROV2 is the
   last two instructions of JOIN with other argument registers. The segment is four sub-walks:
     pfa8b_prov2 : HA_TAIL n -> H_PROV2 n        lib/A/Prog/pf_a8b_p.v  (the snprintf and the jump to TAIL)
     pfa8b_join  : HA_TAIL n -> H_A8B_JOIN n     lib/A/Prog/pf_a8b_j.v  (checks #38/#39, the seen_gen store, the
                                                                         cur_name snprintf, TAIL)
     pfa8b_new   : HA_A8B_JOIN n -> H_NEW n      lib/A/Prog/pf_a8b_n.v  (check #35, c->n, memset, snprintf)
     pfa8b_found : HA_A8B_JOIN n -> H_FOUND n    lib/A/Prog/pf_a8b_r.v  (checks #36/#37, the branch, refuse)
   over the shared vocabulary lib/A/Prog/pf_a8b_d.v (the cut JOIN and its seed), the transport kit
   pf_a8b_k.v, the model and byte-encoding lemmas pf_a8b_m.v, the snprintf step pf_a8b_t.v and JOIN's seed
   pf_a8b_q.v. JOIN is taken at EVERY FP state (HA_A8B_JOIN), because FOUND reaches it after refuse.

   Section hypotheses: the union of the four sub-walks' (each lemma takes only what it uses):
   ASNP (RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA; PROV2,
   JOIN, NEW), AMSET (aintrin_realizes OSet at pa_sigma SS___asan_memset; NEW), REF (refuse_contract at
   BASE + AF_refuse; FOUND), SIGP (seg_sig_prog, the refuse call target; FOUND), OBJ (seg_val_objs, the
   literal atoms of "%s" and F_twice; JOIN, NEW, FOUND), and VRO / SSPX, which ONLY FOUND carries and only
   for pf_a6_k.a6_base_move after the refuse call: refuse's post gives only its journal, the journal keeps
   an image byte only when it is not in as_owned_static B (YCbq.v:479), and whether the GOT word 0xa36d8 and
   the guard 0x5ff078 are owned statics is a listing-stage-2 record fact (SegRecCells.seg_rec_cells, after
   the image-A owner's AF0m); arodata_okP after refuse needs pa_relro_img (VRO). Everywhere else sa_ssp,
   arodata_okP and rt_rom_view come from pf_base (pf_a5_k.a5_rom and the image range [0x10000, kImgEnd),
   which holds no byte this segment writes). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_d pf_a8b_p pf_a8b_j
pf_a8b_n pf_a8b_r.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* ---- the callee texts of A8b (pf_pieces.v's per-segment list), at listing terms ---- *)
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis REF : forall fx0 : YK11.FPState,
  refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* VRO and SSPX: FORCED, for now, only by pf_a6_k.a6_base_move after FOUND's refuse call (see the head
   comment); SSPX is the image-A owner's route A, in lib/A/Prog/reac_segconf_parse.v's shape, discharged by
   SegRecCells.seg_rec_cells after listing stage 2 *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.


(* ======================= S_A8b from the four sub-walks =======================
   NEW (0x8890c) and FOUND (0x88964) both reach the walk-internal cut JOIN (0x889b4, pf_a8b_d.v), which runs
   the seen_gen store and the cur_name snprintf and ends at TAIL; PROV2 (0x889f0) is the same snprintf with
   A12's argument registers. JOIN is taken at every FP state because FOUND reaches it after a refuse call. *)
Theorem pf_a8b_holds : S_A8b B.
Proof.
intros f0 n. split; [|split]; intros HT.
- eapply pfa8b_new; try eassumption. intros f1. eapply pfa8b_join; eassumption.
- eapply pfa8b_found; try eassumption. intros f1. eapply pfa8b_join; eassumption.
- eapply pfa8b_prov2; eassumption.
Qed.

End e.
End f.
End d.
