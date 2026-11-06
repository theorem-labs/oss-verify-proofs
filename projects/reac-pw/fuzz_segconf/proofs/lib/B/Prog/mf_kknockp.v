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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 494 of its 542 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kknock.v, with its module paths and module names changed; 31 of its 79 lines of code are new or changed and 494 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): segment S_MF_KKNOCKP of lib/B/Prog/m_file_m.v
   (KKNOCK 0x86a7c -> KDONE 0x86c1c; 44 owned instructions 0x86a7c-0x86b00, 0x86cf0-0x86cfc, 0x86d48-0x86d54, 0x86f20,
   0x86f3c; also runs 0x86c0c-0x86c18 and the `unimp` 0x86e84's edges). A walk lane of the image-B m_file-family owner's G2B.
   proves function m_file (one segment of its image-B walk): S_MF_KKNOCKP_ok.

   THE PIECES: mf_kknockp_2.v kk_s_kknock (ieq(k, kl, "knock") 0x86a8c, m_file_iq.v's mf_ieq_call; KKNOCK -> KK_R1),
   mf_kknockp_3.v kk_r1_miss (a0 = 0: 0x86c0c, m_refuse 0x86c14 with knock = false, 0x86c18 -> KDONE) and kk_after,
   mf_kknockp_4.v kk_r1_hit (a0 = 1: the check 0x86aa0 of n_kept's load, the UBSan traps 0x86abc / 0x86ac8 not taken,
   the check 0x86adc and the store kept_knock[n_kept] = 1 for n_kept < 8, m_refuse 0x86afc with knock = true, 0x86b00
   -> KDONE) with kk_s_rhit; this file joins them (kk_s_r1) and states the segment at every FP state.
   UBSan trap branches of the owned code (both to the `unimp` 0x86e84), each refuted at its branch by the executor's
   decision (decide_cond2) from a fact the walk holds:
     0x86abc `bltu 7,n_kept`: n_kept is the literal the block encodes (mconf_encp's u32 n_kept, 0 <= n_kept <= 8,
       kk_nkept_val; the run is made once per value, kk_hit_0 .. kk_hit_8), and n_kept <= 7 on this path (0x86ab4).
     0x86ac8 `bltu ~(c + 0x238c),4 n_kept`: 40(s1) = ~(c + 0x238c) (mf_cells' cell 40, the seed's mf_notx 33 0x238c),
       c a heap pointer below 2^47 (the seed's fact HPTR on atom 33), 4 n_kept <= 28.
   Instrumented checks: 0x86aa0 (load4 of n_kept at c + 0x23ac) and 0x86adc (store4 at c + 0x238c + 4 n_kept), each
   decided by m_file_sd.v's shadow entry mf_she_blk of the block [c, c + 9236): the shadow byte is 0, the slow paths
   0x86cf0 / 0x86d48 and the error paths 0x86f20 (errpath_load4) / 0x86f3c (errpath_store4) are not reached.
   Section hypotheses: VOBJS, SIGP (the listing), IMG (SegRecBase.seg_img_facts: its cif_relro_img is m_file_k.v's /
   m_file_rf.v's RELRO), SSP (m_file_rf.v's), IEQ (ieq_contract, m_file_iq.v's), M_REFUSE (m_refuse_contract,
   m_file_rf.v's). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c ieq_c m_refuse_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kknockp_1 mf_kknockp_2 mf_kknockp_3 mf_kknockp_4.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* KK_R1 0x86a90: `beqz a0` on ieq's answer b; the knock line or any other key, then KDONE *)
Lemma kk_s_r1 : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) -> KK_R1_stmt B n.
Proof.
intros n KD. unfold KK_R1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest b CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0.
destruct b.
- exact (kk_r1_hit B VOBJS n (kk_s_rhit B VOBJS SIGP SSP RELRO M_REFUSE n KD) v lyc Sc Wc regs1 memc mdc pos mcc gi
    line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0).
- exact (kk_r1_miss B VOBJS SIGP SSP RELRO M_REFUSE n KD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE
    CELLS RA Hn Hne LOOP FIN R27 NP A0).
Qed.
End e.
End f.
End d.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMG : SegRecBase.seg_img_facts SEGS B.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* the segment: KDONE at every FP state gives KKNOCK at every FP state *)
Lemma S_MF_KKNOCKP_ok : S_MF_KKNOCKP (rc := rc) (SK := SK) (PI := PI) B.
Proof.
unfold S_MF_KKNOCKP. intros n KD fx0.
assert (RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a)
  by (intros a Ha; exact (SegRecBase.cif_relro_img SEGS B IMG a Ha)).
exact (kk_s_kknock (fx := fx0) B VOBJS SIGP RELRO IEQ n (kk_s_r1 (fx := fx0) B VOBJS SIGP SSP RELRO M_REFUSE n KD)).
Qed.
End i.
End h.
End g.

About S_MF_KKNOCKP_ok.
Print Assumptions S_MF_KKNOCKP_ok.
