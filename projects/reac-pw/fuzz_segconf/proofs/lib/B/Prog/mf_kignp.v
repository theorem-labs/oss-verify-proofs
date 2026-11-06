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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 144 of its 186 lines of code are new or changed and 411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kmod_r.v, with its module paths and module names changed; 34 of its 79 lines of code are new or changed and 141 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): segment S_MF_KIGNP of
   its walk (KIGN 0x86968 -> KKNOCK 0x86a7c, KDONE 0x86c1c; the image-B m_file segment table section 9), S_MF_KIGNP_ok, from its
   pieces. A walk lane of the image-B m_file-family owner's G2B. ADAPTED from the image-A m_file-family lane's image-A S_MF_KIGNP lane
   (commit a11e040adbd4: m_file_s_kign_1.v / _m.v / _t.v / _e.v) at image B.
   proves function m_file (reuse search: rule 24, over the four shared refs and the live working-branch heads; the
   result is recorded with the commissioning brief): none released, written new per segment; this file: its segment S_MF_KIGNP.

   The pieces (each `<its exit statements> -> <its entry statement>`):
     mf_kignp_1.v  ki_s_kign  KI_R1 -> KIGN            ieq(k, kl, "ignore") 0x86978
                   ki_s_r1    KKNOCK, KI_R2 -> KI_R1   beqz 0x86980; ieq "yes" 0x86994
     mf_kignp_2.v  ki_s_r2    KI_HIT, KI_R3 -> KI_R2   s4 = 1, bnez 0x8699c; ieq "true" 0x869b0
                   ki_s_r4    KI_HIT, KI_R5 -> KI_R4   bnez 0x869f8 (s4 = 0); ieq "false" 0x86a0c
     mf_kignp_3.v  ki_s_r3    KI_HIT, KI_R4 -> KI_R3   vl = 1 and v[0] = '1' (trap 0x869c4, check 0x869d0); ieq "no"
                   ki_s_r5    KI_HIT, KI_REF -> KI_R5  vl = 1 and v[0] = '0' (trap 0x86be8, check 0x86bf4)
     mf_kignp_h.v  ki_s_hit   KI_SNR -> KI_HIT         trap 0x86a20 (cur & 3), the two checked stores (checks
                                                       0x86a34, 0x86a4c), snprintf(g->ignore_file, ..) 0x86a74
     mf_kignp_r.v  ki_s_ref   KI_S4 -> KI_REF          m_refuse(c, line + 1) 0x86c14 (m_file_rf.v mf_refuse_step)
     mf_kignp_d.v  ki_s_done  KDONE -> KI_SNR, KI_S4   j 0x86c18; li s4,511
   The UBSan trap branches of the owned code, each refuted at its branch by the symbolic executor: 0x869c4 and
   0x86be8 (v = NULL; v = p + ov lies in the text block, >= 4096), 0x86a20 (cur & 3; cur = c + 256 gi, c mod 16 = 0).
   Section hypotheses: VOBJS (the listing's objects), SIGP (the program callees' call targets), SSP and RELRO (the
   image-record facts of m_file_k.v / m_file_rf.v / m_file_sn.v), and the callee rows of the image-B m_file segment table: IEQ (ieq),
   M_REFUSE (m_refuse), ASNPRINTF (snprintf row 4, pc SIGMA SS___interceptor_trampoline_snprintf). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq ieq_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFCmd RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx m_refuse_c m_file_rf m_file_sn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_1 mf_kignp_2 mf_kignp_3 mf_kignp_d mf_kignp_r mf_kignp_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.

Lemma S_MF_KIGNP_ok : S_MF_KIGNP (rc := rc) (SK := SK) (PI := PI) B.
Proof.
unfold S_MF_KIGNP. intros n KD KK fx0.
assert (DSNR : forall fx1 : YK11.FPState, KI_DONE_stmt (fx := fx1) B KI_SNR n).
{ intros fx1. eapply (ki_s_done (fx := fx1) B); try eassumption; [left; reflexivity | exact (KD fx1)]. }
assert (DS4 : forall fx1 : YK11.FPState, KI_DONE_stmt (fx := fx1) B KI_S4 n).
{ intros fx1. eapply (ki_s_done (fx := fx1) B); try eassumption; [right; reflexivity | exact (KD fx1)]. }
assert (HIT : KI_HIT_stmt (fx := fx0) B n) by (eapply (ki_s_hit (fx := fx0) B); try eassumption).
assert (REF : KI_REF_stmt (fx := fx0) B n) by (eapply (ki_s_ref (fx := fx0) B); try eassumption).
assert (R5 : KI_R5_stmt (fx := fx0) B n) by (eapply (ki_s_r5 (fx := fx0) B); try eassumption).
assert (R4 : KI_R4_stmt (fx := fx0) B n) by (eapply (ki_s_r4 (fx := fx0) B); try eassumption).
assert (R3 : KI_R3_stmt (fx := fx0) B n) by (eapply (ki_s_r3 (fx := fx0) B); try eassumption).
assert (R2 : KI_R2_stmt (fx := fx0) B n) by (eapply (ki_s_r2 (fx := fx0) B); try eassumption).
assert (R1 : KI_R1_stmt (fx := fx0) B n) by (eapply (ki_s_r1 (fx := fx0) B); try eassumption; exact (KK fx0)).
eapply (ki_s_kign (fx := fx0) B); eassumption.
Qed.
End e.
End f.
End d.

About S_MF_KIGNP_ok.
Print Assumptions S_MF_KIGNP_ok.
