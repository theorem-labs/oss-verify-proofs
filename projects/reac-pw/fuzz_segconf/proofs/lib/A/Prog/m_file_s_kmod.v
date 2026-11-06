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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 34 of its 64 lines of code are new or changed and 423 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): segment S_MF_KMOD of its walk (KMODEL 0x867b8 -> KIGN 0x8693c
   or KDONE 0x86cd0; the G2 walk owner's guide/MF-CUTS-A.md section 4, 76 instructions): ieq(k, kl, "model") 0x867c8, a
   miss to KIGN; a hit: ln = min(vl, 23), the fold of the value into low.i (cap 24), low[ln] = 0,
   fuzz_catalogue_row(low, ln) 0x86878; NULL: m_refuse(c, line + 1) 0x86ccc; else __asan_memcpy(g->model, low,
   ln + 1) 0x86890 and g->model_set = 1 0x868b0; both to KDONE. The KMOD segment lane of the G2 walk owner's G2.

   The segment is cut at the inner points of lib/A/Prog/m_file_s_kmod_m.v (MK_FOLD 0x867f8, MK_FEXIT 0x86864,
   MK_CPY 0x86880, MK_REFUSE 0x86cc0); each piece is its own file and this one chains them:
     m_file_s_kmod_a.v  mk_kmodel_ok : MF_KIGN_stmt -> MK_FOLD_stmt -> MK_FEXIT_stmt -> MF_KMODEL_stmt
     m_file_s_kmod_l.v  mk_fold_ok   : MK_FEXIT_stmt -> MK_FOLD_stmt                 (the fold loop)
     m_file_s_kmod_b.v  mk_fexit_ok  : MK_REFUSE_stmt -> MK_CPY_stmt -> MK_FEXIT_stmt  (fuzz_catalogue_row)
     m_file_s_kmod_r.v  mk_refuse_ok : MF_KDONE_F -> MK_REFUSE_stmt                    (m_refuse; FP change)
     m_file_s_kmod_c.v  mk_cpy_ok    : MF_KDONE_stmt -> MK_CPY_stmt                   (memcpy, model_set)
   The model and encoding lemmas are m_file_s_kmod_t.v. The Section hypotheses are the G2 walk owner's shared list (a)
   (the m_file cut-statement lane), each piece taking the ones it uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import ieq_c fuzz_catalogue_row_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
  m_file_s_kmod_a m_file_s_kmod_l m_file_s_kmod_b m_file_s_kmod_r m_file_s_kmod_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
(* the G2 walk owner's shared hypothesis list (a) (the m_file cut-statement lane), the ones this segment's pieces use: VOBJS (every seed),
   SIGP and RELRO (the program calls), SSP (m_refuse), and the callees at every FP state *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Hypothesis IEQ : forall fx0 : YK11.FPState, ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis FCR : forall fx0 : YK11.FPState, fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row) SegInstA.STK_fuzz_catalogue_row SegInstA.RLO_A SegInstA.RHI_A SegInstA.catA.

(* S_MF_KMOD: KMODEL at every FP state from KDONE at every FP state and KIGN *)
Lemma s_mf_kmod : S_MF_KMOD B.
Proof.
unfold S_MF_KMOD. intros n KD KI fx0.
assert (REF : MK_REFUSE_stmt (fx := fx0) B n)
  by (eapply m_file_s_kmod_r.mk_refuse_ok; first [exact KD | eassumption]).
assert (CPY : MK_CPY_stmt (fx := fx0) B n)
  by (eapply m_file_s_kmod_c.mk_cpy_ok; first [exact (KD fx0) | eassumption]).
assert (FEX : MK_FEXIT_stmt (fx := fx0) B n)
  by (eapply m_file_s_kmod_b.mk_fexit_ok; first [exact REF | exact CPY | eassumption]).
assert (FOLD : MK_FOLD_stmt (fx := fx0) B n)
  by (eapply m_file_s_kmod_l.mk_fold_ok; first [exact FEX | eassumption]).
eapply m_file_s_kmod_a.mk_kmodel_ok; first [exact (KI fx0) | exact FOLD | exact FEX | eassumption].
Qed.

End i.
End h.
End g.

About s_mf_kmod.
Print Assumptions s_mf_kmod.
