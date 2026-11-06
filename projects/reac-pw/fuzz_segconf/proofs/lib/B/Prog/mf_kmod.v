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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kmod.v, with its module paths and module names changed; 32 of its 65 lines of code are new or changed and 31 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): segment S_MF_KMOD of
   its walk (the image-B m_file segment table section 8, the image-B m_file cut map section 4): KMODEL 0x86840 -> KIGN 0x86968 or
   KDONE 0x86c1c, the "model" arm of m_key. A walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KMOD_ok; the walk is closed by m_file_m.v
   m_file_contract_of_parts from the 13 segment lemmas). Adapted from the image-A m_file-family lane's image-A S_MF_KMOD
   lane (commit c1e1a58468c5, lib/A/Prog/m_file_s_kmod_*.v) and the segconf porter's UBSan walk
   (a working branch, lib/U/Prog/mf_line_kmodel.v): image B calls fold, has the UBSan trap 0x8688c, and
   its own registers and frame cells.

   THE CHAIN (inner cuts and statements: lib/B/Prog/mf_kmod_m.v; model lemmas: mf_kmod_t.v):
     KMODEL --mf_kmod_a.v mk_kmodel_ok--> MK_IRET 0x86854 (ieq "model", m_file_iq.v mf_ieq_call)
     MK_IRET --mf_kmod_i.v mk_iret_ok--> KIGN 0x86968 (miss) | MK_FRET 0x86870 (fold cap 24, m_file_fold.v)
     MK_FRET --mf_kmod_f.v mk_fret_ok--> MK_RRET 0x86880 (fuzz_catalogue_row)
     MK_RRET --mf_kmod_r.v mk_rret_ok--> MK_REFUSE 0x86c08 (no row) | MK_CRET 0x868a4 (the trap 0x8688c refuted,
             checked_memcpy of low ++ [0] into g->model)
     MK_CRET --mf_kmod_c.v mk_cret_ok--> MK_LI 0x86c18 (the check of g + 32 and g->model_set = 1)
     MK_REFUSE --mf_kmod_x.v mk_refuse_ok--> MK_LI at the FP state m_refuse returns (m_file_rf.v mf_refuse_step)
     MK_LI --mf_kmod_x.v mk_li_ok--> KDONE 0x86c1c
   The UBSan trap branch of the segment (0x8688c, cur & 3 <> 0 -> unimp 0x86e84) and its one instrumented check
   (0x868b0, the 4-byte store of g->model_set) are in mf_kmod_r.v / mf_kmod_c.v.
   Section hypotheses: the callee contracts of the segment's calls (ieq, fold, fuzz_catalogue_row, the checked
   memcpy entry, m_refuse) and the image facts of the shared step files (VOBJS, SIGP, SSP, RELRO). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import ieq_c fold_c fuzz_catalogue_row_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_t mf_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require mf_kmod_a mf_kmod_i mf_kmod_f mf_kmod_r mf_kmod_c
  mf_kmod_x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState, ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis FOLD : forall fx0 : YK11.FPState, fold_contract (fx := fx0) SEGS B (BASE + AF_fold) SegInstB.STK_fold.
Hypothesis ROW : forall fx0 : YK11.FPState, fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row) SegInstB.STK_fuzz_catalogue_row SegInstB.RLO_A SegInstB.RHI_A SegInstB.catA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* S_MF_KMOD: KMODEL from KDONE (at every FP state) and KIGN *)
Lemma S_MF_KMOD_ok : S_MF_KMOD (rc := rc) (SK := SK) (PI := PI) B.
Proof.
intros n KD KI fx0.
assert (LI : MK_LI_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_x.mk_li_ok (fx := fx0) B); first [eassumption | exact (KD fx0)]).
assert (RF : MK_REFUSE_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_x.mk_refuse_ok (fx := fx0) B); eassumption).
assert (CR : MK_CRET_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_c.mk_cret_ok (fx := fx0) B); eassumption).
assert (RR : MK_RRET_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_r.mk_rret_ok (fx := fx0) B); eassumption).
assert (FR : MK_FRET_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_f.mk_fret_ok (fx := fx0) B); eassumption).
assert (IR : MK_IRET_stmt (fx := fx0) B n)
  by (eapply (mf_kmod_i.mk_iret_ok (fx := fx0) B); first [eassumption | exact (KI fx0)]).
eapply (mf_kmod_a.mk_kmodel_ok (fx := fx0) B); eassumption.
Qed.
End i.
End h.
End g.

About S_MF_KMOD_ok.
Print Assumptions S_MF_KMOD_ok.
