(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 44 of its 87 lines of code are new or changed and 537 lines of the source are left out. *)
(* The record loop's exit of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan 0x815ec ->
   0x81764): seg_rec_exit of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v.
     0x815ec beq a4,a0,81764    taken when x14 = i + 1 equals x10 = nrec, to the loop's exit (BASE + 0xff0)
   The branch reads two registers and writes nothing, so the state at the exit is the state at the test at
   another pc (the model's lazy-page bookkeeping aside). The helpers are seg_loop's
   (LLVMFuzzerTestOneInput_seg_loop.v); this is the B twin of seg_rec_exit_holds in
   lib/A/Prog/LLVMFuzzerTestOneInput_Loop.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_loop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
(* The Section of the contract and of the boundary layer, in the same order (LLVMFuzzerTestOneInput_inv.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* As the contract's Section states it. *)
Hypothesis LAWS : AR_laws SEGS B.

(* 0x815ec -> 0x81764: the exit, when S i = m_nrec g. *)
Theorem seg_rec_exit : seg_rec_exit_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_rec_exit_stmt. intros g pos mf i W2 c2 HD Heq.
unfold inv_D6_end, acut in HD.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo & Hmok & HEC & HP).
pose proof HP as (Hi & R14 & R10 & _).
pose proof (loop_nrec_range g) as Hnr. pose proof (loop_m_nrec_Z g) as Hnz.
assert (Heq' : Z.of_nat (S i) = SlotModel.nrec (e_pl g)) by (rewrite <- Hnz, Heq; reflexivity).
pose proof (loop_ss_test_ok W2 regs2 mem2) as HS.
unfold cfg_at.
eapply (paj_branch (PI := PI) W2 (Eimg (Ereg regs2 [])) loop_ss_test _ md2 _ BC_EQ (SOff 14 0) (SOff 10 0) HS).
- intros _ HSc.
eapply (loop_run B LAWS W2 regs2 mem2 md2 (add_cond loop_ss_test (mkAC BC_EQ (SOff 14 0) (SOff 10 0)))
0xe78 2 0xff0);
[reflexivity | exact HSc | reflexivity | vm_compute; reflexivity | exact HJ |].
intros regs' X HRG.
unfold inv_exit. rewrite <- Heq. replace (4 * Z.of_nat (S i)) with (4 * Z.of_nat i + 4)
by (rewrite Nat2Z.inj_succ; ring).
apply (loop_acut_moved B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS LAWS
g pos mf _ _ _ W2 ly2 S2 regs2 mem2 md2 regs' X HJ Hfr Hk Hmo Hmok HEC HRG).
cbv beta. unfold rec_live, cur_at, sh_reg, mf_fixed, mf_hw, mf_id3 in HP |- *.
clear - HP HRG.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
try (repeat (rewrite HRG by reflexivity); assumption).
- intros Hbt _. exfalso.
rewrite (loop_sv_reg regs2 14 14%bv _ eq_refl eq_refl R14), (loop_sv_reg regs2 10 10%bv _ eq_refl eq_refl R10) in Hbt.
rewrite loop_beq_w64 in Hbt by (clear - Heq' Hnr; lia).
apply Z.eqb_neq in Hbt. exact (Hbt Heq').
Qed.

Print Assumptions seg_rec_exit.

Check (seg_rec_exit : seg_rec_exit_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
