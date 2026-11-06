(* ARM 3 (op_unmark) at the SR level: LC3Seg.c3_arm is one evt segment of the slot's own code from the loop
   head to the next loop head or the exit, writing only md, mk, the stack window and the slot's globals; one
   cut_evt_or turns it into LGlue's ARM 3. hb and T do not change. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem
  kernel_c model_read_c model_write_c bcmp_c reac_served_unmark_all_c check_socket_c check_marks_c
  check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LGlue LC3Seg.
Import ListNotations.
Local Open Scope Z_scope.

Section G3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Hypothesis KERNEL_C : kernel_contract.
Hypothesis MODEL_READ_C : model_read_contract.
Hypothesis MODEL_WRITE_C : model_write_contract.
Hypothesis BCMP_C : bcmp_contract.
Hypothesis UNMARK_ALL_C : reac_served_unmark_all_contract.
Hypothesis CHECK_SOCKET_C : check_socket_contract.
Hypothesis CHECK_MARKS_C : check_marks_contract.
Hypothesis CHECK_REQUESTS_C : check_requests_contract.

Hypothesis FF : LFF B API.

(* the two ends' program points *)
Lemma lh_ms_pc : forall E i gp ms, lh_ms E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_LH) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                    & F & fc & m & P & N & kbs & mbs & gbs & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma ex_ms_pc : forall E gp ms, ex_ms E gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 L_EXIT) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E gp ms (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s1 & s2 & s3 & s4 & s5 & s6 & s8
                  & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & j & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Theorem glue_arm3 : ARM B API 3.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  set (E := lg_E g md mk) in *.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  eapply SR_mono.
  - apply (cut_evt_or B API FF g L_LH hb T [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)] _ L_LH
             (fun ms => i < 47 /\ lh_ms E (i + 1) (lg_gp g) ms) L_EXIT (ex_ms E (lg_gp g)) c HC
             (hp_md_mk g E hb T HI HT)).
    + intros ms (HL & HO).
      exact (c3_arm KERNEL_C MODEL_READ_C MODEL_WRITE_C BCMP_C UNMARK_ALL_C CHECK_SOCKET_C CHECK_MARKS_C
               CHECK_REQUESTS_C E i (lg_gp g) ms OK HL HO).
    + intros ms' (_ & H). exact (lh_ms_pc _ _ _ _ H).
    + intros ms' H. exact (ex_ms_pc _ _ _ H).
  - intros c' [H1 | H2]; unfold arm_post; exists hb, T; split; try exact HI.
    + left. split.
      * destruct H1 as (fx' & L & A & regs & mem & md' & _ & _ & _ & (c0 & (Hlt & _) & _)). exact Hlt.
      * exact (cut_mono B API g L_LH hb T _ _ c' (fun ms H => proj2 H) H1).
    + right. exact H2.
Qed.

End G3.

Print Assumptions glue_arm3.
