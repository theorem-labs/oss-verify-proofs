(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x141a4 .. the latch, composed: the stretches
   0x141a4 .. 0x143f0 (_op4_tag_a1 / _a / _b / _c / _d.v) against t4_split's model premises, and the
   record stretch 0x143f0 .. the latch as a premise (LLVMFuzzerTestOneInput_op4_tag_rec.v's t4r_rec_stmt). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_s LLVMFuzzerTestOneInput_op4_tag_rec
  LLVMFuzzerTestOneInput_op4_tag_a1 LLVMFuzzerTestOneInput_op4_tag_a LLVMFuzzerTestOneInput_op4_tag_b
  LLVMFuzzerTestOneInput_op4_tag_c LLVMFuzzerTestOneInput_op4_tag_d.
Import ListNotations.
Open Scope Z_scope.

Lemma t4_front : memset_contract -> memcpy_contract -> diginet_session_submit_contract ->
  check_refusal_submit_contract -> check_latest_submit_contract -> t4r_rec_stmt -> llvm_op4_tag_stmt.
Proof.
  intros MSET MCPY SUB CRS CLS REC. unfold llvm_op4_tag_stmt.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms B8 c5 H HT.
  destruct (t4_split _ _ _ _ _ _ _ _ HT) as (-> & HSER & at_ & rc & B3 & B4 & B5 & B6 & EA & ES & ER & EL & E6 & E8).
  pose proof H as H0.
  destruct H0 as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s5 & s6 &
                  t3 & t4 & t5 & t6 & m & jlo & jio & jhi0 & _ & HOPS & HCUR & HBEF & HDSP & HKEY & _ & _ & _).
  pose proof (t4_ncmd_rng B1) as HNR.
  assert (HAR : at_ = -1 \/ 0 <= at_ < CMDS_MAX).
  { unfold t4_atopt in EA. destruct (negb (h_coalescable_m key =? 0)).
    - destruct (t4_findat_rng _ _ _ 0 at_ ltac:(lia) EA) as [R|R]; [right; lia | left; exact R].
    - injection EA as <-. left; reflexivity. }
  eapply t4_A; [exact MSET | exact H | exact HSER |]. intros ms1 H1.
  eapply t4_B1; [exact H1 |]. intros ms2 H2.
  eapply t4_B2; [exact MCPY | exact H2 |]. intros ms3 H3.
  eapply t4_C; [exact H3 |]. intros ms4 H4.
  eapply t4_D; [exact H4 | exact EA |]. intros ms5 H5.
  eapply t4_E1; [exact H5 | exact EA |]. intros ms6 H6.
  eapply t4_E2; [exact SUB | exact CRS | exact CLS | exact H6 | exact ES | exact ER | exact EL |].
  intros ms7 (jhi & LJHI & H7).
  exact (REC data D regs0 m0 Sp lo ops before c3 B1 display key jhi at_ B5 B6 B8 F fc ms7
           HOPS HCUR HDSP HKEY ltac:(lia) LJHI HAR E6 E8 H7).
Qed.
