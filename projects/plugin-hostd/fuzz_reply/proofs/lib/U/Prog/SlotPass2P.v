From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB HarnessGlue HarnessFrame SlotReads SlotEntryRun SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ
  SlotHeadQD SlotPass1 pthread_mutex_lock_c pthread_mutex_unlock_c pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c
  pthread_mutex_lock_ro pthread_mutex_unlock_ro SlotPass9G SlotPass2Run check_no_loss_read_c check_no_loss_c
  check_shape_done_c SlotPass2Check SlotPass2Aux ListTr HarnessTr RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotMove SlotWalk SlotPass2Mv SlotPass2
  SlotPass2D.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Cells.
Import ListNotations.
Local Open Scope Z_scope.

Theorem pass2_holds : forall (F : ResFormT),
  check_bounded_contract -> pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty -> @drain_contract fx rc B (API rc) F) ->
  check_no_loss_read_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @check_no_loss_contract fx rc B (API rc) F) ->
  check_shape_done_contract ->
  forall RI, RI_mono RI -> p2_drain_res_s F RI -> p2_cnl_res_s F RI -> pass_ok RI 2.
Proof.
  intros F CB LCK ULK HD CNR HC CSD RI RIM DRES CRES B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop.
  cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 2) with 0x14334 in HM.
  pose proof (walk_pick E t k 2 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
    (or_introl eq_refl)) as HW2.
  eapply SR_bind; [exact (MI_op2_scan B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 2 k) s c' HF CB LCK HW2 HM)|].
  intros c2 [HL2|HD2]; [apply SR_ret; exists (disp_k E 2 k); exact HL2|].
  exact (p2_drain_path F B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 2 k) c2 HF CB ULK
    (fun fx' => HD B API LS SH SK ra empty rc fx' (proj1 HF)) CNR
    (fun fx' => HC B API LS SH SK ra empty rc fx' (proj1 HF)) CSD DRES CRES HW2 HD2).
Qed.
