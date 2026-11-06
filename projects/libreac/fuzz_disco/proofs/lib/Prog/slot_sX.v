From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_exit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_seg slot_preds.
Import ListNotations.
Open Scope Z_scope.


Lemma seg_X1 : forall X h regs0,
  seg_ev EXIT [] (P_EXIT X h regs0) (fun q R m => q = FREE_PC /\ P_FREEH X h regs0 R m).
Proof.
  intros X h regs0 fx' regs m0 Hf HI (E2 & E3 & E4 & E20 & SV).
  eapply evt_mono; [unfold rmk; apply slot_R29_call|].
  intros ms ->. do 5 eexists. split; [reflexivity|].
  split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [reflexivity|]. unfold P_FREEH.
  split; [reflexivity|]. split; [exact E20|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. exact SV.
Qed.

Lemma seg_X2 : forall X regs0,
  0 <= X -> X + 2592 <= 2 ^ 64 -> getr regs0 2 = Z_to_bv 64 (X + 2592) -> getr regs0 4 = Z_to_bv 64 0x31260 ->
  seg_ev R29_RET [] (P_R29 X regs0) (fun q R m => q = bv_unsigned (ret_pc (getr regs0 1)) /\ P_RET regs0 R m).
Proof.
  intros X regs0 HX0 HX1 E02 E04 fx' regs m0 Hf HI (E2 & E3 & E4 & SV).
  eapply evt_mono; [unfold rmk; apply (slot_R29_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ X _ _ _ _ _ _ _ _ _ _ _ _ _ E2 HX0 HX1 SV)|].
  intros ms ->. do 2 eexists. exists (bv_unsigned (ret_pc (getr regs0 1))). do 2 eexists.
  split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [reflexivity|]. split; [|reflexivity].
  intros r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]];
    [symmetry; exact E02 | exact E3 | exact (eq_trans E4 (eq_sym E04)) | reflexivity | reflexivity |].
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.
