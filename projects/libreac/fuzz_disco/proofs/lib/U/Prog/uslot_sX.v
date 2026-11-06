From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv uslot_norm uslot_exit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_seg uslot_preds.
Import ListNotations.
Open Scope Z_scope.

Lemma seg_X1 : forall X h regs0, xok X ->
  seg_ev EXIT [] (P_EXIT X h regs0) (fun q R m => q = FREE_PC /\ P_FREEH X h regs0 R m).
Proof.
  intros X h regs0 (HX0 & HX16 & HX1 & HXlo) fx' regs m0 Hf HI (E2 & E3 & E4 & C168 & SV).
  assert (RH : ov_read_bytes rsegs m0 (wa (X + 168)) 8 = Some (le8 (Z_to_bv 64 h))).
  { eapply (rw_cells_read_at rsegs m0 (X + 168) [C8 (Z_to_bv 64 h)] 0 (C8 (Z_to_bv 64 h)));
      [exact C168 | reflexivity | reflexivity | rewrite Z.add_0_r; reflexivity]. }
  eapply evt_mono; [unfold rmk; apply (uslot_R29_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    X h E2 ltac:(lia) ltac:(unfold SLOT_FRAME in *; lia) RH)|].
  intros ms ->. do 5 eexists. split; [reflexivity|].
  split; [exact Hf|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [reflexivity|]. unfold P_FREEH.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. exact SV.
Qed.

Lemma seg_X2 : forall X regs0,
  0 <= X -> X + 2624 <= 2 ^ 64 -> getr regs0 2 = Z_to_bv 64 (X + 2624) -> getr regs0 4 = Z_to_bv 64 0x31a20 ->
  seg_ev R29_RET [] (P_R29 X regs0) (fun q R m => q = bv_unsigned (ret_pc (getr regs0 1)) /\ P_RET regs0 R m).
Proof.
  intros X regs0 HX0 HX1 E02 E04 fx' regs m0 Hf HI (E2 & E3 & E4 & SV).
  eapply evt_mono; [unfold rmk; eapply (uslot_R29_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    X); [exact E2 | exact HX0 | exact HX1 | exact SV]|].
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
