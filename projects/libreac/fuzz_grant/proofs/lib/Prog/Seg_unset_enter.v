From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_unset_enter_holds : seg_unset_enter.
Proof.
  unfold seg_unset_enter. intros x t ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hs0 & (Hs1 & Hs9) & Hs11 & HSL & (HTb & HT16 & HTl & HT) & (Hwl & Hstl & HWS & HSTA) &
                 HHr & HI1).
  unfold slots in HSL.
  pose proof HTb as HTb'. unfold blk in HTb'.
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs1, Hs9, Hs0, Hs11, Hsp.
  assert (ESPL : SPL x = x_S x - 592) by reflexivity.
  assert (ELS : LLVM_STACK = 8784) by reflexivity.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  rewrite ELS in Hrs.
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (ESZ : cells_size (map C8 (rev (x_sv x) ++ [x_ra x])) = 104%nat) by (apply saved_size; exact Hsv12).
  set (m0 := ms_mem ms) in *.
  destruct (stk_cell m0 _ _ (SPL x + 32) 8 HST ltac:(lia) ltac:(lia)) as [junk CSL].
  assert (MU : munch [(x_S x - 8784, x_S x)] m0 m0) by apply munch_refl.
  assert (WM : wmono rsegs m0 m0) by apply wmono_refl.
  unfold w64, PC_UNSET0.
  zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. split; [split; [exact MU | exact WM]|].
  fin_at.
Qed.
