From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel __lock_c __ofl_lock_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __ofl_lock_holds : __lock_contract -> __ofl_lock_contract.
Proof.
  intros HLOCK. unfold __ofl_lock_contract, OFL_LOCK_FN, OFL_LOCK_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo [HT [HN HL]] MI ST LO HI.
  unfold A_OFL_HEAD in HI. unfold A_LIBC in HT, HN. unfold A_OFL_LOCK, wz in HL.
  replace (0x95898 + 3) with 0x9589b in HN by reflexivity.
  replace (0x95898 + 1) with 0x95899 in HT by reflexivity.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HLOCK; unfold A_LIBC; eassumption | intros ms' [a1' [a3' ->]]] end.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  apply evt_done. unfold __ofl_lock_post.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.
