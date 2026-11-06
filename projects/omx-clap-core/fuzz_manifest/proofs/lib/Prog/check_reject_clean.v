From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import fuzz_alloc_live_c check_reject_clean_c.
Open Scope Z_scope.

Theorem check_reject_clean_holds : fuzz_alloc_live_contract -> check_reject_clean_contract.
Proof.
  intros LIVE. unfold check_reject_clean_contract, CHECK_REJECT_CLEAN, CHECK_REJECT_CLEAN_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HL HMI ST LO DJ.
  unfold G_LIVE in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 16%nat ST.
  do 5 zstep.
  eapply evt_cut; [eapply LIVE; eassumption|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13280)) with (Z_to_bv 64 0x13280) by (apply bv_eq; vm_compute; reflexivity).
  zstep.
  if_cases HC.
  - exfalso. unfold bv_eqb in HC. rewrite Z.eqb_refl in HC. discriminate.
  - do 3 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.
