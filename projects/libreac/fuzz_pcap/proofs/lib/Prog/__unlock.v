From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel __unlock_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sx32_nonneg_lts : forall w, 0 <= w < 2 ^ 31 -> bv_lts (sx32 (Z_to_bv 64 w)) (Z_to_bv 64 0) = false.
Proof.
  intros w Hw. rewrite bv_lts_zero_r. unfold sx32.
  rewrite (unsigned_lit w) by lia.
  rewrite bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia).
  rewrite unsigned_lit by lia. apply Z.leb_gt. lia.
Qed.

Theorem __unlock_holds : __unlock_contract.
Proof.
  unfold __unlock_contract, UNLOCK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m w HB Hw.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_le4 in BB.
  assert (RD : ov_read_bytes rsegs m a0 4 = Some (le4 (Z_to_bv 64 w))).
  { pose proof (bytes_at_read rsegs m (bv_unsigned a0) (le4 (Z_to_bv 64 w)) 0 4 HB ltac:(lia)
       ltac:(rewrite length_le4; lia)) as E.
    rewrite Z.add_0_r in E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
  step. step.
  rewrite ?sext_extract_le4.
  if_false_by (sx32_nonneg_lts w Hw). step.
  apply evt_done. eexists _. reflexivity.
Qed.
