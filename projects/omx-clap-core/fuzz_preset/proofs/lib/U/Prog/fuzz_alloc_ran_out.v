From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c.
Open Scope Z_scope.

Lemma ran_out_zx8 : forall v : word, bv_unsigned v < 2^8 -> zx8 v = v.
Proof.
  intros v H. unfold zx8. pose proof (bv_unsigned_in_range 64 v) as R.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Theorem fuzz_alloc_ran_out_holds : fuzz_alloc_ran_out_contract.
Proof.
  unfold fuzz_alloc_ran_out_contract, FUZZ_ALLOC_RAN_OUT, G_RAN_OUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ran_out Hlt HR.
  assert (RD : ov_read_bytes rsegs m (wa G_RAN_OUT) 1 = Some (le1 ran_out)).
  { replace (wa G_RAN_OUT) with (wa (G_RAN_OUT + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m G_RAN_OUT (le1 ran_out) 0 1 HR ltac:(lia)) by (rewrite length_le1; lia).
    reflexivity. }
  unfold G_RAN_OUT in RD.
  step. step. step.
  apply evt_done. rewrite (ran_out_zx8 ran_out Hlt). reflexivity.
Qed.
