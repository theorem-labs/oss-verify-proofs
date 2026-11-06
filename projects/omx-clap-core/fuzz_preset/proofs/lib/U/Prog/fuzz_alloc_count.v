From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_count_c.
Open Scope Z_scope.

Theorem fuzz_alloc_count_holds : fuzz_alloc_count_contract.
Proof.
  unfold fuzz_alloc_count_contract, FUZZ_ALLOC_COUNT, G_COUNT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m count HL.
  assert (RD : ov_read_bytes rsegs m (wa G_COUNT) 8 = Some (le8 count)).
  { replace (wa G_COUNT) with (wa (G_COUNT + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m G_COUNT (le8 count) 0 8 HL ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  unfold G_COUNT in RD.
  step. step. step.
  apply evt_done. reflexivity.
Qed.
