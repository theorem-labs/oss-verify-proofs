From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import fuzz_alloc_live_c.
Open Scope Z_scope.

Theorem fuzz_alloc_live_holds : fuzz_alloc_live_contract.
Proof.
  unfold fuzz_alloc_live_contract, FUZZ_ALLOC_LIVE, G_LIVE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m live HL.
  assert (RD : ov_read_bytes rsegs m (wa 0x2f370) 8 = Some (le8 live)).
  { replace (wa 0x2f370) with (wa (0x2f370 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x2f370 (le8 live) 0 8 HL ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  step. step. step.
  apply evt_done. reflexivity.
Qed.
