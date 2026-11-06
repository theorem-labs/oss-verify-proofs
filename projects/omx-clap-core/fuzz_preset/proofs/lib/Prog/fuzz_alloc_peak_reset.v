From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_peak_reset_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma wfin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

Theorem fuzz_alloc_peak_reset_holds : fuzz_alloc_peak_reset_contract.
Proof.
  unfold fuzz_alloc_peak_reset_contract, FUZZ_ALLOC_PEAK_RESET, G_LIVE, G_PEAK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m live HL W.
  assert (RD : ov_read_bytes rsegs m (wa G_LIVE) 8 = Some (le8 live)).
  { replace (wa G_LIVE) with (wa (G_LIVE + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m G_LIVE (le8 live) 0 8 HL ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  unfold G_LIVE in RD.
  pose proof W as (Wo & Wn & _).
  assert (HS : store_ok rsegs m (wa (G_PEAK + 0)) 8 = true) by (eapply wr_at_store_ok; [exact W | lia | lia]).
  unfold G_PEAK in HS.
  step. step. step. step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  rewrite ?Z.add_0_r. apply wfin; cbn [length]; rewrite ?length_le8; lia.
Qed.
