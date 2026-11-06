(* Proof of diginet_sum16_contract (diginet_sum16_c.v; fuzz_frame.asan-ubsan, image B, entry 0x81e30) from the
   footprint proof diginet_sum16_holds_F (diginet_sum16_F.v): take the footprint RNG_all, which holds every access. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_sum16_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_sum16_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_sum16_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_sum16_holds : diginet_sum16_contract.
Proof.
  unfold diginet_sum16_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb lo
    HP BA ST HLO DP APS1 APS2 CELLS DG DC AM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (bytes_at_bound rsegs m p bb BA) as BB.
  apply (ExecF.evtF_evt rsegs RNG_all).
  apply (diginet_sum16_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m p bb lo HP BA ST HLO DP APS1 APS2 CELLS DG DC AM);
    try intros _; apply rng_all; unfold DIGINET_SUM16_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *;
    Z.div_mod_to_equations; lia.
Qed.
