From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA copy_strz_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import copy_strz_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import copy_strz_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* copy_strz_holds proves copy_strz_contract (copy_strz_c.v; image B, entry 0x82db4) from the footprint proof
   copy_strz_holds_F: take the footprint RNG_all, which holds every access. *)
Theorem copy_strz_holds : copy_strz_contract.
Proof.
  unfold copy_strz_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    s old dst src lo E0 E1 Hsrc Hlen BA RW DIS ST HLO OFFS OFFD APS1 APS2 CELLS OFFG OFFK ADS ADD.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof ADS as (PS0 & NS0 & PES & _).
  pose proof ADD as (PD0 & ND0 & PED & _).
  apply (ExecF.evtF_evt rsegs RNG_all).
  apply (copy_strz_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 t3 t4 t5 t6 F fc m s old dst src lo E0 E1 Hsrc Hlen BA RW DIS ST HLO OFFS OFFD APS1 APS2 CELLS OFFG OFFK
    ADS ADD);
    apply rng_all; unfold COPY_STRZ_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.
