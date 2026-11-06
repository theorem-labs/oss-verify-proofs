From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA rd32_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import rd32_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import rd32_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* rd32_contract (rd32_c.v; image B, entry 0x8258c) from the footprint proof rd32_holds_F (rd32_F.v): take the
   footprint RNG_all, which holds every access; each rng premise of rd32_contract_F then needs only a range inside
   [0, 2^64), which the frame bound, the cell addresses and addressable m p 4 give.
   Template: this unit's lib/B/Prog/diginet_mac_is_digidesign.v. *)
Theorem rd32_holds : rd32_contract.
Proof.
  unfold rd32_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p l lo
    HLEN BA ST HLO DP APS1 APS2 CELLS DG DC AM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof AM as (P0 & N0 & PE & _).
  apply (ExecF.evtF_evt rsegs RNG_all).
  apply (rd32_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
    t5 t6 F fc m p l lo HLEN BA ST HLO DP APS1 APS2 CELLS DG DC AM);
    apply rng_all; unfold RD32_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.
