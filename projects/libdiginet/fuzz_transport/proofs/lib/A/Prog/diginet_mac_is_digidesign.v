(* Modified by Theorem Labs, 2026-10: proof of diginet_mac_is_digidesign_contract (fuzz_frame.asan, image A) from the footprint proof, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v:137-155 (reac_frame_is_reac_holds_of_F). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_mac_is_digidesign_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_mac_is_digidesign_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The footprint form implies the evt contract: take the footprint RNG_all, which holds every access. *)
Theorem diginet_mac_is_digidesign_holds : diginet_mac_is_digidesign_contract.
Proof.
  unfold diginet_mac_is_digidesign_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mac l lo
    HMAC HLEN BA ST HLO DM APS1 APS2 CELLS DG DC AM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof AM as (P0 & N0 & PE & _).
  apply (ExecF.evtF_evt rsegs RNG_all).
  apply (diginet_mac_is_digidesign_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
    s8 s9 s10 s11 t3 t4 t5 t6 F fc m mac l lo HMAC HLEN BA ST HLO DM APS1 APS2 CELLS DG DC AM);
    apply rng_all; unfold DIGINET_MAC_IS_DIGIDESIGN_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.
