(* Modified by Theorem Labs, 2026-10: proof of diginet_frame_is_keepalive_contract (image A) from its footprint form, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v's reac_frame_is_reac_holds_of_F. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of lib/A/Prog/diginet_frame_is_keepalive.v for fuzz_frame.asan-ubsan: module paths lib.B and the premise f mod 8 = 0 taken in and passed on. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_is_keepalive_F_c diginet_frame_is_keepalive_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The footprint form implies the evt contract: take the footprint RNG_all, which allows every access; each range
   the footprint premises name lies in [0, 2^64) by the bounds of the premises. *)
Theorem diginet_frame_is_keepalive_holds : diginet_frame_is_keepalive_contract.
Proof.
  unfold diginet_frame_is_keepalive_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f cmd body lo bb HF0 HF8 HCMD HBD BCMD BFB BBB ST HLO CELLS APW1 APW2 DGOT DCELL D30 A30 C40 C32.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof diginet_frame_is_keepalive_holds_F as H. unfold diginet_frame_is_keepalive_contract_F in H.
  apply H with (body := body); try assumption.
  - apply rng_all; unfold DIGINET_FRAME_IS_KEEPALIVE_FRAME in *; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - destruct A30 as (P & _ & PE & _). apply rng_all; unfold APPMEM_END in PE; lia.
  - destruct A30 as (P & _ & PE & _). unfold shadow_addr, ASAN_K, APPMEM_END in *.
    apply rng_all; Z.div_mod_to_equations; lia.
  - intros HC. destruct (C40 HC) as (_ & P & _ & PE & _). apply rng_all; unfold APPMEM_END in PE; lia.
  - intros HC. destruct (C40 HC) as (_ & P & _ & PE & _). unfold shadow_addr, ASAN_K, APPMEM_END in *.
    apply rng_all; Z.div_mod_to_equations; lia.
  - intros HC HL. destruct (C32 HC HL) as (_ & (P & _ & PE & _) & _). apply rng_all; unfold APPMEM_END in PE; lia.
  - intros HC HL. destruct (C32 HC HL) as (_ & (P & _ & PE & _) & _). unfold shadow_addr, ASAN_K, APPMEM_END in *.
    apply rng_all; Z.div_mod_to_equations; lia.
  - intros HC HL. destruct (C32 HC HL) as (_ & _ & _ & (P & _ & PE & _) & _). apply rng_all; unfold APPMEM_END in PE; lia.
  - intros HC HL. destruct (C32 HC HL) as (_ & _ & _ & (P & _ & PE & _) & _). unfold shadow_addr, ASAN_K, APPMEM_END in *.
    apply rng_all; Z.div_mod_to_equations; lia.
Qed.
