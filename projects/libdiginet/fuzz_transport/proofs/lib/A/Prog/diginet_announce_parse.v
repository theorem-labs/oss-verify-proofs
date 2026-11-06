(* diginet_announce_parse_holds proves diginet_announce_parse_contract (diginet_announce_parse_c.v), the image-A
   evt contract of fuzz_frame.asan 0x82bbc. The run is the footprint run of diginet_announce_parse_F.v read under
   the footprint RNG_all, which admits every access (ExecF.evtF_evt): each ExecF.rng premise of
   diginet_announce_parse_contract_F is then ExecF.rng_all of a range the evt contract's own premises bound, the
   data ranges by their addressable premise (p + n <= APPMEM_END) and the frame by the stack premises, and the
   shadow ranges by shadow_addr x = x / 8 + ASAN_K of those bounds. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_announce_parse_c
  diginet_announce_parse_F_c diginet_announce_parse_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(* The bounds an addressable premise gives: APPMEM_END is under 2^64, and so is the shadow address of its last
   byte. *)
Lemma rng_all_of_addr : forall m p n, addressable m p n -> ExecF.rng ExecF.RNG_all p n.
Proof.
  intros m p n (H0 & H1 & H2 & _). unfold APPMEM_END in H2. apply ExecF.rng_all; lia.
Qed.

Lemma rng_all_of_shadow : forall m p n, addressable m p n ->
  ExecF.rng ExecF.RNG_all (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1).
Proof.
  intros m p n (H0 & H1 & H2 & _). unfold APPMEM_END in H2. unfold shadow_addr, ASAN_K.
  apply ExecF.rng_all; Z.div_mod_to_equations; lia.
Qed.

Theorem diginet_announce_parse_holds : diginet_announce_parse_contract.
Proof.
  pose proof diginet_announce_parse_holds_F as T. unfold diginet_announce_parse_contract_F in T.
  unfold diginet_announce_parse_contract, DIGINET_ANNOUNCE_PARSE, DIGINET_ANNOUNCE_PARSE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bb aj f ap cmd body lo E0 E1 Hf Hap Hcmd Hbody BC BF BB ST0 SPLO DF30 DB15 HOK APS1 APS2 CELLS0
    DGOT A30 A40 A32 AB AAP.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST0 as [H _]; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (T ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m bb aj f ap cmd body lo);
    try assumption.
  (* the thirteen footprint premises, each a range the evt contract's premises bound *)
  all: try (apply ExecF.rng_all; unfold DIGINET_ANNOUNCE_PARSE_FRAME; lia).
  all: try (apply ExecF.rng_all; lia).
  all: try (apply ExecF.rng_all; unfold GOT_CELL_K; lia).
  all: try (apply ExecF.rng_all; unfold CELL_K; lia).
  all: try exact (rng_all_of_addr m (f + 30) 1 A30).
  all: try exact (rng_all_of_shadow m (f + 30) 1 A30).
  all: try (intros H; exact (rng_all_of_addr m (f + 40) 8 (A40 H))).
  all: try (intros H; exact (rng_all_of_shadow m (f + 40) 8 (A40 H))).
  all: try (intros H; exact (rng_all_of_addr m (f + 32) 8 (A32 H))).
  all: try (intros H; exact (rng_all_of_shadow m (f + 32) 8 (A32 H))).
  all: try (intros H; exact (rng_all_of_addr m (body + 15) 18 (AB H))).
  all: try (intros H; exact (rng_all_of_shadow m (body + 15) 18 (AB H))).
  all: try (intros H; exact (rng_all_of_addr m ap 40 (AAP H))).
  all: try (intros H; exact (rng_all_of_shadow m ap 40 (AAP H))).
Qed.
