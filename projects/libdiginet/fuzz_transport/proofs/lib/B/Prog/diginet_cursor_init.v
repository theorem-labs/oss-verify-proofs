(* Modified by Theorem Labs, 2026-10: diginet_cursor_init_contract in libdiginet/fuzz_frame's image A (fuzz_frame.asan) from the footprint walk diginet_cursor_init_holds_F at the footprint that admits every access, as proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v:113-130 does. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A proof lib/A/Prog/diginet_cursor_init.v for fuzz_frame.asan-ubsan: Img0 / AsanCells / AsanKA / the statements and the footprint walk are lib/B's, and the intro names one premise more, image B's UBSan premise c mod 8 = 0, passed on to the walk. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_cursor_init_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_cursor_init_F_c diginet_cursor_init_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_cursor_init_holds : diginet_cursor_init_contract.
Proof.
  unfold diginet_cursor_init_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c body len lo E0 E1 E2 Rc Hc0 Rb Rl AL8 ST HLO WR OFFC APS1 APS2 CELLS OFFG OFFK ADR.
  pose proof (u64_range sp) as Rsp.
  pose proof ST as (L0 & _).
  pose proof ADR as (P0 & N0 & PE & _).
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof diginet_cursor_init_holds_F as H. unfold diginet_cursor_init_contract_F in H.
  apply H; try assumption.
  - apply rng_all; unfold DIGINET_CURSOR_INIT_FRAME in *; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - apply rng_all; unfold APPMEM_END in PE; lia.
  - unfold shadow_addr, ASAN_K, APPMEM_END in *. apply rng_all; Z.div_mod_to_equations; lia.
Qed.
