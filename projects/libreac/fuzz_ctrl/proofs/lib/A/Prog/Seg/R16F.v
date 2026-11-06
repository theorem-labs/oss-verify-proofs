(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names and addresses changed; 49 of its 79 lines of code are new or changed and 1472 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R16.v blob 2425e683eaff (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r16_run_of_F re-derives R16.r16_run at ExecF.RNG_all; r16_run_of_F_verbatim checks by constr_eq that its
   type is the type of R16.r16_run. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of R16.v's one run lemma, r16_run (R16.v:28): the second 32-byte sum loop from its head
   0x817ec at turn i, plus the low-byte test, to 0x8191c. Same script over StepF (B3LoopF.b3_loop2_F and
   B3LoopF.b3_tail2_F in place of B3Loop.b3_loop2 / b3_tail2), same post-state predicate.
   Regions (rule (a): the regions the lemma's own premises name): the 32 frame bytes [phi + 18, phi + 50) of its
   `bytes_at rsegs m (phi + 18) xs` / `addressable m (phi + 18) 32` premises, and the shadow bytes of those 32
   bytes, [(phi + 18) / 8 + ASAN_K, (phi + 49) / 8 + ASAN_K], which the instrumented check of each turn reads.
   The loop writes nothing, so there is no store region. R16.v itself is unchanged. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
(* rt_addressable_bound (the bounds of an `addressable` range), used by r16_run_of_F at RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Loop B3LoopF R16.
(* Last: StepF's step / if_false / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The run of R16 from the loop head at index i to 0x8191c, with a0 = 0, under a footprint RNG. *)
Lemma r16_run_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 0) a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS RB RS.
  assert (RS' : ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 18 + 31) / 8 - (phi + 18) / 8 + 1))
    by (replace (phi + 18 + 31) with (phi + 49) by lia; exact RS).
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply ExecF.evtF_cut.
  { apply (b3_loop2_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (phi + 18) xs i);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | exact Hi
      | exact Hlen | exact HB | exact AD | exact RB | exact RS' ]. }
  intros ms' (a4' & a5' & ->).
  eapply ExecF.evtF_cut.
  { apply (b3_tail2_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 (psum xs 32))
             (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (psum xs 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply ExecF.evtF_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* R16.r16_run's statement as a corollary (ExecF.evtF_evt of r16_run_F at RNG_all, each rng premise by
   ExecF.rng_all; the bounds come from the lemma's own `addressable m (phi + 18) 32`). *)
Lemma r16_run_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 0) a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS.
  destruct (rt_addressable_bound m (phi + 18) 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (r16_run_F ExecF.RNG_all); try eassumption;
    apply ExecF.rng_all; try unfold ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

(* The pin: r16_run_of_F's statement is R16.r16_run's, term for term (constr_eq: syntactic, not up to
   conversion). *)
Example r16_run_of_F_verbatim : True.
Proof.
  let a := type of R16.r16_run in let b := type of r16_run_of_F in constr_eq a b.
  exact I.
Qed.
