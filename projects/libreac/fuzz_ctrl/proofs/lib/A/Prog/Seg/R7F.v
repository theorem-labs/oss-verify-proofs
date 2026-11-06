(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 852 of its 1017 lines of code are new or changed and 2392 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7.v, with its module paths and module names changed; 82 of its 148 lines of code are new or changed and 951 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R7.v ff604ad21972 (the blob this tree had at release c5e779efe8c) at 553cd287ffb
   (a Theorem Labs lane's fix of the stale R7, a working branch; auditor a Theorem Labs lane PASSED it 23:19Z).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R7.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R7.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) twins of the two run lemmas of Seg/R7.v (r7_evt :61, r7_latch_evt :224): the same runs, with
   the same post-state predicate, re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified
   footprint RNG. Each run makes exactly one data access, the 8-byte spill load its own ro_cells premise names
   (r7_evt: the reciprocal word [A + 64] at 0x81618; r7_latch_evt: [A + 128] at the latch's ld a0,128(s1)); every
   other instruction is a register move or a branch, and instruction fetch is not an access. The allocator is NOT
   inside either run: r7_evt stops AT the entry of __wrap_malloc (pc 0x5337c after the jal at 0x8163c), so no
   allocator contract and no APIf appears here, exactly as in the source. R7.v itself is unchanged apart from comment text. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
(* The segment file itself (its a_u_cases / a_by_u_f / a_by_u_t and r7_eqb_refl / r7_zxb_nz). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R7.
(* Last: StepF's step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* R7.a_if_false / R7.a_if_true / R7.r7_br / R7.r7_st with the evtF goal shape: the helper names the re-run
   changes, with the same bodies (R7.a_by_u_f / a_by_u_t / r7_eqb_refl / r7_zxb_nz do the work). *)
Ltac r7F_if_false Hu :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; a_by_u_f Hu)
  end; cbv iota.
Ltac r7F_if_true Hu :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by (symmetry; a_by_u_t Hu)
  end; cbv iota.
Ltac r7F_br := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by
                (symmetry; first [apply r7_eqb_refl | apply r7_zxb_nz; assumption | reflexivity]); cbv iota
            | replace c with false by (symmetry; reflexivity); cbv iota ]
  | _ => idtac end.
Ltac r7F_st := step; r7F_br.

(* ---- r7_evt (R7.v:61): 0x815ec .. 0x8163c, the three validity checks of n_b and the jal to __wrap_malloc.
   Its one access is the 8-byte load of the reciprocal spill [A + 64] at 0x81618 (its ro_cells premise). ---- *)
Lemma r7_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n : Z),
    s1 = Z_to_bv 64 A -> s8 = Z_to_bv 64 36 -> a0 = Z_to_bv 64 n ->
    ro_cells rsegs m (A + 64) [C8 (Z_to_bv 64 0xe38f0000)] -> 0 <= A -> A + 72 <= 2 ^ 64 ->
    (exists u, n = 52 + 36 * u /\ 2 <= u <= 40) ->
    ExecF.rng RNG (A + 64) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR (Z_to_bv 64 0x81640) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 n) a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) s3 s4 s5 s6 s7 (Z_to_bv 64 36) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A n -> -> -> RW HA0 HA1 Hu R64.
  (* the spill base does not wrap: solve_accs needs it for the ld at s1 + 64 *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  step. r7F_if_false Hu.               (* 815ec beqz a0,8194c  (n != 0) *)
  step.                                (* 815f0 mv s2,a0 *)
  step.                                (* 815f4 addi a0,a0,-1493 *)
  step.                                (* 815f8 li a1,-1441 *)
  step. r7F_if_true Hu.                (* 815fc bgeu a0,a1,81604 *)
  step.                                (* 81604 addi a0,s2,-52 *)
  step.                                (* 81608 slli a1,a0,0x30 *)
  step.                                (* 8160c srli a2,a1,0x30 *)
  step. r7F_if_true Hu.                (* 81610 bgeu a2,s8,81618 *)
  step.                                (* 81618 ld a2,64(s1) *)
  step.                                (* 8161c mulhu a1,a1,a2 *)
  step.                                (* 81620 srli a1,a1,0x15 *)
  step.                                (* 81624 mul a1,a1,s8 *)
  step.                                (* 81628 sub a0,a0,a1 *)
  step.                                (* 8162c slli a0,a0,0x30 *)
  step. r7F_if_true Hu.                (* 81630 beqz a0,81638  (divisible) *)
  step.                                (* 81638 mv a0,s2 *)
  step.                                (* 8163c jal 0x5337c wrapper_malloc *)
  apply ExecF.evtF_done. do 2 eexists. reflexivity.
Qed.

Lemma r7_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n : Z),
    s1 = Z_to_bv 64 A -> s8 = Z_to_bv 64 36 -> a0 = Z_to_bv 64 n ->
    ro_cells rsegs m (A + 64) [C8 (Z_to_bv 64 0xe38f0000)] -> 0 <= A -> A + 72 <= 2 ^ 64 ->
    (exists u, n = 52 + 36 * u /\ 2 <= u <= 40) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR (Z_to_bv 64 0x81640) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 n) a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) s3 s4 s5 s6 s7 (Z_to_bv 64 36) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A n Es1 Es8 Ea0 RW HA0 HA1 Hu.
  eapply ExecF.evtF_evt,
    (r7_evt_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc m A n); try assumption.
  apply ExecF.rng_all; lia.
Qed.

(* The pin of the first run, in ITS name environment: R7.r7_evt is stated before R7.v's second import block, so
   its seg_rom is Lib.PropExec's. *)
Example r7_evt_of_F_verbatim : True.
Proof.
  let a := type of R7.r7_evt in let b := type of r7_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* R7.v's second import block ("===== the cut and its exits ====="), which precedes r7_latch_evt: from here on
   seg_rom is YK11's, as the printed type of R7.r7_latch_evt shows (YK11.seg_rom A.Img0.rsegs). StepF is required
   again after it, so its step / if_false keep shadowing the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import YK11.
Open Scope Z_scope.

(* ---- r7_latch_evt (R7.v:224): the latch 0x815ec -> 0x8194c -> 0x815cc of turn S b. Its one access is the 8-byte
   load of the spill [A + 128] (its ro_cells premise). ---- *)
Lemma r7_latch_evt_F : forall (RNG : ExecF.footprint) (bz : Z), 0 <= bz <= 5 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A V : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s7 = Z_to_bv 64 bz -> 0 <= A -> A + 416 <= 2 ^ 47 ->
    ro_cells rsegs m (A + 128) [C8 (Z_to_bv 64 V)] ->
    ExecF.rng RNG (A + 128) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 V) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (bz + 1)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG bz Hb.
  assert (E : bz = 0 \/ bz = 1 \/ bz = 2 \/ bz = 3 \/ bz = 4 \/ bz = 5) by lia.
  destruct E as [->|[->|[->|[->|[->| ->]]]]];
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A V -> -> -> HA0 HA1 C128 R128;
  (assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia);
   r7F_st; r7F_st; r7F_st; r7F_st; r7F_st; apply ExecF.evtF_done; do 2 eexists; reflexivity).
Qed.

Lemma r7_latch_evt_of_F : forall (bz : Z), 0 <= bz <= 5 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A V : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s7 = Z_to_bv 64 bz -> 0 <= A -> A + 416 <= 2 ^ 47 ->
    ro_cells rsegs m (A + 128) [C8 (Z_to_bv 64 V)] ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 V) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (bz + 1)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros bz Hb ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A V Es1 Ea0 Es7 HA0 HA1 C128.
  eapply ExecF.evtF_evt,
    (r7_latch_evt_F ExecF.RNG_all bz Hb ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
       s9 s10 s11 t3 t4 t5 t6 F fc m A V); try assumption.
  apply ExecF.rng_all; lia.
Qed.

(* The pins: neither run takes a callee premise, so each corollary states R7's text term for term
   (constr_eq: syntactic, not up to conversion). *)
(* (the latch pin is at the end of the file, in the latch's own name environment) *)

Example r7_latch_evt_of_F_verbatim : True.
Proof.
  let a := type of R7.r7_latch_evt in let b := type of r7_latch_evt_of_F in constr_eq a b.
  exact I.
Qed.
