(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1080 of its 1151 lines of code are new or changed and 940 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R16.v; 53 of its 152 lines of code are new or changed and 1052 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R16.v r16_loop_ind :84 and r16_evt :150 at
     a working branch 3803efccea0 (blob da7cc694ffa98415861e364afadf9f900c638e5c);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r16_evt_of_F (evtF_evt + rng_all) re-derives the source statement of r16_evt, and
     r16_evt_src_check : r16_evt_stmt := R16.r16_evt checks by conversion that r16_evt_stmt IS that statement.
     r16_loop_ind_F re-runs R16.v:88-140 under an evtF EXIT hypothesis; the source r16_loop_ind cannot be
     re-derived from it (its EXIT is an evt, which no evtF follows from), so it has no `_of_F`. *)
(* rule 24: no function proved. *)
(* The run 0x8194c .. 0x81a9c stops AT the free entry 0x534b4 with ra = 0x81aa0, so it is already the `_pre`
   stretch of its call: no `_F` steps through the callee and the source run has no stretch after it.
   Memory touched by the loop, per iteration i (R16.v:8-15): the shadow byte of q + i at
   off + (q + i) / 8 (0x81960 lb, the instrumented check) and the block byte at q + i (0x81968 lbu).  Over the
   whole loop that is the 32 bytes [q, q + 32) and their shadow bytes
   [off + q / 8, off + (q + 31) / 8]; the buffer is not 8-aligned in general, so the shadow length is
   (q + 31) / 8 - q / 8 + 1 (the unaligned form).  Nothing is stored, and the instructions after the loop
   (0x81a8c zext.b, 0x81a90 beqz, 0x81a98 mv, 0x81a9c jal) touch no memory. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R16.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

(* ---- the footprint twin of the loop 0x8194c .. 0x8197c ---- *)

Section LoopF.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hq : 0 < q.
  Hypothesis Hq32 : q + 32 <= 2 ^ 64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.
  Hypothesis Gdat : rng RNG q 32.
  Hypothesis Gsh : rng RNG (off + q / 8) ((q + 31) / 8 - q / 8 + 1).

  Abbreviation ST pc x10 x11 x12 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 (- q)) x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x15 x16,
    evtF rsegs RNG Q (ST 0x81980 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                         (Z_to_bv 64 0) x15 x16).

  Lemma r16_loop_ind_F : forall n i x15 x16, (i + n = 32)%nat -> (0 < n)%nat ->
    evtF rsegs RNG Q (ST 0x8194c (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                         (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x15 x16).
  Proof using Hq Hq32 Hlen HB HSR HAD Gdat Gsh EXIT.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evtF rsegs RNG Q (ST 0x81968 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                           (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m q xs i HB ltac:(lia)) as RD.
      pose proof (psum_range xs i) as PR.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0_signed (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        replace (q + Z.of_nat 31 + 1) with (q + 32) by lia.
        replace (32 - Z.of_nat 31 + -1) with 0 by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    (* 0x8194c / 0x81950: the trap test is not taken *)
    step. step.
    lazymatch goal with
    | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 32)] =>
        rewrite (R16.r16_eqb32 x) by (apply (R16.r16_room_ne x q (Z.of_nat i)); lia)
    end.
    cbn [negb]. cbv iota.
    (* 0x81958 .. 0x81964: the shadow check of a0 = q + i *)
    destruct (asan_shadow_read rsegs m off q 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (q + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((q + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (q + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((q + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End LoopF.

(* ---- the footprint twin of the run 0x8194c .. 0x81a9c ---- *)

Lemma r16_evt_F : forall (RNG : footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (- q) -> a4 = Z_to_bv 64 (32 - Z.of_nat i) -> s11 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat -> 0 < q ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 -> psum xs 32 mod 256 = 0 ->
    rng RNG q 32 -> rng RNG (ASAN_K + q / 8) ((q + 31) / 8 - q / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = MS R F pc' fc None m' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x534b4 /\ m' = m /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8194c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> -> -> Hi Hq Hlen HB AD HS Gdat Gsh.
  destruct (rt_addressable_bound m q 32 AD) as (_ & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  refine (r16_loop_ind_F ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m q ASAN_K xs []
            _ RNG Hq ltac:(lia) Hlen HB HSR HAD Gdat Gsh _ (32 - i)%nat i a5 a6 ltac:(lia) ltac:(lia)).
  intros x15 x16.
  step. step.
  rewrite (unsigned_lit (psum xs 32)) by lia. rewrite (R16.r16_land255 (psum xs 32) HS).
  step. try if_true.
  step. step.
  rewrite ?R16.r16_mv.
  apply evtF_done. do 3 eexists. split; [reflexivity|].
  split; [first [reflexivity | vm_compute; reflexivity]|].
  split; [reflexivity|].
  split; [first [reflexivity | vm_compute; reflexivity]|].
  repeat split.
Qed.

(* ---- compare: the source statement of r16_evt, re-derived from r16_evt_F ---- *)

Definition r16_evt_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (- q) -> a4 = Z_to_bv 64 (32 - Z.of_nat i) -> s11 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat -> 0 < q ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 -> psum xs 32 mod 256 = 0 ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m' : word -> option byte),
         ms' = MS R F pc' fc None m' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x534b4 /\ m' = m /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8194c) fc None m (seg_rom rsegs)).

Lemma r16_evt_of_F : r16_evt_stmt.
Proof.
  unfold r16_evt_stmt. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m q xs i E0 E1 E2 E3 E4 E11 E10 Hi Hq Hlen HB AD HS.
  destruct (rt_addressable_bound m q 32 AD) as (_ & _ & Hq32).
  apply (evtF_evt rsegs RNG_all).
  apply (r16_evt_F RNG_all) with (q := q) (xs := xs) (i := i); try assumption.
  - apply rng_all; lia.
  - apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* The source lemma R16.r16_evt has exactly the statement r16_evt_stmt (checked by conversion). *)
Definition r16_evt_src_check : r16_evt_stmt := R16.r16_evt.
