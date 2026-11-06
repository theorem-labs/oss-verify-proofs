(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1080 of its 1151 lines of code are new or changed and 940 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R16.v, with its module paths and addresses changed; 500 of its 611 lines of code are new or changed and 1040 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/B3Loop.v blob 1cf0cf2a2fce at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives B3Loop.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of B3Loop.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of B3Loop.v's eight run lemmas: the two 32-byte sum loops of the round trip
   (heads 0x81768 / 0x817ec), their low-byte tests (0x81824 / 0x81910) and the two whole runs.
   Each run is re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the
   same post-state predicate and the same script; instruction fetch is not an access.

   THE INDUCTIONS. b3_loop1_ind / b3_loop2_ind walk the 32 turns by induction on the remaining count n. Their
   footprint is fixed ONCE, before the induction, over the loop's WHOLE buffer, not per turn: the section
   hypotheses RB and RS below are two rng premises on
     - the 32 data bytes [q, q + 32)  (the buffer the lemma's own premises name: bytes_at rsegs m q xs,
       asan_addressable rsegs m off q 32);
     - the shadow bytes of that buffer, [q / 8 + off, (q + 31) / 8 + off]  (the range the lemma's own premise
       asan_shadow_rd rsegs m off q 32 W names, in the (lo / 8 + off) form of the recipe).
   Turn i reads one data byte at q + i and one shadow byte at (q + i) / 8 + off; both are inside those two regions
   (ExecF.rng_sub and b3F_sh_rng), so no premise moves with i and the induction hypothesis is the unchanged one.
   b3_tail1_F / b3_tail2_F make no access at all (j ; zext.b ; beqz), so they take no rng premise.

   THE PINS. For the six lemmas whose premises are all first-order, <r>_of_F states B3Loop.<r>'s text term for term
   and <r>_of_F_verbatim checks that with constr_eq. b3_loop1_ind / b3_loop2_ind carry a RUN premise (EXIT, the
   continuation at the loop exit); in the twin that premise is the ExecF.evtF form of the same run, exactly as a
   callee contract premise becomes its _F form (spec "Form", last bullet; Seg/F30F.v's f30_evt_call_of_F). The old
   engine gives no ExecF.evtF at RNG_all, so these two corollaries keep the _F premise. Each is pinned twice
   instead: b3_loop<N>_ind_T is this file's transcription of B3Loop.b3_loop<N>_ind's statement and is checked
   against it with constr_eq; b3_loop<N>_ind_T_F is the same text with that ONE premise in evtF-at-RNG_all form and
   is the corollary's statement. The two Definitions differ in that premise only. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Loop.
(* Last: StepF's step / if_false / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The shadow byte of a data byte y of the block [q, q + 31] lies in the block's shadow range. *)
Lemma b3F_sh_rng : forall (RNG : ExecF.footprint) q off y, 0 <= q -> q <= y -> y <= q + 31 ->
  ExecF.rng RNG (q / 8 + off) ((q + 31) / 8 - q / 8 + 1) ->
  ExecF.rng RNG (y / 8 + off) 1.
Proof.
  intros RNG q off y Hq Hqy Hy H.
  pose proof (Z.div_le_mono q y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y (q + 31) 8 ltac:(lia) ltac:(lia)).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* ---- Loop 1: head 0x81768, body 0x81778, check arm 0x81794, exit 0x81790 ---- *)

Section Loop1F.
  Variable RNG : ExecF.footprint.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hq : 0 <= q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.

  Abbreviation ST1 pc x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x14 x15,
    ExecF.evtF rsegs RNG Q (ST1 0x81790 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                               (Z_to_bv 64 0) x14 x15).

  (* The whole buffer and its whole shadow range, fixed before the induction. *)
  Hypothesis RB : ExecF.rng RNG q 32.
  Hypothesis RS : ExecF.rng RNG (q / 8 + off) ((q + 31) / 8 - q / 8 + 1).

  Lemma b3_loop1_ind_F : forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
    ExecF.evtF rsegs RNG Q (ST1 0x81768 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                               (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15).
  Proof using Hq Hq32 Hlen HB HSR HAD EXIT RB RS.
    induction n as [|n IH]; intros i x14 x15 Hin Hn; [lia|].
    (* turn i's two accesses, both inside the regions fixed above *)
    pose proof (ExecF.rng_sub RNG q 32 (q + Z.of_nat i) 1 RB ltac:(lia) ltac:(lia)) as RDi.
    pose proof (b3F_sh_rng RNG q off (q + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia) RS) as RKi.
    assert (BODY : forall y14 y15,
      ExecF.evtF rsegs RNG Q (ST1 0x81778 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y14 y15)).
    { intros y14 y15.
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
End Loop1F.

(* ---- Loop 2: head 0x817ec, body 0x817fc, check arm 0x81818, exit 0x81814 ---- *)

Section Loop2F.
  Variable RNG : ExecF.footprint.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hq : 0 <= q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length xs = 32%nat.
  Hypothesis HB : bytes_at rsegs m q xs.
  Hypothesis HSR : asan_shadow_rd rsegs m off q 32 W.
  Hypothesis HAD : asan_addressable rsegs m off q 32.

  Abbreviation ST2 pc x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x14 x15,
    ExecF.evtF rsegs RNG Q (ST2 0x81814 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32)) (Z_to_bv 64 (q + 32))
                               (Z_to_bv 64 0) x14 x15).

  Hypothesis RB : ExecF.rng RNG q 32.
  Hypothesis RS : ExecF.rng RNG (q / 8 + off) ((q + 31) / 8 - q / 8 + 1).

  Lemma b3_loop2_ind_F : forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
    ExecF.evtF rsegs RNG Q (ST2 0x817ec (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                               (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15).
  Proof using Hq Hq32 Hlen HB HSR HAD EXIT RB RS.
    induction n as [|n IH]; intros i x14 x15 Hin Hn; [lia|].
    pose proof (ExecF.rng_sub RNG q 32 (q + Z.of_nat i) 1 RB ltac:(lia) ltac:(lia)) as RDi.
    pose proof (b3F_sh_rng RNG q off (q + Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia) RS) as RKi.
    assert (BODY : forall y14 y15,
      ExecF.evtF rsegs RNG Q (ST2 0x817fc (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y14 y15)).
    { intros y14 y15.
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
End Loop2F.

(* ---- The loop lemmas in the segment form: turn i (i < 32) at the head -> the exit pc ---- *)

Lemma b3_loop1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 ->
    ExecF.rng RNG q 32 ->
    ExecF.rng RNG (q / 8 + ASAN_K) ((q + 31) / 8 - q / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> Hi Hlen HB AD RB RS.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  refine (b3_loop1_ind_F RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q
            ASAN_K xs [] _ Hq ltac:(lia) Hlen HB HSR HAD _ RB RS (32 - i)%nat i a4 a5 ltac:(lia) ltac:(lia)).
  intros x14 x15. apply ExecF.evtF_done. cbv beta. exists x14, x15. reflexivity.
Qed.

Lemma b3_loop2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 ->
    ExecF.rng RNG q 32 ->
    ExecF.rng RNG (q / 8 + ASAN_K) ((q + 31) / 8 - q / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i -> -> -> -> -> Hi Hlen HB AD RB RS.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq32).
  pose proof (rt_shadow_rd m q 32 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable m q 32 AD) as HAD.
  refine (b3_loop2_ind_F RNG ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q
            ASAN_K xs [] _ Hq ltac:(lia) Hlen HB HSR HAD _ RB RS (32 - i)%nat i a4 a5 ltac:(lia) ltac:(lia)).
  intros x14 x15. apply ExecF.evtF_done. cbv beta. exists x14, x15. reflexivity.
Qed.

(* ---- The low-byte test after each loop: `j` ; zext.b a0,a1 ; beqz a0 taken when a1 mod 256 = 0.
   No memory access, so no rng premise. ---- *)

(* 0x81790 `j 81824` ; 0x81824 zext.b a0,a1 ; 0x81828 beqz a0,81830 (0x8182c `j 82bf4` not taken). *)
Lemma b3_tail1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> HS H0.
  step. step.
  rewrite (unsigned_lit S) by lia. rewrite (b3_land255 S H0).
  step. try if_true.
  apply ExecF.evtF_done. cbv beta. reflexivity.
Qed.

(* 0x81814 `j 81910` ; 0x81910 zext.b a0,a1 ; 0x81914 beqz a0,8191c (0x81918 `j 82bf4` not taken). *)
Lemma b3_tail2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S -> HS H0.
  step. step.
  rewrite (unsigned_lit S) by lia. rewrite (b3_land255 S H0).
  step. try if_true.
  apply ExecF.evtF_done. cbv beta. reflexivity.
Qed.

(* ---- The whole runs. The buffer is the 32 frame bytes [phi + 18, phi + 50); its shadow range is
   [(phi + 18) / 8 + ASAN_K, (phi + 49) / 8 + ASAN_K]. ---- *)

(* R14's run from the loop head (turn 0: a0 = a2 = Phi_r + 18, a1 = 0, a3 = 32) to 0x81830 (a0 = 0). *)
Lemma b3_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS RB RS.
  assert (RS' : ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 18 + 31) / 8 - (phi + 18) / 8 + 1))
    by (replace (phi + 18 + 31) with (phi + 49) by lia; exact RS).
  destruct (b3_blk_at m phi _ HF HL) as (HB & Hlen).
  rewrite <- (b3_rt_g inp b) in HB, Hlen.
  pose proof (psum_range (skipn 18 (SlotModel.rt_g inp b)) 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply ExecF.evtF_cut.
  { apply (b3_loop1_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (phi + 18) (skipn 18 (SlotModel.rt_g inp b)) 0%nat);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | lia
      | exact Hlen | exact HB | exact AD | exact RB | exact RS' ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply ExecF.evtF_cut.
  { apply (b3_tail1_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50))
             (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32)) (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0)
             a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (psum (skipn 18 (SlotModel.rt_g inp b)) 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply ExecF.evtF_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* R16's run from the loop head (turn 0) to 0x8191c (a0 = 0). *)
Lemma b3_run2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS RB RS.
  assert (RS' : ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 18 + 31) / 8 - (phi + 18) / 8 + 1))
    by (replace (phi + 18 + 31) with (phi + 49) by lia; exact RS).
  destruct (b3_blk_at m phi _ HF HL) as (HB & Hlen).
  rewrite <- (b3_rt_g inp b) in HB, Hlen.
  pose proof (psum_range (skipn 18 (SlotModel.rt_g inp b)) 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply ExecF.evtF_cut.
  { apply (b3_loop2_F RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (phi + 18) (skipn 18 (SlotModel.rt_g inp b)) 0%nat);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | lia
      | exact Hlen | exact HB | exact AD | exact RB | exact RS' ]. }
  intros ms' (a4' & a5' & ->).
  replace (phi + 18 + 32) with (phi + 50) by lia.
  eapply ExecF.evtF_cut.
  { apply (b3_tail2_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 50))
             (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32)) (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0)
             a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (psum (skipn 18 (SlotModel.rt_g inp b)) 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply ExecF.evtF_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* ==== The corollaries: B3Loop's statements re-derived at ExecF.RNG_all ==== *)

(* Every rng premise of this file at RNG_all: the buffer is addressable, so 0 <= p and p + n <= APPMEM_END, and
   the shadow range is p / 8 + ASAN_K .. with ASAN_K = 0x7fff8000. *)
Ltac b3F_rng_all := apply ExecF.rng_all; unfold ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.

Lemma b3_loop1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i E0 E1 E2 E3 E10 Hi Hlen HB AD.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (b3_loop1_F ExecF.RNG_all); try eassumption; b3F_rng_all.
Qed.

Lemma b3_loop2_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (q + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) -> a2 = Z_to_bv 64 (q + Z.of_nat i) ->
    a3 = Z_to_bv 64 (32 - Z.of_nat i) -> s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m q xs -> addressable m q 32 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q xs i E0 E1 E2 E3 E10 Hi Hlen HB AD.
  destruct (rt_addressable_bound m q 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (b3_loop2_F ExecF.RNG_all); try eassumption; b3F_rng_all.
Qed.

Lemma b3_tail1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S E1 HS H0.
  eapply ExecF.evtF_evt, (b3_tail1_F ExecF.RNG_all); eassumption.
Qed.

Lemma b3_tail2_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z),
    a1 = Z_to_bv 64 S -> 0 <= S < 2 ^ 64 -> S mod 256 = 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S E1 HS H0.
  eapply ExecF.evtF_evt, (b3_tail2_F ExecF.RNG_all); eassumption.
Qed.

Lemma b3_run1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81830) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS.
  destruct (rt_addressable_bound m (phi + 18) 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (b3_run1_F ExecF.RNG_all); try eassumption; b3F_rng_all.
Qed.

Lemma b3_run2_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (inp : list byte) (b : Z),
    a0 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (phi + 18) -> a3 = Z_to_bv 64 32 ->
    s10 = Z_to_bv 64 ASAN_K ->
    bytes_at rsegs m phi (SlotModel.rt_F inp b) -> (50 <= length (SlotModel.rt_F inp b))%nat ->
    addressable m (phi + 18) 32 ->
    blocksum (skipn 18 (SlotModel.rt_g inp b)) = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0)
                       (Z_to_bv 64 (psum (skipn 18 (SlotModel.rt_g inp b)) 32))
                       (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi inp b E0 E1 E2 E3 E10 HF HL AD HS.
  destruct (rt_addressable_bound m (phi + 18) 32 AD) as (Hq & _ & Hq47).
  eapply ExecF.evtF_evt, (b3_run2_F ExecF.RNG_all); try eassumption; b3F_rng_all.
Qed.

(* ---- The two inductions. Their shadow region is (q / 8 + off) with `off` a BINDER that B3Loop's statement does
   not bound, so ExecF.rng_all cannot discharge that one rng premise at RNG_all. By the lead's rule (22:4xZ, plus
   the auditor's conditions) these two get `<r>_of_F_bounded` instead of `<r>_of_F`: the source statement with
   exactly the two missing bounds of that one region, `0 <= lo` and `lo + len <= 2^64`, inserted right after the
   source premises, and NO verbatim pin. The EXIT premise is the source run premise in its ExecF.evtF form at
   ExecF.RNG_all (spec "Form", callee-premise bullet).
   b3_loop<N>_ind_T is this file's transcription of B3Loop.b3_loop<N>_ind's statement (the section Abbreviation
   ST<N> written out); b3_loop<N>_ind_T_verbatim pins it to B3Loop's text with constr_eq, so the shape check
   b3_loop<N>_ind_of_F_bounded_shape : b3_loop<N>_ind_T -> b3_loop<N>_ind_T_Fb is a compiled proof that the
   bounded corollary is the source statement plus premises only. ---- *)

Definition b3_loop1_ind_T : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
         (Q : machine_state -> Prop),
    0 <= q -> q + 32 <= 2^64 -> length xs = 32%nat -> bytes_at rsegs m q xs ->
    asan_shadow_rd rsegs m off q 32 W -> asan_addressable rsegs m off q 32 ->
    (forall x14 x15,
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                  (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) x14 x15 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs))) ->
    forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
      evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).

Definition b3_loop1_ind_T_Fb : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
         (Q : machine_state -> Prop),
    0 <= q -> q + 32 <= 2^64 -> length xs = 32%nat -> bytes_at rsegs m q xs ->
    asan_shadow_rd rsegs m off q 32 W -> asan_addressable rsegs m off q 32 ->
    (forall x14 x15,
       ExecF.evtF rsegs ExecF.RNG_all Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                  (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) x14 x15 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81790) fc None m (seg_rom rsegs))) ->
    0 <= q / 8 + off -> q / 8 + off + ((q + 31) / 8 - q / 8 + 1) <= 2^64 ->
    forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
      evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x81768) fc None m (seg_rom rsegs)).

Lemma b3_loop1_ind_of_F_bounded : b3_loop1_ind_T_Fb.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
    Hq Hq32 Hlen HB HSR HAD EXIT Hsh0 Hsh1 n i x14 x15 Hin Hn.
  eapply ExecF.evtF_evt.
  refine (b3_loop1_ind_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
            F fc m q off xs W Q Hq Hq32 Hlen HB HSR HAD EXIT _ _ n i x14 x15 Hin Hn).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* The bounded corollary is the source statement plus premises only. *)
Lemma b3_loop1_ind_of_F_bounded_shape : b3_loop1_ind_T -> b3_loop1_ind_T_Fb.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
    Hq Hq32 Hlen HB HSR HAD EXIT Hsh0 Hsh1 n i x14 x15 Hin Hn.
  apply (H ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
           Hq Hq32 Hlen HB HSR HAD
           (fun y14 y15 => ExecF.evtF_evt rsegs ExecF.RNG_all Q _ (EXIT y14 y15)) n i x14 x15 Hin Hn).
Qed.

Definition b3_loop2_ind_T : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
         (Q : machine_state -> Prop),
    0 <= q -> q + 32 <= 2^64 -> length xs = 32%nat -> bytes_at rsegs m q xs ->
    asan_shadow_rd rsegs m off q 32 W -> asan_addressable rsegs m off q 32 ->
    (forall x14 x15,
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                  (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) x14 x15 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs))) ->
    forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
      evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).

Definition b3_loop2_ind_T_Fb : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q off : Z) (xs : list byte) (W : list ivl)
         (Q : machine_state -> Prop),
    0 <= q -> q + 32 <= 2^64 -> length xs = 32%nat -> bytes_at rsegs m q xs ->
    asan_shadow_rd rsegs m off q 32 W -> asan_addressable rsegs m off q 32 ->
    (forall x14 x15,
       ExecF.evtF rsegs ExecF.RNG_all Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + 32)) (Z_to_bv 64 (psum xs 32))
                  (Z_to_bv 64 (q + 32)) (Z_to_bv 64 0) x14 x15 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81814) fc None m (seg_rom rsegs))) ->
    0 <= q / 8 + off -> q / 8 + off + ((q + 31) / 8 - q / 8 + 1) <= 2^64 ->
    forall n i x14 x15, (i + n = 32)%nat -> (0 < n)%nat ->
      evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (psum xs i))
                 (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x14 x15 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).

Lemma b3_loop2_ind_of_F_bounded : b3_loop2_ind_T_Fb.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
    Hq Hq32 Hlen HB HSR HAD EXIT Hsh0 Hsh1 n i x14 x15 Hin Hn.
  eapply ExecF.evtF_evt.
  refine (b3_loop2_ind_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
            F fc m q off xs W Q Hq Hq32 Hlen HB HSR HAD EXIT _ _ n i x14 x15 Hin Hn).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

Lemma b3_loop2_ind_of_F_bounded_shape : b3_loop2_ind_T -> b3_loop2_ind_T_Fb.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
    Hq Hq32 Hlen HB HSR HAD EXIT Hsh0 Hsh1 n i x14 x15 Hin Hn.
  apply (H ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m q off xs W Q
           Hq Hq32 Hlen HB HSR HAD
           (fun y14 y15 => ExecF.evtF_evt rsegs ExecF.RNG_all Q _ (EXIT y14 y15)) n i x14 x15 Hin Hn).
Qed.

(* ==== The pins (constr_eq: syntactic, not up to conversion) ==== *)

Example b3_loop1_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_loop1 in let b := type of b3_loop1_of_F in constr_eq a b.
  exact I.
Qed.

Example b3_loop2_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_loop2 in let b := type of b3_loop2_of_F in constr_eq a b.
  exact I.
Qed.

Example b3_tail1_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_tail1 in let b := type of b3_tail1_of_F in constr_eq a b.
  exact I.
Qed.

Example b3_tail2_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_tail2 in let b := type of b3_tail2_of_F in constr_eq a b.
  exact I.
Qed.

Example b3_run1_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_run1 in let b := type of b3_run1_of_F in constr_eq a b.
  exact I.
Qed.

Example b3_run2_of_F_verbatim : True.
Proof.
  let a := type of B3Loop.b3_run2 in let b := type of b3_run2_of_F in constr_eq a b.
  exact I.
Qed.

(* Not a pin of an _of_F (the two inductions have none): the check that the transcription b3_loop<N>_ind_T used by
   the shape lemmas IS B3Loop.b3_loop<N>_ind's statement. *)
Example b3_loop1_ind_T_verbatim : True.
Proof.
  let a := type of B3Loop.b3_loop1_ind in
  let b := eval cbv delta [b3_loop1_ind_T] in b3_loop1_ind_T in
  constr_eq a b.
  exact I.
Qed.

Example b3_loop2_ind_T_verbatim : True.
Proof.
  let a := type of B3Loop.b3_loop2_ind in
  let b := eval cbv delta [b3_loop2_ind_T] in b3_loop2_ind_T in
  constr_eq a b.
  exact I.
Qed.
