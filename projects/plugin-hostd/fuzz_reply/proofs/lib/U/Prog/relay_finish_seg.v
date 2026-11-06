(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 578 of its 664 lines of code are new or changed and 1143 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  send_line_c gesture_end_c relay_event_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c
  relay_finish_b_c KindB.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fi_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma fi_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma fi_head : pthread_mutex_lock_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 203040 <= lo ->
  mem_inv rsegs m ->
  rw_cells rsegs m 202912 [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 78092) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2'
                   (Z_to_bv 64 203000) (Z_to_bv 64 202912) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 78092) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -48, bv_unsigned sp); (203004, 203008)] m m' /\ wmono rsegs m m' /\
       mem_inv rsegs m' /\
       rw_cells rsegs m' (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
       rw_cells rsegs m' 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RELAY_FINISH) fc None m (seg_rom rsegs)).
Proof.
  intros SPL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO LOG MI TU GL.
  unfold RELAY_FINISH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct (fi_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (fi_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  cbn [cells_size csize Nat.add Z.of_nat] in GL1, GL2.
  assert (TB : bytes_at rsegs m 203000 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. apply bytes_at_app in B. exact (proj1 B). }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (203004, 203008)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 10 step.
  if_true.
  do 3 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            203000 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  finish.
  - destruct (fi_cut _ _ [_] [_; _; _; _; _] FR) as [_ FR2]. cbn [cells_size csize Z.of_nat] in FR2.
    replace (bv_unsigned sp + -40) with (bv_unsigned sp + -48 + 8) by lia. exact FR2.
  - exact (fi_join _ _ _ [_] [_; _] GL0 (fi_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl).
Qed.

Lemma fi_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fi_chk1 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N C : Z),
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] -> 0 < N <= 4 ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 78108) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 78092) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N C
    NS HN.
  assert (N = 1 \/ N = 2 \/ N = 3 \/ N = 4) as HC by lia.
  destruct HC as [-> | [-> | [-> | ->]]];
    step; rewrite ?fi_sx32 by lia; step; if_false; step; step; apply evt_done; eexists; reflexivity.
Qed.

Lemma fi_chk0 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (C : Z),
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 C)] ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0' a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 78212) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 78092) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m C NS.
  step. rewrite ?fi_sx32 by lia. step.
  if_true.
  apply evt_done. eexists. reflexivity.
Qed.

(* The ubsan checks of the loop body: an unsigned compare or a computed flag, each followed by a branch to the trap. *)
Ltac fi_cmp :=
  repeat match goal with
  | |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] =>
      first
        [ replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  end.

Ltac fi_land :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) with 0
        by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia;
            Z.div_mod_to_equations; lia)
  end.

Ltac fi_if_f :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Lemma fi_b1 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G i buf : Z),
  rw_cells rsegs m 202960 [C8 (Z_to_bv 64 G)] ->
  ov_read_bytes rsegs m (wa (G + 56 * i + 16)) 8 = Some (le8 (Z_to_bv 64 buf)) ->
  0 < G -> G mod 8 = 0 -> G + 896 < 2 ^ 64 -> 0 <= i < 4 -> 0 <= buf < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a1' a2' a3' : word,
       ms' = MS (mkR (Z_to_bv 64 78164) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) (Z_to_bv 64 buf) a1' a2' a3'
                   a4 a5 a6 a7 (Z_to_bv 64 (56 * i)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 89932) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (56 * i)) s3 s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 78108) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G i buf
    GS RD HG0 HGA HG1 HI HB.
  assert (GA : (56 * i + G) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  step. step.
  step. fi_if_f.
  step. fi_cmp. step. fi_cmp. step.
  step. fi_if_f.
  step. fi_if_f.
  step. step. fi_land.
  step. fi_if_f.
  step. fi_if_f.
  step. step.
  apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma fi_b2 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G i : Z),
  rw_cells rsegs m 202960 [C8 (Z_to_bv 64 G)] ->
  0 < G -> G + 896 < 2 ^ 64 -> 0 <= i < 4 ->
  evt rsegs
    (fun ms' => exists a1' a2' : word,
       ms' = MS (mkR (Z_to_bv 64 78196) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) (Z_to_bv 64 (G + 56 * i)) a1' a2'
                   a3 a4 a5 a6 a7 (Z_to_bv 64 (56 * i)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 78336) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (56 * i)) s3 s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 78164) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G i
    GS HG0 HG1 HI.
  step. step.
  step. fi_if_f.
  step. fi_cmp. step. fi_cmp. step. step. fi_if_f.
  step.
  replace (56 * i + G) with (G + 56 * i) by lia.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma fi_tl1 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N C i : Z),
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] -> 0 <= i -> i + 1 < N -> N <= 4 ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0' a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (56 * (i + 1))) (Z_to_bv 64 (i + 1)) s4 s5 s6 s7 s8 s9 s10 s11
                   t3 t4 t5 t6)
                F (Z_to_bv 64 78108) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (56 * i))
             (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 78196) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N C i
    NS HI HN HN4.
  assert ((i = 0 /\ (N = 2 \/ N = 3 \/ N = 4)) \/ (i = 1 /\ (N = 3 \/ N = 4)) \/ (i = 2 /\ N = 4)) as HC by lia.
  destruct HC as [[-> [-> | [-> | ->]]] | [[-> [-> | ->]] | [-> ->]]];
    step; rewrite ?fi_sx32 by lia; step; step; step; if_true; apply evt_done; eexists; reflexivity.
Qed.

Lemma fi_tl0 :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N C i : Z),
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] -> 0 <= i -> i + 1 = N -> N <= 4 ->
  evt rsegs
    (fun ms' => exists a0' s2' s3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0' a1 a2 a3 a4 a5 a6 a7
                   s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 78212) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 202912) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (56 * i))
             (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 78196) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N C i
    NS HI HN HN4.
  assert ((i = 0 /\ N = 1) \/ (i = 1 /\ N = 2) \/ (i = 2 /\ N = 3) \/ (i = 3 /\ N = 4)) as HC by lia.
  destruct HC as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]];
    step; rewrite ?fi_sx32 by lia; step; step; step; if_false; apply evt_done; do 3 eexists; reflexivity.
Qed.

Lemma fi_exit : pthread_mutex_unlock_contract ->
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (sp0 v0 v1 v2 v3 ra0 : word)
         (N C lst cl : Z),
  stk rsegs m lo (bv_unsigned sp0) -> lo + 96 <= bv_unsigned sp0 -> 203040 <= lo ->
  mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp0 + -40) [C8 v3; C8 v2; C8 v1; C8 v0; C8 ra0] ->
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] ->
  rw_cells rsegs m 136736 [C4 (Z_to_bv 64 lst); C4 (Z_to_bv 64 cl)] ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' v0 v1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                   v2 v3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned sp0 - 96, bv_unsigned sp0); (202936, 202940); (136736, 136744); (203004, 203008)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp0) /\
       rw_cells rsegs m' 202936 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 C)] /\
       rw_cells rsegs m' 136736 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
       rw_cells rsegs m' 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -48)) gp tp t0 t1 t2 (Z_to_bv 64 203000) (Z_to_bv 64 202912) a0 a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 78212) fc None m (seg_rom rsegs)).
Proof.
  intros SPU ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    sp0 v0 v1 v2 v3 ra0 N C lst cl ST LO LOG MI FR NS LS LK.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp0 - 96, bv_unsigned sp0); (202936, 202940); (136736, 136744);
    (203004, 203008)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 14 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -48 + 48)) with sp0
    by (replace (bv_unsigned sp0 + -48 + 48) with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 203000 lo)
    | post_call rsegs mm ]
  end.
  1: reflexivity.
  1: eassumption.
  1: eassumption.
  1: lia.
  1: lia.
  1: assumption.
  finish.
Qed.

Lemma fi_rsegs_rw : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fi_wr_rd : forall m a, YP09.writable_at rsegs m a -> exists b, YP09.mbyte rsegs m a = Some b.
Proof.
  intros m a W. revert W. unfold YP09.writable_at, wview, YP09.mbyte.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Fs;
    [|intros W; exfalso; exact (W eq_refl)].
  destruct (seg_writable seg) eqn:Wr; [|intros W; exfalso; exact (W eq_refl)].
  assert (Rd : seg_readable seg = true).
  { pose proof (proj1 (forallb_forall _ rsegs) fi_rsegs_rw seg (YK1j.find_segment_in _ _ _ _ Fs)) as H.
    cbv beta in H. rewrite Wr in H. exact H. }
  unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Fs. cbv beta iota. rewrite Rd.
  cbv beta iota zeta. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [intros _; exists b; reflexivity|].
  intros W. exfalso. exact (W eq_refl).
Qed.

Lemma fi_bytes_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 b); lia | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma fi_le_rt : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (fi_bytes_nonneg bs) as Nn.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8) as [Hl|Hg].
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. apply Z.mod_pow2_bits_high. lia.
  - replace (Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8) with (bytes_le_to_Z bs); [exact IH|].
    rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite Z.lor_0_l. reflexivity.
Qed.

Lemma fi_c4 : forall m a, 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> YP09.writable_at rsegs m (a + i)) -> exists v, rw_cells rsegs m a [C4 v].
Proof.
  intros m a H0 H1 W.
  destruct (fi_wr_rd m (a + 0) (W 0 ltac:(lia))) as [b0 E0].
  destruct (fi_wr_rd m (a + 1) (W 1 ltac:(lia))) as [b1 E1].
  destruct (fi_wr_rd m (a + 2) (W 2 ltac:(lia))) as [b2 E2].
  destruct (fi_wr_rd m (a + 3) (W 3 ltac:(lia))) as [b3 E3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  assert (L4 : le4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])) = [b0; b1; b2; b3]).
  { unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z_to_le_bytes_mod by lia. exact (fi_le_rt [b0; b1; b2; b3]). }
  split; [split|].
  - cbn. auto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, L4. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; [exact E0 | exact E1 | exact E2 | exact E3 | lia].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i Hi).
Qed.

Lemma fi_rw_tr : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> YP09.mbyte rsegs m' (A + i) = YP09.mbyte rsegs m (A + i) /\
     (YP09.writable_at rsegs m (A + i) -> YP09.writable_at rsegs m' (A + i))) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hn & Hb)] (Wa & Wn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    change (YP09.mbyte rsegs m' (A + Z.of_nat i) = nth_error (cells_bytes cs) i).
    rewrite (proj1 (E (Z.of_nat i) ltac:(lia))). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi. exact (proj2 (E i Hi) (Hw i Hi)).
Qed.

Lemma fi_find_none_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true -> top <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma fi_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fi_ro_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  rewrite (fi_find_none_above rsegs (2 ^ 20) a 1 fi_rsegs_top) by lia. reflexivity.
Qed.

Lemma fi_ro_low : forall A n, forallb (fun i => negb (ro_addr rsegs (wa (A + Z.of_nat i)))) (seq 0 n) = true ->
  forall i, 0 <= i < Z.of_nat n -> ro_addr rsegs (wa (A + i)) = false.
Proof.
  intros A n H i Hi.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat i) ltac:(apply in_seq; lia)) as E.
  cbv beta in E. rewrite Z2Nat.id in E by lia. apply negb_true_iff in E. exact E.
Qed.

Lemma fi_ro_g1 : forall i, 0 <= i < 128 -> ro_addr rsegs (wa (202912 + i)) = false.
Proof. apply (fi_ro_low 202912 128). vm_compute. reflexivity. Qed.

Lemma fi_ro_g2 : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (136736 + i)) = false.
Proof. apply (fi_ro_low 136736 8). vm_compute. reflexivity. Qed.

Lemma fi_norm_eq : forall m a, ro_addr rsegs a = false -> normalize rsegs m a = m a.
Proof. intros m a H. unfold normalize. rewrite H. reflexivity. Qed.

Lemma fi_rw_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs Hro [[Hwf Hb] Hw] Hra.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ Hro Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m Hro) Hw Hra).
Qed.

Lemma fi_stk_norm : forall m lo hi, stk rsegs m lo hi -> 2 ^ 20 <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H0 & H1 & H) Hlo. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [W [b E]].
  assert (R : ro_addr rsegs (wa a) = false) by (apply fi_ro_hi; lia).
  assert (EW : wview rsegs (normalize rsegs m) (wa a) = wview rsegs m (wa a))
    by (unfold wview; rewrite (fi_norm_eq m _ R); reflexivity).
  assert (ER : mrd rsegs (normalize rsegs m) (wa a) = mrd rsegs m (wa a))
    by (unfold mrd; rewrite (fi_norm_eq m _ R); reflexivity).
  rewrite EW, ER. split; [exact W | exists b; exact E].
Qed.

Lemma fi_rw_back : forall m1 m0 A cs, mem_rel rsegs m1 m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m1 A cs.
Proof.
  intros m1 m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m1 m0 A _ HR) Hb)]|].
  exact (wr_at_rel rsegs m1 m0 A _ HR Hw).
Qed.

Lemma fi_back : forall m m0' m1 W, ro_agree rsegs m -> mem_rel rsegs m1 m0' -> ro_same rsegs m m1 ->
  munch W (normalize rsegs m) m0' -> wmono rsegs (normalize rsegs m) m0' ->
  munch W m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1.
Proof.
  intros m m0' m1 W Hro HR Hs MU WM. pose proof (mem_rel_normalize rsegs m Hro) as HR0.
  split; [exact (munch_rel rsegs W m (normalize rsegs m) m1 m0' HR0 HR Hs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR0 HR Hs WM)|].
  exact (ro_agree_same rsegs m m1 Hro Hs).
Qed.

Section Regs.
Context {fx : YK11.FPState}.

Lemma fi_canon : forall regs pc mem rom,
  RegisterBridge.canonical_register_state (YK11.mkst regs pc mem rom) =
  MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof using. reflexivity. Qed.

Lemma fi_eqv_mkst : forall R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms -> F = fp_regs ->
  fc = fp_csr -> exists R', ms = YK11.mkst R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof using.
  intros R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) -> ->.
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

End Regs.

Lemma fi_getr_eqv : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> YK11.getr R r = reg_get M r.
Proof. intros M R r H NZ. unfold YK11.getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Lemma fi_vm_id : forall md, with_vmmaps (m_vmmaps md) md = md.
Proof. intros [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma fi_vm_vm : forall a b md, with_vmmaps a (with_vmmaps b md) = with_vmmaps a md.
Proof. intros a b [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma fi_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & Ep).
  pose proof (YO10.block_in_slot s g am idx fr HW Hu Hi Hfr) as (_ & _ & H). lia.
Qed.

Lemma fi_nodup : forall {X : Type} (l : list X), NoDup l -> List.NoDup l.
Proof.
  intros X l H. induction H as [|x l Hn _ IH]; constructor; [|exact IH].
  intros Hi. apply Hn. clear -Hi. induction l as [|y l IHl]; [destruct Hi|].
  destruct Hi as [->|Hi]; hnf; [constructor 1 | constructor 2; exact (IHl Hi)].
Qed.

Lemma fi_nodup_fst : forall {X Y : Type} (l : list (X * Y)) x a b,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l. induction l as [|[x0 y0] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Hn ND'].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - rewrite Ea in Eb. injection Eb as E. exact E.
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Hb).
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Ha).
  - exact (IH x a b ND' Ha Hb).
Qed.

Section FR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTXO : ctx_owned Bm API.

Lemma fi_low : forall L A mem md a, aa_MR API L A mem md -> owned Bm L A a -> 0 <= a < YM05.alloc_ceiling.
Proof using. intros L A mem md a HM Ho. exact (mr_owned_low Bm _ (aa_laws API) L A mem md a HM Ho). Qed.

Lemma fi_not_owned_img : forall L A mem md a, aa_MR API L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using AX.
  intros L A mem md a HM (Hi & Hs & Hc & _) [Ho|Ho].
  - exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
  - exact (Hs Ho).
Qed.

Lemma fi_owned_img : forall L A mem md L' A' mem' md' a, aa_MR API L A mem md -> aa_MR API L' A' mem' md' ->
  in_img Bm a -> owned Bm L' A' a -> owned Bm L A a.
Proof using AX CTXO.
  intros L A mem md L' A' mem' md' a HM HM' Hi [Ho|Ho].
  - exact (CTXO L A mem md a HM (ax_img AX L' A' mem' md' a HM' Hi Ho)).
  - right. exact Ho.
Qed.

Lemma fi_comp : forall K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 K2 Rc E2 F2 L2 A2 R2 m2 md2,
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m1 md1 ->
  relay_post Bm API K2 E2 F2 L1 A1 Rc m1 md1 L2 A2 R2 m2 md2 ->
  (forall a, spZ R0 - K <= a < spZ R0 -> YM05.alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, scratch_k Bm K2 Rc a -> scratch_k Bm K R0 a) ->
  (forall a, scratch_k Bm K R0 a -> ~ scratch_k Bm K2 Rc a -> ~ E2 a) ->
  (forall p n, 0 < n -> In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L0 p) ->
     ~ F2 (ptr_addr L0 p)) ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> ~ owned Bm L0 A0 a -> ~ scratch_k Bm K R0 a ->
     E2 a -> E a) ->
  (forall p n i, In (p, n) (user_blocks A0) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L0 p) -> 0 <= i < n ->
     E2 (ptr_addr L0 p + i) -> E (ptr_addr L0 p + i)) ->
  relay_post Bm API K E F L0 A0 R0 m0 md0 L2 A2 R0 m2 md2.
Proof using.
  intros K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 K2 Rc E2 F2 L2 A2 R2 m2 md2 P1 P2 SCA SCK SCE CF CE CB.
  destruct P1 as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  destruct P2 as (M2 & W2 & B2 & LL2 & LN2 & AD2 & SV2 & Z2 & OW2 & RP2 & MD2 & FR2 & BY2 & SC2).
  assert (KEEP : forall p n, In (p, n) (user_blocks A0) -> 0 < n -> ~ F (ptr_addr L0 p) ->
            In (p, n) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L0 p).
  { intros p n H0 Hn NF. pose proof (SV1 p n H0 Hn NF) as H1. split; [exact H1 | exact (AD1 p n H0 H1 NF)]. }
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LL1 as (C1 & S1 & K1 & R1'). destruct LL2 as (C2 & S2 & K2' & R2').
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite R2' by lia. apply R1'. exact Hr. }
  split; [lia|].
  split.
  { intros p n H0 H2 NF.
    pose proof (fi_ub_nonneg A2 p n W2 H2) as Hn.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    - destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [_ E2']. congruence.
    - destruct (KEEP p n H0 ltac:(lia) NF) as [H1 E1].
      rewrite (AD2 p n H1 H2 ltac:(rewrite E1; exact (CF p n ltac:(lia) H0 H1 NF))). exact E1. }
  split.
  { intros p n H0 Hn NF. destruct (KEEP p n H0 Hn NF) as [H1 E1].
    apply (SV2 p n H1 Hn). rewrite E1. exact (CF p n Hn H0 H1 NF). }
  split.
  { intros p H0. destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [H2 E2']. split; [exact H2 | congruence]. }
  split.
  { intros a Hi Ho. exact (OW1 a Hi (OW2 a Hi Ho)). }
  split; [intros r Hr; reflexivity|].
  split.
  { destruct MD1 as [v1 ->]. destruct MD2 as [v2 ->]. exists v2. apply fi_vm_vm. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { destruct Ha as [Ha|Ha].
      - intros Ho. pose proof (fi_low L1 A1 m1 md1 a M1 Ho). lia.
      - intros Ho. exact (NO0 (OW1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    destruct (FR2 a Ha NO1 NO2 (fun H => NS (SCK a H)) (fun H => NE (CE a Ha NO0 NS H))) as [E2' W2'].
    split; [congruence | tauto]. }
  split.
  { intros p n i H0 H2 NF Hi NE.
    destruct (KEEP p n H0 ltac:(lia) NF) as [H1 E1].
    pose proof (BY2 p n i H1 H2) as B2'. rewrite E1 in B2'.
    rewrite (B2' (CF p n ltac:(lia) H0 H1 NF) Hi (fun H => NE (CB p n i H0 H1 NF Hi H))).
    exact (BY1 p n i H0 H1 NF Hi NE). }
  intros a Ha.
  assert (D : scratch_k Bm K2 Rc a \/ ~ scratch_k Bm K2 Rc a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (SC2 a D)|].
  pose proof (SC1 a Ha) as Wm.
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  pose proof (SCA a Ha) as Hc.
  assert (N1 : ~ owned Bm L1 A1 a) by (intros Ho; pose proof (fi_low L1 A1 m1 md1 a M1 Ho); lia).
  assert (N2 : ~ owned Bm L2 A2 a) by (intros Ho; pose proof (fi_low L2 A2 m2 md2 a M2 Ho); lia).
  apply (proj2 (FR2 a (or_introl Hc) N1 N2 D (SCE a (or_introl Ha) D))). exact Wm.
Qed.

Lemma fi_outside_dec : forall W a, outside W a \/ ~ outside W a.
Proof using.
  induction W as [|[lo hi] W IH]; intros a; cbn [outside]; [left; exact I|].
  destruct (IH a) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi); [right; lia | left; split; [lia | exact H] ..].
Qed.

Lemma fi_kA : forall K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 m2 W,
  ms_segs Bm = rsegs ->
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m1 md1 ->
  munch W m1 m2 -> wmono (ms_segs Bm) m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> outside W a \/
     (spZ R0 - K <= a < spZ R0 /\ YM05.alloc_ceiling <= a) \/ (img_plain Bm a /\ E a)) ->
  relay_post Bm API K E F L0 A0 R0 m0 md0 L1 A1 R0 m2 md1.
Proof using AX.
  intros K E F L0 A0 R0 m0 md0 L1 A1 m1 md1 m2 W SEGS P1 MU WM HW.
  destruct P1 as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FR1 & BY1 & SC1).
  pose proof (aa_laws API) as LAWS.
  assert (SAME : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
  { intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. }
  assert (BLK : forall p n i, In (p, n) (user_blocks A1) -> 0 <= i < n ->
            0 <= ptr_addr L1 p + i < 2 ^ 64 /\ outside W (ptr_addr L1 p + i)).
  { intros p n i Hp Hi.
    destruct (mr_blocks Bm _ LAWS L1 A1 m1 md1 p n i M1 Hp Hi) as (_ & H4 & Hc & _).
    pose proof (ax_blocks_img AX L1 A1 m1 md1 p n i M1 Hp Hi) as NI.
    pose proof alloc_ceiling_lt as ACL.
    split; [lia|].
    destruct (HW (ptr_addr L1 p + i) ltac:(lia)) as [H|[H|[(H & _) _]]]; [exact H | lia | exfalso; exact (NI H)]. }
  assert (OWN : forall a, owned Bm L1 A1 a -> 0 <= a < 2 ^ 64 /\ outside W a).
  { intros a Ho. pose proof (fi_low L1 A1 m1 md1 a M1 Ho) as LOWa. pose proof alloc_ceiling_lt as ACL.
    split; [lia|].
    destruct (HW a ltac:(lia)) as [H|[H|[H _]]]; [exact H | lia | exfalso; exact (fi_not_owned_img L1 A1 m1 md1 a M1 H Ho)]. }
  destruct (mr_model Bm _ LAWS L1 A1 m1 md1 M1) as (Hh & Hl & Hm).
  assert (M2 : aa_MR API L1 A1 m2 md1).
  { apply (mr_frame Bm _ LAWS L1 A1 m1 m2 md1 md1 M1).
    - intros a Ho. destruct (OWN a Ho) as [Ha Hout]. unfold mbyte. rewrite (SAME a Ha Hout). reflexivity.
    - intros a Ho [b Hb]. destruct (OWN a Ho) as [Ha Hout]. exists b. rewrite (SAME a Ha Hout). exact Hb.
    - intros p n i Hp Hi. destruct (BLK p n i Hp Hi) as [Ha Hout].
      destruct (mr_blocks Bm _ LAWS L1 A1 m1 md1 p n i M1 Hp Hi) as ([b Hb] & _).
      exists b. rewrite (SAME _ Ha Hout). exact Hb.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact M2|]. split; [exact W1|]. split; [exact B1|]. split; [exact LL1|]. split; [exact LN1|].
  split; [exact AD1|]. split; [exact SV1|]. split; [exact Z1|]. split; [exact OW1|]. split; [exact RP1|].
  split; [exact MD1|].
  split.
  { intros a Ha NO0 NO1 NS NE.
    assert (AR : 0 <= a < 2 ^ 64).
    { destruct Ha as [Ha|Ha]; [pose proof YM05.alloc_ceiling_val; lia|].
      pose proof (in_img_low Bm SEGS a Ha). lia. }
    assert (Hout : outside W a).
    { destruct (HW a AR) as [H|[(H & _)|(_ & H)]]; [exact H | exfalso; apply NS; left; exact H | exfalso; exact (NE H)]. }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    split.
    - unfold mbyte. rewrite (SAME a AR Hout). exact E1.
    - unfold writable_at, wview in *. rewrite (SAME a AR Hout). exact W1'. }
  split.
  { intros p n i H0 H1 NF Hi NE.
    rewrite <- (AD1 p n H0 H1 NF). rewrite <- (AD1 p n H0 H1 NF) in NE.
    destruct (BLK p n i H1 Hi) as [Ha Hout].
    unfold mbyte at 1. rewrite (SAME _ Ha Hout). fold (mbyte (ms_segs Bm) m1 (ptr_addr L1 p + i)).
    rewrite (AD1 p n H0 H1 NF). rewrite (AD1 p n H0 H1 NF) in NE. exact (BY1 p n i H0 H1 NF Hi NE). }
  intros a Ha. apply WM. exact (SC1 a Ha).
Qed.

Lemma fi_free_rp : forall L A R m md L' A' R' m' md' p n,
  WF A -> In (p, n) (user_blocks A) -> 0 < n -> aa_MR API L A m md ->
  call_post Bm (aa_MR API) L A R m md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' R' m' md' ->
  (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  relay_post Bm API ALLOC_STACK (fun a => ptr_addr L p <= a < ptr_addr L p + n) (fun q => q = ptr_addr L p)
    L A R m md L' A' R' m' md'.
Proof using AX CTXO.
  intros L A R m md L' A' R' m' md' p n HW Hp Hn HM CP SURV LN.
  destruct CP as (M' & W' & B' & LL & AD & RP & MD & FR & BY & SC).
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact LL|]. split; [exact LN|].
  split; [intros q k H1 H2 _; exact (AD q k H1 H2)|].
  split; [intros q k H1 _ NF; apply SURV; [exact H1|]; intros ->; exact (NF eq_refl)|].
  split.
  { intros q H1.
    assert (Q : q <> p).
    { intros ->. pose proof (fi_nodup_fst _ p 0 n (YO10.user_block_ptrs_NoDup A HW) H1 Hp). lia. }
    pose proof (SURV q 0 H1 Q) as H2. split; [exact H2 | exact (AD q 0 H1 H2)]. }
  split; [intros a Hi Ho; exact (fi_owned_img L A m md L' A' m' md' a HM M' Hi Ho)|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | exact NE]|].
  split; [intros q k i H1 H2 _ Hi _; exact (BY q k i H1 H2 Hi)|].
  exact SC.
Qed.

End FR.
