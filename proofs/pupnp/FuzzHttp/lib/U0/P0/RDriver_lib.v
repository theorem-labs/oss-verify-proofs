(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Malloc.
Import ListNotations.
Open Scope Z_scope.

Definition strlen_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' A (str ++ Z_to_bv 8 0 :: slack).
Lemma strlen_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (str slack : list byte),
  bytes_at rsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  evt rsegs (strlen_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x248ac) fc None m (seg_rom rsegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (F_strlen.strlen_spec) with (str := str) (slack := slack); rewrite ?EA; [exact STR | exact NONUL | exact PAD | exact MI]. }
  intros ms' P. unfold F_strlen.strlen_post in P. rewrite EA in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' S src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S N : Z) (src junk : list byte),
  bytes_at rsegs m S src ->
  length src = Z.to_nat N -> 0 <= N -> D + N < 2^64 -> S + N < 2^64 ->
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  (S + N <= D \/ D + N <= S)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240e0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN HN HD HS DST SEP MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B1. pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (F_memcpy.memcpy_spec) with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

Lemma lb_remove_hd : forall p b LB, blk_id b = p -> List.NoDup (map blk_id (b :: LB)) -> lb_remove p (b :: LB) = LB.
Proof. intros p b LB <- ND. apply lb_remove_head. exact ND. Qed.

Lemma lb_remove_second : forall p b0 b LB,
  blk_id b = p -> List.NoDup (map blk_id (b0 :: b :: LB)) -> lb_remove p (b0 :: b :: LB) = b0 :: LB.
Proof.
  intros p b0 b LB <- ND. unfold lb_remove. rewrite filter_cons.
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (decide _) as [Y|N].
  - f_equal. apply (lb_remove_head b LB). exact ND.
  - exfalso. apply N. destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [| exact I].
    apply bptr_eqb_eq in E. apply NI. left. symmetry. exact E.
Qed.
