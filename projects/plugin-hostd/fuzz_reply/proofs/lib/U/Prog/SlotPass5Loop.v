From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRep HarnessRep SlotPass5Run
  check_no_loss_read_c check_no_loss_c check_shape_ends_c check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op5_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma op5_sl3 : forall z, 0 <= z < 2 ^ 40 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3) = Z_to_bv 64 (8 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma op5_sl6 : forall z, 0 <= z < 2 ^ 40 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6) = Z_to_bv 64 (64 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Lemma op5_sub56 : forall z, 0 <= z < 2 ^ 40 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (64 * z)) - bv_unsigned (Z_to_bv 64 (8 * z))) = Z_to_bv 64 (56 * z).
Proof. intros z Hz. rewrite !unsigned_lit by lia. f_equal. lia. Qed.

Lemma op5_snez : forall z, 0 < z < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z H. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt 0 z)) by lia. reflexivity.
Qed.

Lemma op5_seqz0 : forall z, 0 < z < 2 ^ 64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge z 1)) by lia. reflexivity.
Qed.

Lemma op5_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma op5_head : forall m K e es, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  bytes_at rsegs m K (concat (map entry_bytes (e :: es))) ->
  bytes_at rsegs m K (le4 (Z_to_bv 64 (re_fd e))) /\ bytes_at rsegs m (K + 56) (concat (map entry_bytes es)).
Proof.
  intros m K e es H1 H2 H. cbn [map concat] in H. apply bytes_at_app in H. destruct H as [HE HR].
  rewrite op5_entry_len in HR by assumption. split; [|exact HR].
  unfold entry_bytes in HE. apply bytes_at_app in HE. exact (proj1 HE).
Qed.

Lemma op5_entry_fd : forall m es G (j : nat) e,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  nth_error es j = Some e -> bytes_at rsegs m G (concat (map entry_bytes es)) ->
  bytes_at rsegs m (G + 56 * Z.of_nat j) (le4 (Z_to_bv 64 (re_fd e))).
Proof.
  intros m es. induction es as [|e0 es IH]; intros G j e HW HN HB; [destruct j; discriminate|].
  apply Forall_cons_iff in HW. destruct HW as [(P1 & P2 & _) HW].
  destruct (op5_head m G e0 es P1 P2 HB) as (BF & BR).
  destruct j as [|j]; cbn [nth_error] in HN.
  - injection HN as <-. replace (G + 56 * Z.of_nat 0) with G by lia. exact BF.
  - replace (G + 56 * Z.of_nat (S j)) with (G + 56 + 56 * Z.of_nat j) by lia. exact (IH (G + 56) j e HW HN BR).
Qed.

Lemma op5_l1_start : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) x10 x11
      x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat 0)) (Z_to_bv 64 4) (Z_to_bv 64 0x318a0) x21 x22 x23
      x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144d4) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x318a0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144c8) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. op5_eq.
Qed.

Definition op5_l1_next (SP : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  ((S i < 4)%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat (S i))) x10 x11 x12 x13 x14
              x15 x16 x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat (S i))) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25
              x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144d4) fc None m ro) \/
  (S i = 4%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (SP + 32)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30 x31) F
              (Z_to_bv 64 0x144f0) fc None m ro).

Lemma op5_l1_ret : forall (SP : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 ->
  evt rsegs (op5_l1_next SP i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27
      x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30
      x31) F (Z_to_bv 64 0x144e4) fc None m ro).
Proof.
  intros SP i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HS0 HS1.
  step. step. step.
  if_cases HE; rewrite op5_eqb in HE by lia.
  - apply Bool.negb_true_iff, Z.eqb_neq in HE.
    apply evt_done. unfold op5_l1_next. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.eqb_eq in HE.
    apply evt_done. unfold op5_l1_next. right. split; [lia|]. op5_eq.
Qed.

Lemma op5_l1_head : forall (SP r : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> 0 <= r < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) ->
  evt rsegs (fun ms =>
      (r <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x144e4) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28
                  x29 x30 x31) F (Z_to_bv 64 CHECK_NO_LOSS_READ) fc None m ro) \/
      (r = 0 /\
       op5_l1_next SP i x1 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26
         x27 x28 x29 x30 x31 F fc m ro ms))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30
      x31) F (Z_to_bv 64 0x144d4) fc None m ro).
Proof.
  intros SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HS0 HS1 Hr RR.
  step. rewrite (op5_sx32 r) by lia.
  step. if_cases H0; rewrite op5_eqb in H0 by lia.
  - apply Z.eqb_eq in H0. subst r.
    eapply evt_mono; [apply op5_l1_ret; lia|].
    intros ms Hms. right. split; [reflexivity|exact Hms].
  - apply Z.eqb_neq in H0.
    step. step. apply evt_done. left. split; [exact H0|]. op5_eq.
Qed.

Lemma op5_l2_start : forall (SP N : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= N < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  evt rsegs (fun ms =>
      (N = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x145bc) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16
                  x17 x18 x19 (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
              (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro) \/
      (0 < N /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0))
                  (Z_to_bv 64 (8 * Z.of_nat 0)) (Z_to_bv 64 (64 * Z.of_nat 0)) x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 (Z.of_nat 0)) (Z_to_bv 64 (56 * Z.of_nat 0)) (Z_to_bv 64 0x318a0)
                  (Z_to_bv 64 (4 - Z.of_nat 0)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14510) fc None
              m ro))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x318a0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144f0) fc None m ro).
Proof.
  intros SP N x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro HN RN.
  step. rewrite (op5_sx32 N) by lia.
  step. rewrite (op5_lts 0 N) by lia. if_cases HC.
  - apply Bool.negb_true_iff, Z.ltb_ge in HC.
    step. step. apply evt_done. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.ltb_lt in HC.
    step. step. step. step. step. step. apply evt_done. right. split; [exact HC|]. op5_eq.
Qed.

Definition op5_l2_next (SP N : Z) (i j : nat) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  ((S i < 4)%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat (S i))) x10 x11 x12 x13 x14
              x15 x16 x17 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (56 * Z.of_nat j)) (Z_to_bv 64 0x318a0)
              (Z_to_bv 64 (4 - Z.of_nat (S i))) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14510) fc
           None m ro) \/
  (S i = 4%nat /\ Z.of_nat (S j) < N /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0))
              (Z_to_bv 64 (8 * Z.of_nat (S j))) (Z_to_bv 64 (64 * Z.of_nat (S j))) x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (Z.of_nat (S j))) (Z_to_bv 64 (56 * Z.of_nat (S j))) (Z_to_bv 64 0x318a0)
              (Z_to_bv 64 (4 - Z.of_nat 0)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14510) fc None
           m ro) \/
  (S i = 4%nat /\ N <= Z.of_nat (S j) /\
   ms = MS (mkR (Z_to_bv 64 0x145bc) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) v x11 x12 x13 x14
              x15 x16 x17 (Z_to_bv 64 (Z.of_nat (S j))) (Z_to_bv 64 4) (Z_to_bv 64 0x318a0) (Z_to_bv 64 10) x22 x23
              x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro).

Lemma op5_l2_adv : forall (SP N : Z) (i j : nat) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= N < 2 ^ 31 -> Z.of_nat j < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 32)) 8 = Some (le8 v) ->
  evt rsegs (op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (56 * Z.of_nat j)) (Z_to_bv 64 0x318a0) (Z_to_bv 64 (4 - Z.of_nat i))
      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14568) fc None m ro).
Proof.
  intros SP N i j v x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HN Hj RN RV.
  step. step. step.
  if_cases HC; rewrite op5_eqb in HC by lia.
  - apply Bool.negb_true_iff, Z.eqb_neq in HC.
    apply evt_done. unfold op5_l2_next. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.eqb_eq in HC.
    step. rewrite (op5_sx32 N) by lia.
    step. step. rewrite op5_lts by lia. if_cases HJN.
    + apply Z.ltb_lt in HJN.
      step. rewrite (op5_sl3 (Z.of_nat j + 1)) by lia.
      step. rewrite (op5_sl6 (Z.of_nat j + 1)) by lia.
      step.
      step. rewrite (op5_sub56 (Z.of_nat j + 1)) by lia.
      step.
      apply evt_done. unfold op5_l2_next. right. left. split; [lia|]. split; [lia|]. op5_eq.
    + apply Z.ltb_ge in HJN.
      step. step. step. step. step.
      apply evt_done. unfold op5_l2_next. right. right. split; [lia|]. split; [lia|]. op5_eq.
Qed.

Lemma op5_l2_head : forall (es : list rentry) (tail : list byte) (SP G N fd op : Z) (i j : nat) (e : rentry)
    (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= N < 2 ^ 31 -> 0 <= fd < 2 ^ 31 -> 0 <= op < 2 ^ 31 -> nth_error es j = Some e ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318d0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 32)) 8 = Some (le8 v) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] ->
  G <> 0 -> G mod 8 = 0 ->
  evt rsegs (fun ms =>
      (op <> 0 /\ fd = re_fd e /\
       ms = MS (mkR (Z_to_bv 64 0x14558) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 1) (Z_to_bv 64 0) x14 x15
                  x16 x17 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (56 * Z.of_nat j)) (Z_to_bv 64 0x318a0)
                  (Z_to_bv 64 (4 - Z.of_nat i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
              (Z_to_bv 64 CHECK_NO_LOSS) fc None m ro) \/
      (op = 0 /\
       op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26
         x27 x28 x29 x30 x31 F fc m ro ms) \/
      (op <> 0 /\ fd <> re_fd e /\
       op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (re_fd e)) (Z_to_bv 64 fd) (Z_to_bv 64 1)
         (Z_to_bv 64 0) x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ms))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (56 * Z.of_nat j)) (Z_to_bv 64 0x318a0) (Z_to_bv 64 (4 - Z.of_nat i))
      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14510) fc None m ro).
Proof.
  intros es tail SP G N fd op i j e v x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m ro Hi HN Hfd Hop HE HW RN RG RV TB HS HG0 HG8.
  pose proof (op5_len es HW) as HLn.
  destruct (op5_slot2 m i fd op HS) as [RF RO]. clear HS.
  destruct TB as [[TW HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_wf cell_wf] in TW. destruct TW as [TL _]. rewrite length_app, HLn in TL.
  pose proof HB as (G0 & G1 & _). rewrite length_app, HLn in G1.
  apply bytes_at_app in HB. destruct HB as [HB _].
  assert (Hj : (j < length es)%nat) by (apply nth_error_Some; congruence).
  assert (Re : 0 <= re_fd e < 2 ^ 31).
  { rewrite Forall_forall in HW. destruct (HW e (nth_error_In es j HE)) as (_ & _ & R & _). exact R. }
  assert (G8 : (G + 56 * Z.of_nat j) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (op5_rd4 m _ _ (op5_entry_fd m es G j e HW HE HB)) as RE. clear HB.
  step. rewrite (op5_sx32 op) by lia.
  step. if_cases H0; rewrite op5_eqb in H0 by lia.
  - apply Z.eqb_eq in H0. subst op.
    eapply evt_mono; [apply (op5_l2_adv SP N i j v); first [exact Hi | exact RN | exact RV | lia]|].
    intros ms Hms. right. left. split; [reflexivity|exact Hms].
  - apply Z.eqb_neq in H0.
    step.
    step.
    step. u5_nt.
    step. rewrite (op5_snez G) by lia.
    step. rewrite (op5_seqz0 (G + 56 * Z.of_nat j)) by lia.
    step.
    step. u5_nt.
    step. u5_nt.
    step. rewrite (unsigned_lit (G + 56 * Z.of_nat j)), (op5_land7 (G + 56 * Z.of_nat j) G8) by lia.
    step. u5_nt.
    step. rewrite (op5_sx32 fd) by lia.
    step. rewrite (op5_sx32 (re_fd e)) by lia.
    step. if_cases H1; rewrite op5_eqb in H1 by lia.
    + apply Bool.negb_true_iff, Z.eqb_neq in H1.
      eapply evt_mono; [apply (op5_l2_adv SP N i j v); first [exact Hi | exact RN | exact RV | lia]|].
      intros ms Hms. right. right. split; [exact H0|]. split; [exact H1|exact Hms].
    + apply Bool.negb_false_iff, Z.eqb_eq in H1.
      step. step. step. apply evt_done. left. split; [exact H0|]. split; [exact H1|]. op5_eq.
Qed.

Lemma op5_l2_mid : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14568) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 (Z_to_bv 64 (SP + 40))
      (Z_to_bv 64 (SP + 32)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_SHAPE_ENDS) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14558) fc None m ro).
Proof.
  intros. step. step. step. step. apply evt_done. reflexivity.
Qed.
