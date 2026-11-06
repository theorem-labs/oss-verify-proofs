From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRep ListStep HarnessRep SlotPass2Run
  SlotPass5Run check_no_loss_read_c check_no_loss_c check_shape_ends_c check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op5_bv : forall a b, a = b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b ->. reflexivity. Qed.

Ltac op5_eq := cbv beta; unfold mkR;
  repeat match goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end;
  try (apply op5_bv; unfold G_S in *; lia).

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

Lemma op5_entry_fd : forall m es G (j : nat) e,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  nth_error es j = Some e -> bytes_at rsegs m G (concat (map entry_bytes es)) ->
  bytes_at rsegs m (G + 56 * Z.of_nat j) (le4 (Z_to_bv 64 (re_fd e))).
Proof.
  intros m es. induction es as [|e0 es IH]; intros G j e HW HN HB; [destruct j; discriminate|].
  apply Forall_cons_iff in HW. destruct HW as [(P1 & P2 & _) HW].
  destruct (p2_head m G e0 es P1 P2 HB) as (BF & _ & BR).
  destruct j as [|j]; cbn [nth_error] in HN.
  - injection HN as <-. replace (G + 56 * Z.of_nat 0) with G by lia. exact BF.
  - replace (G + 56 * Z.of_nat (S j)) with (G + 56 + 56 * Z.of_nat j) by lia. exact (IH (G + 56) j e HW HN BR).
Qed.

Lemma op5_slot2 : forall m (i : nat) fd op,
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 fd)) /\
  ov_read_bytes rsegs m (Z_to_bv 64 (G_S + 96 * Z.of_nat i + 4)) 4 = Some (le4 (Z_to_bv 64 op)).
Proof.
  intros m i fd op [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  apply bytes_at_app in H. destruct H as [H1 H2]. rewrite length_le4 in H2. split.
  - apply p2_rd4. exact H1.
  - replace (G_S + 96 * Z.of_nat i + 4) with (G_S + 96 * Z.of_nat i + Z.of_nat 4) by lia. apply p2_rd4. exact H2.
Qed.

Lemma op5_l1_start : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) x10 x11
      x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat 0)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f08) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x30fc0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f00) fc None m ro).
Proof.
  intros. step. step. apply evt_done. op5_eq.
Qed.

Definition op5_l1_next (SP : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  ((S i < 4)%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat (S i))) x10 x11 x12 x13 x14
              x15 x16 x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat (S i))) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) x21
              x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f08) fc None m ro) \/
  (S i = 4%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29
              x30 x31) F (Z_to_bv 64 0x13f24) fc None m ro).

Lemma op5_l1_ret : forall (SP : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 ->
  evt rsegs (op5_l1_next SP i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28
      x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f18) fc None m ro).
Proof.
  intros SP i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HS0 HS1.
  step. step. step.
  if_cases HE; rewrite p2_eqb in HE by lia.
  - apply Bool.negb_true_iff, Z.eqb_neq in HE.
    apply evt_done. unfold op5_l1_next. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.eqb_eq in HE.
    apply evt_done. unfold op5_l1_next. right. split; [lia|]. op5_eq.
Qed.

Lemma op5_l1_head : forall (SP r : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> 0 <= r < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) ->
  evt rsegs (fun ms =>
      (r <> 0 /\
       ms = MS (mkR (Z_to_bv 64 0x13f18) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) x21 x22 x23
                  x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CHECK_NO_LOSS_READ) fc None m ro) \/
      (r = 0 /\
       op5_l1_next SP i x1 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27
         x28 x29 x30 x31 F fc m ro ms))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f08) fc None m ro).
Proof.
  intros SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro Hi HS0 HS1 Hr RR.
  step. rewrite (ls_sx32 r) by lia.
  step. if_cases H0; rewrite p2_eqb in H0 by lia.
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
  ov_read_bytes rsegs m (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  evt rsegs (fun ms =>
      (N = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x14054) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16
                  x17 x18 x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
              (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro) \/
      (0 < N /\
       ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) (Z_to_bv 64 N) x11 x12
                  x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat 0)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27
                  x28 x29 x30 x31) F (Z_to_bv 64 0x13f34) fc None m ro))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x30fc0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f24) fc None m ro).
Proof.
  intros SP N x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro HN RN.
  step. rewrite (ls_sx32 N) by lia.
  step. rewrite p2_lts0 by lia. if_cases HC.
  - apply Bool.negb_true_iff, Z.ltb_ge in HC.
    step. step. step. apply evt_done. left. split; [lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.ltb_lt in HC.
    step. step. apply evt_done. right. split; [exact HC|]. op5_eq.
Qed.

Definition op5_l2_next (SP N : Z) (i j : nat) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  ((S i < 4)%nat /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat (S i))) (Z_to_bv 64 0x311c0)
              x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat j)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26
              x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f34) fc None m ro) \/
  (S i = 4%nat /\ Z.of_nat (S j) < N /\
   ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat 0)) (Z_to_bv 64 N) x11 x12
              x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat (S j))) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27
              x28 x29 x30 x31) F (Z_to_bv 64 0x13f34) fc None m ro) \/
  (S i = 4%nat /\ N <= Z.of_nat (S j) /\
   ms = MS (mkR (Z_to_bv 64 0x14054) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) v x11 x12 x13 x14
              x15 x16 x17 (Z_to_bv 64 (Z.of_nat (S j))) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29
              x30 x31) F (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro).

Lemma op5_l2_adv : forall (SP N : Z) (i j : nat) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= N < 2 ^ 31 -> Z.of_nat j < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 32)) 8 = Some (le8 v) ->
  evt rsegs (op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (Z.of_nat j)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 0x13f78) fc None m ro).
Proof.
  intros SP N i j v x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m ro Hi HN Hj RN RV.
  step. step. step.
  if_cases HC; rewrite p2_eqb in HC by (unfold G_S; lia).
  - apply Bool.negb_true_iff, Z.eqb_neq in HC.
    apply evt_done. unfold op5_l2_next. left. split; [unfold G_S in HC; lia|]. op5_eq.
  - apply Bool.negb_false_iff, Z.eqb_eq in HC.
    step. rewrite (ls_sx32 N) by lia.
    step. step. rewrite op5_lts by lia. if_cases HJN.
    + apply Z.ltb_lt in HJN.
      step. apply evt_done. unfold op5_l2_next. right. left.
      split; [unfold G_S in HC; lia|]. split; [lia|]. op5_eq.
    + apply Z.ltb_ge in HJN.
      step. step. step. apply evt_done. unfold op5_l2_next. right. right.
      split; [unfold G_S in HC; lia|]. split; [lia|]. op5_eq.
Qed.

Lemma op5_l2_head : forall (es : list rentry) (tail : list byte) (SP G N fd op : Z) (i j : nat) (e : rentry)
    (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  (i < 4)%nat -> 0 <= N < 2 ^ 31 -> 0 <= fd < 2 ^ 31 -> 0 <= op < 2 ^ 31 -> nth_error es j = Some e ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x30ff0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 32)) 8 = Some (le8 v) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  rw_cells rsegs m (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] ->
  evt rsegs (fun ms =>
      (op <> 0 /\ fd = re_fd e /\
       ms = MS (mkR (Z_to_bv 64 0x13f68) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
                  (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 (8 * Z.of_nat j))
                  (Z_to_bv 64 (56 * Z.of_nat j)) x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat j)) x19 (Z_to_bv 64 0x30fc0)
                  x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CHECK_NO_LOSS) fc None m ro) \/
      (op = 0 /\
       op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28
         x29 x30 x31 F fc m ro ms) \/
      (op <> 0 /\ fd <> re_fd e /\
       op5_l2_next SP N i j v x1 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (re_fd e)) (Z_to_bv 64 (8 * Z.of_nat j))
         (Z_to_bv 64 (56 * Z.of_nat j)) x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ms))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (Z.of_nat j)) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 0x13f34) fc None m ro).
Proof.
  intros es tail SP G N fd op i j e v x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 F fc m ro Hi HN Hfd Hop HE HW RN RG RV TB HS.
  pose proof (op5_len es HW) as HLn.
  destruct (op5_slot2 m i fd op HS) as [RF RO]. clear HS.
  destruct TB as [[TW HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_wf cell_wf] in TW. destruct TW as [TL _]. rewrite length_app, HLn in TL.
  apply bytes_at_app in HB. destruct HB as [HB _].
  assert (Hj : (j < length es)%nat) by (apply nth_error_Some; congruence).
  assert (Re : 0 <= re_fd e < 2 ^ 31).
  { rewrite Forall_forall in HW. destruct (HW e (nth_error_In es j HE)) as (_ & _ & R & _). exact R. }
  pose proof (p2_rd4 m _ _ (op5_entry_fd m es G j e HW HE HB)) as RE. clear HB.
  step. rewrite (ls_sx32 op) by lia.
  step. if_cases H0; rewrite p2_eqb in H0 by lia.
  - apply Z.eqb_eq in H0.
    eapply evt_mono; [apply (op5_l2_adv SP N i j v); first [exact Hi | exact RN | exact RV | lia]|].
    intros ms Hms. right. left. split; [exact H0|exact Hms].
  - apply Z.eqb_neq in H0.
    step. rewrite (ls_sx32 fd) by lia.
    step.
    step. rewrite (op5_sl3 (Z.of_nat j)) by lia.
    step. rewrite (op5_sl6 (Z.of_nat j)) by lia.
    step. rewrite (op5_sub56 (Z.of_nat j)) by lia.
    step.
    step. rewrite (ls_sx32 (re_fd e)) by lia.
    step. if_cases H1; rewrite p2_eqb in H1 by lia.
    + apply Bool.negb_true_iff, Z.eqb_neq in H1.
      eapply evt_mono; [apply (op5_l2_adv SP N i j v); first [exact Hi | exact RN | exact RV | lia]|].
      intros ms Hms. right. right. split; [exact H0|]. split; [exact H1|exact Hms].
    + apply Bool.negb_false_iff, Z.eqb_eq in H1.
      step. step. step. apply evt_done. left. split; [exact H0|]. split; [exact H1|]. op5_eq.
Qed.

Lemma op5_l2_mid : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x13f78) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 (Z_to_bv 64 (SP + 40))
      (Z_to_bv 64 (SP + 32)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_SHAPE_ENDS) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
      x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13f68) fc None m ro).
Proof.
  intros. step. step. step. step. apply evt_done. reflexivity.
Qed.
