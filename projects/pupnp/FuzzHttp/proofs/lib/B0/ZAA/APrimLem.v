(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import APrim.
Import ListNotations.
Open Scope Z_scope.

Lemma rup_ge : forall x a, 0 < a -> x <= rup x a.
Proof. intros x a Ha. unfold rup. Z.div_mod_to_equations. nia. Qed.
Lemma rup_lt : forall x a, 0 < a -> rup x a < x + a.
Proof. intros x a Ha. unfold rup. Z.div_mod_to_equations. nia. Qed.
Lemma rup_mod : forall x a, 0 < a -> rup x a mod a = 0.
Proof. intros x a Ha. unfold rup. apply Z_mod_mult. Qed.
Lemma rup_le : forall x y a, 0 < a -> x <= y -> y mod a = 0 -> rup x a <= y.
Proof.
  intros x y a Ha Hxy Hy. unfold rup. assert (Hy' : y = (y / a) * a) by (Z.div_mod_to_equations; nia).
  assert (L : (x + a - 1) / a < y / a + 1) by (apply Z.div_lt_upper_bound; [lia| nia]). nia.
Qed.
Lemma rup_id : forall x a, 0 < a -> x mod a = 0 -> rup x a = x.
Proof.
  intros x a Ha Hx. pose proof (rup_ge x a Ha). pose proof (rup_le x x a Ha ltac:(lia) Hx). lia.
Qed.

Lemma u32s_repeat0 : forall k, u32s (repeat (wz 0) k) = repeat (Z_to_bv 8 0) (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH.
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. reflexivity.
Qed.

Lemma u32arr_extend_zeros : forall m A ws n,
  u32arr asegs m A ws -> 0 <= n -> n mod 4 = 0 ->
  rw_cells asegs m (A + 4 * Z.of_nat (length ws)) [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  u32arr asegs m A (ws ++ repeat (wz 0) (Z.to_nat (n / 4))).
Proof.
  intros m A ws n [B W] N0 N4 [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize] in ZB, ZW.
  rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
  assert (E4 : (4 * Z.to_nat (n / 4))%nat = Z.to_nat n) by (Z.div_mod_to_equations; lia).
  split.
  - rewrite u32s_app, u32s_repeat0, E4. apply bytes_at_app. split; [exact B|]. rewrite u32s_length.
    replace (A + Z.of_nat (4 * length ws)) with (A + 4 * Z.of_nat (length ws)) by lia. exact ZB.
  - rewrite app_length, repeat_length.
    replace (4 * Z.of_nat (length ws + Z.to_nat (n / 4))) with (4 * Z.of_nat (length ws) + n) by (Z.div_mod_to_equations; lia).
    apply wr_at_app; [lia| lia|]. split; [exact W|]. rewrite Z2Nat.id in ZW by lia. exact ZW.
Qed.

Lemma rw_cells_to_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[Hwf Hb] Hw]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact Hwf| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma rw_cells_ex_CB : forall m A cs n, rw_cells asegs m A cs -> cells_size cs = n ->
  exists bs, rw_cells asegs m A [CB n bs].
Proof. intros m A cs n H <-. eexists. apply rw_cells_to_CB. exact H. Qed.

Lemma stk_mid_chunk : forall m lo hi a (n : nat),
  stk asegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells asegs m a [CB n junk].
Proof.
  intros m lo hi a n ST LA AH.
  destruct (stk_split asegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve asegs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ [junk FR]].
  replace (a + Z.of_nat n - Z.of_nat n) with a in FR by lia. exists junk. exact FR.
Qed.

Lemma sh_in_window : forall beg size, 0 <= size ->
  (sh beg / 4096) * 4096 <= sh beg /\ sh beg + size / 8 <= ((sh (beg + size) + 4095) / 4096) * 4096.
Proof. intros beg size S0. unfold sh. Z.div_mod_to_equations. nia. Qed.

Lemma firstn_app_le : forall {A} (n : nat) (l1 l2 : list A), (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof. intros A n l1 l2 Hn. rewrite firstn_app. replace (n - length l1)%nat with 0%nat by lia. cbn. apply app_nil_r. Qed.

Ltac demod H :=
  unfold id in H;
  lazymatch type of H with
  | ?a mod ?b = 0 =>
      apply (proj1 (Z.mod_divide a b ltac:(lia))) in H;
      let z := fresh "qz" in let H2 := fresh H in unfold Z.divide in H; destruct H as [z H2]
  end.
Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
Ltac unhide H := unfold id in H.
