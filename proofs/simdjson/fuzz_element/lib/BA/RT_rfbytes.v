(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_glue_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Lemma farun_add : forall a b, 0 <= a -> 0 <= b -> farun (a + b) = farun a ++ farun b.
Proof. intros a b Ha Hb. unfold farun. rewrite Z2Nat.inj_add by lia. apply repeat_app. Qed.

Lemma farun_length : forall k, 0 <= k -> length (farun k) = Z.to_nat k.
Proof. intros k Hk. unfold farun. apply repeat_length. Qed.

Lemma bytes_farun_split : forall (m : mem) A a b, 0 <= a -> 0 <= b ->
  bytes_at asegs m A (farun (a + b)) <-> bytes_at asegs m A (farun a) /\ bytes_at asegs m (A + a) (farun b).
Proof.
  intros m A a b Ha Hb. rewrite farun_add by lia. rewrite bytes_at_app. rewrite farun_length, Z2Nat.id by lia. tauto.
Qed.

Lemma bytes_farun_sub : forall (m : mem) A k A' k', bytes_at asegs m A (farun k) -> A <= A' -> 0 <= k' -> A' + k' <= A + k ->
  bytes_at asegs m A' (farun k').
Proof.
  intros m A k A' k' H H1 H2 H3.
  replace k with ((A' - A) + (k' + (A + k - A' - k'))) in H by lia.
  apply (proj1 (bytes_farun_split m A (A' - A) (k' + (A + k - A' - k')) ltac:(lia) ltac:(lia))) in H as (_ & H).
  apply (proj1 (bytes_farun_split m (A + (A' - A)) k' (A + k - A' - k') ltac:(lia) ltac:(lia))) in H as (H & _).
  replace (A + (A' - A)) with A' in H by lia. exact H.
Qed.

Lemma fl_ble_range4 : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  assert (Hs : 0 <= Z.shiftl (bytes_le_to_Z bs) 8) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs)))) with (2 ^ 8 * 2 ^ (8 * Z.of_nat (length bs))).
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (fl_ble_range4 bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_stk : forall (m : mem) A (k : nat), stk asegs m A (A + 4 * Z.of_nat k) -> exists ws, length ws = k /\ u32arr asegs m A ws.
Proof.
  intros m A k. revert A. induction k as [|k IH]; intros A St.
  - exists []. split; [reflexivity|]. destruct St as (S0 & S1 & _). cbn [length Nat.mul] in S1 |- *. split; [exact (bytes_at_nil asegs m A ltac:(lia))|].
    unfold wr_at. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - destruct (stk_split asegs m A (A + 4) (A + 4 * Z.of_nat (S k)) St ltac:(lia)) as [S1 S2].
    destruct (stk_bytes asegs m A (A + 4) S1 ltac:(lia)) as (b4 & Hl & Hb). replace (A + 4 - A) with 4 in Hl by lia.
    destruct (IH (A + 4) ltac:(replace (A + 4 + 4 * Z.of_nat k) with (A + 4 * Z.of_nat (S k)) by lia; exact S2)) as (ws & Hws & (Hb2 & W2)).
    exists (le_bytes_to_word b4 :: ws). split; [cbn; rewrite Hws; reflexivity|]. split.
    + cbn [u32s]. rewrite le4_of_bytes by (cbn in Hl; lia). apply bytes_at_app. split; [exact Hb|]. rewrite Hl. cbn [Z.to_nat Pos.to_nat]. exact Hb2.
    + destruct St as (X0 & X1 & Xw). split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. exact (proj1 (Xw (A + i) ltac:(cbn [length] in Hi; lia))).
Qed.

Lemma stk_of_u32arr : forall (m : mem) A ws, u32arr asegs m A ws -> stk asegs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros m A ws ((B0 & B1 & Hb) & (W0 & W1 & Ww)). rewrite u32s_length in B1, Hb. split; [exact W0|]. split; [exact W1|]. intros a Ha.
  split; [replace a with (A + (a - A)) by lia; apply Ww; lia|].
  replace a with (A + Z.of_nat (Z.to_nat (a - A))) by lia. rewrite Hb by lia.
  destruct (nth_error (u32s ws) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. rewrite u32s_length in E. lia.
Qed.

Lemma stk_join : forall (m : mem) a b c, stk asegs m a b -> stk asegs m b c -> stk asegs m a c.
Proof.
  intros m a b c (A0 & A1 & Aw) (B0 & B1 & Bw). split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z_lt_ge_dec x b) as [X|X]; [apply Aw; lia | apply Bw; lia].
Qed.

Lemma farun_of_cells : forall (m : mem) A k, 0 <= k -> rw_cells asegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 250) (Z.to_nat k))] ->
  bytes_at asegs m A (farun k).
Proof.
  intros m A k Hk ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. unfold farun. exact Hb.
Qed.
