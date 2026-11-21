(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Loop1.
Variable t : tree_id.
Variable MC : Z.
Local Notation ML := (sd_max_length t).
Local Notation BASE := (sd_extra_base t).

Definition xbits (n : Z) : Z := if BASE <=? n then arr_get (sd_extra_bits t) (n - BASE) else 0.

Definition GB1 (X : deflate_state) (h ovf : Z) : deflate_state * Z :=
  let n := heap_get X h in
  let bits := Len X t (Dad X t n) + 1 in
  let '(bits, overflow) := (if ML <? bits then (ML, ovf + 1) else (bits, ovf)) in
  let X1 := set_Len X t n bits in
  if MC <? n then (X1, overflow)
  else
    let X2 := bl_count_set X1 bits (bl_count_get X1 bits + 1) in
    let xb := if BASE <=? n then arr_get (sd_extra_bits t) (n - BASE) else 0 in
    let fq := Freq X2 t n in
    let X3 := set_opt_len X2 (wrap64 (ds_opt_len X2 + fq * (bits + xb))) in
    let X4 := if stree_has t
              then set_static_len X3 (wrap64 (ds_static_len X3 + fq * (stree_Len t n + xb)))
              else X3 in
    (X4, overflow).

Lemma GL1_step : forall f X h ovf,
  gen_bitlen_loop1 (S f) X t MC BASE ML h ovf =
  if h <? HEAP_SIZE then let '(X', o') := GB1 X h ovf in gen_bitlen_loop1 f X' t MC BASE ML (h + 1) o'
  else (X, ovf).
Proof.
  intros f X h ovf. cbn [gen_bitlen_loop1]. unfold GB1.
  destruct (h <? HEAP_SIZE); [|reflexivity].
  destruct (ML <? Len X t (Dad X t (heap_get X h)) + 1); destruct (MC <? heap_get X h); reflexivity.
Qed.

Lemma GL1_done : forall f X h ovf, HEAP_SIZE <= h ->
  gen_bitlen_loop1 f X t MC BASE ML h ovf = (X, ovf).
Proof.
  intros f X h ovf Hh. destruct f; [reflexivity|]. cbn [gen_bitlen_loop1].
  replace (h <? HEAP_SIZE) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Fixpoint gb1_ok (f : nat) (X : deflate_state) (h ovf : Z) : Prop :=
  match f with
  | O => True
  | S f' =>
      if h <? HEAP_SIZE then
        0 <= Dad X t (heap_get X h) < tsize t
        /\ (let '(X', o') := GB1 X h ovf in gb1_ok f' X' (h + 1) o')
      else True
  end.

Lemma GB1_flat : forall s FC DL HP HL HM DP BC OL SL h ovf,
  let n := arr_get HP h in
  let bits0 := arr_get DL (arr_get DL n) + 1 in
  let bits := (if ML <? bits0 then ML else bits0) in
  let ovf' := (if ML <? bits0 then ovf + 1 else ovf) in
  let DL' := arr_set DL n (wrap16 bits) in
  GB1 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) h ovf =
  if MC <? n then (bt_upd s t FC DL' HP HL HM DP BC OL SL MC, ovf')
  else (bt_upd s t FC DL' HP HL HM DP (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
               (wrap64 (OL + arr_get FC n * (bits + xbits n)))
               (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits n)) else SL) MC, ovf').
Proof.
  intros. unfold GB1. subst n bits0.
  rewrite bt_heap_get, bt_Dad, bt_Len.
  destruct (ML <? arr_get DL (arr_get DL (arr_get HP h)) + 1); subst bits ovf' DL';
    rewrite bt_set_Len; destruct (MC <? arr_get HP h); try reflexivity;
    rewrite bt_bl_count_get, bt_bl_count_set, bt_Freq, bt_opt_len, bt_set_opt_len; unfold xbits;
    destruct (stree_has t); rewrite ?bt_static_len, ?bt_set_static_len; reflexivity.
Qed.


End Loop1.


Section Loop2.
Variable t : tree_id.
Variable ML : Z.

Definition bl_adj (BC : arr) (r : Z) : arr :=
  let BC1 := arr_set BC r (wrap16 (arr_get BC r - 1)) in
  let BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2)) in
  arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1)).

Lemma bl_adj_lt : forall BC r, arr_len BC = 16 -> 0 <= r -> r + 1 < ML -> ML < 16 ->
  bl_adj BC r = arr_set (arr_set (arr_set BC r (wrap16 (arr_get BC r - 1))) (r + 1) (wrap16 (arr_get BC (r + 1) + 2)))
                        ML (wrap16 (arr_get BC ML - 1)).
Proof.
  intros BC r HL Hr Hr1 HML. unfold bl_adj.
  rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, HL.
  replace ((r =? r + 1) && ((0 <=? r) && (r <? 16))) with false by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.eqb_neq; lia).
  replace ((r + 1 =? ML) && ((0 <=? r + 1) && (r + 1 <? 16))) with false by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.eqb_neq; lia).
  replace ((r =? ML) && ((0 <=? r) && (r <? 16))) with false by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

Lemma bl_adj_eq : forall BC r, arr_len BC = 16 -> 0 <= r -> r + 1 = ML -> ML < 16 ->
  bl_adj BC r = arr_set (arr_set (arr_set BC r (wrap16 (arr_get BC r - 1))) (r + 1) (wrap16 (arr_get BC (r + 1) + 2)))
                        ML (wrap16 (wrap16 (arr_get BC (r + 1) + 2) - 1)).
Proof.
  intros BC r HL Hr Hr1 HML. unfold bl_adj.
  rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, HL.
  replace ((r =? r + 1) && ((0 <=? r) && (r <? 16))) with false by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.eqb_neq; lia).
  replace ((r + 1 =? ML) && ((0 <=? r + 1) && (r + 1 <? 16))) with true by (symmetry; rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.leb_le, Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma find_spec : forall f X b, 0 <= gen_bitlen_find f X b ->
  let r := gen_bitlen_find f X b in
  r <= b /\ (forall j, r < j <= b -> bl_count_get X j = 0) /\ (r = b - Z.of_nat f \/ bl_count_get X r <> 0).
Proof.
  induction f as [|f IH]; intros X b Hr; cbn [gen_bitlen_find] in *.
  - split; [lia|]. split; [intros; lia|]. left. lia.
  - destruct (Z.eqb_spec (bl_count_get X b) 0) as [Hz|Hz].
    + destruct (IH X (b - 1) Hr) as (A & B & C). split; [lia|]. split.
      * intros j Hj. destruct (Z.eq_dec j b) as [->|]; [exact Hz|]. apply B. lia.
      * destruct C as [C|C]; [left; lia | right; exact C].
    + split; [lia|]. split; [intros; lia|]. right. exact Hz.
Qed.

Lemma GL2_step : forall f s FC DL HP HL HM DP BC OL SL MC ovf,
  let X := bt_upd s t FC DL HP HL HM DP BC OL SL MC in
  let r := gen_bitlen_find (Z.to_nat ML) X (ML - 1) in
  gen_bitlen_loop2 (S f) X ML ovf =
    (let X' := bt_upd s t FC DL HP HL HM DP (bl_adj BC r) OL SL MC in
     if 0 <? ovf - 2 then gen_bitlen_loop2 f X' ML (ovf - 2) else X').
Proof.
  intros. cbn [gen_bitlen_loop2]. subst r X.
  repeat (first [rewrite bt_bl_count_get | rewrite bt_bl_count_set]).
  unfold bl_adj. reflexivity.
Qed.

Fixpoint gb2_ok (f : nat) (X : deflate_state) (ovf : Z) : Prop :=
  match f with
  | O => True
  | S f' =>
      let r := gen_bitlen_find (Z.to_nat ML) X (ML - 1) in
      0 <= r
      /\ (let X1 := bl_count_set X r (bl_count_get X r - 1) in
          let X2 := bl_count_set X1 (r + 1) (bl_count_get X1 (r + 1) + 2) in
          let X3 := bl_count_set X2 ML (bl_count_get X2 ML - 1) in
          if 0 <? ovf - 2 then gb2_ok f' X3 (ovf - 2) else True)
  end.

Lemma gb2_ok_step : forall f s FC DL HP HL HM DP BC OL SL MC ovf,
  let X := bt_upd s t FC DL HP HL HM DP BC OL SL MC in
  let r := gen_bitlen_find (Z.to_nat ML) X (ML - 1) in
  gb2_ok (S f) X ovf ->
  0 <= r /\ (0 < ovf - 2 -> gb2_ok f (bt_upd s t FC DL HP HL HM DP (bl_adj BC r) OL SL MC) (ovf - 2)).
Proof.
  intros f s FC DL HP HL HM DP BC OL SL MC ovf. cbn [gb2_ok]. intros [Hr Hrest]. split; [exact Hr|].
  intros Ho. replace (0 <? ovf - 2) with true in Hrest by (symmetry; apply Z.ltb_lt; exact Ho).
  revert Hrest. repeat (first [rewrite bt_bl_count_get | rewrite bt_bl_count_set]).
  unfold bl_adj. exact (fun H => H).
Qed.

End Loop2.


Section Loop3.
Variable t : tree_id.
Variable MC : Z.

Definition GB3i (X : deflate_state) (bits n h : Z) : deflate_state * Z * Z :=
  let h' := h - 1 in
  let m := heap_get X h' in
  if MC <? m then (X, n, h')
  else
    let X' := if negb (Len X t m =? bits)
              then set_Len (set_opt_len X (wrap64 (ds_opt_len X + (bits - Len X t m) * Freq X t m))) t m bits
              else X in
    (X', n - 1, h').

Lemma GL3i_step : forall f X bits n h,
  gen_bitlen_loop3i (S f) X t MC bits n h =
  if negb (n =? 0) then let '(X', n', h') := GB3i X bits n h in gen_bitlen_loop3i f X' t MC bits n' h'
  else (X, h).
Proof.
  intros f X bits n h. cbn [gen_bitlen_loop3i]. unfold GB3i.
  destruct (negb (n =? 0)); [|reflexivity]. destruct (MC <? heap_get X (h - 1)); reflexivity.
Qed.

Lemma GL3i_done : forall f X bits h, gen_bitlen_loop3i f X t MC bits 0 h = (X, h).
Proof. intros f X bits h. destruct f; reflexivity. Qed.

Lemma GL3_step : forall f X bits h,
  gen_bitlen_loop3 (S f) X t MC bits h =
  if negb (bits =? 0) then
    let '(X', h') := gen_bitlen_loop3i 574%nat X t MC bits (bl_count_get X bits) h in
    gen_bitlen_loop3 f X' t MC (bits - 1) h'
  else X.
Proof. intros. reflexivity. Qed.

Lemma GL3_done : forall f X h, gen_bitlen_loop3 f X t MC 0 h = X.
Proof. intros f X h. destruct f; reflexivity. Qed.

Lemma GB3i_flat : forall s FC DL HP HL HM DP BC OL SL bits n h,
  let m := arr_get HP (h - 1) in
  GB3i (bt_upd s t FC DL HP HL HM DP BC OL SL MC) bits n h =
  if MC <? m then (bt_upd s t FC DL HP HL HM DP BC OL SL MC, n, h - 1)
  else if arr_get DL m =? bits then (bt_upd s t FC DL HP HL HM DP BC OL SL MC, n - 1, h - 1)
  else (bt_upd s t FC (arr_set DL m (wrap16 bits)) HP HL HM DP BC
               (wrap64 (OL + (bits - arr_get DL m) * arr_get FC m)) SL MC, n - 1, h - 1).
Proof.
  intros. unfold GB3i. subst m. rewrite bt_heap_get.
  destruct (MC <? arr_get HP (h - 1)); [reflexivity|].
  rewrite !bt_Len. destruct (arr_get DL (arr_get HP (h - 1)) =? bits); cbn [negb]; [reflexivity|].
  rewrite bt_Freq, bt_opt_len, bt_set_opt_len, bt_set_Len. reflexivity.
Qed.

Fixpoint gb3i_ok (f : nat) (X : deflate_state) (bits n h : Z) : Prop :=
  match f with
  | O => True
  | S f' =>
      if negb (n =? 0) then
        1 <= h <= 573 /\ 0 <= heap_get X (h - 1) < 573
        /\ (let '(X', n', h') := GB3i X bits n h in gb3i_ok f' X' bits n' h')
      else True
  end.

Fixpoint gb3_ok (f : nat) (X : deflate_state) (bits h : Z) : Prop :=
  match f with
  | O => True
  | S f' =>
      if negb (bits =? 0) then
        gb3i_ok 574%nat X bits (bl_count_get X bits) h
        /\ (let '(X', h') := gen_bitlen_loop3i 574%nat X t MC bits (bl_count_get X bits) h in
            gb3_ok f' X' (bits - 1) h')
      else True
  end.

End Loop3.


Definition bt_safe (ds : deflate_state) (t : tree_id) : Prop :=
  let E := sd_elems t in
  let ML := sd_max_length t in
  let BASE := sd_extra_base t in
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_fc ds t) i < 65536)
  /\ 0 <= ds_opt_len ds < 2 ^ 64 /\ 0 <= ds_static_len ds < 2 ^ 64
  /\ (let s0 := set_heap_max (set_heap_len ds 0) HEAP_SIZE in
      let '(s1, mc1) := build_tree_loop1 (Z.to_nat E) s0 t E 0 (-1) in
      let '(s2, mc) := build_tree_loop2 2%nat s1 t mc1 in
      let s3 := set_max_code s2 t mc in
      (forall i, 1 <= i <= ds_heap_len s3 -> 0 <= heap_get s3 i < tsize t)
      /\ (forall i, 0 <= i < 573 -> 0 <= depth_get s3 i < 256)
      /\ (forall i, 0 <= i < tsize t -> 0 <= Freq s3 t i < 65536)
      /\ (let s4 := build_tree_loop3 (Z.to_nat (ds_heap_len s3 / 2)) s3 t (ds_heap_len s3 / 2) in
          let s5 := build_tree_loop4 573%nat s4 t E in
          let s6 := set_heap_max s5 (ds_heap_max s5 - 1) in
          let s7 := heap_set s6 (ds_heap_max s6) (heap_get s6 SMALLEST) in
          (forall h, ds_heap_max s7 + 1 <= h < HEAP_SIZE -> 0 <= heap_get s7 h < tsize t)
          /\ (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl s7 t) i < 65536)
          /\ (let s8 := set_bl_count s7 (arr_fill (ds_bl_count s7) 0 (MAX_BITS + 1) 0) in
              let s9 := set_Len s8 t (heap_get s8 (ds_heap_max s8)) 0 in
              gb1_ok t mc 573%nat s9 (ds_heap_max s9 + 1) 0
              /\ (let '(s10, ovf) := gen_bitlen_loop1 573%nat s9 t mc BASE ML (ds_heap_max s9 + 1) 0 in
                  (ovf <> 0 -> gb2_ok ML 573%nat s10 ovf
                               /\ gb3_ok t mc (Z.to_nat ML) (gen_bitlen_loop2 573%nat s10 ML ovf) ML HEAP_SIZE))
              /\ (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen s7 t) t i <= 15)))).
