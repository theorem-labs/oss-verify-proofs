(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ItableModel3 RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3.ItableModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition it_here_op (ty : codetype) (work : arr) (w : Z) : Z :=
  if w + 1 <? it_match ty then 0 else if it_match ty <=? w then wrap8 (it_extra ty work (w - it_match ty)) else 96.
Definition it_here_val (ty : codetype) (work : arr) (w : Z) : Z :=
  if w + 1 <? it_match ty then w else if it_match ty <=? w then it_base ty work (w - it_match ty) else 0.

Definition it_huff_next (huff len : Z) : Z :=
  let incr := it_incr_back huff len in if negb (incr =? 0) then Z.land huff (incr - 1) + incr else 0.

Definition it_st1 (x : ItCtx) (st : ItSt) : ItSt :=
  let w := arr_get (t_work st) (t_sym st) in
  let here := code_pack (it_here_op (x_ty x) (t_work st) w) (wrap8 (t_len st - t_drop st)) (it_here_val (x_ty x) (t_work st) w) in
  let fill := shl32 1 (t_curr st) in
  let tbl := it_fill here (shl32 1 (t_len st - t_drop st)) (t_huff st) (t_drop st) (t_next st) fill (t_tbl st) in
  let sym := wrap32 (t_sym st + 1) in
  let c := wrap16 (arr_get (t_count st) (t_len st) - 1) in
  let len := if (c =? 0) && negb (t_len st =? x_max x)
             then arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) sym) else t_len st in
  mkItSt (it_huff_next (t_huff st) (t_len st)) sym len (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st)
         fill (arr_set (t_count st) (t_len st) c) tbl (t_work st).

Definition it_brk (x : ItCtx) (st : ItSt) : bool :=
  (wrap16 (arr_get (t_count st) (t_len st) - 1) =? 0) && (t_len st =? x_max x).

Definition it_sub (x : ItCtx) (s1 : ItSt) : ItStep :=
  if (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) then
    let drop := if t_drop s1 =? 0 then x_root x else t_drop s1 in
    let next := t_next s1 + t_min s1 in
    let curr := it_subtable_curr (t_count s1) (t_len s1) drop (x_max x) in
    let used := wrap32 (t_used s1 + Z.shiftl 1 curr) in
    if it_not_enough (x_ty x) used
    then ItFail (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop (t_low s1) used (t_min s1) (t_count s1) (t_tbl s1) (t_work s1))
    else
      let low := Z.land (t_huff s1) (x_mask x) in
      ItCont (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop low used (t_min s1) (t_count s1)
                     (arr_set (t_tbl s1) (x_table x + low) (code_pack curr (x_root x) (next - x_table x))) (t_work s1))
  else ItCont s1.

Lemma it_step_eq : forall x st, it_step x st = if it_brk x st then ItBreak (it_st1 x st) else it_sub x (it_st1 x st).
Proof.
  intros x st. unfold it_step, it_brk, it_sub, it_st1, it_here_op, it_here_val, it_huff_next. cbv zeta.
  destruct (arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x)); [reflexivity|].
  destruct (it_match (x_ty x) <=? arr_get (t_work st) (t_sym st)); reflexivity.
Qed.


Definition it_fin (table root bits : Z) (r : ItSt + ItSt) : Z * arr * Z * Z * arr :=
  match r with
  | inr st => (1, t_tbl st, table, bits, t_work st)
  | inl st => (0, (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                   else t_tbl st), table + t_used st, root, t_work st)
  end.

Section Exits.
Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr).
Let count := itm_count lens lens_ofs codes.
Let max := itm_max count.
Let min := itm_min count max.
Let root := itm_root bits max min.
Let work1 := itm_work lens lens_ofs codes (itm_offs count) work.

Lemma inflate_table_eq_max0 : max = 0 ->
  inflate_table ty lens lens_ofs codes tbl table bits work
  = (0, arr_set (arr_set tbl table (code_pack 64 1 0)) (table + 1) (code_pack 64 1 0), table + 2, 1, work).
Proof. intros H. rewrite inflate_table_phases. cbv zeta. fold count max. rewrite H. reflexivity. Qed.

Lemma inflate_table_eq_reject : max <> 0 -> itm_reject ty max (it_left_check count) = true ->
  inflate_table ty lens lens_ofs codes tbl table bits work = (-1, tbl, table, bits, work).
Proof.
  intros H R. rewrite inflate_table_phases. cbv zeta. fold count max.
  replace (max =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). rewrite R. reflexivity.
Qed.

Lemma inflate_table_eq_nospace : max <> 0 -> itm_reject ty max (it_left_check count) = false ->
  it_not_enough ty (itm_used root) = true ->
  inflate_table ty lens lens_ofs codes tbl table bits work = (1, tbl, table, bits, work1).
Proof.
  intros H R N. rewrite inflate_table_phases. cbv zeta. fold count max min root work1.
  replace (max =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). rewrite R, N. reflexivity.
Qed.

Lemma inflate_table_eq_loop : max <> 0 -> itm_reject ty max (it_left_check count) = false ->
  it_not_enough ty (itm_used root) = false ->
  inflate_table ty lens lens_ofs codes tbl table bits work
  = it_fin table root bits (it_loop_n (itm_ctx ty lens lens_ofs table root max) (codes + 1) (itm_st0 min table root count tbl work1)).
Proof.
  intros H R N. rewrite inflate_table_phases. cbv zeta. fold count max min root work1.
  replace (max =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). rewrite R, N.
  rewrite it_loop_is_n. unfold it_fin. destruct (it_loop_n _ _ _); reflexivity.
Qed.
End Exits.


Definition tab16 (a : arr) (n : nat) : bool :=
  forallb (fun i => (0 <=? arr_get a (Z.of_nat i)) && (arr_get a (Z.of_nat i) <? 65536)) (seq 0 n).
Lemma tab16_sound : forall a n i, tab16 a n = true -> 0 <= i < Z.of_nat n -> 0 <= arr_get a i < 65536.
Proof.
  intros a n i H Hi. unfold tab16 in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma tab16_lbase : tab16 lbase_a 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tab16_lext : tab16 lext_a 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tab16_dbase : tab16 dbase_a 32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tab16_dext : tab16 dext_a 32 = true. Proof. vm_compute. reflexivity. Qed.

Lemma it_base_range : forall ty wk i, ty16 wk -> 0 <= i < it_ext_len ty 288 -> 0 <= it_base ty wk i < 65536.
Proof.
  intros ty wk i TY Hi. unfold it_base. unfold it_ext_len in Hi. destruct ty.
  - apply TY.
  - apply (tab16_sound lbase_a 31); [exact tab16_lbase| lia].
  - apply (tab16_sound dbase_a 32); [exact tab16_dbase| lia].
Qed.
Lemma it_extra_range : forall ty wk i, ty16 wk -> 0 <= i < it_ext_len ty 288 -> 0 <= it_extra ty wk i < 65536.
Proof.
  intros ty wk i TY Hi. unfold it_extra. unfold it_ext_len in Hi. destruct ty.
  - apply TY.
  - apply (tab16_sound lext_a 31); [exact tab16_lext| lia].
  - apply (tab16_sound dext_a 32); [exact tab16_dext| lia].
Qed.
Lemma it_here_op_range : forall ty wk w, 0 <= it_here_op ty wk w < 256.
Proof.
  intros. unfold it_here_op. destruct (_ <? _); [lia|]. destruct (_ <=? _); [|lia]. rewrite wrap8_mod. apply Z.mod_pos_bound. lia.
Qed.
Lemma it_here_val_range : forall ty wk w, ty16 wk -> 0 <= w < 65536 ->
  (it_match ty <= w -> w - it_match ty < it_ext_len ty 288) -> 0 <= it_here_val ty wk w < 65536.
Proof.
  intros ty wk w TY Hw Hx. unfold it_here_val. destruct (Z.ltb_spec (w + 1) (it_match ty)); [lia|].
  destruct (Z.leb_spec (it_match ty) w); [|lia]. apply it_base_range; [exact TY| lia].
Qed.

Lemma code_pack_wrap8_bits : forall a b c, code_pack a (wrap8 b) c = code_pack a b c.
Proof. intros. unfold code_pack. rewrite !wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.
Lemma shl32_pow2' : forall k, 0 <= k <= 31 -> shl32 1 k = 2 ^ k.
Proof.
  intros k Hk. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_id. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia].
Qed.
Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. change 1 with (2 ^ 0). change 32768 with (2 ^ 15). split; apply Z.pow_le_mono_r; lia. Qed.


Lemma curr_step_small' : forall cnt drop mx curr lft,
  0 <= curr <= 15 -> 0 <= drop <= 15 ->
  curr_step cnt drop mx (curr, lft) =
  (if curr + drop <? mx then
     if lft - arr_get cnt (curr + drop) <=? 0 then (false, (curr, lft - arr_get cnt (curr + drop)))
     else (true, (curr + 1, Z.shiftl (lft - arr_get cnt (curr + drop)) 1))
   else (false, (curr, lft))).
Proof. intros. unfold curr_step. rewrite !wrap32_id by lia. reflexivity. Qed.

Lemma curr_rec_bound : forall cnt dp mx n c lft, 0 <= dp <= 15 -> 0 <= c <= 15 -> mx <= 15 ->
  c <= fst (curr_rec cnt dp mx n c lft) <= Z.max c (mx - dp).
Proof.
  intros cnt dp mx n. induction n as [|n IH]; intros c lft Hdp Hc Hmx; cbn [curr_rec]; [cbn [fst]; lia|].
  rewrite curr_step_small' by lia. destruct (Z.ltb_spec (c + dp) mx).
  - destruct (_ <=? 0); cbn [fst snd]; [lia|]. specialize (IH (c + 1) (Z.shiftl (lft - arr_get cnt (c + dp)) 1) ltac:(lia) ltac:(lia) Hmx). lia.
  - cbn [fst]. lia.
Qed.

Lemma it_subtable_curr_eq : forall cnt len dp mx, 0 <= dp <= len -> len <= 15 ->
  it_subtable_curr cnt len dp mx = fst (curr_rec cnt dp mx 16 (len - dp) (2 ^ (len - dp))).
Proof.
  intros cnt len dp mx H1 H2. rewrite it_subtable_curr_rec. rewrite (wrap32_id (len - dp)) by lia.
  rewrite Z.shiftl_1_l, swrap32_id; [reflexivity|]. split; [pose proof (Z.pow_nonneg 2 (len - dp)); lia|].
  apply (Z.le_lt_trans _ (2 ^ 15)); [apply Z.pow_le_mono_r; lia| apply Z.pow_lt_mono_r; lia].
Qed.
