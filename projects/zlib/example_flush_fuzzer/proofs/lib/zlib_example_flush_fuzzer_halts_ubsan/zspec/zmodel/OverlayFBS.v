(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateInvKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition fbs_tree_lens (s : deflate_state) : Prop :=
  arr_len (ds_dyn_ltree_fc s) = 573 /\ arr_len (ds_dyn_ltree_dl s) = 573
  /\ arr_len (ds_dyn_dtree_fc s) = 61 /\ arr_len (ds_dyn_dtree_dl s) = 61
  /\ arr_len (ds_bl_tree_fc s) = 39 /\ arr_len (ds_bl_tree_dl s) = 39
  /\ arr_len (ds_bl_count s) = 16 /\ arr_len (ds_heap s) = 573 /\ arr_len (ds_depth s) = 573.

Definition sym_valid (dl : Z * Z) : Prop :=
  let '(d, lc) := dl in (d = 0 /\ 0 <= lc <= 255) \/ (1 <= d <= 32768 - MIN_LOOKAHEAD /\ 0 <= lc <= 255).

Definition sym_lcode (dl : Z * Z) : Z :=
  let '(d, lc) := dl in if d =? 0 then lc else arr_get length_code_a lc + LITERALS + 1.
Definition sym_dcode (dl : Z * Z) : option Z :=
  let '(d, lc) := dl in if d =? 0 then None else Some (d_code (d - 1)).

Definition zcount {A} (f : A -> bool) (l : list A) : Z := Z.of_nat (length (filter f l)).

Record FBS (fbs_syms : list (Z * Z)) (s : deflate_state) (buf : option Z) (len last : Z) : Prop := MkFBS {
  fbs_n := Z.of_nat (length fbs_syms);
  fbs_L := ds_lit_bufsize s;
  fbs_pending : ds_pending s = 0;
  fbs_bi_valid : 0 <= ds_bi_valid s <= 16;
  fbs_bi_buf : 0 <= ds_bi_buf s < 2 ^ 16;
  fbs_Lpow : exists k, 7 <= k <= 15 /\ fbs_L = 2 ^ k;
  fbs_pbl : arr_len (ds_pending_buf s) = 4 * fbs_L;
  fbs_sym_end : ds_sym_end s = 3 * (fbs_L - 1);
  fbs_sym_next : ds_sym_next s = 3 * fbs_n;
  fbs_n_range : 0 <= fbs_n <= fbs_L - 1;
  fbs_syms_valid : Forall sym_valid fbs_syms;
  fbs_sym_bytes : forall i d lc, nth_error fbs_syms i = Some (d, lc) ->
      arr_get (ds_pending_buf s) (fbs_L + 3 * Z.of_nat i) = d mod 256
      /\ arr_get (ds_pending_buf s) (fbs_L + 3 * Z.of_nat i + 1) = d / 256
      /\ arr_get (ds_pending_buf s) (fbs_L + 3 * Z.of_nat i + 2) = lc;
  fbs_freq_l : forall c, 0 <= c < L_CODES ->
      Freq s TL c = zcount (fun dl => sym_lcode dl =? c) fbs_syms + (if c =? END_BLOCK then 1 else 0);
  fbs_freq_d : forall j, 0 <= j < D_CODES ->
      Freq s TD j = zcount (fun dl => match sym_dcode dl with Some j' => j' =? j | None => false end) fbs_syms;
  fbs_freq_b : forall j, 0 <= j < BL_CODES -> Freq s TB j = 0;
  fbs_lens : fbs_tree_lens s;
  fbs_cty : cty s;
  fbs_opt_len : ds_opt_len s = 0;
  fbs_static_len : ds_static_len s = 0;
  fbs_level : 1 <= ds_level s <= 9;
  fbs_strategy : 0 <= ds_strategy s <= 4;
  fbs_data_type : - 2 ^ 31 <= cs_data_type (ds_strm s) < 2 ^ 31;
  fbs_last : last = 0 \/ last = 1;
  fbs_len : 0 <= len < 2 ^ 32;
  fbs_buf : forall off, buf = Some off ->
      0 <= off /\ off + len <= arr_len (ds_window s)
      /\ forall i, 0 <= i < arr_len (ds_window s) -> 0 <= arr_get (ds_window s) i < 256 }.
