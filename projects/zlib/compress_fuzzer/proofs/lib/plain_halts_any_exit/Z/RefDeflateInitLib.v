(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition di_level (level : Z) : Z := if level =? Z_DEFAULT_COMPRESSION then 6 else level.
Definition di_wrap (wb : Z) : Z := if wb <? 0 then 0 else if 15 <? wb then 2 else 1.
Definition di_wb (wb : Z) : Z := if wb <? 0 then - wb else if 15 <? wb then wb - 16 else wb.

Definition di_a6 (wb : Z) : Z := if wb <? 0 then 1 else if 15 <? wb then 1 else 0.

Definition di_chk (level method wb memLevel strategy : Z) : bool :=
  (memLevel <? 1) || (MAX_MEM_LEVEL <? memLevel) || negb (method =? Z_DEFLATED)
  || (di_wb wb <? 8) || (15 <? di_wb wb) || (di_level level <? 0) || (9 <? di_level level)
  || (strategy <? 0) || (Z_FIXED <? strategy) || ((di_wb wb =? 8) && negb (di_wrap wb =? 1)).

Definition di_bad (level method wb memLevel strategy : Z) : bool :=
  ((wb <? 0) && (wb <? -15)) || di_chk level method wb memLevel strategy.
Definition di_wb9 (wb : Z) : Z := if di_wb wb =? 8 then 9 else di_wb wb.

Lemma di_wrap_range : forall wb, 0 <= di_wrap wb <= 2.
Proof. intros wb. unfold di_wrap. destruct (wb <? 0); [lia|]. destruct (15 <? wb); lia. Qed.

Lemma di_triple : forall wb,
  (if wb <? 0 then (0, - wb, wb <? -15) else if 15 <? wb then (2, wb - 16, false) else (1, wb, false))
  = (di_wrap wb, di_wb wb, (wb <? 0) && (wb <? -15)).
Proof.
  intros wb. unfold di_wrap, di_wb. destruct (wb <? 0); [reflexivity|]. destruct (15 <? wb); reflexivity.
Qed.

Lemma pow2_range_9_15 : forall k, 9 <= k <= 15 -> 512 <= 2 ^ k <= 32768.
Proof.
  intros k Hk. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.
Lemma pow2_range_8_16 : forall k, 8 <= k <= 16 -> 256 <= 2 ^ k <= 65536.
Proof.
  intros k Hk. split.
  - change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
  - change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia.
Qed.
Lemma pow2_range_7_15 : forall k, 7 <= k <= 15 -> 128 <= 2 ^ k <= 32768.
Proof.
  intros k Hk. split.
  - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Definition cfg_good (lv : Z) : Z := let '(g, _, _, _) := configuration_table lv in g.
Definition cfg_lazy (lv : Z) : Z := let '(_, l, _, _) := configuration_table lv in l.
Definition cfg_nice (lv : Z) : Z := let '(_, _, n, _) := configuration_table lv in n.
Definition cfg_chain (lv : Z) : Z := let '(_, _, _, c) := configuration_table lv in c.

Lemma cfg_eta : forall lv, configuration_table lv = (cfg_good lv, cfg_lazy lv, cfg_nice lv, cfg_chain lv).
Proof. intros lv. unfold cfg_good, cfg_lazy, cfg_nice, cfg_chain. destruct (configuration_table lv) as [[[g l] n] c]. reflexivity. Qed.

Definition CFGTAB : Z := 0x2e050.

Lemma cfg_ranges : forall lv, 0 <= cfg_good lv <= 32 /\ 0 <= cfg_lazy lv <= 258 /\ 0 <= cfg_nice lv <= 258 /\ 0 <= cfg_chain lv <= 4096.
Proof.
  intros lv. unfold cfg_good, cfg_lazy, cfg_nice, cfg_chain, configuration_table.
  destruct lv as [|p|p]; [cbn; lia | | cbn; lia].
  repeat (destruct p as [p|p|]; try (cbn; lia)).
Qed.

Definition A5_1 : Z := 165.
Definition A5_2 : Z := 42405.
Definition A5_4 : Z := 2779096485.
Definition A5_8 : Z := 11936128518282651045.

Definition cs_init (zc : ZCall) : cstrm := cset_msg (cstrm_of_call zc) MSG_NULL.

Definition s_setup (g0 : Z -> Z) (b0 : blk) (cs : cstrm) (wrap wbits memLevel : Z) : deflate_state :=
  let s := ds_of_oracle g0 b0 cs in
  let s := set_status s INIT_STATE in
  let s := set_wrap s wrap in
  let s := set_gzhead s 0 in
  let s := set_w_bits s wbits in
  let s := set_w_size s (Z.shiftl 1 wbits) in
  let s := set_w_mask s (ds_w_size s - 1) in
  let s := set_hash_bits s (memLevel + 7) in
  let s := set_hash_size s (Z.shiftl 1 (ds_hash_bits s)) in
  let s := set_hash_mask s (ds_hash_size s - 1) in
  set_hash_shift s ((ds_hash_bits s + MIN_MATCH - 1) / MIN_MATCH).

Definition s_win (s : deflate_state) (rw : option (blk * (Z -> Z))) : deflate_state :=
  match rw with
  | Some (bw, gw) => set_window_blk (set_window s (blk_bytes gw (2 * ds_w_size s))) (Some bw)
  | None => set_window_blk (set_window s (arr_make 0 0)) None
  end.
Definition s_prv (s : deflate_state) (rp : option (blk * (Z -> Z))) : deflate_state :=
  match rp with
  | Some (bp, gp) => set_prev_blk (set_prev s (blk_ush gp (ds_w_size s))) (Some bp)
  | None => set_prev_blk (set_prev s (arr_make 0 0)) None
  end.
Definition s_hd (s : deflate_state) (rh : option (blk * (Z -> Z))) : deflate_state :=
  match rh with
  | Some (bh, gh) => set_head_blk (set_head s (blk_ush gh (ds_hash_size s))) (Some bh)
  | None => set_head_blk (set_head s (arr_make 0 0)) None
  end.
Definition s_lbs (s : deflate_state) (memLevel : Z) : deflate_state :=
  set_lit_bufsize (set_high_water s 0) (Z.shiftl 1 (memLevel + 6)).
Definition s_pb (s : deflate_state) (rb : option (blk * (Z -> Z))) : deflate_state :=
  let s := match rb with
           | Some (bb, gb) => set_pending_buf_blk (set_pending_buf s (blk_bytes gb (ds_lit_bufsize s * 4))) (Some bb)
           | None => set_pending_buf_blk (set_pending_buf s (arr_make 0 0)) None
           end in
  set_pending_buf_size s (ds_lit_bufsize s * 4).
Definition s_fin (s : deflate_state) (level strategy method : Z) : deflate_state :=
  set_method (set_strategy (set_level (set_sym_end s ((ds_lit_bufsize s - 1) * 3)) level) strategy) (wrap8 method).
Definition s_fail (s : deflate_state) : deflate_state :=
  let s := set_status s FINISH_STATE in
  set_strm s (cset_msg (ds_strm s) (MSG_ERR Z_MEM_ERROR)).
Definition all_some (s : deflate_state) : bool :=
  match ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s with
  | Some _, Some _, Some _, Some _ => true
  | _, _, _, _ => false
  end.

Definition RK0 (s : deflate_state) : deflate_state :=
  let st := ds_strm s in
  let st := cset_total_in st 0 in
  let st := cset_total_out st 0 in
  let st := cset_msg st MSG_NULL in
  let st := cset_data_type st Z_UNKNOWN in
  let s := set_strm s st in
  let s := set_pending s 0 in
  let s := set_pending_out s 0 in
  let s := set_status s (if Z.eqb (ds_wrap s) 2 then GZIP_STATE else INIT_STATE) in
  let s := set_strm s (cset_adler (ds_strm s) (if Z.eqb (ds_wrap s) 2 then crc32_init else adler32_init)) in
  set_last_flush s (-2).

Definition LM (s : deflate_state) : deflate_state :=
  let s := set_window_size s (2 * ds_w_size s) in
  let s := clear_hash s in
  let s := set_max_lazy_match s (cfg_lazy (ds_level s)) in
  let s := set_good_match s (cfg_good (ds_level s)) in
  let s := set_nice_match s (cfg_nice (ds_level s)) in
  let s := set_max_chain_length s (cfg_chain (ds_level s)) in
  let s := set_strstart s 0 in
  let s := set_block_start s 0 in
  let s := set_lookahead s 0 in
  let s := set_insert s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  set_ins_h s 0.

Lemma lm_init_LM : forall s, lm_init s = LM s.
Proof. intros s. cbv beta zeta delta [lm_init LM]. rewrite (cfg_eta (ds_level (clear_hash (set_window_size s (2 * ds_w_size s))))). reflexivity. Qed.

Lemma deflateReset_eq : forall s, deflateStateCheck s = false -> 0 <= ds_wrap s ->
  deflateReset s = (LM (tr_init (RK0 s)), Z_OK).
Proof.
  intros s Hc Hw. cbv beta zeta delta [deflateReset deflateResetKeep RK0]. rewrite Hc.
  replace (ds_wrap (set_pending_out (set_pending (set_strm s (cset_data_type (cset_msg (cset_total_out (cset_total_in (ds_strm s) 0) 0) MSG_NULL) Z_UNKNOWN)) 0) 0) <? 0)
    with false by (symmetry; apply Z.ltb_ge; destruct s; cbn; exact Hw).
  cbv beta iota. change (Z_OK =? 0) with true. cbv beta iota. rewrite lm_init_LM. reflexivity.
Qed.

Section Proj.
  Variable g0 : Z -> Z.
Variable b0 : blk.
Variable cs : cstrm.
Variable wrap : Z.
Variable wbits : Z.
Variable memLevel : Z.
  Let s1 := s_setup g0 b0 cs wrap wbits memLevel.

End Proj.

Section Blks.
  Variable s1 : deflate_state.
Variable rw : option (blk * (Z -> Z)).
Variable rp : option (blk * (Z -> Z)).
Variable rh : option (blk * (Z -> Z)).
Variable rb : option (blk * (Z -> Z)).
Variable memLevel : Z.
  Let s5 := s_pb (s_lbs (s_hd (s_prv (s_win s1 rw) rp) rh) memLevel) rb.
  Lemma s5_window_blk : ds_window_blk s5 = option_map fst rw.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_prev_blk : ds_prev_blk s5 = option_map fst rp.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_head_blk : ds_head_blk s5 = option_map fst rh.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_pending_buf_blk : ds_pending_buf_blk s5 = option_map fst rb.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.

End Blks.
