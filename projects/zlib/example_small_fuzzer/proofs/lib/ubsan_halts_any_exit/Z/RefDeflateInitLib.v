(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
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

Lemma di_a6_spec : forall wb, di_a6 wb = (if di_wrap wb =? 1 then 0 else 1).
Proof. intros wb. unfold di_a6, di_wrap. destruct (wb <? 0); [reflexivity|]. destruct (15 <? wb); reflexivity. Qed.

Lemma di_triple : forall wb,
  (if wb <? 0 then (0, - wb, wb <? -15) else if 15 <? wb then (2, wb - 16, false) else (1, wb, false))
  = (di_wrap wb, di_wb wb, (wb <? 0) && (wb <? -15)).
Proof.
  intros wb. unfold di_wrap, di_wb. destruct (wb <? 0); [reflexivity|]. destruct (15 <? wb); reflexivity.
Qed.


Lemma mod64_small : forall x, 0 <= x < 2 ^ 64 -> x mod 2 ^ 64 = x.
Proof. intros x Hx. apply Z.mod_small. exact Hx. Qed.

Lemma mod64_neg : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof.
  intros x Hx. rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma eqm1_iff : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> (x mod 2 ^ 64 = 18446744073709551615 <-> x = -1).
Proof.
  intros x Hx. destruct (Z_lt_le_dec x 0).
  - rewrite mod64_neg by lia. lia.
  - rewrite mod64_small by lia. lia.
Qed.

Lemma ltu_iff : forall c x, 0 <= c < 2 ^ 63 -> - 2 ^ 63 <= x < 2 ^ 63 ->
  (c < x mod 2 ^ 64 <-> (x < 0 \/ c < x)).
Proof.
  intros c x Hc Hx. destruct (Z_lt_le_dec x 0).
  - rewrite mod64_neg by lia. lia.
  - rewrite mod64_small by lia. lia.
Qed.

Lemma subnz_iff : forall x k, - 2 ^ 63 <= x - k < 2 ^ 63 -> ((x - k) mod 2 ^ 64 <> 0 <-> x <> k).
Proof.
  intros x k Hx. destruct (Z_lt_le_dec (x - k) 0).
  - rewrite mod64_neg by lia. lia.
  - rewrite mod64_small by lia. lia.
Qed.
Lemma addnz_iff : forall x k, - 2 ^ 63 <= x + k < 2 ^ 63 -> ((x + k) mod 2 ^ 64 <> 0 <-> x <> - k).
Proof.
  intros x k Hx. destruct (Z_lt_le_dec (x + k) 0).
  - rewrite mod64_neg by lia. lia.
  - rewrite mod64_small by lia. lia.
Qed.

Lemma memchk_iff : forall m, - 2 ^ 31 <= m < 2 ^ 31 ->
  (8 < szwrap 32 (m + -1) mod 2 ^ 64 <-> (m < 1 \/ 9 < m)).
Proof.
  intros m Hm. destruct (Z.eq_dec m (- 2 ^ 31)) as [->|Hne].
  - unfold szwrap. vm_compute. split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite szwrap32_small by lia. rewrite ltu_iff by lia. lia.
Qed.

Lemma wbchk_iff : forall w, 0 <= w < 2 ^ 31 ->
  (7 < szwrap 32 (w + -8) mod 2 ^ 64 <-> (w < 8 \/ 15 < w)).
Proof. intros w Hw. rewrite szwrap32_small by lia. rewrite ltu_iff by lia. lia. Qed.

Lemma negw_small : forall w, - 2 ^ 31 < w < 2 ^ 31 -> szwrap 32 (0 - w) = - w.
Proof. intros w Hw. rewrite szwrap32_small by lia. lia. Qed.

Lemma hash_shift_magic : forall m, 1 <= m <= 9 ->
  m * 2863311531 / 2 ^ 33 + 3 = (m + 7 + MIN_MATCH - 1) / MIN_MATCH.
Proof.
  intros m Hm. unfold MIN_MATCH.
  assert (H : m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; reflexivity.
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

Definition CFGTAB : Z := 0x2df20.

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

Lemma zrepeat_znth : forall n i, 0 <= i < n -> znth 0 (zrepeat 165 n) i = 165.
Proof.
  intros n i Hi. unfold znth, zrepeat.
  destruct (i <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
  apply nth_repeat_lt. lia.
Qed.
Lemma zlength_zrepeat : forall (v : Z) n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros v n Hn. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

Lemma arr_u16_of_a5 : forall off st n i, 0 <= i < n -> arr_get (arr_u16_of (fun _ => 165) off st n) i = A5_2.
Proof. intros off st n i Hi. unfold arr_u16_of. rewrite arr_get_init by lia. reflexivity. Qed.
Lemma arr_s32_of_a5 : forall off st n i, 0 <= i < n -> arr_get (arr_s32_of (fun _ => 165) off st n) i mod 2 ^ 32 = A5_4.
Proof. intros off st n i Hi. unfold arr_s32_of. rewrite arr_get_init by lia. reflexivity. Qed.
Lemma arr_u8_of_a5 : forall off st n i, 0 <= i < n -> arr_get (arr_u8_of (fun _ => 165) off st n) i = A5_1.
Proof. intros off st n i Hi. unfold arr_u8_of. rewrite arr_get_init by lia. reflexivity. Qed.
Lemma blk_bytes_a5 : forall n i, 0 <= i < n -> arr_get (blk_bytes (fun _ => 165) n) i = A5_1.
Proof. intros n i Hi. unfold blk_bytes. rewrite arr_get_init by lia. reflexivity. Qed.
Lemma blk_ush_a5 : forall n i, 0 <= i < n -> arr_get (blk_ush (fun _ => 165) n) i = A5_2.
Proof. intros n i Hi. unfold blk_ush. rewrite arr_get_init by lia. reflexivity. Qed.


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

  Lemma s_setup_w_size : ds_w_size s1 = Z.shiftl 1 wbits. Proof. reflexivity. Qed.
  Lemma s_setup_hash_size : ds_hash_size s1 = Z.shiftl 1 (memLevel + 7). Proof. reflexivity. Qed.
  Lemma s_setup_hash_bits : ds_hash_bits s1 = memLevel + 7. Proof. reflexivity. Qed.
  Lemma s_setup_w_bits : ds_w_bits s1 = wbits. Proof. reflexivity. Qed.
  Lemma s_setup_wrap : ds_wrap s1 = wrap. Proof. reflexivity. Qed.
  Lemma s_setup_status : ds_status s1 = INIT_STATE. Proof. reflexivity. Qed.
  Lemma s_setup_self : ds_self_blk s1 = b0. Proof. reflexivity. Qed.
  Lemma s_setup_strm : ds_strm s1 = cs. Proof. reflexivity. Qed.
End Proj.

Lemma s_win_w_size : forall s rw, ds_w_size (s_win s rw) = ds_w_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_win_hash_size : forall s rw, ds_hash_size (s_win s rw) = ds_hash_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_prv_w_size : forall s rp, ds_w_size (s_prv s rp) = ds_w_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_prv_hash_size : forall s rp, ds_hash_size (s_prv s rp) = ds_hash_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_hd_hash_size : forall s rh, ds_hash_size (s_hd s rh) = ds_hash_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_hd_w_size : forall s rh, ds_w_size (s_hd s rh) = ds_w_size s.
Proof. intros s [[b g]|]; reflexivity. Qed.
Lemma s_lbs_lit_bufsize : forall s m, ds_lit_bufsize (s_lbs s m) = Z.shiftl 1 (m + 6).
Proof. intros s m; reflexivity. Qed.
Lemma s_lbs_w_size : forall s m, ds_w_size (s_lbs s m) = ds_w_size s.
Proof. intros s m; reflexivity. Qed.
Lemma s_lbs_hash_size : forall s m, ds_hash_size (s_lbs s m) = ds_hash_size s.
Proof. intros s m; reflexivity. Qed.
Lemma s_pb_lit_bufsize : forall s rb, ds_lit_bufsize (s_pb s rb) = ds_lit_bufsize s.
Proof. intros s [[b g]|]; reflexivity. Qed.

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
  Lemma s5_self_blk : ds_self_blk s5 = ds_self_blk s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_w_size : ds_w_size s5 = ds_w_size s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_hash_size : ds_hash_size s5 = ds_hash_size s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_lit_bufsize : ds_lit_bufsize s5 = Z.shiftl 1 (memLevel + 6).
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_status : ds_status s5 = ds_status s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_wrap : ds_wrap s5 = ds_wrap s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
  Lemma s5_strm : ds_strm s5 = ds_strm s1.
  Proof. subst s5. destruct rw as [[]|], rp as [[]|], rh as [[]|], rb as [[]|]; reflexivity. Qed.
End Blks.
