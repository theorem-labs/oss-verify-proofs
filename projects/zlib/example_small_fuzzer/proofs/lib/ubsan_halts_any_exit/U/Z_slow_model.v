(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk DeflateOverlay FlushBlockModel FillWinModel SendModel RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 ZCorollaries SymEx2Expr.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZCorollaries OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma tr_flush_bits_strm' : forall s, ds_strm (tr_flush_bits s) = ds_strm s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.

Definition fbo1 (X : deflate_state) (last : Z) : deflate_state := tr_flush_block X (fb_buf X) (fb_len X) last.
Definition fbo2 (X : deflate_state) (last : Z) : deflate_state := set_block_start (fbo1 X last) (ds_strstart (fbo1 X last)).
Definition fbo3 (X : deflate_state) (last : Z) : deflate_state := tr_flush_bits (fbo2 X last).

Lemma fbo_eq : forall X last,
  flush_block_only X last = (if fp_len (fbo3 X last) =? 0 then fbo3 X last else fp_tail (fbo3 X last) (fp_len (fbo3 X last))).
Proof. intros X last. unfold flush_block_only. cbv zeta. rewrite flush_pending_eq. unfold fbo3, fbo2, fbo1, fb_buf, fb_len. reflexivity. Qed.

Lemma tfb_keep : forall X last,
  ds_strstart (fbo1 X last) = ds_strstart X /\ ds_lookahead (fbo1 X last) = ds_lookahead X
  /\ cs_out_rev (ds_strm (fbo1 X last)) = cs_out_rev (ds_strm X)
  /\ cs_avail_out (ds_strm (fbo1 X last)) = cs_avail_out (ds_strm X).
Proof.
  intros X last. unfold fbo1.
  pose proof (tfb_lz_view X (fb_buf X) (fb_len X) last) as V. unfold lz_view in V.
  split; [congruence|]. split; [congruence|].
  rewrite tr_flush_block_strm. destruct (_ && _); [destruct (ds_strm X)|]; split; reflexivity.
Qed.

Lemma fbo3_strm : forall X last, ds_strm (fbo3 X last) = ds_strm (fbo1 X last).
Proof. intros X last. unfold fbo3, fbo2. rewrite tr_flush_bits_strm'. reflexivity. Qed.

Lemma cs_emit_out_len' : forall c l, length (cs_out_rev (cs_emit c l)) = (length (cs_out_rev c) + length l)%nat.
Proof.
  intros c l. unfold cs_emit. destruct c as [ci cn ca o cao cti cto cm cd cad]. cbn [DeflateState.cs_out_rev cset_out_rev].
  rewrite rev_append_rev, length_app, length_rev. lia.
Qed.

Lemma fp_tail_out : forall s len,
  cs_out_rev (ds_strm (fp_tail s len)) = cs_out_rev (cs_emit (ds_strm s) (arr_slice (ds_pending_buf s) (ds_pending_out s) len)).
Proof. intros s len. unfold fp_tail. cbv zeta. destruct (_ - _ =? 0); reflexivity. Qed.

Lemma fbo_out_mono : forall X last,
  (length (cs_out_rev (ds_strm X)) <= length (cs_out_rev (ds_strm (flush_block_only X last))))%nat.
Proof.
  intros X last. rewrite fbo_eq. destruct (tfb_keep X last) as (_ & _ & EO & _).
  pose proof (fbo3_strm X last) as ES.
  destruct (fp_len (fbo3 X last) =? 0).
  - rewrite ES, EO. lia.
  - rewrite fp_tail_out, cs_emit_out_len', ES, EO. lia.
Qed.

Lemma flush_ok_fbo : forall X last, flush_ok X last -> ds_lit_bufsize X = 16384 ->
  fb_safe X (fb_buf X) (fb_len X) last /\ SendModel.BINV 65536 X /\ 0 <= ds_strstart X - ds_block_start X < 2 ^ 32
  /\ - 2 ^ 63 <= ds_block_start X /\ 0 <= ds_strstart X <= 2 * ds_w_size X /\ 0 <= ds_lookahead X <= 2 * ds_w_size X
  /\ (forall j, 0 <= j < 2 * ds_w_size X -> 0 <= arr_get (ds_window X) j < 256)
  /\ SendModel.BINV 65536 (fbo2 X last) /\ ds_pending (fbo3 X last) <= 65536
  /\ 0 <= ds_pending (fbo3 X last) < 2 ^ 31 /\ 0 <= ds_pending_out (fbo3 X last)
  /\ ds_pending_out (fbo3 X last) + fp_len (fbo3 X last) <= 65536
  /\ 0 <= cs_total_out (ds_strm (fbo3 X last)) < 2 ^ 64.
Proof. intros X last F LB. unfold flush_ok in F. rewrite LB in F. exact F. Qed.

Lemma fbo_buf_ok : forall X last, flush_ok X last -> ds_w_size X = 32768 ->
  fb_buf_okP (fb_buf X) (fb_len X) /\ fb_len X = ds_strstart X - ds_block_start X
  /\ (0 <= ds_block_start X -> fb_buf X = Some (ds_block_start X)) /\ (ds_block_start X < 0 -> fb_buf X = None).
Proof.
  intros X last F Hw. unfold flush_ok in F. cbv zeta in F. destruct F as (_ & _ & Hd & _ & Hs & _).
  apply (fb_buf_ok_core X); [exact Hd| exact Hs| lia].
Qed.


Lemma land_low_irrel : forall a b hm, 0 <= hm < 2^31 -> a mod 2^32 = b mod 2^32 -> Z.land a hm = Z.land b hm.
Proof.
  intros a b hm Hm E. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec. destruct (Z.ltb_spec n 31) as [Hl|Hl].
  - f_equal. rewrite <- (Z.mod_pow2_bits_low a 32 n), <- (Z.mod_pow2_bits_low b 32 n) by lia. rewrite E. reflexivity.
  - replace (Z.testbit hm n) with false; [rewrite !andb_false_r; reflexivity|]. symmetry.
    destruct (Z.eq_dec hm 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    assert (Z.log2 hm < 31) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lxor_mod32 : forall a c, (Z.lxor a c) mod 2^32 = Z.lxor (a mod 2^32) (c mod 2^32).
Proof. intros a c. apply SymEx2Expr.lxor_mod. lia. Qed.

Lemma swrap32_mod64_mod32 : forall v, (bv_swrap 32 v mod 2^64) mod 2^32 = v mod 2^32.
Proof.
  intros v. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma hash_mach : forall s ih c, 0 <= ds_hash_shift s < 32 -> 0 <= ds_hash_mask s < 2^31 ->
  Z.land (Z.lxor (bv_swrap 32 (Z.shiftl ih (ds_hash_shift s mod 32)) mod 18446744073709551616) (c mod 18446744073709551616)) (ds_hash_mask s)
  = update_hash s ih c.
Proof.
  intros s ih c Hs Hm. unfold update_hash. rewrite (Z.mod_small (ds_hash_shift s) 32) by lia.
  apply land_low_irrel; [exact Hm|]. rewrite !lxor_mod32. change 18446744073709551616 with (2^64).
  rewrite swrap32_mod64_mod32, wrap32_mod, Z.mod_mod by lia. f_equal.
  apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.

Lemma update_hash_range : forall s ih c, 0 <= ds_hash_mask s -> 0 <= update_hash s ih c <= ds_hash_mask s.
Proof. intros s ih c Hm. unfold update_hash. rewrite Z.land_comm. apply SymEx2Expr.land_upper. exact Hm. Qed.

Lemma shl32_shr31 : forall h, 0 <= h < 2^32 -> Z.shiftr (Z.shiftl h 32 mod 18446744073709551616) 31 = 2 * h.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.


Definition ILI (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2^31 /\ ds_hash_mask X = 32767 /\ ds_w_mask X = 32767 /\ 0 <= ds_hash_shift X < 32
  /\ (forall j, 0 <= j < 65536 -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < 32768 -> 0 <= arr_get (ds_head X) j < 65536).

Lemma ILI_step : forall X mi, ILI X ->
  ILI (insl_st X mi) /\ ds_strstart (insl_st X mi) = ds_strstart X + 1 /\ ds_prev_length (insl_st X mi) = ds_prev_length X - 1.
Proof.
  intros X mi (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb).
  unfold ILI, insl_st, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str. destruct (ds_strstart X + 1 <=? mi); dsred.
  - pose proof (update_hash_range (set_strstart X (ds_strstart X + 1)) (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 1 + 2)) ltac:(dsred; lia)) as Hh.
    dsred in Hh. rewrite Hhm in Hh.
    set (h := update_hash _ _ _) in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
    intros j Hj; rewrite arr_get_set; destruct (_ && _); [pose proof (wrap16_range (ds_strstart X + 1)); lia | apply Hhb; exact Hj].
  - repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
Qed.

Lemma slow_insert_last : forall X mi, ds_prev_length X = 1 -> deflate_slow_insert 1 X mi = insl_st X mi.
Proof.
  intros X mi H. rewrite deflate_slow_insert_step. cbv zeta.
  replace (ds_prev_length (insl_st X mi)) with 0 by (unfold insl_st; dsred; lia). reflexivity.
Qed.

Lemma slow_insert_more : forall n X mi, ds_prev_length X = Z.of_nat (S (S n)) ->
  deflate_slow_insert (S (S n)) X mi = deflate_slow_insert (S n) (insl_st X mi) mi.
Proof.
  intros n X mi H. rewrite deflate_slow_insert_step. cbv zeta.
  replace (ds_prev_length (insl_st X mi) =? 0) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. unfold insl_st. dsred. lia.
Qed.
