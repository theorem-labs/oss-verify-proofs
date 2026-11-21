(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure InfPure_type InfPure_stored.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ck_st (st : ist) (m cin hold bits out : Z) : ist :=
  IST m (t_last st) (t_flags st) cin (t_cout st) hold bits out (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_ck : forall cx st lf cf m cin hold bits out,
  sinv cx st lf cf -> t_flags st = 0 ->
  (m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD) ->
  t_cin st <= cin <= c_n cx -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (out = t_out st /\ (CHECK < t_mode st -> CHECK < m)) \/ (out = c_osz cx - t_cout st /\ CHECK < m) ->
  sinv cx (ck_st st m cin hold bits out) lf cf.
Proof.
  intros cx st lf cf m cin hold bits out (R & W & P & Mo) Hf0 Hm Hc Hb Hh Hbc HW Hout.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin' cout hold' bits' out' ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags t_out t_cout] in *. icx_cbn. subst flags.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split]].
  - unfold RNG, ck_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, ck_st, Wm in *; icx_cbn. mode_consts. lia_std.
  - clear W P. unfold MODE in Mo. unfold MODE, ck_st; icx_cbn. clear Mo. mode_consts.
    destruct Hm as [Hm|[Hm|[Hm|Hm]]]; subst m;
    (split_conj; first [ right; lia_std | left; lia_std | intros X; exfalso; lia_std ]).
Qed.

Lemma meas_ck : forall cx st m cin hold bits out,
  8 * (c_n cx - cin) + bits < 8 * (c_n cx - t_cin st) + t_bits st \/
  (8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st /\ rank m < rank (t_mode st)) ->
  meas cx (ck_st st m cin hold bits out) < meas cx st.
Proof.
  intros cx st m cin hold bits out H.
  destruct H as [H | [H1 H2]].
  - apply meas_dec_W. unfold Wm, ck_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
  - apply meas_dec_rank; [| unfold ck_st; cbn; exact H2]. unfold Wm, ck_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
Qed.
