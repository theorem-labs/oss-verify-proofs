(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import InfPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition hd_st (st : ist) (m flags cin hold bits : Z) : ist :=
  IST m (t_last st) flags cin (t_cout st) hold bits (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_hd : forall cx st lf cf m flags cin hold bits,
  sinv cx st lf cf -> (t_mode st <? CHECK) = true ->
  (m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD) ->
  (flags = t_flags st \/ flags = 0) -> (flags = -1 -> m = HEAD \/ m = BAD) ->
  t_cin st <= cin <= c_n cx -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin ->
  8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st ->
  sinv cx (hd_st st m flags cin hold bits) lf cf.
Proof.
  intros cx st lf cf m flags cin hold bits (R & W & P & Mo) Hlt Hm Hfl Hfm Hc Hb Hh Hbc HW. apply Z.ltb_lt in Hlt.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags' cin' cout hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits t_flags] in *. icx_cbn.
  unfold IDefs.RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split]].
  - unfold IDefs.RNG, hd_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, hd_st, Wm in *; icx_cbn. mode_consts. lia_std.
  - pose proof (proj1 (proj2 Mo)) as Mf. clear W P. unfold MODE in Mo. unfold MODE, hd_st; icx_cbn.
    assert (Hco : flags' = -1 -> cout = 0) by (intros E; exact (proj2 (Mf E))). clear Mo Mf. mode_consts.
    destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]]]; subst m;
    (split_conj;
      first [ right; lia_std | left; lia_std | intros X; exfalso; lia_std
            | intros X; split; [ destruct (Hfm X); [left | right]; lia_std | apply Hco; lia_std ] ]).
Qed.

Lemma meas_hd : forall cx st m flags cin hold bits,
  8 * (c_n cx - cin) + bits < 8 * (c_n cx - t_cin st) + t_bits st \/
  (8 * (c_n cx - cin) + bits <= 8 * (c_n cx - t_cin st) + t_bits st /\ rank m < rank (t_mode st)) ->
  meas cx (hd_st st m flags cin hold bits) < meas cx st.
Proof.
  intros cx st m flags cin hold bits H. unfold meas, Wm, hd_st. destruct cx, st. icx_cbn.
  pose proof (rank_range m) as RR1. pose proof (rank_range t_mode) as RR2. destruct H as [HA | [HB HC]]; lia.
Qed.
