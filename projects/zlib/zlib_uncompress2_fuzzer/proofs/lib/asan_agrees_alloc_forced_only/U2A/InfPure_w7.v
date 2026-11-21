(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.
Ltac prog_transfer P :=
  first [ exact P
        | let P1 := fresh in let P2 := fresh in let P3 := fresh in
          destruct P as (P1 & P2 & P3); unfold PROG; icx_cbn; split; [exact P1 | split; [exact P2 |]];
          first [ exact P3
                | let E := fresh in let C := fresh in
                  destruct P3 as [E | [E C]];
                  first [ left; exact E
                        | right; split; [exact E | clear - C; modes_cbv; lia_std]
                        | exfalso; clear - C; modes_cbv; lia_std ] ] ].

Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 32768 with (2 ^ 15); apply pow2_le; lia]. Qed.
Lemma pow2_48 : forall k, 0 <= k <= 48 -> 1 <= 2 ^ k <= 281474976710656.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 281474976710656 with (2 ^ 48); apply pow2_le; lia]. Qed.
Lemma pow2_add8 : forall k, 0 <= k -> 2 ^ (k + 8) = 256 * 2 ^ k.
Proof. intros. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. Qed.

Lemma land_ones_range : forall a k, 0 <= k -> 0 <= Z.land a (2 ^ k - 1) < 2 ^ k.
Proof.
  intros a k Hk. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by exact Hk. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma land_mask_r : forall x k, 0 <= k -> 0 <= Z.land x (2 ^ k - 1) < 2 ^ k.
Proof. intros. apply land_ones_range. assumption. Qed.
Lemma land_mask_l : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k - 1) x < 2 ^ k.
Proof. intros. rewrite Z.land_comm. apply land_ones_range. assumption. Qed.
Lemma srl_hold : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= bits <= 63 -> 0 <= k <= 63 ->
  Z.shiftr (hold mod 18446744073709551616) (k mod 64) = hold / 2 ^ k.
Proof.
  intros hold bits k Hh Hb Hk.
  assert (2 ^ bits <= 2 ^ 63) by (apply pow2_le; lia).
  rewrite (Z.mod_small k 64) by lia. rewrite Z.mod_small by (change 18446744073709551616 with (2 * 2 ^ 63); lia).
  apply Z.shiftr_div_pow2. lia.
Qed.
Lemma hold_shr_bound : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= k <= bits ->
  0 <= hold / 2 ^ k < 2 ^ (bits - k).
Proof.
  intros hold bits k Hh Hk. pose proof (pow2_pos k ltac:(lia)).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (bits - k)) with bits by lia. lia.
Qed.
Lemma shl_byte : forall b s, 0 <= b < 256 -> 0 <= s <= 63 -> Z.shiftl b (s mod 64) = b * 2 ^ s.
Proof. intros b s Hb Hs. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma hold_pull1 : forall hold bits b, 0 <= hold < 2 ^ bits -> 0 <= bits -> 0 <= b < 256 ->
  0 <= b * 2 ^ bits /\ 0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8).
Proof.
  intros hold bits b Hh Hbits Hb. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (pow2_pos bits Hbits). nia.
Qed.
Lemma shiftl_2 : forall x, Z.shiftl x (2 mod 64) = 4 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (2 mod 64)) with 4. lia. Qed.
Lemma zext32_shift30 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (30 mod 64) = 4 * x.
Proof.
  intros x Hx. change (30 mod 64) with 30. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shiftl_1_pow : forall k, 0 <= k -> Z.shiftl 1 k = 2 ^ k.
Proof. intros. rewrite Z.shiftl_1_l. reflexivity. Qed.
Lemma land_255_id : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as E. rewrite (Z.lxor_lor _ _ D), Z.lor_ldiff_and in E.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_range_r : forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof. intros a b Hb. split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]. Qed.

Lemma shiftl_3 : forall x, Z.shiftl x (3 mod 64) = 8 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (3 mod 64)) with 8. lia. Qed.

Definition bad_ofP (st : ist) : ist :=
  IST BAD (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma sinv_bad_ofP : forall cx st lf cf, sinv cx st lf cf -> sinv cx (bad_ofP st) lf cf.
Proof.
  intros cx st lf cf (R & W & P & Mo). destruct cx, st. unfold sinv, bad_ofP in *. icx_cbn.
  split; [exact R | split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]].
  destruct Mo as (Mr & Mf & Mrest). unfold MODE in *. icx_cbn.
  split; [unfold reach; cbv [HEAD DICTID MEM BAD]; right; lia_std |].
  split; [intros Hf; destruct (Mf Hf) as [_ Hc]; split; [right; reflexivity | exact Hc] |].
  clear. split_conj; mode_vacuous.
Qed.
Lemma meas_bad_ofP : forall cx st, meas cx (bad_ofP st) + rank (t_mode st) = meas cx st.
Proof. intros cx st. destruct cx, st. unfold meas, Wm, bad_ofP. icx_cbn. change (rank BAD) with 0. lia_std. Qed.



Definition st_pull (st : ist) (ci H B : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma sinv_pull : forall cx st lf cf ci H B,
  sinv cx st lf cf ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  sinv cx (st_pull st ci H B) lf cf /\ meas cx (st_pull st ci H B) <= meas cx st.
Proof.
  intros cx st lf cf ci H B (R & W & P & Mo) H1 H2 H3 H4 H5 H6 H7 H8.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_pull, meas, Wm in *. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  split; [split; [| split; [exact W | split; [| exact Mo]]] |].
  - clear W Mo P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mo. unfold PROG, Wm. icx_cbn. clear - P1 P2 P3 H1 H8. lia_std.
  - clear - H8. lia_std.
Qed.

Definition st_dx (st : ist) (m off ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) off ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma sinv_to_distext : forall cx st lf cf off ex,
  sinv cx st lf cf -> t_mode st = DIST -> 0 <= off -> off < 65536 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_dx st DISTEXT off ex) lf cf /\ meas cx (st_dx st DISTEXT off ex) < meas cx st.
Proof.
  intros cx st lf cf off ex SI Hm Ho1 Ho2 He1 He2.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_dx, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (DIST = HEAD \/ DIST = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP DIST -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST DIST last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mold : DIST = DIST -> 1 <= length /\ length < 65536) by mode_get Mo. specialize (Mold eq_refl).
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive Mold. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Mold Ho1 Ho2 He1 He2; destr_conj Mold; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_match : forall cx st lf cf off,
  sinv cx st lf cf -> t_mode st = DISTEXT -> 0 <= off -> off < 98304 ->
  sinv cx (st_dx st MATCH off (t_extra st)) lf cf /\ meas cx (st_dx st MATCH off (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf off SI Hm Ho1 Ho2.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_dx, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (DISTEXT = HEAD \/ DISTEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP DISTEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST DISTEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mold : DISTEXT = DISTEXT -> extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536) by mode_get Mo. specialize (Mold eq_refl).
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive Mold. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Mold Ho1 Ho2; destr_conj Mold; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.


Definition st_upd (st : ist) (m copy len' : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st + copy) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len' (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_upd : forall cx st lf cf m copy len',
  sinv cx st lf cf -> (t_mode st = MATCH \/ t_mode st = LIT) ->
  1 <= copy -> copy <= c_osz cx - t_cout st -> 0 <= len' -> len' <= t_length st ->
  ((m = MATCH /\ t_mode st = MATCH /\ 1 <= len') \/ m = LEN) ->
  sinv cx (st_upd st m copy len') lf cf /\ meas cx (st_upd st m copy len') < meas cx st.
Proof.
  intros cx st lf cf m copy len' (R & W & P & Mo) Hmode Hc1 Hc3 Hl1 Hl2 Hm.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_upd, meas, Wm in *. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mr : reach mode) by mode_get Mo.
  assert (Mf : flags = -1 -> (mode = HEAD \/ mode = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP mode -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mma : mode = MATCH -> 1 <= length /\ length < 65536 /\ offset < 98304) by mode_get Mo.
  clear Mo.
  assert (Hfl : flags <> -1) by (intros E; destruct (Mf E) as [HM _]; clear - HM Hmode; cbv [MATCH LIT HEAD BAD] in *; lia_std).
  assert (TL : tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf)
    by (apply Mlive; clear - Hmode; unfold codes_liveP; cbv [MATCH LIT LEN_] in *; lia_std).
  assert (HMA : m = MATCH -> 1 <= len' /\ len' < 65536 /\ offset < 98304)
    by (intros E; destruct Hm as [(_ & E2 & E3) | E'];
        [destruct (Mma E2) as (A1 & A2 & A3); clear - A2 A3 E3 Hl2; lia_std | clear - E E'; cbv [MATCH LEN] in *; lia_std]).
  clear Mma.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 Mr Mf Mlive TL HMA. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 Hc1 Hmode Hm. unfold PROG, Wm. icx_cbn.
    split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct Hmode as [-> | ->]; destruct Hm as [(-> & _) | ->]; modes_cbv; lia_std ].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear - Hm; unfold reach; cbv [HEAD DICTID MEM MATCH LEN] in *; lia_std |].
    split; [intros E; exfalso; exact (Hfl E) |].
    split_conj; first [ intros _; exact TL | exact HMA
                      | destruct Hm as [(-> & _) | ->]; mode_vacuous ].
  - clear - Hm Hmode Hc1. assert (rank m <= 18) by (destruct Hm as [(-> & _)| ->]; [change (rank MATCH) with 14 | change (rank LEN) with 18]; lia_std).
    assert (13 <= rank mode) by (destruct Hmode as [-> | ->]; [change (rank MATCH) with 14 | change (rank LIT) with 13]; lia_std). lia_std.
Qed.


Definition st_le (st : ist) (m len ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len (t_offset st) ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_len_set : forall cx st lf cf m len,
  sinv cx st lf cf -> t_mode st = LEN -> (m = LEN \/ m = LIT \/ m = TYPE) -> 0 <= len -> len < 4294967296 ->
  sinv cx (st_le st m len (t_extra st)) lf cf.
Proof.
  intros cx st lf cf m len SI Hm Hm' Hl1 Hl2.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split; [prog_transfer P|]]].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
Qed.

Lemma sinv_to_lenext : forall cx st lf cf len ex,
  sinv cx st lf cf -> t_mode st = LEN -> 1 <= len -> len <= 32768 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_le st LENEXT len ex) lf cf /\ meas cx (st_le st LENEXT len ex) < meas cx st.
Proof.
  intros cx st lf cf len ex SI Hm Hl1 Hl2 He1 He2.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2 He1 He2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_dist : forall cx st lf cf len,
  sinv cx st lf cf -> t_mode st = LENEXT -> 1 <= len -> len < 65536 ->
  sinv cx (st_le st DIST len (t_extra st)) lf cf /\ meas cx (st_le st DIST len (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf len SI Hm Hl1 Hl2.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LENEXT = HEAD \/ LENEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LENEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.


Definition st_fast (st : ist) (m ci co H B : Z) : ist :=
  IST m (t_last st) (t_flags st) ci co H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_after_fast : forall cx st lf cf m ci co H B,
  sinv cx st lf cf -> t_mode st = LEN ->
  0 <= ci -> ci <= c_n cx -> t_cout st <= co -> co <= c_osz cx ->
  0 <= B -> B <= 7 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B + (c_osz cx - co) < 8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st) ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = LEN \/ m = TYPE \/ m = BAD) ->
  sinv cx (st_fast st m ci co H B) lf cf /\ meas cx (st_fast st m ci co H B) < meas cx st.
Proof.
  intros cx st lf cf m ci co H B SI Hm Hci1 Hci2 Hco1 Hco2 HB1 HB2 HH1 HH2 HBc HW HI Hm'.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_fast, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  destruct P as (P1 & P2 & P3). unfold PROG, Wm in P1, P2, P3 |- *. icx_cbn.
  split; [split; [| split; [exact W | split]] |].
  - clear W Mf Mlive P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mf Mlive Hm'. split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std] ].
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros HL; destruct Hm' as [-> | [-> | ->]];
              [ apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std ]
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
  - clear - HW Hm'. pose proof (rank_range m) as RR. change (rank LEN) with 18. lia_std.
Qed.


Lemma sinv_len_ : forall cx st lf cf,
  sinv cx st lf cf -> t_mode st = LEN_ ->
  sinv cx (st_le st LEN (t_length st) (t_extra st)) lf cf /\ meas cx (st_le st LEN (t_length st) (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf SI Hm.
  destruct SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN_ = HEAD \/ LEN_ = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN_ -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  split; [split; [exact R | split; [exact W | split; [prog_transfer P|]]] |].
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.


Lemma sinv_lenext_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = LENEXT ->
  t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  assert (X : LENEXT = LENEXT -> extra <= 15 /\ 1 <= length /\ length <= 32768) by mode_get Mo. exact (X eq_refl).
Qed.
Lemma sinv_dist_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = DIST -> 1 <= t_length st /\ t_length st < 65536.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  assert (X : DIST = DIST -> 1 <= length /\ length < 65536) by mode_get Mo. exact (X eq_refl).
Qed.
Lemma sinv_distext_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = DISTEXT ->
  t_extra st <= 15 /\ 1 <= t_length st /\ t_length st < 65536 /\ t_offset st < 65536.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  assert (X : DISTEXT = DISTEXT -> extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536) by mode_get Mo. exact (X eq_refl).
Qed.
Lemma sinv_match_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = MATCH ->
  1 <= t_length st /\ t_length st < 65536 /\ t_offset st < 98304.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  assert (X : MATCH = MATCH -> 1 <= length /\ length < 65536 /\ offset < 98304) by mode_get Mo. exact (X eq_refl).
Qed.

Ltac st_norm H :=
  unfold st_le, st_pull, st_dx, st_upd, st_fast in H;
  cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.
