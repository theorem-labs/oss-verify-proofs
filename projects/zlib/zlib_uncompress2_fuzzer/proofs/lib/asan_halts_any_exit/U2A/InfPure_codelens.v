(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr InfPure InfPure_w7 ItAPure ItBridgeA InfPure_table.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition st_cl (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_cl : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = CODELENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= t_nlen st + t_ndist st ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' i <= 15) ->
  sinv cx (st_cl st ci H B j) lf' cf /\ meas cx (st_cl st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_cl, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). destruct MC as (A1 & A2 & A3 & A4 & _ & _ & CT). clear Mo.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf CT. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try assumption; unfold ctable_live; cbn [t_lc t_lb t_nx]; exact CT |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

Lemma cl_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = CODELENS ->
  257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\ 0 <= t_shave st /\ t_shave st <= t_nlen st + t_ndist st
  /\ (forall i, 0 <= i < t_shave st -> lf i <= 15)
  /\ t_lc st = CDyn 0 /\ 1 <= t_lb st /\ t_lb st <= 15 /\ 0 <= t_nx st /\ t_nx st <= 1444
  /\ tab_ok CODES (rdc cf (CDyn 0)) (t_lb st) (t_nx st) = true
  /\ (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) /\ (forall i, 0 <= i < 1444 -> 0 <= cf i < 4294967296).
Proof.
  intros cx st lf cf (R & _ & _ & Mo) Hm.
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\ t_shave st <= t_nlen st + t_ndist st /\
            (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by (unfold MODE in Mo; tauto).
  destruct (MC Hm) as (A1 & A2 & A3 & A4 & A5 & A6 & (C1 & C2 & C3 & C4 & C5)).
  unfold IDefs.RNG in R. cbv zeta in R. cbv [N_LENS N_CODES] in *. destr_conj R.
  split_conj; try assumption; try lia.
Qed.

Lemma ctab_bits : forall cf lb nx i,
  tab_ok CODES (rdc cf (CDyn 0)) lb nx = true -> 0 <= i < 2 ^ lb -> 1 <= code_bits (cf i) <= lb /\ 2 ^ lb <= nx.
Proof.
  intros cf lb nx i T Hi. pose proof (tab_root_entry CODES (rdc cf (CDyn 0)) lb nx i T Hi) as (X & _ & Y & _).
  unfold rdc in X. rewrite Z.add_0_l in X. split; [exact X | exact Y].
Qed.

Lemma lens15_upd : forall (lf : Z -> Z) j v, (forall i, 0 <= i < j -> lf i <= 15) -> v <= 15 ->
  forall i, 0 <= i < j + 1 -> fupd lf j v i <= 15.
Proof. intros lf j v H Hv i Hi. unfold fupd. destruct (Z.eqb_spec i j); [exact Hv| apply H; lia]. Qed.

Definition buf_ok (cx : ictx) (st : ist) (ci H B : Z) : Prop :=
  t_cin st <= ci /\ ci <= c_n cx /\ 0 <= B /\ B <= 40 /\ 0 <= H /\ H < 2 ^ B /\ B <= 8 * ci
  /\ 8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st.

Lemma buf_ok_pulled : forall cx st lf cf ci H B, sinv cx st lf cf ->
  t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 -> buf_ok cx st ci H B.
Proof.
  intros cx st lf cf ci H B (R & _) HC HB HH H40. unfold IDefs.RNG in R. cbv zeta in R.
  destruct R as (R1 & R2 & _ & _ & _ & R6 & R7 & R8 & R9 & R10 & _). unfold buf_ok. lia.
Qed.

Lemma buf_ok_drop : forall cx st ci H B k, buf_ok cx st ci H B -> 0 <= k <= B -> buf_ok cx st ci (H / 2 ^ k) (B - k).
Proof.
  intros cx st ci H B k (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) Hk. unfold buf_ok.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ B = 2 ^ k * 2 ^ (B - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (0 <= H / 2 ^ k) by (apply Z.div_pos; lia).
  assert (H / 2 ^ k < 2 ^ (B - k)) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma sinv_clb : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = CODELENS -> buf_ok cx st ci H B ->
  0 <= j -> j <= t_nlen st + t_ndist st ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' i <= 15) ->
  sinv cx (st_cl st ci H B j) lf' cf /\ meas cx (st_cl st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' SI Hm (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) Hj0 Hj1 R L.
  exact (sinv_cl cx st lf cf ci H B j lf' SI Hm A1 A2 A3 A4 A5 A6 A7 A8 Hj0 Hj1 R L).
Qed.

Lemma sinv_clb_leave : forall cx st lf cf ci H B,
  sinv cx st lf cf -> buf_ok cx st ci H B -> sinv cx (st_pull st ci H B) lf cf.
Proof.
  intros cx st lf cf ci H B SI (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (proj1 (sinv_pull cx st lf cf ci H B SI A1 A2 A3 A4 A5 A6 A7 A8)).
Qed.
