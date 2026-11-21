(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure InfPure_w7 ItAPure ItBridgeA ItA_range InfPure_table.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition st_itab (st : ist) (isd : bool) (b nx : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (if isd then t_lb st else b) (if isd then b else t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).
Definition st_ret (st : ist) (rv : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Definition st_llok (st : ist) : ist :=
  IST CODELENS (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) 0
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) 0 (t_nx st) (t_whave st) (t_wnext st).

Lemma rng_fields : forall cx st lf cf st' cf',
  IDefs.RNG cx st lf cf ->
  t_cin st' = t_cin st -> t_cout st' = t_cout st -> t_bits st' = t_bits st -> t_hold st' = t_hold st -> t_out st' = t_out st ->
  t_last st' = t_last st -> t_flags st' = t_flags st -> t_length st' = t_length st -> t_offset st' = t_offset st -> t_extra st' = t_extra st ->
  t_ncode st' = t_ncode st -> t_nlen st' = t_nlen st -> t_ndist st' = t_ndist st -> t_whave st' = t_whave st -> t_wnext st' = t_wnext st ->
  t_dc st' = t_dc st ->
  0 <= t_ret st' < 18446744073709551616 -> 0 <= t_lb st' < 4294967296 -> 0 <= t_db st' < 4294967296 -> 0 <= t_shave st' < 4294967296 ->
  0 <= t_nx st' <= N_CODES -> match t_lc st' with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  IDefs.RNG cx st' lf cf'.
Proof.
  intros cx st lf cf st' cf' R E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 A1 A2 A3 A4 A5 A6 A7.
  unfold IDefs.RNG in *. cbv zeta in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16.
  destr_conj R. split_conj; try assumption; try lia.
Qed.

Lemma rng_ll_after : forall cx st lf cf cf' b nx,
  IDefs.RNG cx st lf cf -> 0 <= b < 4294967296 -> 0 <= nx <= N_CODES -> (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  IDefs.RNG cx (st_itab (st_lt st 7 0) false b nx) lf cf'.
Proof.
  intros cx st lf cf cf' b nx R Hb Hnx Rcf. pose proof R as R0. unfold IDefs.RNG in R0. cbv zeta in R0. destr_conj R0.
  eapply (rng_fields cx st lf cf); [exact R| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity | | | | | | | exact Rcf];
    unfold st_itab, st_lt; ist_cbn; unfold N_CODES in *; first [assumption | lia].
Qed.

Lemma ll_itc : forall cx st lf cf wf,
  sinv cx st lf cf -> t_mode st = LENLENS -> t_shave st = 19 -> (forall i, 0 <= i < 288 -> 0 <= wf i < 65536) ->
  itc CODES lf 0 19 0 7 cf wf.
Proof.
  intros cx st lf cf wf SI Hm Hsh Rwf. pose proof SI as (R & _ & _ & Mo).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by (unfold MODE in Mo; tauto).
  specialize (ML Hm). rewrite Hsh in ML. destruct ML as (_ & _ & _ & _ & _ & _ & _ & Hlf7).
  assert (L7 : forall i, 0 <= i < 19 -> lf i <= 7) by (apply order_covers; intros j0 Hj0; apply Hlf7; exact Hj0).
  unfold IDefs.RNG in R. cbv zeta in R. destr_conj R.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  clear - L7 Rlf Rcf Rwf.
  constructor.
  - exact Rlf.
  - exact Rcf.
  - exact Rwf.
  - lia.
  - unfold N_LENS. lia.
  - lia.
  - lia.
  - intros s Hs. rewrite Z.add_0_l. pose proof (L7 s Hs). lia.
  - intros _. split; [lia| split; [reflexivity|]]. intros s Hs. rewrite Z.add_0_l. apply L7. exact Hs.
  - intros X. discriminate X.
  - lia.
  - lia.
  - lia.
  - cbn [it_room]. unfold N_CODES, ENOUGH_LENS. lia.
Qed.

Lemma resA_eq : forall ty lf lo codes nx bits cf wf,
  resA ty lf lo codes nx bits cf wf = inflate_table ty (arr_init N_LENS lf) lo codes (arr_init N_CODES cf) nx bits (arr_init N_WORK wf).
Proof. reflexivity. Qed.
Lemma ll_bridge : forall lf cf wf r,
  itc CODES lf 0 19 0 7 cf wf -> r = resA CODES lf 0 19 0 7 cf wf ->
  (it_ret r = 0 -> tab_ok CODES (rdc (arr_get (it_tbl r)) (CDyn 0)) (it_bits r) (it_table r) = true
                   /\ 1 <= it_bits r <= 15 /\ 0 <= it_table r <= N_CODES)
  /\ (it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 7)
  /\ (forall i, 0 <= i < N_CODES -> 0 <= arr_get (it_tbl r) i < 4294967296)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r) i < 65536)
  /\ 0 <= it_bits r < 4294967296 /\ 0 <= it_table r <= N_CODES.
Proof.
  intros lf cf wf r C ER. pose proof (resA_ranges CODES lf 0 19 0 7 cf wf C) as (RT & RW).
  rewrite <- ER in RT, RW.
  pose proof (tab_ok_of_itable CODES lf cf wf (arr_get (it_tbl r)) 0 19 0 7) as BR0.
  pose proof (it_fail_shape CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) as FS0.
  cbv zeta in BR0, FS0.
  rewrite (resA_eq CODES lf 0 19 0 7 cf wf) in ER.
  rewrite <- ER in BR0, FS0. clear ER.
  destruct C as [Rlf Rcf Rwf C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11].
  assert (OK : it_ret r = 0 -> tab_ok CODES (rdc (arr_get (it_tbl r)) (CDyn 0)) (it_bits r) (it_table r) = true
                   /\ 1 <= it_bits r <= 15 /\ 0 <= it_table r <= N_CODES).
  { intros Hr. specialize (BR0 C1 C2 C3 C4 Rlf C5 C6 C7 C8 C9 C10 C11 Hr (fun i _ => eq_refl)).
    destruct BR0 as (T & B & TT & _). rewrite Z.sub_0_r in T. split; [exact T| split; [exact B|]].
    cbn [it_room] in TT. unfold N_CODES. clear - TT B.
    assert (0 < 2 ^ it_bits r) by (apply Z.pow_pos_nonneg; lia). lia. }
  split; [exact OK|]. split; [exact FS0|]. split; [exact RT|]. split; [exact RW|].
  destruct (Z.eq_dec (it_ret r) 0) as [Hr|Hr].
  - destruct (OK Hr) as (_ & B & TT). clear - B TT. lia.
  - destruct (FS0 Hr) as (E1 & E2). rewrite E1, E2. unfold N_CODES. lia.
Qed.
