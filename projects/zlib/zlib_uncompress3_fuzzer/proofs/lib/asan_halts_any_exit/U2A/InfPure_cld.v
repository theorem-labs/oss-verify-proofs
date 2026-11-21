(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure InfPure_w7 ItAPure ItBridgeA ItA_range InfPure_table InfPure_itab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition st_tab (st : ist) (m rv lb : Z) (dc : codeptr) (db nx : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) dc lb db
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).

Lemma sinv_cl_bad : forall cx st lf cf cf' rv lb dc db nx,
  sinv cx st lf cf -> t_mode st = CODELENS -> 0 <= rv < 18446744073709551616 ->
  0 <= lb < 4294967296 -> 0 <= db < 4294967296 ->
  match dc with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end -> 0 <= nx -> nx <= N_CODES ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st BAD rv lb dc db nx) lf cf' /\ meas cx (st_tab st BAD rv lb dc db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' rv lb dc db nx (R & W & P & Mo) Hm Hrv Hlb Hdb Hdc Hnx1 Hnx2 Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_cl_len_ : forall cx st lf cf cf' lb o2 db nx,
  sinv cx st lf cf -> t_mode st = CODELENS ->
  1 <= lb -> lb <= 15 -> 1 <= db -> db <= 15 -> 0 <= o2 -> o2 <= nx -> nx <= N_CODES ->
  tab_ok LENS (rdc cf' (CDyn 0)) lb o2 = true -> tab_ok DISTS (rdc cf' (CDyn o2)) db (nx - o2) = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) lf cf' /\ meas cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' lb o2 db nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hdb1 Hdb2 Ho1 Ho2 Hnx TL TD Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf TL TD. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [mode_vacuous |].
    split; [intros _; unfold tables_live; cbn [t_lc t_dc t_lb t_db t_nx]; cbv [N_CODES]; split_conj; try reflexivity; try assumption; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_cl_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = CODELENS ->
  257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\ t_shave st <= t_nlen st + t_ndist st
  /\ (forall i, 0 <= i < t_shave st -> lf i <= 15).
Proof.
  intros cx st lf cf (_ & _ & _ & Mo) Hm.
  assert (ML : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by (unfold MODE in Mo; tauto).
  destruct (ML Hm) as (A & B & C & D & E & F & _). tauto.
Qed.

Lemma cl_itc_lens : forall cx st lf cf wf,
  sinv cx st lf cf -> t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> (forall i, 0 <= i < 288 -> 0 <= wf i < 65536) ->
  itc LENS lf 0 (t_nlen st) 0 9 cf wf.
Proof.
  intros cx st lf cf wf SI Hm Hsh Rwf. destruct (sinv_cl_facts _ _ _ _ SI Hm) as (N1 & N2 & D1 & D2 & SH & L15).
  pose proof SI as (R & _). unfold IDefs.RNG in R. cbv zeta in R. destr_conj R.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  clear - N1 N2 D1 D2 SH L15 Hsh Rlf Rcf Rwf.
  constructor.
  - exact Rlf.
  - exact Rcf.
  - exact Rwf.
  - lia.
  - unfold N_LENS. lia.
  - lia.
  - lia.
  - intros s Hs. rewrite Z.add_0_l. apply L15. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
  - lia.
  - lia.
  - lia.
  - cbn [it_room]. unfold N_CODES, ENOUGH_LENS. lia.
Qed.

Lemma cl_bridge_lens : forall lf cf wf nlen r,
  itc LENS lf 0 nlen 0 9 cf wf -> r = resA LENS lf 0 nlen 0 9 cf wf ->
  (it_ret r = 0 -> tab_ok LENS (rdc (arr_get (it_tbl r)) (CDyn 0)) (it_bits r) (it_table r) = true
                   /\ 1 <= it_bits r <= 15 /\ 0 <= it_table r <= ENOUGH_LENS)
  /\ (it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 9)
  /\ (forall i, 0 <= i < N_CODES -> 0 <= arr_get (it_tbl r) i < 4294967296)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r) i < 65536)
  /\ 0 <= it_bits r < 4294967296 /\ 0 <= it_table r <= ENOUGH_LENS.
Proof.
  intros lf cf wf nlen r C ER. pose proof (resA_ranges LENS lf 0 nlen 0 9 cf wf C) as (RT & RW).
  rewrite <- ER in RT, RW.
  pose proof (tab_ok_of_itable LENS lf cf wf (arr_get (it_tbl r)) 0 nlen 0 9) as BR0.
  pose proof (it_fail_shape LENS (arr_init N_LENS lf) 0 nlen (arr_init N_CODES cf) 0 9 (arr_init N_WORK wf)) as FS0.
  cbv zeta in BR0, FS0.
  rewrite (resA_eq LENS lf 0 nlen 0 9 cf wf) in ER.
  rewrite <- ER in BR0, FS0. clear ER.
  destruct C as [Rlf Rcf Rwf C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11].
  assert (OK : it_ret r = 0 -> tab_ok LENS (rdc (arr_get (it_tbl r)) (CDyn 0)) (it_bits r) (it_table r) = true
                   /\ 1 <= it_bits r <= 15 /\ 0 <= it_table r <= ENOUGH_LENS).
  { intros Hr. specialize (BR0 C1 C2 C3 C4 Rlf C5 C6 C7 C8 C9 C10 C11 Hr (fun i _ => eq_refl)).
    destruct BR0 as (T & B & TT & _). rewrite Z.sub_0_r in T. split; [exact T| split; [exact B|]].
    cbn [it_room] in TT. clear - TT B.
    assert (0 < 2 ^ it_bits r) by (apply Z.pow_pos_nonneg; lia). lia. }
  split; [exact OK|]. split; [exact FS0|]. split; [exact RT|]. split; [exact RW|].
  destruct (Z.eq_dec (it_ret r) 0) as [Hr|Hr].
  - destruct (OK Hr) as (_ & B & TT). clear - B TT. lia.
  - destruct (FS0 Hr) as (E1 & E2). rewrite E1, E2. unfold ENOUGH_LENS. lia.
Qed.

Lemma cl_itc_dists : forall cx st lf cf cf1 wf1 nx1,
  sinv cx st lf cf -> t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf1 i < 4294967296) -> (forall i, 0 <= i < 288 -> 0 <= wf1 i < 65536) -> 0 <= nx1 <= ENOUGH_LENS ->
  itc DISTS lf (t_nlen st) (t_ndist st) nx1 6 cf1 wf1.
Proof.
  intros cx st lf cf cf1 wf1 nx1 SI Hm Hsh Rcf1 Rwf1 Hnx. destruct (sinv_cl_facts _ _ _ _ SI Hm) as (N1 & N2 & D1 & D2 & SH & L15).
  pose proof SI as (R & _). unfold IDefs.RNG in R. cbv zeta in R. destr_conj R.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  clear - N1 N2 D1 D2 SH L15 Hsh Rlf Rcf1 Rwf1 Hnx.
  constructor.
  - exact Rlf.
  - exact Rcf1.
  - exact Rwf1.
  - lia.
  - unfold N_LENS. lia.
  - lia.
  - lia.
  - intros s Hs. apply L15. lia.
  - intros X. discriminate X.
  - intros _. lia.
  - lia.
  - lia.
  - lia.
  - cbn [it_room]. unfold N_CODES, ENOUGH_LENS, ENOUGH_DISTS in *. lia.
Qed.

Lemma cl_bridge_dists : forall lf cf1 wf1 nlen ndist nx1 lb1 r,
  itc DISTS lf nlen ndist nx1 6 cf1 wf1 -> r = resA DISTS lf nlen ndist nx1 6 cf1 wf1 ->
  tab_ok LENS (rdc cf1 (CDyn 0)) lb1 nx1 = true ->
  (it_ret r = 0 -> tab_ok LENS (rdc (arr_get (it_tbl r)) (CDyn 0)) lb1 nx1 = true
                   /\ tab_ok DISTS (rdc (arr_get (it_tbl r)) (CDyn nx1)) (it_bits r) (it_table r - nx1) = true
                   /\ 1 <= it_bits r <= 15 /\ nx1 <= it_table r <= N_CODES)
  /\ (it_ret r <> 0 -> it_table r = nx1 /\ it_bits r = 6)
  /\ (forall i, 0 <= i < N_CODES -> 0 <= arr_get (it_tbl r) i < 4294967296)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r) i < 65536)
  /\ 0 <= it_bits r < 4294967296 /\ nx1 <= it_table r <= N_CODES.
Proof.
  intros lf cf1 wf1 nlen ndist nx1 lb1 r C ER TL. pose proof (resA_ranges DISTS lf nlen ndist nx1 6 cf1 wf1 C) as (RT & RW).
  rewrite <- ER in RT, RW.
  pose proof (tab_ok_of_itable DISTS lf cf1 wf1 (arr_get (it_tbl r)) nlen ndist nx1 6) as BR0.
  pose proof (it_fail_shape DISTS (arr_init N_LENS lf) nlen ndist (arr_init N_CODES cf1) nx1 6 (arr_init N_WORK wf1)) as FS0.
  cbv zeta in BR0, FS0.
  rewrite (resA_eq DISTS lf nlen ndist nx1 6 cf1 wf1) in ER.
  rewrite <- ER in BR0, FS0. clear ER.
  destruct C as [Rlf Rcf Rwf C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11].
  assert (OK : it_ret r = 0 -> tab_ok LENS (rdc (arr_get (it_tbl r)) (CDyn 0)) lb1 nx1 = true
                   /\ tab_ok DISTS (rdc (arr_get (it_tbl r)) (CDyn nx1)) (it_bits r) (it_table r - nx1) = true
                   /\ 1 <= it_bits r <= 15 /\ nx1 <= it_table r <= N_CODES).
  { intros Hr. specialize (BR0 C1 C2 C3 C4 Rlf C5 C6 C7 C8 C9 C10 C11 Hr (fun i _ => eq_refl)).
    destruct BR0 as (T & B & TT & OUT).
    assert (P2 : 0 < 2 ^ it_bits r) by (apply Z.pow_pos_nonneg; lia).
    split.
    { eapply tab_ok_ext_rd; [| exact TL]. intros i Hi. unfold rdc. rewrite !Z.add_0_l. apply OUT; [unfold N_CODES in *; cbn [it_room] in *; lia| lia]. }
    split; [exact T|]. split; [exact B|]. cbn [it_room] in *. unfold N_CODES in *. lia. }
  split; [exact OK|]. split; [exact FS0|]. split; [exact RT|]. split; [exact RW|].
  destruct (Z.eq_dec (it_ret r) 0) as [Hr|Hr].
  - destruct (OK Hr) as (_ & _ & B & TT). clear - B TT. lia.
  - destruct (FS0 Hr) as (E1 & E2). rewrite E1, E2. cbn [it_room] in C11. unfold N_CODES, ENOUGH_DISTS in *. lia.
Qed.

Definition st_len_ (st : ist) : ist :=
  IST LEN_ (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) 0
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Definition st_badr (st : ist) (rv : Z) : ist :=
  IST BAD (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Definition st_pre1 (st : ist) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (t_dc st) 9 (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) 0 (t_whave st) (t_wnext st).
Definition st_pre2 (st : ist) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (CDyn (t_nx st)) (t_lb st) 6
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma rng_fields2 : forall cx st lf cf st' cf',
  IDefs.RNG cx st lf cf ->
  t_cin st' = t_cin st -> t_cout st' = t_cout st -> t_bits st' = t_bits st -> t_hold st' = t_hold st -> t_out st' = t_out st ->
  t_last st' = t_last st -> t_flags st' = t_flags st -> t_length st' = t_length st -> t_offset st' = t_offset st -> t_extra st' = t_extra st ->
  t_ncode st' = t_ncode st -> t_nlen st' = t_nlen st -> t_ndist st' = t_ndist st -> t_whave st' = t_whave st -> t_wnext st' = t_wnext st ->
  match t_dc st' with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end ->
  0 <= t_ret st' < 18446744073709551616 -> 0 <= t_lb st' < 4294967296 -> 0 <= t_db st' < 4294967296 -> 0 <= t_shave st' < 4294967296 ->
  0 <= t_nx st' <= N_CODES -> match t_lc st' with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  IDefs.RNG cx st' lf cf'.
Proof.
  intros cx st lf cf st' cf' R E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 A0 A1 A2 A3 A4 A5 A6 A7.
  unfold IDefs.RNG in *. cbv zeta in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15.
  destr_conj R. split_conj; try assumption; try lia.
Qed.

Lemma cl_exits : forall cx st lf cf wf r1 r2,
  sinv cx st lf cf -> t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> (forall i, 0 <= i < 288 -> 0 <= wf i < 65536) ->
  r1 = resA LENS lf 0 (t_nlen st) 0 9 cf wf ->
  r2 = resA DISTS lf (t_nlen st) (t_ndist st) (it_table r1) 6 (arr_get (it_tbl r1)) (arr_get (it_work r1)) ->
  let S1 := st_itab (st_pre1 st) false (it_bits r1) (it_table r1) in
  let S2 := st_itab (st_pre2 S1) true (it_bits r2) (it_table r2) in
  itc LENS lf 0 (t_nlen st) 0 9 cf wf
  /\ IDefs.RNG cx S1 lf (arr_get (it_tbl r1)) /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r1) i < 65536)
  /\ t_nlen st <= 286 /\ t_ndist st <= 30
  /\ (it_ret r1 <> 0 -> sinv cx (bad_ofP (st_ret S1 (it_ret r1 mod 18446744073709551616))) lf (arr_get (it_tbl r1))
                        /\ meas cx (bad_ofP (st_ret S1 (it_ret r1 mod 18446744073709551616))) < meas cx st)
  /\ (it_ret r1 = 0 ->
        itc DISTS lf (t_nlen st) (t_ndist st) (it_table r1) 6 (arr_get (it_tbl r1)) (arr_get (it_work r1))
        /\ IDefs.RNG cx S2 lf (arr_get (it_tbl r2)) /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r2) i < 65536)
        /\ (it_ret r2 = 0 -> sinv cx (st_len_ S2) lf (arr_get (it_tbl r2)) /\ meas cx (st_len_ S2) <= meas cx st)
        /\ (it_ret r2 <> 0 -> sinv cx (st_badr S2 (it_ret r2 mod 18446744073709551616)) lf (arr_get (it_tbl r2))
                              /\ meas cx (st_badr S2 (it_ret r2 mod 18446744073709551616)) < meas cx st)).
Proof.
  intros cx st lf cf wf r1 r2 SI Hm Hsh Rwf ER1 ER2 S1 S2.
  destruct (sinv_cl_facts _ _ _ _ SI Hm) as (N1 & N2 & D1 & D2 & SH & L15).
  pose proof (cl_itc_lens cx st lf cf wf SI Hm Hsh Rwf) as ITC1.
  destruct (cl_bridge_lens lf cf wf (t_nlen st) r1 ITC1 ER1) as (BOK1 & BFS1 & RT1 & RW1 & RB1 & RX1).
  pose proof (proj1 SI) as R0. pose proof R0 as R0'. unfold IDefs.RNG in R0'. cbv zeta in R0'. destr_conj R0'.
  assert (M64 : forall x, 0 <= x mod 18446744073709551616 < 18446744073709551616) by (intros x; apply Z.mod_pos_bound; reflexivity).
  assert (RN1 : IDefs.RNG cx S1 lf (arr_get (it_tbl r1))).
  { eapply (rng_fields cx st lf cf); [exact R0| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity | | | | | | | exact RT1];
      subst S1; unfold st_itab, st_pre1; ist_cbn; unfold N_CODES, ENOUGH_LENS in *; first [assumption | lia | exact I]. }
  split; [exact ITC1|]. split; [exact RN1|]. split; [exact RW1|]. split; [exact N2|]. split; [exact D2|].
  split.
  { intros NE. destruct (BFS1 NE) as (ET & EB).
    destruct (sinv_cl_bad cx st lf cf (arr_get (it_tbl r1)) (it_ret r1 mod 18446744073709551616) 9 (t_dc st) (t_db st) 0 SI Hm (M64 _)
                ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(unfold N_CODES; lia) RT1) as (SIB & MEB).
    subst S1. rewrite ET, EB. destruct st. exact (conj SIB MEB). }
  intros E0. destruct (BOK1 E0) as (TOK1 & LB1 & NX1).
  pose proof (cl_itc_dists cx st lf cf (arr_get (it_tbl r1)) (arr_get (it_work r1)) (it_table r1) SI Hm Hsh RT1 RW1 NX1) as ITC2.
  destruct (cl_bridge_dists lf (arr_get (it_tbl r1)) (arr_get (it_work r1)) (t_nlen st) (t_ndist st) (it_table r1) (it_bits r1) r2 ITC2 ER2 TOK1)
    as (BOK2 & BFS2 & RT2 & RW2 & RB2 & RX2).
  split; [exact ITC2|].
  assert (RN2 : IDefs.RNG cx S2 lf (arr_get (it_tbl r2))).
  { eapply (rng_fields2 cx st lf cf); [exact R0| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| | | | | | | | exact RT2];
      subst S2 S1; unfold st_itab, st_pre2, st_pre1; ist_cbn; unfold N_CODES, ENOUGH_LENS in *; first [assumption | lia | exact I | reflexivity]. }
  split; [exact RN2|]. split; [exact RW2|].
  split.
  - intros E2. destruct (BOK2 E2) as (TL2 & TD2 & DB2 & NX2).
    destruct (sinv_cl_len_ cx st lf cf (arr_get (it_tbl r2)) (it_bits r1) (it_table r1) (it_bits r2) (it_table r2) SI Hm
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) TL2 TD2 RT2) as (SIL & MEL).
    subst S2 S1. destruct st. split; [exact SIL| exact (Z.lt_le_incl _ _ MEL)].
  - intros NE2. destruct (BFS2 NE2) as (ET2 & EB2).
    destruct (sinv_cl_bad cx st lf cf (arr_get (it_tbl r2)) (it_ret r2 mod 18446744073709551616) (it_bits r1) (CDyn (it_table r1)) 6 (it_table r1) SI Hm (M64 _)
                ltac:(lia) ltac:(lia) ltac:(unfold N_CODES, ENOUGH_LENS in *; lia) ltac:(lia) ltac:(unfold N_CODES, ENOUGH_LENS in *; lia) RT2) as (SIB & MEB).
    subst S2 S1. rewrite ET2, EB2. destruct st. exact (conj SIB MEB).
Qed.
