(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure InfPure_w7 ItAPure ItBridgeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

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

Definition order_f (i : Z) : Z := arr_get order_a i.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land31_mod : forall h, 0 <= h -> Z.land h 31 = h mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma bits_54_59 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 54 mod 18446744073709551616) 59 = (h / 32) mod 32.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 54) with 18014398509481984. change (2 ^ 59) with 576460752303423488. nia.
Qed.
Lemma bits_50_60 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 50 mod 18446744073709551616) 60 = (h / 1024) mod 16.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 50) with 1125899906842624. change (2 ^ 60) with 1152921504606846976. nia.
Qed.
Lemma mod_range : forall a m, 0 < m -> 0 <= a mod m < m.
Proof. intros. apply Z.mod_pos_bound. assumption. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma it_fail_shape : forall ty lens lens_ofs codes tbl table bits work,
  let r := inflate_table ty lens lens_ofs codes tbl table bits work in
  it_ret r <> 0 -> it_table r = table /\ it_bits r = bits.
Proof. intros. apply inflate_table_fail_shape. assumption. Qed.

Lemma order_covers : forall (lf : Z -> Z) b,
  (forall j, 0 <= j < 19 -> lf (order_f j) <= b) -> forall i, 0 <= i < 19 -> lf i <= b.
Proof.
  intros lf b H i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
              i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18) by lia_std.
  decompose [or] C; subst;
    [ change (lf 0) with (lf (order_f 3))
    | change (lf 1) with (lf (order_f 17))
    | change (lf 2) with (lf (order_f 15))
    | change (lf 3) with (lf (order_f 13))
    | change (lf 4) with (lf (order_f 11))
    | change (lf 5) with (lf (order_f 9))
    | change (lf 6) with (lf (order_f 7))
    | change (lf 7) with (lf (order_f 5))
    | change (lf 8) with (lf (order_f 4))
    | change (lf 9) with (lf (order_f 6))
    | change (lf 10) with (lf (order_f 8))
    | change (lf 11) with (lf (order_f 10))
    | change (lf 12) with (lf (order_f 12))
    | change (lf 13) with (lf (order_f 14))
    | change (lf 14) with (lf (order_f 16))
    | change (lf 15) with (lf (order_f 18))
    | change (lf 16) with (lf (order_f 0))
    | change (lf 17) with (lf (order_f 1))
    | change (lf 18) with (lf (order_f 2)) ];
    apply H; lia_std.
Qed.


Definition st_sh (st : ist) (j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
Definition st_ll (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
Definition st_ct (st : ist) (m rv lb nx sh : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (t_dc st) lb (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) sh nx (t_whave st) (t_wnext st).
Definition st_lt (st : ist) (lb nx : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (t_dc st) lb (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).
Definition st_tb (st : ist) (m ci H B ncode nlen ndist sh : Z) : ist :=
  IST m (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      ncode nlen ndist sh (t_nx st) (t_whave st) (t_wnext st).

Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.

Lemma sinv_ll : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = LENLENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= 19 ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' (order_f i) <= 7) ->
  sinv cx (st_ll st ci H B j) lf' cf /\ meas cx (st_ll st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_ll, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). destruct ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try assumption; intros j0 Hj; rewrite <- order_f_model by lia_std; apply Hlf'; exact Hj |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

Lemma sinv_ll_ct : forall cx st lf cf cf' lb nx,
  sinv cx st lf cf -> t_mode st = LENLENS ->
  1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= N_CODES -> tab_ok CODES (rdc cf' (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st CODELENS 0 lb nx 0) lf cf' /\ meas cx (st_ct st CODELENS 0 lb nx 0) < meas cx st.
Proof.
  intros cx st lf cf cf' lb nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). destruct ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try lia_std; unfold ctable_live; cbn; cbv [N_CODES]; split_conj; try reflexivity; try lia_std; exact TOK |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_ll_bad : forall cx st lf cf cf' rv,
  sinv cx st lf cf -> t_mode st = LENLENS -> 0 <= rv < 18446744073709551616 ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st BAD rv 7 0 (t_shave st)) lf cf' /\ meas cx (st_ct st BAD rv 7 0 (t_shave st)) < meas cx st.
Proof.
  intros cx st lf cf cf' rv (R & W & P & Mo) Hm Hrv Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_tb : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  4 <= ncode -> ncode <= 19 -> 257 <= nlen -> nlen <= 286 -> 1 <= ndist -> ndist <= 30 ->
  sinv cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) lf cf /\
  meas cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try lia_std; intros j0 Hj0; exfalso; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.
Lemma sinv_tb_bad : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= ncode -> ncode < 4294967296 -> 0 <= nlen -> nlen < 4294967296 -> 0 <= ndist -> ndist < 4294967296 ->
  sinv cx (bad_ofP (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) lf cf /\
  meas cx (bad_ofP (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, bad_ofP, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. destruct P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

