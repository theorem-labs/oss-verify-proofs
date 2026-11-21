(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK Require Import ItBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.I7S Require Import SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.I7S Require Import S_Type S_MatchL S_DistL S_TableL S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_TAB_SKIP : Z := 88196.
Definition L_LL_SETUP : Z := 88288.
Definition L_LL_FILL : Z := 88432.
Definition L_LL_TABLE : Z := 88508.
Definition L_LL_RET : Z := 88560.
Definition L_TBLERR : Z := 89868.
Definition L_BAD_TAB : Z := 89312.

Lemma mem_u64_eqv {RCa1 : RunCtx}  : forall M a v v', v = v' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

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

Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr {RCa1 : RunCtx}  : forall M p, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

Lemma rom_it_tabs {RCa1 : RunCtx}  : forall M, rom_ok M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

Lemma i_frame_slots {RCa1 : RunCtx}  : forall cx M, i_frame cx M ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -208) (c_p cx + 1384) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -192) (c_p cx + 160) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -216) (c_p cx + 136) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -200) (c_p cx + 808) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -128) (c_u cx) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -120) 0 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -136) (-16180) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -224) (c_p cx + 140).
Proof. intros cx M H. unfold i_frame in H. destr_conj H. split_conj; assumption. Qed.

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
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)   (* LENLENS sets distcode with lencode (smodel14-r1) *)
      (t_ncode st) (t_nlen st) (t_ndist st) sh nx (t_whave st) (t_wnext st).
Definition st_lt (st : ist) (lb nx : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)   (* distcode with lencode *)
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
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
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
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
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
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
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
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
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
  sinv cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) lf cf /\
  meas cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, bad_of, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
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

Local Ltac st_cell_tac Hp1 Hp2 :=
  lazymatch goal with
  | |- mem_u32 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u32_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u64 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u64_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u32 _ (wbytes _ _ _) _ _ => apply mem_u32_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- mem_u64 _ (wbytes _ _ _) _ _ => apply mem_u64_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- _ => assumption
  end.
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_sh, st_ct, st_lt, st_tb in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split; st_cell_tac Hp1 Hp2.
Lemma st_rest_set140 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st v) (wbytes M (w64 (c_p cx + 156)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_llt {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_lt st v 0)
    (* the distcode store (p+128) comes between lencode and lenbits *)
    (wbytes (wbytes (wbytes (wbytes M (w64 (c_p cx + 120)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                            (w64 (c_p cx + 128)) (Z_to_le_bytes 8 (c_p cx + 1384)))
                    (w64 (c_p cx + 136)) (Z_to_le_bytes 4 v))
            (w64 (c_p cx + 160)) (Z_to_le_bytes 8 (c_p cx + 1384))).
Proof.
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_lt in *; icx_cbn. cbv [cp_addr o_codes]. icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  rewrite Z.mul_0_r, Z.add_0_r.
  repeat split; st_cell_tac Hp1 Hp2.
Qed.

Lemma st_rest_tb3 {RCa1 : RunCtx}  : forall cx st M vc vn vd,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_tb st (t_mode st) (t_cin st) (t_hold st) (t_bits st) vc vn vd (t_shave st))
    (wbytes (wbytes (wbytes M (w64 (c_p cx + 144)) (Z_to_le_bytes 4 vc))
                    (w64 (c_p cx + 148)) (Z_to_le_bytes 4 vn))
            (w64 (c_p cx + 152)) (Z_to_le_bytes 4 vd)).
Proof.
  intros cx st M vc vn vd H Hp1 Hp2; destruct cx, st; unfold st_rest, st_tb in *; icx_cbn.
  pose proof two64_eq as TW64.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; st_cell_tac Hp1 Hp2.
Qed.

Definition PL {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M0 : mem) (st : ist) (cf : Z -> Z) (j : Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st j) M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\ mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx).

Lemma PL_store140 {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> a = c_p cx + 156 -> 0 <= v < 4294967296 ->
  PL cx fin M0 st cf v (wbytes M (w64 a) (Z_to_le_bytes 4 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H -> Hv.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & [Hmode SREST] & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (st_rest_set140 _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1. clear SREST.
  unfold st_sh in SR1, Hmode |- *. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1, Hmode |- *.
  zmem_transport M (p + 156) (Z_to_le_bytes 4 v).
  split_conj; try assumption; try close_std; try exact HAG. split; assumption.
Qed.

Lemma PL_store_lens {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> c_p cx + 168 <= a -> a + 2 <= c_p cx + 808 ->
  PL cx fin M0 st cf jo (wbytes M (w64 a) (Z_to_le_bytes 2 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & SAT & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 2 v).
  split_conj; try assumption; try close_std; try exact HAG.
Qed.

Lemma PL_intro {RCa1 : RunCtx}  : forall cx fin M0 st lf cf M,
  k_mem cx fin M0 st lf cf M -> PL cx fin M0 st cf (t_shave st) M /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf.
Proof.
  intros cx fin M0 st lf cf M H. open_kmem H. split; [| exact Hlens]. unfold PL. destruct st. split_conj; assumption.
Qed.
Lemma PL_kmem {RCa1 : RunCtx}  : forall cx fin M0 st lf cf j M,
  PL cx fin M0 st cf j M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> k_mem cx fin M0 (st_sh st j) lf cf M.
Proof.
  intros cx fin M0 st lf cf j M (A & B & C & C2 & D & E) HL. unfold k_mem. destruct st. split_conj; assumption.
Qed.

Section TABLE_CODE.
Context {RCa1 : RunCtx}.
Hypothesis ITABLE : itable_spec_s.
Hypothesis CLHEAD : clhead_stmt.

Definition s_regs_llt (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -224 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS6 = c_p cx + 168 /\ zget_l Rb l kS4 = 16209 /\
  zget_l Rb l kS9 = JTAB_ADDR /\ zget_l Rb l kS1 = c_osz cx - t_cout st /\
  s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st.

Lemma ll_table_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_TABLE (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). rewrite Hsh in ML. dand ML as (_ & _ & _ & Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hlf7). clear MODE_.
  assert (L7 : forall i, 0 <= i < 19 -> lf i <= 7).
  { apply order_covers. intros j0 Hj0. rewrite order_f_model by exact Hj0. apply Hlf7. exact Hj0. }
  clear Hlf7.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode shave. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (i_frame_slots _ _ FRM) as FS. icx_cbn. cbv [JTAB_ADDR] in FS.
  dand FS as (S16 & S32 & S8 & S24 & S96 & S104 & S88 & S0).
  prune_rng.
  zkeysb. unfold L_LL_TABLE, L_LL_RET, L_TBLERR, L_CL_HEAD, L_RELOAD_A1, L_ITABLE in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  zstep Rfd.
  pose proof (st_rest_llt _ _ _ 7 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_lt in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST Hmode.
  (* FOUR stores here: lencode (p+120), distcode (p+128, new in 1.4), lenbits (p+136), next (p+160) *)
  zstep Rfd.                          (* sd a1,120(s0) *)
  zstep Rfd.                          (* sd a1,128(s0): 1.4 *)
  zstep Rfd.                          (* sw a0,136(s0) *)
  zstep Rfd.                          (* sd a1,160(s0) *)
  rename SR1 into SREST.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4) end.
  lazymatch goal with H120 : mem_u32 _ ?Mx (p + 136) 7, H144 : mem_u64 _ ?Mx (p + 160) (p + 1384) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    rename H120 into C120n; rename H144 into C144n end.
  unfold itable_spec_s, itable_spec_at in ITABLE.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ITABLE Rx lx Mx MD T CODES p 0 19 0 7 (p + 136) (u + -224) 88560 zc lf cf wf Hh) end.
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => left; cbv [o_lenbits]; reflexivity
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| exact C144n]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros _; split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]
       | |- _ = DISTS -> _ => intros X; discriminate X
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; replace (0 + s) with s by lia; pose proof (L7 s Hs); lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT DEXT_ADDR]; cbn [it_room]; first [assumption | lia]
       end | match goal with |- ?G => idtac "ITFAIL" G end ].
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  pose proof (tab_ok_of_itable CODES lf cf wf cf' 0 19 0 7) as BR0.
  pose proof (it_fail_shape CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) as FS0.
  set (r := inflate_table CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) in *.
  clearbody r. cbv zeta in BR0, FS0.
  assert (BR : it_ret r = 0 ->
     tab_ok CODES (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room CODES /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hrz. apply BR0; cbv [N_LENS N_CODES]; cbn [it_room]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. pose proof (L7 s Hs). lia.
    - intros _. split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]. }
  assert (FS : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 7) by (intros Hnz; exact (FS0 Hnz)).
  clear BR0 FS0.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes.
  unfold st_rest in SREST. icx_cbn. cbv [cp_addr o_codes] in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & _ & C124 & C128 & C132 & C136 & C140 & _).
  unfold it_fp in HP. cbv [o_next o_work o_codes N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [N_CODES] in Rcf', BR. cbn [it_room] in BR. cbv [o_next o_codes] in Hnext'.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz].
  -
    dand (BR Hr0) as (TOK & Hb15 & Htab & Hout). clear BR FS.
    rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    clear C140.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_ll_ct _ _ lf cf cf' (it_bits r) (it_table r) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) TOK ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLHEAD (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_ct (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext)
                       CODELENS 0 (it_bits r) (it_table r) 0)
                lf cf' CX0 Hh Hfin eq_refl SI1) end.
    + unfold s_regs_cl, s_fix, s_vars, st_ct; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  -
    destruct (FS Hnz) as [Ht0 Hb7]. clear BR FS.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz E) | rewrite E | rewrite E]; clear;
        [ change (1 mod 18446744073709551616) with 1 | change ((-1) mod 18446744073709551616) with 18446744073709551615 ]; lia_std. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with H : mem_u64 _ ?Mx (u + -160) _ |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in H; rewrite Hrm in H end.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_ll_bad _ _ lf cf cf' rm SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1)) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    ist_cbn. rewrite Ht0 in Hnext'. rewrite Hb7 in Hbits'.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end.
    + unfold s_regs_reload, st_ct; icx_cbn; zkeys; split_conj; try zreg; try (intros C; discriminate C).
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

Lemma ll_fill_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_ncode st <= t_shave st -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> zget_l Rb l kA5 = t_shave st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FILL (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG La5 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  prune_rng.
  zkeysb. unfold L_LL_FILL, L_LL_TABLE, L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  zstep Rfd.
  destruct (Z_lt_dec 18 shave) as [H19 | H18].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end.
    + unfold s_regs_llt, s_vars; icx_cbn; zkeys; split_conj; zreg.
    + apply (PL_kmem _ _ _ _ lf cf shave) in HP; [exact HP | exact Hlens].
    + exact KA0.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 * shave) ltac:(rewrite shiftl_1m; reflexivity).
    zstep Rfd.
    zstep Rfd. zlit.
    zstep Rfd. zlit.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fill_loop 19 (fun (_ : Z) Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                 (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf shave Mq)
                Rx lx Mx MD T p shave shave lf Hh) end;
      try zreg; try assumption; try lia.
    + unfold ZSEP. exact (sep_p_rom _ _ SEP).
    + intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
    + intros M' jo' a v HP' Ha1 Ha2. eapply PL_store_lens; [exact CX0 | exact HP' | cbn; lia | cbn; lia].
    +
      intros R' M' lf' Ha2 Wp' Hord' Hlens' Rlf' Hlf7' HP' HKC. cbv [keptc KS_LF] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FEND in *.
      clear Hlens Hord Hin Wp Wstk Wob Ww ROM FRM CST HK Hcodes HP.
      pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                    (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    cf jo M' a v CX0) as HPa.
      tstoreP Rfd HP' HPa.
      pose proof (sinv_ll _ _ lf cf cin hold bits 19 lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7') as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                  (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin hold bits 19)
                  lf' cf CX0 Hh Hfin eq_refl eq_refl SI1) end.
      * unfold s_regs_llt, s_vars, st_ll; icx_cbn; zkeys; split_conj; try zreg; keptc_trans.
      * apply (PL_kmem _ _ _ _ lf' cf 19) in HP'; [exact HP' | exact Hlens'].
      * eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

Lemma ll_setup_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st < t_ncode st -> sinv cx st lf cf ->
  s_fix cx Rb l -> s_vars cx st Rb l -> zget_l Rb l kS11 = c_q cx + t_cin st ->
  zget_l Rb l kA5 = t_shave st -> zget_l Rb l kA2 = t_ncode st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_SETUP (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI FX VR L10 La5 La2 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_fix in FX. unfold s_vars in VR. icx_cbn. destr_conj FX. destr_conj VR.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  prune_rng.
  zkeysb. unfold L_LL_SETUP, L_LL_HEAD, L_LL_FILL0, L_LL_FILL, L_LEAVE_LD, A_ORDER in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd. zext32.
  zstep Rfd.
  zsetreg (2 * shave) ltac:(symmetry; apply zext32_shift31; lia).
  zstep Rfd. zlit.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPa.
  pose proof (fun M' jo a v => PL_store_lens (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPb.
  cbn [c_p] in HPa, HPb.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (lenlens_loop 19 (fun jo Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
               (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq)
              Rx lx Mx MD T p q n ncode shave cin bits hold fin lf Hh) end;
    try zreg; try assumption; try lia.
  - unfold ZSEP. exact (sep_p_q _ _ SEP).
  - unfold ZSEP. exact (sep_p_rom _ _ SEP).
  - intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
  -
    intros R' M' j' B' H' lf' G9 G24 G25 G27 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys.
    pose proof (sinv_ll _ _ lf cf n H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    pose proof (PL_kmem _ _ _ _ lf' cf j' _ HP' Hlens') as KM'. dand KM' as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KLL Rx Mx (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n H' B' j') lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption. all: try (rewrite G25; lia).
    + exact STD'.
    + exact SAT'.
    + exact SRET'.
    + exact SOUT'.
    + exact HL'.
    + exact HC'.
    + exact HP0'.
  -
    intros R' M' ci' B' H' lf' G9 G24 G25 G27 G13 G26 G2 X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FILL0, L_LL_FILL in *.
    pose proof (sinv_ll _ _ lf cf ci' H' B' ncode lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' ncode)
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_llt, s_vars, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption.
    + unfold st_ll; cbn [t_shave]; zreg.
    + apply (PL_kmem _ _ _ _ lf' cf ncode) in HP'; [exact HP' | exact Hlens'].
    + eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

Theorem arm_LENLENS_s0 : arm_stmt L_LENLENS LENLENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  assert (C128 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 144) ncode) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  assert (C140 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 156) shave) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  clear SREST Hmode STD SRET SOUT Hlens Hcodes HP0.
  zkeysb. unfold L_LENLENS, L_LL_SETUP, L_LL_FILL in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  tstep1 Rfd.
  tstep1 Rfd.
  destruct (Z_lt_dec shave ncode) as [Hlt | Hge].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end;
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | unfold s_vars; icx_cbn; zkeys; split_conj; zreg
      | (icx_cbn; zkeys; zreg) .. | exact KM0 | exact K ].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end;
      [ unfold s_regs_llt, s_vars; icx_cbn; zkeys; split_conj; zreg
      | icx_cbn; zkeys; zreg | exact KM0 | exact K ].
Qed.

Ltac zval k :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with Some ?v => v end
  end.

Lemma table_body : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = TABLE -> sinv cx st lf cf ->
  s_fix cx Rb l ->
  zget_l Rb l kS2 = c_n cx - cin1 -> zget_l Rb l kS3 = c_ob cx + t_cout st -> zget_l Rb l kRA = c_osz cx - t_cout st ->
  zget_l Rb l kS7 = hold1 -> zget_l Rb l kS8 = bits1 ->
  zget_l Rb l kS11 = c_q cx + cin1 -> zget_l Rb l kS10 = c_q cx + cin1 ->
  t_cin st <= cin1 -> cin1 <= c_n cx -> 14 <= bits1 -> bits1 <= 40 -> 0 <= hold1 -> hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI FX L25 L20 L19 L24 L9 L27 L28
         Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  unfold s_fix in FX. icx_cbn. destr_conj FX.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TAB_BODY, L_LL_SETUP, L_BAD_TAB, L_BADMSG_S11 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  zsetreg (hold1 mod 32) ltac:(symmetry; apply land31_mod; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (hold1 / 2 ^ 14) ltac:(rewrite (Z.mod_small hold1) by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  zstep Rfd.
  zstep Rfd.
  zsetreg ((hold1 / 32) mod 32) ltac:(symmetry; apply bits_54_59; lia).
  zstep Rfd.
  zsetreg ((hold1 / 1024) mod 16) ltac:(symmetry; apply bits_50_60; lia).
  zstep Rfd.
  zstep Rfd.
  pose proof (mod_range hold1 32 ltac:(lia)) as R1. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as R2.
  pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as R3.
  pose proof (hold_shr_bound hold1 bits1 14 ltac:(lia) ltac:(lia)) as R4.
  let vc := zval 13%positive in let vn := zval 16%positive in let vd := zval 17%positive in
  pose proof (st_rest_tb3 _ _ _ vc vn vd SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_tb in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  rename SR1 into SREST.
  zstep Rfd.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (JB : forall RJ,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kS6 = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kS9 = 67008 -> zget RJ kS4 = 16209 ->
    zget RJ kS2 = n - cin1 -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kS10 = q + cin1 -> zget RJ kS7 = hold1 / 2 ^ 14 -> zget RJ kS8 = bits1 - 14 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 89312 (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. zkeys.
    zstep Rfd. zstep Rfd. zlit.
    zstep Rfd.
    pose proof (sinv_tb_bad _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                  SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
    ist_cbn.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB11 Rx Mx _ lf cf SI1 ME1) end.
    - unfold s_regs_disp, s_fix, s_vars, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [TABLE]; assumption | exact HAG]. }
  destruct (Z_lt_dec 29 (hold1 mod 32)) as [Hn1 | Hn1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec ((hold1 / 32) mod 32) 30) as [Hn2 | Hn2].
  2: { zbr Rfd true.
       lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end; zreg. }
  zbr Rfd false.
  clear JB.
  zstep Rfd.
  zstep Rfd.
  clear Hmode.
  zstep Rfd.
  pose proof (st_rest_set140 _ _ _ 0 SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1.
  unfold st_sh in SR1. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1.
  clear SREST.
  zstep Rfd.
  rename SR1 into SREST.
  zstep Rfd.
  pose proof (sinv_tb _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
              (st_tb (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                     LENLENS cin1 (hold1 / 2 ^ 14) (bits1 - 14) ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1) 0)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
  - unfold s_fix, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold s_vars, st_tb; icx_cbn; zkeys; split_conj; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold k_mem, st_at, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LENLENS]; assumption | exact HAG].
  - eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
Qed.

Theorem arm_TABLE_s0 : arm_stmt L_TABLE TABLE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. pose proof K as KA0. open_K K. open_kmem KM. open_std STD.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  clear SAT SRET SOUT Hlens Hcodes ROM Wstk Wp Wob Ww FRM CST HK.
  prune_rng.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TABLE, L_TAB_LOOP, L_TAB_BODY, L_TAB_SKIP, L_LEAVE_LD in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.
  destruct (Z_lt_dec 13 bits) as [Hb14 | Hb14].
  - zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_body _ fin MD T M0 Rx lx Mx
                (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI) end;
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | (icx_cbn; zkeys; first [zreg | lia]) .. | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd.
    assert (Hkk : exists k : nat, 14 - 8 * Z.of_nat k <= bits < 22 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { destruct (Z_lt_dec bits 6); [exists 2%nat | exists 1%nat]; cbn; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_loop k Rx lx Mx MD T q n cin hold bits fin Hh Hfin Hk1 Hk2) end;
      [ lia | lia | lia | lia | lia | lia | lia | zreg .. | exact Hin | | ].
    +
      intros R' hold' j' G27 G25 G24 G9 Hj' Hh' Hkn HKC. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      pose proof (sinv_pull _ _ lf cf n hold' j' SI ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 _].
      dand KM0 as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx (st_pull (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n hold' j') lf cf SI1) end;
        [ unfold s_regs_leave_ld, st_pull; icx_cbn; zkeys; split_conj; try zreg; try assumption; rewrite G25; lia
        | exact STD' | exact SAT' | exact SRET' | exact SOUT' | exact HL' | exact HC' | exact HP0' ].
    +
      intros R' hold' j' G28 G27 G25 G24 G9 Hj' Hh' Hkn HKC. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (table_body _ fin MD T M0 Rx [] Mx
                  (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI) end;
        [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; try zreg; assumption
        | (icx_cbn; zkeys; first [zreg | assumption | lia]) .. | exact KM0 | exact KA0 ].
Qed.
End TABLE_CODE.

