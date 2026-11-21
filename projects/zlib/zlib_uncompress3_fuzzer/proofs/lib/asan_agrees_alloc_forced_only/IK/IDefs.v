(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition kRA : positive := 2.  Definition kSP : positive := 3.
Definition kGP : positive := 4.  Definition kTP : positive := 5.
Definition kT0 : positive := 6.  Definition kT1 : positive := 7.  Definition kT2 : positive := 8.
Definition kS0 : positive := 9.  Definition kS1 : positive := 10.
Definition kA0 : positive := 11. Definition kA1 : positive := 12. Definition kA2 : positive := 13.
Definition kA3 : positive := 14. Definition kA4 : positive := 15. Definition kA5 : positive := 16.
Definition kA6 : positive := 17. Definition kA7 : positive := 18.
Definition kS2 : positive := 19. Definition kS3 : positive := 20. Definition kS4 : positive := 21.
Definition kS5 : positive := 22. Definition kS6 : positive := 23. Definition kS7 : positive := 24.
Definition kS8 : positive := 25. Definition kS9 : positive := 26. Definition kS10 : positive := 27.
Definition kS11 : positive := 28.
Definition kT3 : positive := 29. Definition kT4 : positive := 30. Definition kT5 : positive := 31.
Definition kT6 : positive := 32.

Definition kept_keys : list positive := [kSP; kGP; kTP; kS0; kS1; kS2; kS3; kS4; kS5; kS6; kS7; kS8; kS9; kS10; kS11].

Definition zs_next_in : Z := 8.    Definition zs_avail_in : Z := 16.  Definition zs_total_in : Z := 24.
Definition zs_next_out : Z := 32.  Definition zs_avail_out : Z := 40. Definition zs_total_out : Z := 48.
Definition zs_msg : Z := 56.       Definition zs_state : Z := 64.     Definition zs_zalloc : Z := 72.
Definition zs_zfree : Z := 80.     Definition zs_opaque : Z := 88.    Definition zs_data_type : Z := 96.
Definition zs_adler : Z := 104.    Definition zs_reserved : Z := 112.
Definition ZS_OFF : Z := 0.        (* 1.4: uncompress2_z keeps its z_stream at the caller's sp + 0 *)
Definition ZS_SIZE : Z := 112.

Definition o_strm : Z := 0.      Definition o_mode : Z := 8.      Definition o_last : Z := 12.
Definition o_wrap : Z := 16.     Definition o_havedict : Z := 24. Definition o_flags : Z := 28.
Definition o_dmax : Z := 32.     Definition o_check : Z := 40.    Definition o_total : Z := 48.
Definition o_head : Z := 56.     Definition o_wbits : Z := 68.    Definition o_wsize : Z := 72.
Definition o_whave : Z := 76.    Definition o_wnext : Z := 80.    Definition o_window : Z := 88.
Definition o_hold : Z := 96.     Definition o_bits : Z := 104.     Definition o_length : Z := 108.
Definition o_offset : Z := 112.   Definition o_extra : Z := 116.   Definition o_lencode : Z := 120.
Definition o_distcode : Z := 128. Definition o_lenbits : Z := 136. Definition o_distbits : Z := 140.
Definition o_ncode : Z := 144.   Definition o_nlen : Z := 148.    Definition o_ndist : Z := 152.
Definition o_shave : Z := 156.   Definition o_next : Z := 160.    Definition o_lens : Z := 168.
Definition o_work : Z := 808.    Definition o_codes : Z := 1384.  Definition o_sane : Z := 7160.
Definition o_back : Z := 7164.   Definition o_was : Z := 7168.
Definition STATE_SIZE : Z := 7176.
Definition N_LENS : Z := 320.    Definition N_WORK : Z := 288.    Definition N_CODES : Z := 1444.
Definition WIN_SIZE : Z := 32768.

Definition ORDER_ADDR : Z := 66116.
Definition LENFIX_ADDR : Z := 67422.
Definition DISTFIX_ADDR : Z := 69470.
Definition LBASE_ADDR : Z := 67170.
Definition LEXT_ADDR : Z := 67232.
Definition DBASE_ADDR : Z := 67294.
Definition DEXT_ADDR : Z := 67358.
Definition JTAB_ADDR : Z := 67008.
Definition MOD31_ADDR : Z := 66928.

Definition Z_OK : Z := 0.  Definition Z_STREAM_END : Z := 1.  Definition Z_NEED_DICT : Z := 2.
Definition Z_STREAM_ERROR : Z := -2.  Definition Z_DATA_ERROR : Z := -3.  Definition Z_MEM_ERROR : Z := -4.
Definition Z_BUF_ERROR : Z := -5.

Definition FRA : Z := 1024.
Definition ROM_LO_ALL : Z := 65536.

Record ictx := ICX {
  c_u    : Z;
  c_p    : Z;
  c_q    : Z;
  c_n    : Z;
  c_ob   : Z;
  c_osz  : Z;
  c_w    : Z;
  c_cin0 : Z;
  c_cout0 : Z;
  c_W0   : Z;
  c_K    : positive -> Z;
  c_zc   : Z
}.

Definition ctx_lin (rhi : Z) (cx : ictx) : Prop :=
  let u := c_u cx in let p := c_p cx in let q := c_q cx in let n := c_n cx in
  let ob := c_ob cx in let osz := c_osz cx in let w := c_w cx in let K := c_K cx in
  let zc := c_zc cx in
  zc + FRA <= u /\ u + 208 <= 140737488355328 /\
  0 < p /\ p + STATE_SIZE <= zc /\
  1 <= q /\ 0 <= n /\ n < 67108864 /\ q + n <= zc /\
  0 < ob /\ 0 <= osz /\ osz <= 262144 /\ ob + osz <= u /\
  0 <= w /\ w + WIN_SIZE <= zc /\
  0 <= c_cin0 cx /\ c_cin0 cx <= n /\ 0 <= c_cout0 cx /\ c_cout0 cx <= osz /\
  ROM_LO_ALL < rhi /\ rhi <= ob /\ rhi <= zc /\
  K kSP = u /\ Z.land (K kRA) (-2) = K kRA /\
  0 <= K kRA < 18446744073709551616 /\ 0 <= K kGP < 18446744073709551616 /\ 0 <= K kTP < 18446744073709551616 /\
  0 <= K kS0 < 18446744073709551616 /\ 0 <= K kS1 < 18446744073709551616 /\ 0 <= K kS2 < 18446744073709551616 /\
  0 <= K kS3 < 18446744073709551616 /\ 0 <= K kS4 < 18446744073709551616 /\ 0 <= K kS5 < 18446744073709551616 /\
  0 <= K kS6 < 18446744073709551616 /\ 0 <= K kS7 < 18446744073709551616 /\ 0 <= K kS8 < 18446744073709551616 /\
  0 <= K kS9 < 18446744073709551616 /\ 0 <= K kS10 < 18446744073709551616 /\ 0 <= K kS11 < 18446744073709551616.

Definition ctx_al (cx : ictx) : Prop :=
  c_u cx mod 16 = 0 /\ c_p cx mod 16 = 0 /\ c_w cx mod 16 = 0.

Definition ctx_sep (rhi : Z) (cx : ictx) : Prop :=
  let u := c_u cx in let p := c_p cx in let q := c_q cx in let n := c_n cx in
  let ob := c_ob cx in let osz := c_osz cx in let w := c_w cx in
  (p + STATE_SIZE <= q \/ q + n <= p) /\
  (p + STATE_SIZE <= ob \/ ob + osz <= p) /\
  (ob + osz <= q \/ q + n <= ob) /\
  (ob + osz <= u - FRA \/ u + 7 <= ob) /\
  (p + STATE_SIZE <= ROM_LO_ALL \/ rhi <= p) /\
  (w = 0 \/ (p + STATE_SIZE <= w \/ w + WIN_SIZE <= p)) /\
  (w = 0 \/ (w + WIN_SIZE <= q \/ q + n <= w)) /\
  (w = 0 \/ (w + WIN_SIZE <= ob \/ ob + osz <= w)) /\
  (w = 0 \/ (w + WIN_SIZE <= ROM_LO_ALL \/ rhi <= w)).
Definition ctx_ok (rhi : Z) (cx : ictx) : Prop := ctx_lin rhi cx /\ ctx_al cx /\ ctx_sep rhi cx.

Definition ZSEP (P : Prop) : Prop := P.

Section Sep.
  Variables (rhi : Z) (cx : ictx). Hypothesis S : ctx_sep rhi cx.
  Let u := c_u cx. Let p := c_p cx. Let q := c_q cx. Let n := c_n cx.
  Let ob := c_ob cx. Let osz := c_osz cx. Let w := c_w cx.
  Local Ltac sep := pose proof S as S'; unfold ctx_sep in S'; decompose [and] S'; assumption.
  Lemma sep_p_q : p + STATE_SIZE <= q \/ q + n <= p. Proof. sep. Qed.
  Lemma sep_p_ob : p + STATE_SIZE <= ob \/ ob + osz <= p. Proof. sep. Qed.
  Lemma sep_ob_q : ob + osz <= q \/ q + n <= ob. Proof. sep. Qed.
  Lemma sep_ob_u : ob + osz <= u - FRA \/ u + 7 <= ob. Proof. sep. Qed.
  Lemma sep_p_rom : p + STATE_SIZE <= ROM_LO_ALL \/ rhi <= p. Proof. sep. Qed.
  Lemma sep_w_p : w = 0 \/ (p + STATE_SIZE <= w \/ w + WIN_SIZE <= p). Proof. sep. Qed.
  Lemma sep_w_q : w = 0 \/ (w + WIN_SIZE <= q \/ q + n <= w). Proof. sep. Qed.
  Lemma sep_w_ob : w = 0 \/ (w + WIN_SIZE <= ob \/ ob + osz <= w). Proof. sep. Qed.
  Lemma sep_w_rom : w = 0 \/ (w + WIN_SIZE <= ROM_LO_ALL \/ rhi <= w). Proof. sep. Qed.
End Sep.

Record ist := IST {
  t_mode : Z;  t_last : Z;  t_flags : Z;
  t_cin : Z;
  t_cout : Z;
  t_hold : Z;  t_bits : Z;
  t_out : Z;
  t_ret : Z;
  t_length : Z; t_offset : Z; t_extra : Z;
  t_lc : codeptr; t_dc : codeptr;
  t_lb : Z; t_db : Z;
  t_ncode : Z; t_nlen : Z; t_ndist : Z;
  t_shave : Z;
  t_nx : Z;
  t_whave : Z; t_wnext : Z
}.

Definition cp_addr (cx : ictx) (cp : codeptr) : Z :=
  match cp with
  | CDyn ofs => c_p cx + o_codes + 4 * ofs
  | CLenfix => LENFIX_ADDR
  | CDistfix => DISTFIX_ADDR
  end.
Definition rdc (cf : Z -> Z) (cp : codeptr) : Z -> Z :=
  match cp with
  | CDyn ofs => fun i => cf (ofs + i)
  | CLenfix => arr_get lenfix_a
  | CDistfix => arr_get distfix_a
  end.
Definition wsz (cx : ictx) : Z := if c_w cx =? 0 then 0 else WIN_SIZE.

Definition Wm (cx : ictx) (st : ist) : Z :=
  8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st).

Definition rank (m : Z) : Z :=
  if m =? STORED then 30 else if m =? COPY_ then 29 else if m =? COPY then 28
  else if m =? HEAD then 27 else if m =? DICTID then 26 else if m =? DICT then 25
  else if m =? TYPE then 24 else if m =? TYPEDO then 23 else if m =? TABLE then 22
  else if m =? LENLENS then 21 else if m =? CODELENS then 20 else if m =? LEN_ then 19
  else if m =? LEN then 18 else if m =? LENEXT then 17 else if m =? DIST then 16
  else if m =? DISTEXT then 15 else if m =? MATCH then 14 else if m =? LIT then 13
  else if m =? CHECK then 12 else if m =? LENGTH then 11 else if m =? DONE then 10
  else if m =? MEM then 2 else if m =? SYNC then 1 else 0 .

Lemma rank_range : forall m, 0 <= rank m <= 30.
Proof. intros m. unfold rank. repeat (destruct (_ =? _); [lia|]). lia. Qed.

Definition meas (cx : ictx) (st : ist) : Z := 32 * Wm cx st + rank (t_mode st).

Definition meas2 (n osz cin cout bits : Z) : Z := (8 * (n - cin) + bits + (osz - cout)) * 134217728 + (n - cin).

Definition reach (m : Z) : Prop := m = HEAD \/ (DICTID <= m /\ m <= MEM).

Definition codes_liveP (m : Z) : Prop := LEN_ <= m /\ m <= LIT.

Definition tables_live (cx : ictx) (st : ist) (cf : Z -> Z) : Prop :=
  match t_lc st, t_dc st with
  | CLenfix, CDistfix => t_lb st = 9 /\ t_db st = 5
  | CDyn o1, CDyn o2 =>
      o1 = 0 /\ 1 <= t_lb st <= 15 /\ 1 <= t_db st <= 15 /\ 0 <= o2 /\ o2 <= t_nx st /\ t_nx st <= N_CODES /\
      tab_ok LENS (rdc cf (CDyn 0)) (t_lb st) o2 = true /\
      tab_ok DISTS (rdc cf (CDyn o2)) (t_db st) (t_nx st - o2) = true
  | _, _ => False
  end.

Definition ctable_live (st : ist) (cf : Z -> Z) : Prop :=
  t_lc st = CDyn 0 /\ 1 <= t_lb st <= 15 /\ 0 <= t_nx st /\ t_nx st <= N_CODES /\
  tab_ok CODES (rdc cf (CDyn 0)) (t_lb st) (t_nx st) = true.


Definition RNG (cx : ictx) (st : ist) (lf cf : Z -> Z) : Prop :=
  let n := c_n cx in let osz := c_osz cx in
  0 <= t_cin st /\ t_cin st <= n /\ 0 <= t_cout st /\ t_cout st <= osz /\ c_cout0 cx <= t_cout st /\
  0 <= t_bits st /\ t_bits st <= 40 /\ 0 <= t_hold st /\ t_hold st < 2 ^ t_bits st /\
  t_bits st <= 8 * t_cin st /\
  osz - t_cout st <= t_out st /\ t_out st <= osz /\ t_out st - (osz - t_cout st) <= t_cout st /\
  - 2147483648 <= t_last st < 2147483648 /\ (t_flags st = 0 \/ t_flags st = -1) /\
  0 <= t_ret st < 18446744073709551616 /\
  0 <= t_length st < 4294967296 /\ 0 <= t_offset st < 4294967296 /\ 0 <= t_extra st < 4294967296 /\
  0 <= t_lb st < 4294967296 /\ 0 <= t_db st < 4294967296 /\
  0 <= t_ncode st < 4294967296 /\ 0 <= t_nlen st < 4294967296 /\ 0 <= t_ndist st < 4294967296 /\ 0 <= t_shave st < 4294967296 /\
  0 <= t_nx st /\ t_nx st <= N_CODES /\
  match t_lc st with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end /\
  match t_dc st with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end /\
  0 <= t_whave st /\ 0 <= t_wnext st /\
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) /\
  (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296).

Definition WIN (cx : ictx) (st : ist) : Prop :=
  (c_w cx = 0 -> t_whave st = 0 /\ t_wnext st = 0) /\
  (c_w cx <> 0 -> t_whave st <= WIN_SIZE /\ t_wnext st < WIN_SIZE /\ (t_whave st < WIN_SIZE -> t_wnext st = t_whave st)).

Definition PROG (cx : ictx) (st : ist) : Prop :=
  Wm cx st + (t_cout st - c_cout0 cx) <= c_W0 cx /\ (Wm cx st < c_W0 cx \/ c_cin0 cx <= t_cin st) /\
  (t_out st = c_osz cx - c_cout0 cx \/ (t_out st = c_osz cx - t_cout st /\ CHECK < t_mode st)).

Definition MODE (cx : ictx) (st : ist) (lf cf : Z -> Z) : Prop :=
  reach (t_mode st) /\
  (t_flags st = -1 -> (t_mode st = HEAD \/ t_mode st = BAD) /\ t_cout st = 0) /\
  (t_mode st = LENLENS ->
     4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
     257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
     (forall j, 0 <= j < t_shave st -> lf (arr_get order_a j) <= 7)) /\
  (t_mode st = CODELENS ->
     257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
     t_shave st <= t_nlen st + t_ndist st /\
     (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) /\
  (codes_liveP (t_mode st) -> tables_live cx st cf) /\
  (t_mode st = LENEXT -> t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768) /\
  (t_mode st = DIST -> 1 <= t_length st /\ t_length st < 65536) /\
  (t_mode st = DISTEXT -> t_extra st <= 15 /\ 1 <= t_length st /\ t_length st < 65536 /\ t_offset st < 65536) /\
  (t_mode st = MATCH -> 1 <= t_length st /\ t_length st < 65536 /\ t_offset st < 98304) /\
  (t_mode st = COPY_ \/ t_mode st = COPY -> t_length st < 65536).

Definition sinv (cx : ictx) (st : ist) (lf cf : Z -> Z) : Prop :=
  RNG cx st lf cf /\ WIN cx st /\ PROG cx st /\ MODE cx st lf cf.

Definition ainv (cx : ictx) (st : ist) (lf cf : Z -> Z) : Prop :=
  RNG cx st lf cf /\ WIN cx st /\ MODE cx st lf cf.

Lemma Wm_nonneg : forall cx st lf cf, sinv cx st lf cf -> 0 <= Wm cx st.
Proof. intros cx st lf cf (R & _). unfold RNG in R. unfold Wm. lia. Qed.

Lemma meas_nonneg : forall cx st lf cf, sinv cx st lf cf -> 0 <= meas cx st.
Proof. intros cx st lf cf H. pose proof (Wm_nonneg _ _ _ _ H). pose proof (rank_range (t_mode st)). unfold meas. lia. Qed.

Lemma meas_dec_W : forall cx st st', Wm cx st' < Wm cx st -> meas cx st' < meas cx st.
Proof. intros cx st st' H. pose proof (rank_range (t_mode st)). pose proof (rank_range (t_mode st')). unfold meas. lia. Qed.
Lemma meas_dec_rank : forall cx st st', Wm cx st' <= Wm cx st -> rank (t_mode st') < rank (t_mode st) -> meas cx st' < meas cx st.
Proof. intros cx st st' H1 H2. unfold meas. lia. Qed.

Definition rebase (cx : ictx) (cin cout W0 : Z) (K : positive -> Z) : ictx :=
  ICX (c_u cx) (c_p cx) (c_q cx) (c_n cx) (c_ob cx) (c_osz cx) (c_w cx) cin cout W0 K (c_zc cx).
Definition with_win (cx : ictx) (w : Z) : ictx :=
  ICX (c_u cx) (c_p cx) (c_q cx) (c_n cx) (c_ob cx) (c_osz cx) w (c_cin0 cx) (c_cout0 cx) (c_W0 cx) (c_K cx) (c_zc cx).

Lemma wsz_none : forall cx, c_w cx = 0 -> wsz cx = 0.
Proof. intros cx H. unfold wsz. rewrite H. reflexivity. Qed.
Lemma wsz_some : forall cx, c_w cx <> 0 -> wsz cx = WIN_SIZE.
Proof. intros cx H. unfold wsz. destruct (Z.eqb_spec (c_w cx) 0); [contradiction | reflexivity]. Qed.

Definition fp_loop (cx : ictx) : list (Z * Z) :=
  [(c_u cx - FRA, FRA); (c_u cx, ZS_SIZE); (c_p cx, STATE_SIZE); (c_ob cx, c_osz cx)].
Definition fp_win (cx : ictx) : list (Z * Z) := [(c_w cx, WIN_SIZE)].
Definition fp_lib (cx : ictx) : list (Z * Z) :=
  [(c_u cx - FRA, FRA + 112); (c_u cx + 176, 16); (c_p cx, STATE_SIZE); (c_ob cx, c_osz cx)].
