(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Image.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memcpy_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fwritex_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_pad_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_main_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_splitR.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_splitH.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_lib_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_calls_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre3_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Lemma lxor_sign_lt : forall x y, (-2^63 <= x < 2^63)%Z -> (-2^63 <= y < 2^63)%Z ->
  (Z.lxor (Z.land x 18446744073709551615) 9223372036854775808 <? Z.lxor (Z.land y 18446744073709551615) 9223372036854775808) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. rewrite !land_W64. change 9223372036854775808%Z with (2^63)%Z.
  rewrite !zb_lxor_sign by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec0 x y); [apply Z.ltb_lt | apply Z.ltb_ge]; mlia.
Qed.
Lemma lxor_sign_lt_m4 : forall x, (-2^63 <= x < 2^63)%Z ->
  (Z.lxor (Z.land x 18446744073709551615) 9223372036854775808 <? 9223372036854775804) = (x <? -4)%Z.
Proof. intros x Hx. rewrite <- (lxor_sign_lt x (-4)) by lia. reflexivity. Qed.
Lemma ltb1_eqb0 : forall p, (0 <= p)%Z -> (p <? 1) = (p =? 0)%Z.
Proof. intros p Hp. destruct (Z.ltb_spec0 p 1), (Z.eqb_spec p 0); try reflexivity; lia. Qed.
Lemma lnot_W64 : forall e, Z.lxor (Z.land e 18446744073709551615) 18446744073709551615 = Z.land (- e - 1) 18446744073709551615.
Proof.
  intros e. pose proof (Z.mod_pos_bound e (2^64) ltac:(lia)).
  rewrite zb_lxor_ones by (rewrite land_W64; lia). rewrite !land_W64. mlia.
Qed.

(* [comment removed for export] *)
Definition gadj_pp (p : Z) : Z := (p + Z.b2z (p <? 1))%Z.
Definition gadj_c1 (p e : Z) : Z :=
  Z.b2z (Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 <? Z.lxor (Z.land (gadj_pp p) 18446744073709551615) 9223372036854775808)%Z.
Definition gadj_c2 (e : Z) : Z := Z.lxor (Z.b2z (Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 <? 9223372036854775804)%Z) 1.

Lemma gadj_pp_eq : forall p, (0 <= p)%Z -> gadj_pp p = (if p =? 0 then p + 1 else p)%Z.
Proof. intros p Hp. unfold gadj_pp. rewrite ltb1_eqb0 by lia. destruct (p =? 0)%Z; cbn; lia. Qed.
Lemma gadj_c12 : forall p e, (0 <= p < 2^62)%Z -> (-2^62 <= e < 2^62)%Z ->
  Z.land (gadj_c1 p e) (gadj_c2 e) = Z.b2z (gadj_cond p e).
Proof.
  intros p e Hp He. unfold gadj_c1, gadj_c2, gadj_cond. rewrite <- gadj_pp_eq by lia.
  pose proof (gadj_pp_eq p ltac:(lia)) as E. assert (Rpp : (0 <= gadj_pp p < 2^62 + 1)%Z) by (rewrite E; destruct (p =? 0)%Z; lia).
  rewrite lxor_sign_lt, lxor_sign_lt_m4 by lia.
  destruct (Z.ltb_spec0 e (gadj_pp p)), (Z.ltb_spec0 e (-4)), (Z.leb_spec0 (-4) e); try lia; reflexivity.
Qed.
Lemma gadj_t4 : forall t p e, (2 <= t < 2^31)%Z -> (0 <= p < 2^62)%Z -> (-2^62 <= e < 2^62)%Z ->
  bv_swrap 32 (Z.land (t + Z.land (gadj_c1 p e) (gadj_c2 e)) 18446744073709551615 + -2)
  = (if gadj_cond p e then t - 1 else t - 2)%Z.
Proof.
  intros t p e Ht Hp He. rewrite gadj_c12 by lia. rewrite land_W64, swrap32_eq. destruct (gadj_cond p e); cbn [Z.b2z]; mlia.
Qed.
Lemma gadj_s2 : forall p e, (0 <= p < 2^30)%Z -> (-2^30 <= e < 2^30)%Z ->
  bv_swrap 32 (Z.lor (Z.land (Z.land (gadj_c1 p e) (gadj_c2 e) + -1) 18446744073709551615)
                     (Z.lxor (Z.land e 18446744073709551615) 18446744073709551615)
               + Z.land (gadj_pp p) 18446744073709551615)
  = (let p' := (if p =? 0 then p + 1 else p)%Z in if gadj_cond p e then p' - (e + 1) else p' - 1)%Z.
Proof.
  intros p e Hp He. rewrite gadj_c12 by lia. rewrite <- gadj_pp_eq by lia. cbv zeta.
  pose proof (gadj_pp_eq p ltac:(lia)) as E. assert (Rpp : (0 <= gadj_pp p < 2^30 + 1)%Z) by (rewrite E; destruct (p =? 0)%Z; lia).
  rewrite (land_W64_small (gadj_pp p)) by lia. rewrite lnot_W64.
  destruct (gadj_cond p e); cbn [Z.b2z Z.add].
  - change (Z.land 0 18446744073709551615) with 0%Z. rewrite Z.lor_0_l. rewrite land_W64, swrap32_eq. mlia.
  - replace (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615%Z by reflexivity.
    replace (Z.lor 18446744073709551615 (Z.land (- e - 1) 18446744073709551615)) with 18446744073709551615%Z.
    2:{ pose proof (Z.mod_pos_bound (-e-1) (2^64) ltac:(lia)) as Hy. rewrite land_W64.
        set (y := ((- e - 1) mod 2 ^ 64)%Z) in *. clearbody y.
        change 18446744073709551615%Z with (Z.ones 64).
        destruct (Z.eq_dec y 0) as [->|Hne]; [reflexivity|].
        symmetry. rewrite Z.lor_comm. apply Z.lor_ones_low; [lia|]. apply Z.log2_lt_pow2; lia. }
    rewrite swrap32_eq. mlia.
Qed.

Lemma lor32_eq : forall t c, Z.lor t 32 = c -> (t = c \/ t = c - 32)%Z.
Proof.
  intros t c H. pose proof (Z.add_lor_land t 32) as E. rewrite H in E.
  assert (L : Z.land t 32 = (32 * ((t / 32) mod 2))%Z) by (change 32%Z with (2^5)%Z at 1 2; rewrite zb_land_pow2 by lia; reflexivity).
  rewrite L in E. pose proof (Z.mod_pos_bound (t / 32) 2 ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma andn32_70 : forall t, (0 <= t)%Z -> (Z.land t (-33) = 70 <-> Z.lor t 32 = 102)%Z.
Proof.
  intros t Ht.
  assert (L : Z.land t 32 = (32 * ((t / 32) mod 2))%Z) by (change 32%Z with (2^5)%Z at 1 2; rewrite zb_land_pow2 by lia; reflexivity).
  pose proof (Z.add_lor_land t 32) as E1.
  assert (E2 : Z.land t (-33) = (t - Z.land t 32)%Z).
  { change (-33)%Z with (Z.lnot 32). rewrite <- Z.ldiff_land.
    pose proof (Z.add_lor_land (Z.ldiff t 32) (Z.land t 32)) as E. rewrite Z.lor_ldiff_and in E.
    replace (Z.land (Z.ldiff t 32) (Z.land t 32)) with 0%Z in E; [lia|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit t n), (Z.testbit 32 n); reflexivity. }
  pose proof (Z.mod_pos_bound (t / 32) 2 ltac:(lia)). rewrite E2. split; intros; lia.
Qed.

(* [comment removed for export] *)
Lemma landW_shl1_9 : forall k, Z.land (Z.shiftl (Z.land (4 * k) 18446744073709551615) 1 + k) 18446744073709551615 = Z.land (9 * k) 18446744073709551615.
Proof. intros k. rewrite !land_W64, Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z. mlia. Qed.
Lemma landW_inner : forall x y, Z.land (Z.land x 18446744073709551615 + y) 18446744073709551615 = Z.land (x + y) 18446744073709551615.
Proof. intros. rewrite !land_W64. mlia. Qed.
Lemma landW_inner_sub : forall x j y, Z.land (Z.land x 18446744073709551615 - j + y) 18446744073709551615 = Z.land (x - j + y) 18446744073709551615.
Proof. intros. rewrite !land_W64. mlia. Qed.
Lemma sgtz_max : forall X, (-2^62 <= X < 2^62)%Z ->
  Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land X 18446744073709551615) 9223372036854775808)) 18446744073709551615)
         (Z.land X 18446744073709551615) = Z.max 0 X.
Proof.
  intros X HX. change 9223372036854775808%Z with (2^63)%Z. rewrite (land_W64 X).
  rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec0 (2^63) ((X mod 2^64 + 2^63) mod 2^64)) as [H|H]; cbn [Z.b2z Z.sub].
  - change (Z.land (0 - 1) 18446744073709551615) with 18446744073709551615%Z.
    rewrite Z.land_comm, land_W64. mlia.
  - change (Z.land (0 - 0) 18446744073709551615) with 0%Z. rewrite Z.land_0_l. mlia.
Qed.
Lemma land_t_m33 : forall t, (0 <= t < 2^64)%Z -> Z.land t 18446744073709551583 = Z.land t (-33).
Proof.
  intros t Ht. change 18446744073709551583%Z with (Z.land (Z.ones 64) (-33)). rewrite Z.land_assoc.
  rewrite Z.land_ones_low; [reflexivity| lia |]. destruct (Z.eq_dec t 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Ltac weq := apply Z_to_bv_eqm; rewrite ?land_W64; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.shiftr_div_pow2 by lia;
            change (2^1)%Z with 2%Z; change (2^2)%Z with 4%Z; change (2^3)%Z with 8%Z; mlia.

(* [comment removed for export] *)
Definition rot10 (v : Z) : Z :=
  Z.lor (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (v * 18446744072850558157) 18446744073709551615)) 1)) 18446744073709551615)
        (Z.land (bv_swrap 32 (Z.shiftl (Z.land (v * 18446744072850558157) 18446744073709551615) 31)) 18446744073709551615).

Lemma land_small_mul_2p31 : forall a k, (0 <= a < 2^31)%Z -> Z.land a (k * 2^31) = 0%Z.
Proof.
  intros a k Ha. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 31).
  - rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
  - rewrite (Z.bits_above_log2 a n); [reflexivity|lia|].
    destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma rot10_eq : forall v, (0 <= v)%Z ->
  let x32 := ((v * 3435973837) mod 2^32)%Z in
  rot10 v = (x32 / 2 + (x32 mod 2) * (8589934591 * 2^31))%Z.
Proof.
  intros v Hv. cbv zeta. unfold rot10.
  rewrite (land_W64 (v * _)).
  assert (EM : ((v * 18446744072850558157) mod 2 ^ 64) mod 2^32 = ((v * 3435973837) mod 2^32)%Z).
  { rewrite Z.mod_mod_divide by (exists (2^32)%Z; reflexivity).
    rewrite (Z.mul_mod v 18446744072850558157), (Z.mul_mod v 3435973837) by lia.
    replace (18446744072850558157 mod 2 ^ 32)%Z with (3435973837 mod 2 ^ 32)%Z by reflexivity. reflexivity. }
  set (x := ((v * 18446744072850558157) mod 2 ^ 64)%Z) in *.
  assert (Rx : (0 <= x < 2^64)%Z) by (subst x; apply Z.mod_pos_bound; lia).
  set (x32 := ((v * 3435973837) mod 2 ^ 32)%Z) in *.
  assert (Rx32 : (0 <= x32 < 2^32)%Z) by (subst x32; apply Z.mod_pos_bound; lia).
  assert (Ex2 : (x mod 2 = x32 mod 2)%Z).
  { rewrite <- EM. rewrite Z.mod_mod_divide by (exists (2^31)%Z; reflexivity). reflexivity. }
  (* [comment removed for export] *)
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite EM.
  rewrite (Z.shiftr_div_pow2 x32 1) by lia. change (2^1)%Z with 2%Z.
  replace (bv_swrap 32 (x32 / 2)) with (x32 / 2)%Z by (rewrite swrap32_eq; mlia).
  rewrite (land_W64_small (x32 / 2)) by mlia.
  (* [comment removed for export] *)
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (Z.land (bv_swrap 32 (x * 2 ^ 31)) 18446744073709551615) with ((x32 mod 2) * (8589934591 * 2^31))%Z.
  2:{ rewrite land_W64, swrap32_eq, <- Ex2. change (2^64)%Z with 18446744073709551616%Z. change (2^31)%Z with 2147483648%Z. mlia. }
  (* [comment removed for export] *)
  pose proof (Z.add_lor_land (x32 / 2) (x32 mod 2 * (8589934591 * 2 ^ 31))) as E.
  rewrite Z.mul_assoc, land_small_mul_2p31 in E by mlia. rewrite Z.mul_assoc. lia.
Qed.

Lemma rot10_spec : forall v, (0 <= v < 2^32)%Z -> (rot10 v <= 429496729 <-> v mod 10 = 0)%Z.
Proof.
  intros v Hv. rewrite rot10_eq by lia. cbv zeta.
  pose proof (Z.div_mod v 10 ltac:(lia)) as Ev. pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as Rs.
  set (q := (v / 10)%Z) in *. set (s := (v mod 10)%Z) in *. clearbody q s. subst v.
  replace ((10 * q + s) * 3435973837)%Z with ((2 * q + s * 3435973837) + (8 * q) * 2^32)%Z by lia.
  rewrite Z.mod_add by lia.
  assert (Hs : (s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6 \/ s = 7 \/ s = 8 \/ s = 9)%Z) by lia.
  change (2^32)%Z with 4294967296%Z. change (2^31)%Z with 2147483648%Z.
  destruct Hs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; mlia.
Qed.

Lemma remuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
  v_remuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v mod i)%Z.
Proof.
  intros v i Hv Hi. unfold v_remuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite (Z.mod_small i 4294967296), (Z.mod_small v 4294967296) by lia. destruct (Z.eqb_spec i 0); [lia|].
  f_equal. rewrite swrap32_eq. pose proof (Z.mod_pos_bound v i ltac:(lia)).
  rewrite (Z.mod_small (v mod i + 2147483648) 4294967296) by lia. lia.
Qed.
Lemma pow10_le_v : forall n v, (0 <= n)%Z -> (10 ^ n <= v)%Z -> (v < 1000000000)%Z -> (n <= 8)%Z.
Proof.
  intros n v Hn Hle Hv. destruct (Z.le_gt_cases n 8); [assumption|].
  assert (10 ^ 9 <= 10 ^ n)%Z by (apply Z.pow_le_mono_r; lia). change (10^9)%Z with 1000000000%Z in H0. lia.
Qed.
Lemma rot10_range : forall v, (0 <= v)%Z -> (0 <= rot10 v < 2^64)%Z.
Proof.
  intros v Hv. rewrite rot10_eq by lia. cbv zeta.
  pose proof (Z.mod_pos_bound (v * 3435973837) (2^32) ltac:(lia)). mlia.
Qed.

(* [comment removed for export] *)
Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^3)%Z with (2^67)%Z.
  pose proof (Z.div_mod x 10 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R.
  pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 10 (2^64) ltac:(lia) ltac:(lia)) as Q1.
  set (q := (x / 10)%Z) in *. set (s := (x mod 10)%Z) in *. clearbody q s. subst x.
  symmetry. apply (Z.div_unique_pos _ _ _ (2 * q + s * 14757395258967641293)%Z).
  - change (2^67)%Z with 147573952589676412928%Z. change (2^64)%Z with 18446744073709551616%Z in Q1. lia.
  - change (2^67)%Z with 147573952589676412928%Z. lia.
Qed.

Lemma palt_eq : forall p2 a8 fl, (0 <= p2)%Z -> (0 <= a8)%Z -> (a8 = 0%Z <-> Z.land fl 8 = 0%Z) ->
  (if negb (p2 =? 0)%Z || negb (Z.land fl 8 =? 0)%Z then 1%Z else 0%Z) = Z.b2z (0 <? Z.lor p2 a8)%Z.
Proof.
  intros p2 a8 fl Hp Ha [H1 H2].
  pose proof (Z.lor_nonneg p2 a8) as N. pose proof (Z.lor_eq_0_iff p2 a8) as [E1 E2].
  destruct (Z.eqb_spec p2 0) as [Hp0|Hp0]; destruct (Z.eqb_spec (Z.land fl 8) 0) as [Hf|Hf]; destruct (Z.ltb_spec0 0 (Z.lor p2 a8)) as [L|L]; cbn; try reflexivity; exfalso.
  - pose proof (H2 Hf). rewrite E2 in L by lia. lia.
  - assert (Z.lor p2 a8 = 0%Z) by lia. destruct (E1 H). pose proof (H1 H3). congruence.
  - assert (Z.lor p2 a8 = 0%Z) by lia. destruct (E1 H). lia.
  - assert (Z.lor p2 a8 = 0%Z) by lia. destruct (E1 H). lia.
Qed.

(* [comment removed for export] *)
Lemma abs32_trick : forall e, (-2^31 < e < 2^31)%Z ->
  bv_swrap 32 (Z.lxor (Z.land e 18446744073709551615)
                      (Z.land (bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land e 18446744073709551615)) 31)) 18446744073709551615)
               - Z.land (bv_swrap 32 (Z.shiftr (bv_swrap 32 (Z.land e 18446744073709551615)) 31)) 18446744073709551615)
  = Z.abs e.
Proof.
  intros e He. rewrite (land_W64 e).
  assert (E1 : bv_swrap 32 (e mod 2 ^ 64) = e).
  { rewrite swrap32_eq. change (2^64)%Z with 18446744073709551616%Z. mlia. }
  rewrite E1. rewrite Z.shiftr_div_pow2 by lia. change (2^31)%Z with 2147483648%Z.
  destruct (Z.lt_ge_cases e 0) as [Hn|Hp].
  - replace (e / 2147483648)%Z with (-1)%Z by mlia. change (bv_swrap 32 (-1)) with (-1)%Z.
    change (Z.land (-1) 18446744073709551615) with 18446744073709551615%Z.
    rewrite zb_lxor_ones by mlia. rewrite swrap32_eq. mlia.
  - replace (e / 2147483648)%Z with 0%Z by mlia. change (bv_swrap 32 0) with 0%Z.
    change (Z.land 0 18446744073709551615) with 0%Z. rewrite Z.lxor_0_r. rewrite swrap32_eq. mlia.
Qed.

Definition K_set12 (K : midK) (eb : list byte) : midK :=
  MidK (K_pad K) (K_jk40 K) (K_jk8 K) (K_jk3 K) eb (K_jk37 K) (K_p1 K) (K_prefix K) (K_pl K) (K_plz K) (K_pfx K) (K_Ft K).
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof.
  intros d Hd.
  assert (H : (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9)%Z) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity.
Qed.
Inductive lboxed : list Z -> list Z -> Prop := LBoxed : forall a, lboxed a a.
Lemma lboxed_intro : forall b : list Z, exists a, lboxed a b.
Proof. intros b. exists b. constructor. Qed.
Lemma rw_cells_CB_length : forall m A n (bs : list byte) rest, rw_cells rsegs m A (CB n bs :: rest) -> length bs = n.
Proof. intros m A n bs rest [[Hwf _] _]. cbn in Hwf. destruct Hwf as [H _]. exact H. Qed.
Lemma sign_trick : forall e, (-2^62 <= e < 2^62)%Z ->
  (Z.land (Z.shiftr (Z.land e 18446744073709551615) 62) 2 + 43)%Z = (if e <? 0 then 45 else 43)%Z.
Proof.
  intros e He. rewrite land_W64, Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec0 e 0).
  - replace (e mod 2 ^ 64 / 2 ^ 62)%Z with 3%Z by mlia. reflexivity.
  - replace (e mod 2 ^ 64 / 2 ^ 62)%Z with 0%Z by mlia. reflexivity.
Qed.
Lemma u8_small : forall t, (0 <= t < 256)%Z -> u8 t = t.
Proof. intros t Ht. unfold u8. apply Z.mod_small. lia. Qed.

Lemma bytes_at_slice : forall m a (bs : list byte) i n, bytes_at rsegs m a bs -> (i + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros m a bs i n H Hin.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.
Lemma zb_zsub : forall l i n, (0 <= i)%Z -> (0 <= n)%Z -> zb (zsub l i n) = firstn (Z.to_nat n) (skipn (Z.to_nat i) (zb l)).
Proof. intros. unfold zb, zsub. rewrite <- firstn_map, <- skipn_map. reflexivity. Qed.
Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply map_length. Qed.
Lemma zb_app : forall l1 l2, zb (l1 ++ l2) = zb l1 ++ zb l2.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zsub_length : forall l i n, (0 <= i)%Z -> (0 <= n)%Z -> (Z.to_nat i + Z.to_nat n <= length l)%nat -> length (zsub l i n) = Z.to_nat n.
Proof. intros. unfold zsub. rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia. Qed.
Lemma pad_id : forall o c w l fl, (w <= l)%Z -> pad o c w l fl = Some o.
Proof.
  intros. unfold pad. rewrite (proj2 (Z.leb_le w l)) by lia. rewrite Bool.orb_true_r. reflexivity.
Qed.
Lemma land_le_r : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.land a b <= b)%Z.
Proof.
  intros a b Ha Hb.
  assert (E : Z.ldiff (Z.land a b) b = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit b n), (Z.testbit a n); reflexivity. }
  pose proof (Z.ldiff_le _ _ Hb E). lia.
Qed.

(* [comment removed for export] *)
Lemma fwritex_callR : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  rw_cells rsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk)) (B + Z.of_nat (length content)) j2 lbfw) ->
  rw_cells rsegs m B [CB (length content) content; CB (length junk) junk] ->
  Z.land (bv_unsigned fl0) 32 = 0%Z -> (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z ->
  (0 < B)%Z -> (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z ->
  (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z ->
  bytes_at rsegs m S bs ->
  Z.of_nat (length bs) = L ->
  (length bs <= length junk)%nat ->
  stk rsegs m (q - 64) q ->
  mem_inv rsegs m ->
  (64 <= q < 2^64)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
  (Fp + 148 <= q - 64 \/ q <= Fp)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= q - 64 \/ q <= B)%Z ->
  (S + L <= q - 64 \/ q <= S)%Z ->
  (S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
  (S + L <= Fp \/ Fp + 148 <= S)%Z ->
  evt rsegs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk S bs m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb3290) fc None m (seg_rom rsegs)).
Proof.
  intros. apply fwritex_call; try assumption. unfold wfile. cbv delta [F_memcpy_u5.rsegs]. cbv delta [rsegs] in *.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
Definition K_set37 (K : midK) (bf : list byte) : midK :=
  MidK (K_pad K) (K_jk40 K) (K_jk8 K) (K_jk3 K) (K_jk12 K) bf (K_p1 K) (K_prefix K) (K_pl K) (K_plz K) (K_pfx K) (K_Ft K).
Lemma pow10_succ : forall s, (1 <= s)%Z -> (10 ^ s = 10 * 10 ^ (s - 1))%Z.
Proof. intros s Hs. replace s with (Z.succ (s - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rel_slice9 : forall (bf : list byte) (b : list Z) s,
  (forall i, (s <= i < 9)%Z -> nth_error bf (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
  (9 <= length bf)%nat -> (9 <= length b)%nat -> (0 <= s <= 9)%Z ->
  firstn (Z.to_nat (9 - s)) (skipn (Z.to_nat s) bf) = zb (zsub b s (9 - s)).
Proof.
  intros bf b s REL Lbf Lb Hs. rewrite zb_zsub by lia. unfold zb.
  apply nth_error_ext. intros n.
  rewrite !nth_error_firstn.
  destruct (PeanoNat.Nat.ltb_spec0 n (Z.to_nat (9 - s))); [|reflexivity].
  rewrite !nth_error_skipn, nth_error_map.
  replace (Z.to_nat s + n)%nat with (Z.to_nat (s + Z.of_nat n)) by lia.
  rewrite (REL (s + Z.of_nat n)%Z) by lia.
  destruct (nth_error b (Z.to_nat (s + Z.of_nat n))) as [v|] eqn:E.
  - cbn [option_map]. f_equal. f_equal. unfold znth. destruct (Z.ltb_spec0 (s + Z.of_nat n) 0); [lia|].
    erewrite nth_error_nth; [reflexivity | exact E].
  - apply nth_error_None in E. lia.
Qed.
Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. intros. unfold zx32, wval. f_equal. Qed.
Lemma dot_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 69572 [Z_to_bv 8 46].
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma rel_slice : forall (bf : list byte) (b : list Z) s n,
  (forall i, (s <= i < 9)%Z -> nth_error bf (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
  (9 <= length bf)%nat -> (9 <= length b)%nat -> (0 <= s)%Z -> (0 <= n)%Z -> (s + n <= 9)%Z ->
  firstn (Z.to_nat n) (skipn (Z.to_nat s) bf) = zb (zsub b s n).
Proof.
  intros bf b s n REL Lbf Lb Hs Hn Hsn. rewrite zb_zsub by lia. unfold zb.
  apply nth_error_ext. intros k.
  rewrite !nth_error_firstn.
  destruct (PeanoNat.Nat.ltb_spec0 k (Z.to_nat n)); [|reflexivity].
  rewrite !nth_error_skipn, nth_error_map.
  replace (Z.to_nat s + k)%nat with (Z.to_nat (s + Z.of_nat k)) by lia.
  rewrite (REL (s + Z.of_nat k)%Z) by lia.
  destruct (nth_error b (Z.to_nat (s + Z.of_nat k))) as [v|] eqn:E.
  - cbn [option_map]. f_equal. f_equal. unfold znth. destruct (Z.ltb_spec0 (s + Z.of_nat k) 0); [lia|].
    erewrite nth_error_nth; [reflexivity | exact E].
  - apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma pad_callR : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  rw_cells rsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk)) (B + Z.of_nat (length content)) j2 lbfw) ->
  rw_cells rsegs m B [CB (length content) content; CB (length junk) junk] ->
  Z.land (bv_unsigned fl0) 32 = 0%Z -> (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z ->
  (0 < B)%Z -> (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z ->
  (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z ->
  rw_cells rsegs m 827936 [C8 (Z_to_bv 64 1036928)] -> rw_cells rsegs m 1036928 [C8 canary] ->
  stk rsegs m (q - 368) q ->
  mem_inv rsegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (1036928 + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  evt rsegs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4850) fc None m (seg_rom rsegs)).
Proof.
  intros. apply pad_call; try assumption.
  - unfold wfile. cbv delta [F_memcpy_u5.rsegs]. cbv delta [rsegs] in *.
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  - unfold ssp_cells, got_ssp, ssp_guard. cbv delta [F_memcpy_u5.rsegs]. cbv delta [rsegs] in *. split; assumption.
Qed.

Lemma fint_d : forall k big a r d o d' o', fmt_fp_fint k big a r (d, o) = Some (d', o') -> (d <= r + 1)%Z -> d' = (r + 1)%Z.
Proof.
  induction k as [|k IH]; intros big a r d o d' o' H Hd; [discriminate H|].
  rewrite fmt_fp_fint_step in H. destruct (Z.leb_spec0 d r).
  - unfold fmt_fp_fint_body in H. destruct (fmt_u (znth big d) (zrepeat 0 37) 9) as [[s b]|]; [|discriminate H].
    destruct (if negb (d =? a) then _ else _) as [[s1 b1]|]; [|discriminate H].
    apply IH in H; lia.
  - injection H as <- <-. lia.
Qed.
Lemma F2_extends : forall o big z p fl d o2, ffp_F2 o big z p fl d = Some o2 -> extends o o2.
Proof.
  intros o big z p fl d o2 H. unfold ffp_F2 in H.
  destruct (fmt_fp_ffrac BIG_FUEL big z _) as [[[d3 p3] o3]|] eqn:E; [|discriminate H].
  apply ffrac_extends in E. apply pad_extends in H.
  eapply extends_trans; [|eapply extends_trans; [exact E | exact H]].
  destruct (negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0))%Z; [apply extends_out | apply extends_refl].
Qed.

(* [comment removed for export] *)
Lemma landW_sign : forall x, (-2^63 <= x < 2^63)%Z -> (Z.land x 18446744073709551615 < 9223372036854775808 <-> 0 <= x)%Z.
Proof. intros x Hx. rewrite land_W64. change 9223372036854775808%Z with (2^63)%Z. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma rel_sliceN : forall (bf : list byte) (b : list Z) N s n,
  (forall i, (s <= i < N)%Z -> nth_error bf (Z.to_nat i) = Some (Z_to_bv 8 (znth b i))) ->
  (Z.to_nat N <= length bf)%nat -> (Z.to_nat N <= length b)%nat -> (0 <= s)%Z -> (0 <= n)%Z -> (s + n <= N)%Z ->
  firstn (Z.to_nat n) (skipn (Z.to_nat s) bf) = zb (zsub b s n).
Proof.
  intros bf b N s n REL Lbf Lb Hs Hn Hsn. rewrite zb_zsub by lia. unfold zb.
  apply nth_error_ext. intros k.
  rewrite !nth_error_firstn.
  destruct (PeanoNat.Nat.ltb_spec0 k (Z.to_nat n)); [|reflexivity].
  rewrite !nth_error_skipn, nth_error_map.
  replace (Z.to_nat s + k)%nat with (Z.to_nat (s + Z.of_nat k)) by lia.
  rewrite (REL (s + Z.of_nat k)%Z) by lia.
  destruct (nth_error b (Z.to_nat (s + Z.of_nat k))) as [v|] eqn:E.
  - cbn [option_map]. f_equal. f_equal. unfold znth. destruct (Z.ltb_spec0 (s + Z.of_nat k) 0); [lia|].
    erewrite nth_error_nth; [reflexivity | exact E].
  - apply nth_error_None in E. lia.
Qed.
