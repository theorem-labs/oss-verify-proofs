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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.I7S Require Import SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_DLOOP1 : Z := 92480.
Definition L_D04 : Z := 92552.
Definition L_DLOOP2 : Z := 92640.
Definition L_D8BC : Z := 92736.
Definition L_DXLOOP : Z := 92852.
Definition L_DX80 : Z := 92928.
Definition L_LXLOOP : Z := 87168.
Definition L_LX60 : Z := 89348.
Definition L_LVX_L1 : Z := 93520.
Definition L_LVX_L2 : Z := 93604.
Definition L_LVX_EXT : Z := 93564.

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

Lemma mask_not_sllw : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl (-1) (k mod 32))) (-1) = 2 ^ k - 1.
Proof.
  intros k Hk. rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (B : 1 <= 2 ^ k <= 1073741824) by (split; [pose proof (pow2_pos k ltac:(lia)); lia | change 1073741824 with (2 ^ 30); apply pow2_le; lia]).
  rewrite swrap32_small by lia. rewrite lxor_m1. lia.
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
Lemma srlw_small : forall x k, 0 <= x < 2147483648 -> 0 <= k <= 31 ->
  bv_swrap 32 (Z.shiftr (x mod 4294967296) (k mod 32)) = x / 2 ^ k.
Proof.
  intros x k Hx Hk. rewrite (Z.mod_small k 32) by lia. rewrite (Z.mod_small x 4294967296) by lia.
  rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos k ltac:(lia)).
  assert (0 <= x / 2 ^ k <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]).
  apply swrap32_small. lia.
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

Ltac tld4_op Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_op (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_bits Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_bits (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_val Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_val (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.
Ltac zlastval := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?x) :: _)) _ _) _ => x end.

Fixpoint keptc (Rb : tree Z) (l : list (positive * Z)) (R' : tree Z) (ks : list positive) : Prop :=
  match ks with
  | [] => True
  | k :: ks' => zget R' k = zget_l Rb l k /\ keptc Rb l R' ks'
  end.
Definition KS_D1 : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 16; 18; 19; 20; 21; 23; 25; 26; 28; 29; 30; 32]%positive.
Definition KS_D2 : list positive := [2; 3; 4; 5; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 23; 26; 27; 28]%positive.
Definition KS_X : list positive := [2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 14; 19; 20; 21; 23; 25; 26; 27; 28; 29; 30; 32]%positive.

Ltac keptc_close := cbv [keptc KS_D1 KS_D2 KS_X]; split_conj; try exact I; zreg.
Ltac keptc_chain HK := cbv [keptc KS_D1 KS_D2 KS_X] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

Lemma d_loop1 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db dm c0 b0 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA5 = da -> zget_l Rb l kA7 = dm -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kT1 = q + ci ->
  zget_l Rb l kT0 = B -> zget_l Rb l kA3 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kA4 = code_bits (rdD (Z.land dm H)) -> zget_l Rb l kA6 = da + 4 * Z.land dm H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdD (Z.land dm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  dm = 2 ^ db - 1 -> 1 <= db -> db <= 15 -> 2 ^ db <= nd -> tab_ok DISTS rdD db nd = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_D1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA3 = B' -> zget R' kT0 = B' -> zget R' kS7 = H' ->
     zget R' kA4 = code_bits (rdD (Z.land dm H')) -> zget R' kA6 = da + 4 * Z.land dm H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdD (Z.land dm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D04 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db dm c0 b0 ci B H fin rdD Hh La5 La7 La2 Lt1 Lt0 La3 Ls7 La4 La6 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP1, L_D04, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  pose proof (land_mask_l H db ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_l H' db ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land dm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Htab (Z.land dm H').
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (rdD (Z.land dm H')))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db dm c0 b0 (ci + 1) (B + 8) H' fin rdD Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.

Lemma d_loop2 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db lo v m2 c1 b1 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kT1 = m2 -> zget_l Rb l kA4 = db -> zget_l Rb l kA6 = v -> zget_l Rb l kA5 = da ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  zget_l Rb l kA7 = n - ci -> zget_l Rb l kT6 = q + ci -> zget_l Rb l kT4 = B -> zget_l Rb l kT0 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kT3 = da + 4 * (v + Z.land H m2 / 2 ^ db) -> zget_l Rb l kT2 = code_bits (rdD (v + Z.land H m2 / 2 ^ db)) ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (db + lo) - 1 -> 1 <= db -> db <= 15 -> 1 <= lo -> lo <= 15 - db -> 0 <= v -> v + 2 ^ lo <= nd -> nd <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdD (v + j))) = false /\ term_ok DISTS (15 - db) (rdD (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_D2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kT5 = q + ci' -> zget R' kA7 = n - ci' -> zget R' kT0 = B' -> zget R' kT4 = B' -> zget R' kS7 = H' ->
     zget R' kT3 = da + 4 * (v + Z.land H' m2 / 2 ^ db) -> zget R' kT2 = code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D8BC (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db lo v m2 c1 b1 ci B H fin rdD Hh Lt1 La4 La6 La5 La2 La3 Ls11
    La7 Lt6 Lt4 Lt0 Ls7 Lt3 Lt2 HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP2, L_D8BC, L_LVX_L2 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (db + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_DISTS in TM0 as [Hbits0 _].
  assert (HB29 : B <= 29) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_r H' (db + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.
  zsetreg (Z.land H' m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_DISTS in TM1 as [Hbits1 _].
  zstep Rfd.
  zsetreg (v + Z.land H' m2 / 2 ^ db) ltac:(lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.
  tld4_bits Htab (v + Z.land H' m2 / 2 ^ db).
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdD Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G31 G18 G6 G30 G24 G29 G8 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.

Lemma x_loop {RCa1 : RunCtx}  : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n ext c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_LXLOOP /\ pcx = L_LX60) \/ (pc = L_DXLOOP /\ pcx = L_DX80)) ->
  m_halted MD = None ->
  zget_l Rb l kA3 = ext -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kA6 = q + ci -> zget_l Rb l kA4 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < ext -> ext <= 15 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_X ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_EXT (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kA5 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA4 = B' -> zget R' kS7 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> ext <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_X ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n ext c0 b0 ci B H fin Hpc Hh La3 La2 La6 La4 Ls7 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hext HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_LXLOOP, L_LX60, L_DXLOOP, L_DX80, L_LVX_EXT in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [-> ->]]; (
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ first [ zbr Rfd true | zbr Rfd false; zstep Rfd ];
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_close ]
    | first [ zbr Rfd false | zbr Rfd true ];
      pose proof (Rfin ci ltac:(lia)) as Rb1;
      tld1 Hin ci Rfin;
      tstep1 Rfd;
      zstep Rfd;
      zstep Rfd;
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia);
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      tstep1 Rfd;
      zstep Rfd;
      zsetreg (H + fin ci * 2 ^ B) ltac:(lia);
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      zstep Rfd;
      destruct (Z_lt_dec (B + 8) ext) as [Hmore | Hdone];
      [ zbr Rfd true;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n ext c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end;
        [ first [left; split; reflexivity | right; split; reflexivity] | ..];
        try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chain HK
      | zbr Rfd false;
        zstep Rfd;
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
        try zreg; try lia; keptc_close ] ]).
Qed.



Definition tabsP {RCa1 : RunCtx}  (cx : ictx) (st : ist) (cf : Z -> Z) (M : mem) (na nd : Z) : Prop :=
  let la := cp_addr cx (t_lc st) in let da := cp_addr cx (t_dc st) in
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na (rdc cf (t_lc st)) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd (rdc cf (t_dc st)) /\
  tab_ok LENS (rdc cf (t_lc st)) (t_lb st) na = true /\ tab_ok DISTS (rdc cf (t_dc st)) (t_db st) nd = true /\
  0 < la /\ la + 4 * na <= c_zc cx /\ 0 < da /\ da + 4 * nd <= c_zc cx /\ na <= 2048 /\ nd <= 2048 /\
  la mod 2 = 0 /\ da mod 2 = 0 /\
  ZSEP (la + 4 * na <= c_ob cx \/ c_ob cx + c_osz cx <= la) /\ ZSEP (la + 4 * na <= c_p cx \/ c_p cx + 1384 <= la) /\
  ZSEP (da + 4 * nd <= c_ob cx \/ c_ob cx + c_osz cx <= da) /\ ZSEP (da + 4 * nd <= c_p cx \/ c_p cx + 1384 <= da) /\
  ZSEP (la + 4 * na <= c_p cx + 7160 \/ c_p cx + 7176 <= la) /\ ZSEP (da + 4 * nd <= c_p cx + 7160 \/ c_p cx + 7176 <= da) /\
  (65536 <= c_p cx -> 65536 <= la /\ 65536 <= da).

Lemma live_tabs {RCa1 : RunCtx}  : forall cx st lf cf M,
  ctx_ok ROMHI_S cx -> RNG cx st lf cf -> tables_live cx st cf -> rom_ok M ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  exists na nd, tabsP cx st cf M na nd.
Proof.
  intros cx st lf cf M CX R TL ROM Hcodes.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  pose proof (sep_p_ob ROMHI_S _ SEP) as Spob. pose proof (sep_p_rom ROMHI_S _ SEP) as Sprom.
  icx_cbn. cbv [STATE_SIZE ROM_LO_ALL ROMHI_S] in Spob, Sprom.
  dand AL as (ALu & ALp & ALw). icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold RNG in R; icx_cbn; cbv [N_CODES N_LENS] in R; destr_conj R.
  unfold tables_live in TL. unfold tabsP. icx_cbn. cbv [N_CODES ] in *.
  destruct lc as [o1 | |]; destruct dc as [o2 | |]; try contradiction.
  -
    dand TL as (Ho1 & Hlb & Hdb & Ho2 & Ho2nx & Hnx & TOKL & TOKD). subst o1.
    exists o2, (nx - o2). unfold cp_addr, rdc. icx_cbn. cbv [o_codes].
    split_conj; try assumption; try (unfold ZSEP; lia).
    + replace (p + 1384 + 4 * 0) with (p + 1384 + 4 * 0) by lia.
      exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf 0 o2 Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf o2 (nx - o2) Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + clear - ALp. Z.to_euclidean_division_equations; lia.
    + clear - ALp Ho2. Z.to_euclidean_division_equations; lia.
  -
    destruct TL as [Hlb Hdb]. subst lb db.
    exists 512, 32. unfold cp_addr, rdc. cbv [LENFIX_ADDR DISTFIX_ADDR].
    split_conj; try exact lenfix_ok; try exact distfix_ok; try (unfold ZSEP; lia).
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 67422 512 lenfix_f). { exact (rom_lenfix_arr M ROM). } exact lenfix_f_model.
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 69470 32 distfix_f). { exact (rom_distfix_arr M ROM). } exact distfix_f_model.
    + reflexivity.
    + reflexivity.
Qed.

Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.

Ltac prog_transfer P :=
  first [ exact P
        | let P1 := fresh in let P2 := fresh in let P3 := fresh in
          dand P as (P1 & P2 & P3); unfold PROG; icx_cbn; split; [exact P1 | split; [exact P2 |]];
          first [ exact P3
                | let E := fresh in let C := fresh in
                  destruct P3 as [E | [E C]];
                  first [ left; exact E
                        | right; split; [exact E | clear - C; modes_cbv; lia_std]
                        | exfalso; clear - C; modes_cbv; lia_std ] ] ].

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
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
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
  dand SI as (R & W & P & Mo).
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
  dand SI as (R & W & P & Mo).
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

Lemma shiftl_3 : forall x, Z.shiftl x (3 mod 64) = 8 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (3 mod 64)) with 8. lia. Qed.

Definition KS_L1 : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 20; 21; 23; 24; 26; 27; 29; 30; 32]%positive.
Ltac keptc_closeL := cbv [keptc KS_L1]; split_conj; try exact I; zreg.

Lemma stub_L1 {RCa1 : RunCtx}  : forall (pc : Z) Rb l M MD T (q n c0 b0 u rv : Z),
  (pc = L_LVX_L1 \/ pc = L_LVX_EXT) -> m_halted MD = None ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 -> zget_l Rb l kSP = u + -224 ->
  0 <= n - c0 -> n - c0 < 4294967296 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -160) rv ->
  (forall R', zget R' kS8 = b0 + 8 * (n - c0) -> zget R' kS11 = q + n -> zget R' kS2 = 0 -> zget R' kS1 = rv ->
     keptc Rb l R' KS_L1 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros pc Rb l M MD T q n c0 b0 u rv Hpc Hh Ls8 Ls0 Ls10 Lsp H1 H2 Hrv K.
  zkeys. unfold L_LVX_L1, L_LVX_EXT, L_LEAVE in *.
  destruct Hpc as [-> | ->].
  - zstep Rfd.
    zstep Rfd.
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeL.
  - zstep Rfd.
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeL.
Qed.

Definition KS_L2 : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 20; 21; 23; 24; 26; 27; 29; 30; 32]%positive.
Lemma stub_L2 {RCa1 : RunCtx}  : forall Rb l M MD T (q n c1 b1 : Z),
  m_halted MD = None ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  0 <= n - c1 -> n - c1 < 4294967296 ->
  (forall R', zget R' kS8 = b1 + 8 * (n - c1) -> zget R' kS11 = q + n -> zget R' kS2 = 0 ->
     keptc Rb l R' KS_L2 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c1 b1 Hh La2 La3 Ls11 H1 H2 K.
  zkeys. unfold L_LVX_L2, L_LEAVE_LD in *.
  zstep Rfd.
  zstep Rfd.
  zsetreg (8 * (n - c1)) ltac:(symmetry; apply shiftl_3).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg.
  cbv [keptc KS_L2]; split_conj; try exact I; zreg.
Qed.

Definition st_w3 (st : ist) (len off ex : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len off ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_w3 in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split;
  first [ apply mem_u32_stored; clear - Hp1 Hp2; lia_std
        | (apply mem_u64_frame || apply mem_u32_frame); [assumption | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std] ].
Lemma st_rest_set92 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st v (t_offset st) (t_extra st)) (wbytes M (w64 (c_p cx + 108)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set96 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) v (t_extra st)) (wbytes M (w64 (c_p cx + 112)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set100 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) (t_offset st) v) (wbytes M (w64 (c_p cx + 116)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Ltac st_prestore lem v SREST :=
  let SR1 := fresh "SR1" in
  pose proof (lem _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1;
  unfold st_w3 in SR1;
  cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1;
  clear SREST; rename SR1 into SREST.
Ltac st_prestore_k lem k SREST :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with
    | Some ?v => st_prestore lem v SREST
    | _ => fail "st_prestore_k: register not in the update list" k
    end
  end.

Ltac prune_rng :=
  repeat match goal with
  | H : _ < 4294967296 |- _ => clear H | H : 0 <= _ < 18446744073709551616 |- _ => clear H | H : _ < 18446744073709551616 |- _ => clear H
  | H : - 2147483648 <= _ |- _ => clear H | H : _ < 2147483648 |- _ => clear H | H : - 2147483648 <= _ < 2147483648 |- _ => clear H
  end.
