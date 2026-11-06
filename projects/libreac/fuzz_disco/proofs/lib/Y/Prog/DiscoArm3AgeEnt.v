(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths changed; 216 of its 242 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3AgeShort.v; 870 of its 927 lines of code are new or changed and 185 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3 DiscoArm3TailK DiscoArm3AgeSt DiscoArm3AgeKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
slot_inv disco_table_c reac_disco_table_age_c disco_table.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition LH_OFF : Z := 0x944.
Definition e_ex (T : list byte) : list word := [Z_to_bv 64 (u_at T 384 4); Z_to_bv 64 (u_at T 392 4)].
Definition e_fcs : list YP09.chunk :=
  [YP09.mkChunk 2544 (CVal 4 (SOff 563 0)); YP09.mkChunk 2552 (CVal 4 (SOff 564 0))].
Definition e_cnt (T : list byte) (now j : Z) : Z := age_count (fun x => disco_stale T x now) (Z.to_nat j).
Definition e_win_ok (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some 60%nat) && (192 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 208))) rs.

Lemma e_cnt_S : forall T now j, 0 <= j ->
  e_cnt T now (j + 1) = e_cnt T now j + (if disco_stale T j now then 1 else 0).
Proof.
intros T now j Hj. unfold e_cnt. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
cbn [age_count]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma e_cnt_rng : forall T now j, 0 <= j -> 0 <= e_cnt T now j <= j.
Proof.
intros T now j Hj. unfold e_cnt.
assert (H : forall m : nat, 0 <= age_count (fun x => disco_stale T x now) m <= Z.of_nat m).
{ induction m as [|m IH]; cbn [age_count]; [lia|]. destruct (disco_stale T (Z.of_nat m) now); lia. }
specialize (H (Z.to_nat j)). lia.
Qed.

Lemma e_stale_ge : forall T j now, now <= last_of T j -> disco_stale T j now = false.
Proof.
intros T j now H. unfold disco_stale. rewrite (proj2 (Z.ltb_ge (last_of T j) now) ltac:(lia)). reflexivity.
Qed.

Lemma e_stale_near : forall T j now, now - last_of T j < REAC_DISCO_STALE_NS + 1 -> disco_stale T j now = false.
Proof.
intros T j now H. unfold disco_stale.
rewrite (proj2 (Z.ltb_ge REAC_DISCO_STALE_NS (now - last_of T j)) ltac:(lia)). apply andb_false_r.
Qed.

Lemma e_stale_yes : forall T j now, last_of T j < now -> REAC_DISCO_STALE_NS + 1 <= now - last_of T j ->
  disco_stale T j now = true.
Proof.
intros T j now H1 H2. unfold disco_stale.
rewrite (proj2 (Z.ltb_lt (last_of T j) now) ltac:(lia)), (proj2 (Z.ltb_lt REAC_DISCO_STALE_NS (now - last_of T j)) ltac:(lia)).
reflexivity.
Qed.

Lemma e_u_rng : forall (T : list byte) k m, 0 <= k -> (Z.to_nat k + m <= length T)%nat ->
  0 <= u_at T k m < 2 ^ (8 * Z.of_nat m).
Proof.
intros T k m Hk Hm. unfold u_at.
assert (LS : length (sub T k m) = m) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_bound (sub T k m)) as Hb. rewrite LS in Hb.
pose proof (bytes_le_to_Z_nonneg (sub T k m)) as Hb0. lia.
Qed.

Lemma e_u_of_n : forall T : list byte, length T = 400%nat -> 0 <= n_of T -> u_at T 384 4 = n_of T.
Proof.
intros T LT Hn. unfold n_of, s32_at in *.
pose proof (e_u_rng T 384 4 ltac:(lia) ltac:(lia)) as Hb. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.

Lemma e_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Lemma e_ble_digit : forall (bs : list byte) j, (j < length bs)%nat ->
  (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat j)) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; [cbn in Hj; lia|].
rewrite e_ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth length] in *. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
  rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
  change (2 ^ 8) with 256.
  replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs).
  + apply IH. lia.
  + rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b)) by lia. lia.
Qed.

Lemma e_vm_byte : forall (bs : list byte) j, (j < length bs)%nat ->
  Z_to_bv 8 (YO0f.le_byte (bytes_le_to_Z bs) (length bs) j) = nth j bs (Z_to_bv 8 0).
Proof.
intros bs j Hj. pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1.
unfold YO0f.le_byte. rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite e_ble_digit by exact Hj.
apply Z_to_bv_bv_unsigned.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e_vm_of_bytes : forall m a (bs : list byte),
  (forall j, (j < length bs)%nat -> mbyte SEGS m (a + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0))) ->
  val_mem SEGS m a (length bs) (bytes_le_to_Z bs).
Proof. intros m a bs H j Hj. rewrite H by exact Hj. f_equal. symmetry. apply e_vm_byte. exact Hj. Qed.

Lemma e_ga_nth : forall m base (L : list byte),
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) ->
  forall j, (j < length L)%nat -> mbyte SEGS m (base + Z.of_nat j) = Some (nth j L (Z_to_bv 8 0)).
Proof.
intros m base L HG j Hj.
pose proof (garr8_mbyte SEGS m base _ j HG ltac:(rewrite length_map; exact Hj)) as Hm.
rewrite Hm. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite (map_nth (fun b : byte => bv_unsigned b)). apply Z_to_bv_bv_unsigned.
Qed.

Lemma e_age_val : forall m (A : list byte) p k (nn : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) -> 0 <= k -> (Z.to_nat k + nn <= length A)%nat ->
  val_mem SEGS m (p + k) nn (u_at A k nn).
Proof.
intros m A p k nn HG Hk Hn. unfold u_at.
assert (Ls : length (sub A k nn) = nn) by (apply length_sub; lia).
rewrite <- Ls at 1. apply e_vm_of_bytes. intros j Hj. rewrite Ls in Hj.
pose proof (e_ga_nth m p A HG (Z.to_nat k + j)%nat ltac:(lia)) as Hm.
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hm. f_equal.
assert (Hns : nth_error (sub A k nn) j = nth_error A (Z.to_nat k + j)).
{ unfold sub. rewrite nth_firstn by lia. apply nth_skipn. }
rewrite (nth_error_nth' (sub A k nn) (Z_to_bv 8 0) (n := j) ltac:(lia)) in Hns.
rewrite (nth_error_nth' A (Z_to_bv 8 0) (n := (Z.to_nat k + j)%nat) ltac:(lia)) in Hns.
injection Hns as Hns. congruence.
Qed.

Lemma e_val8_mod : forall m a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H kk Hk. rewrite (H kk Hk). do 2 f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma e_bv64_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Lemma e_zbv_zcanon : forall x, Z_to_bv 64 (zcanon x) = Z_to_bv 64 x.
Proof. intros x. unfold zcanon, M64. apply e_bv64_mod. Qed.

Lemma e_t_chunk : forall E (m : word -> option byte) (T : list byte) FB a (w : N) k,
  garr8 SEGS m (FB + 2160) (map (fun b : byte => bv_unsigned b) T) -> length T = 400%nat ->
  ew E a = Z_to_bv 64 (u_at T k (N.to_nat w)) -> 0 <= k -> (Z.to_nat k + N.to_nat w <= 400)%nat -> Z.of_N w <= 8 ->
  YP09.chunk_ok SEGS E m FB (YP09.mkChunk (2160 + k) (CVal w (SOff a 0))).
Proof.
intros E m T FB a w k HG HL Ha Hk Hkw Hw.
apply (chunk_ok_val SEGS E m FB (2160 + k) w (SOff a 0) (u_at T k (N.to_nat w))).
- rewrite sv_denot_SOff0. exact Ha.
- pose proof (e_u_rng T k (N.to_nat w) Hk ltac:(lia)) as R. rewrite N_nat_Z in R. exact R.
- exact Hw.
- replace (FB + (2160 + k)) with (FB + 2160 + k) by lia.
  apply (e_age_val m T (FB + 2160) k (N.to_nat w) HG Hk). lia.
Qed.

Lemma e_atom : forall cx E regs ex j a, a = (563 + j)%nat -> (j < length ex)%nat ->
  ew (d_env cx E (a3_vals regs ex)) a = nth j ex (Z_to_bv 64 0).
Proof.
intros cx E regs ex j a -> Hj.
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite d_env_x by (unfold a3_vals; rewrite length_app, length_map, length_seq; lia).
unfold a3_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
Qed.

Lemma e_afact : forall E a v lo hi, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E a (mkAF lo hi 0).
Proof.
intros E a v lo hi He Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Lemma e_sub_U : forall E a b L now, ew E a = Z_to_bv 64 L -> ew E b = Z_to_bv 64 now ->
  0 <= L < 2 ^ 64 -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff b 0) (SMd M_MUL (SOff a 0) (SLit (-1)))) = (now - L) mod 2 ^ 64.
Proof.
intros E a b L now HL HN RL RN.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E a L HL RL), (U_atom E b now HN RN), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia.
replace (now + L * (2 ^ 64 - 1)) with (now - L + L * 2 ^ 64) by ring. apply Z_mod_plus_full.
Qed.

Lemma e_shal : forall E FB j, ew E 516 = w64 FB -> ew E 32 = w64 SHADOW_OFF -> ew E 529 = w64 (shadow_addr FB) ->
  0 <= FB -> FB + 4096 <= 2 ^ 47 -> FB mod 8 = 0 -> 0 <= j < 8 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 (2200 + 48 * j)) (SLit 3)) (SOff 32 0)) =
  sv_denot E (SOff 529 (275 + 6 * j)).
Proof.
intros E FB j HF H32 HSH HF0 HFb HFm Hj.
assert (EF : bv_unsigned (ew E 516) = FB) by (rewrite HF; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (rewrite H32; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (ESH : bv_unsigned (ew E 529) = shadow_addr FB)
  by (rewrite HSH; unfold w64; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (Hd : (FB + (2200 + 48 * j)) / 8 = FB / 8 + (275 + 6 * j)).
{ replace (FB + (2200 + 48 * j)) with ((275 + 6 * j) * 8 + FB) by lia.
  rewrite Z.div_add_l by lia. lia. }
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, EF, E32, ESH, Z.add_0_r.
rewrite (zcanon_id (FB + (2200 + 48 * j))) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite Hd. unfold shadow_addr. f_equal. lia.
Qed.

Lemma e_in_wrange_win : forall E rs a, e_win_ok rs = true -> in_wrange E rs a ->
  bv_unsigned (ew E 60) + 192 <= a < bv_unsigned (ew E 60) + 208.
Proof.
intros E rs a H (r & Hin & Ha). unfold e_win_ok in H. rewrite forallb_forall in H. specialize (H r Hin).
apply orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply YP09.obase_eqb_eq in H1. rewrite H1 in Ha. cbn [base_val] in Ha. apply Z.leb_le in H2, H3. lia.
Qed.

Lemma e_chunk_in_val : forall E m r od e v,
  region_ok SEGS E m r -> YP09.r_base r = Some 60%nat ->
  In (YP09.mkChunk od (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v ->
  val_mem SEGS m (bv_unsigned (ew E 60) + od) 8 v.
Proof.
intros E m r od e v HR Hb Hin He.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
apply e_val8_mod. change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok SEGS E m _ od 8%N e (v mod 2 ^ 64) Hck).
- rewrite He. symmetry. apply e_bv64_mod.
- pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)). cbn. lia.
- cbn. lia.
Qed.


Lemma e_lit_eq : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.

Ltac e_win HS n lo hi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let RO := fresh "RO" in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as RO;
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r lo hi RO ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
     first [ exfalso; lia | apply (proj1 (proj2 (proj2 RO))); cbn [YP09.r_wlo YP09.r_whi]; lia ]))) as HS3;
clear HS RO; rename HS3 into HS; norm_ss HS end.

Ltac e_grg HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) =>
  pose proof (st_ok_pi_restrict_reg _ Ex ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in
  change (sr_get (ss_regs ss) r) with v in Hr
end.

Ltac e_regok HS n Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ss ?msx =>
  let rs := eval vm_compute in (ss_mem ss) in
  let i := idx_of_base rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ss msx i r HS ltac:(vm_compute; reflexivity)) as Hr
end.

Ltac e_awr EA :=
lazymatch goal with
| |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
  let a := fresh "a" in let Ha := fresh "Ha" in let Hb := fresh "Hb" in
  intros a Ha; pose proof (e_in_wrange_win Ex rs a ltac:(vm_compute; reflexivity) Ha) as Hb;
  rewrite EA in Hb; left; unfold LLVMF_STK; lia
end.

Ltac e_vk HK H :=
lazymatch type of HK with
| forall a, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview _ (w_H ?W) ?m' a = aview _ _ ?m a =>
  apply (a3_val_mem_keep W m m' lo hi _ 8 _ HK);
    [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
     | let x := fresh "x" in let Hx := fresh "Hx" in
       intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | exact H]
end.

Ltac e_gk HK HL H :=
lazymatch type of HK with
| forall a, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview _ (w_H ?W) ?m' a = aview _ _ ?m a =>
  apply (a3_garr8_keep W m m' lo hi _ _ HK);
    [unfold d_obj, dobj_off; lia
     | rewrite length_map, HL; unfold d_obj, dobj_off; cbn; lia
     | let x := fresh "x" in let Hx := fresh "Hx" in
       intros x Hx; rewrite length_map, HL in Hx; unfold d_obj, dobj_off in Hx; cbn in Hx; lia
     | exact H]
end.

Ltac e_kacc :=
lazymatch goal with
| KA : forall x, aview ?SG ?H _ x = aview _ _ ?m0 x,
  HFx : frame_of ?Ex ?rsx (mrestrict ?H ?mm) (mrestrict ?H ?m') |- _ =>
  let K2 := fresh "KB" in
  assert (K2 : forall x, aview SG H m' x = aview SG H m0 x)
    by (let x := fresh "x" in intros x;
        rewrite (a3_kept_all H mm m' (fun y Hy => a3_kept_frame Ex rsx H mm m' 0 0 HFx
          (fun a Ha => False_ind _ (a3_nowin Ex rsx a ltac:(vm_compute; reflexivity) Ha)) y Hy ltac:(lia)) x);
        exact (KA x));
  clear KA HFx; rename K2 into KA
end.

Ltac e_pacc :=
lazymatch goal with
| PA : forall a, apresent ?H ?m0 a -> apresent _ _ a,
  HGx : mem_grows (mrestrict ?H ?mm) (mrestrict ?H ?m') |- _ =>
  let P2 := fresh "PB" in
  assert (P2 : forall a, apresent H m0 a -> apresent H m' a)
    by (let a := fresh "a" in let Hp := fresh "Hp" in
        intros a Hp; exact (a3_present_grows H mm m' HGx a (PA a Hp)));
  clear PA HGx; rename P2 into PA
end.

Ltac e_nowin :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; exfalso; revert Ha; apply a3_nowin; vm_compute; reflexivity.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBKEEP : d_body_keep_stmt B.

Definition p_lh (cx : dcx) (h i n now op : Z) (T0 : list byte) (W0 : world SEGS) (c0 : config) (jz : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\ 0 <= jz < n_of T0 /\
    a3_st B MT XM_LIB RLO RHI tfib_K cx LH_OFF (EV_HEAD i) h i n now []
      (fun regs => getr regs 10 = w64 (d_obj cx OT + 40 + 48 * jz) /\
         getr regs 13 = w64 (d_obj cx OT + 40 + 48 * jz) /\
         getr regs 11 = w64 (48 * jz - 384) /\ getr regs 12 = w64 (n_of T0 - jz) /\
         getr regs 15 = w64 (STALE_NS + 1) /\ getr regs 23 = w64 (e_cnt T0 now jz) /\
         getr regs 22 = w64 (s32_at T0 392) /\ getr regs 25 = w64 (n_of T0) /\ getr regs 26 = w64 now)
      (fun W m => d_sp1 cx i n now W m /\ a3_t0 cx T0 W m /\ d_spOP cx op W m) W c.

Lemma e_entry : forall cx h i n now op (W : world SEGS) (c : config),
  arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists T0,
    p_age B MT XM_LIB RLO RHI tfib_K cx h i n now op W c T0 W' c' \/ p_lh cx h i n now op T0 W c 0 W' c').
Proof.
intros cx h i n now op W c HIN. pose proof HIN as HIN0.
destruct HIN as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hcfg & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hop3 & HRA & Hsp0 & HOP & Hbody).
subst c.
pose proof Hbody as (T0 & G0 & Lk0 & H0 & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HOBJ as (HTl & HTg & HTok & _).
pose proof HRA as (HrL & R22 & R14 & R26 & R25 & R16 & R23 & R15).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_val as Hac.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA & GA32).
unfold MFRAME in GA. unfold LLVMF_STK in GSlo.
assert (HN8 : 0 <= n_of T0 <= 8) by (pose proof (proj1 HTok) as Q; unfold tbl_T1 in Q; lia).
assert (U563 : u_at T0 384 4 = n_of T0) by (apply e_u_of_n; [exact HTl | lia]).
assert (HTg' : garr8 SEGS (rd W mem3) (d_FB cx + 2160) (map (fun b : byte => bv_unsigned b) T0)) by exact HTg.
assert (Hacc' : acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX)
  by (clear - Hacc MT_TRIV; rewrite MT_TRIV in *; cbn [mo_malloc ameter_triv]; lia).
assert (Hfrom : a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W
  (cfg_at (fx := fq) SEGS (BASE + ARM3_OFF) regs mem3 md3) W).
{ split; [exact HIN0|]. split; [apply wle_refl|]. split; [exact HTl|].
  exists fq, regs, mem3, md3. split; [reflexivity | exact HTg]. }
assert (CH : forall E0, d_E cx E0 ->
  Forall (YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs (e_ex T0))) (rd W mem3) (d_FB cx)) e_fcs).
{ intros E0 HE0. unfold e_fcs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (e_t_chunk _ _ T0 _ 563%nat 4 384 HTg' HTl); [| lia | lia | lia].
    rewrite (e_atom cx E0 regs (e_ex T0) 0 563%nat eq_refl ltac:(cbn; lia)). reflexivity.
  - apply (e_t_chunk _ _ T0 _ 564%nat 4 392 HTg' HTl); [| lia | lia | lia].
    rewrite (e_atom cx E0 regs (e_ex T0) 1 564%nat eq_refl ltac:(cbn; lia)). reflexivity. }
destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx ARM3_OFF h n [] dsh_loop ly3 S3 W regs mem3 md3 k
  (e_ex T0) [] e_fcs [] [] [] HC HrL Hbody
  (fun E0 HE0 => conj I (conj I (conj (Forall_nil _) (conj (CH E0 HE0) (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
pose proof (a3_regs_ok B cx E regs (e_ex T0) HdE HrL) as HRO.
pose proof (proj1 (proj2 (proj2 HdE))) as HEIE.
pose proof (a3_env_img cx E (a3_vals regs (e_ex T0)) HdE) as HEI.
pose proof (d_E_env cx E (a3_vals regs (e_ex T0)) HdE) as HdEx.
pose proof HdEx as (EER & E32 & EIMG & E60 & EF & ESH).
change AT_A with 60%nat in E60. change AT_F with 516%nat in EF. change AT_SH with 529%nat in ESH.
assert (EA60u : bv_unsigned (ew (d_env cx E (a3_vals regs (e_ex T0))) 60) = d_A cx)
  by (rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (EFu : bv_unsigned (ew (d_env cx E (a3_vals regs (e_ex T0))) 516) = d_FB cx)
  by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
assert (E563 : ew (d_env cx E (a3_vals regs (e_ex T0))) 563 = Z_to_bv 64 (n_of T0))
  by (rewrite (e_atom cx E regs (e_ex T0) 0 563%nat eq_refl ltac:(cbn; lia)); unfold e_ex; cbn [nth];
      rewrite U563; reflexivity).
assert (E564 : ew (d_env cx E (a3_vals regs (e_ex T0))) 564 = Z_to_bv 64 (u_at T0 392 4))
  by (rewrite (e_atom cx E regs (e_ex T0) 1 564%nat eq_refl ltac:(cbn; lia)); reflexivity).
assert (R392 : 0 <= u_at T0 392 4 < 2 ^ 32)
  by (pose proof (e_u_rng T0 392 4 ltac:(lia) ltac:(lia)) as Q; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Q; lia).
unfold ss_d in HS.
e_win HS 516%nat 0 0. e_win HS 529%nat 0 0. e_win HS 60%nat 192 208.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + ARM3_OFF)) with (Z_to_bv 64 (BASE + ARM3_OFF)).
destruct (Z.eq_dec (n_of T0) 0) as [HZ | HZ].
- pose proof (st_ok_pi_add_fact _ _ _ 563%nat (mkAF 0 0 0) HS
    (e_afact _ 563%nat (n_of T0) 0 0 E563 ltac:(lia) ltac:(lia))) as HS2.
  clear HS. rename HS2 into HS. norm_ss HS.
  paj_run_shc RUNP RUNC HS HJ.
  { e_awr EA60u. }
  apply SRr_ret. exists T0. left. split; [exact Hfrom|].
  lazymatch type of HS with st_ok _ ?Ex (setpc ?ssF (SIGMA ?s)) _ =>
    pose proof (a3_pcall_pi fq Ex ssF _ s HS) as HSp;
    assert (RG : forall r r0 : bv 5, sr_get (ss_regs (setpc ssF (SIGMA s))) r = sr_get a3_sr r0 ->
      getr (ms_regs ms) r = getr regs r0)
      by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS _ _ _ ms r HS), Heq; symmetry; exact (HRO r0))
  end.
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 192 <= a < d_A cx + 208) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
      apply (a3_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) (d_A cx + 192) (d_A cx + 208) HFr);
      intros a Ha; pose proof (e_in_wrange_win Ex rsx a ltac:(vm_compute; reflexivity) Ha) as Hb;
      rewrite EA60u in Hb; lia end. }
  e_regok HSp 60%nat RA60.
  assert (V192 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 192) 8 n).
  { rewrite <- EA60u. apply (e_chunk_in_val _ _ _ 192 (SOff 545 0) n RA60 eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))).
    rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0) 14%bv 545%nat eq_refl) R14). }
  assert (V200 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 200) 8 (d_cur cx n)).
  { rewrite <- EA60u. apply (e_chunk_in_val _ _ _ 200 (SOff 556 0) (d_cur cx n) RA60 eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))).
    rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0) 25%bv 556%nat eq_refl) R25). }
  pose proof (st_ok_pi_restrict_reg (w_H W) _ _ ms 1%bv HSp) as Hra.
  lazymatch type of Hra with _ = sv_denot _ (sr_get ?sr _) =>
    let v := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with v in Hra end.
  cbn [sv_denot] in Hra. rewrite d_env_old in Hra by (cbv; lia).
  rewrite (HEIE 240%nat ltac:(cbv; lia)) in Hra.
  e_grg HSp (10%bv : bv 5) H10. cbn [sv_denot] in H10. rewrite EFu in H10.
  e_grg HSp (24%bv : bv 5) H24. cbn [sv_denot] in H24. rewrite EFu in H24.
  e_grg HSp (23%bv : bv 5) H23. cbn [sv_denot] in H23.
  e_grg HSp (25%bv : bv 5) H25. cbn [sv_denot] in H25. rewrite E563 in H25.
  rewrite unsigned_lit_small in H25 by lia. rewrite Z.add_0_r in H25.
  e_grg HSp (22%bv : bv 5) H22.
  rewrite denot_lit_U, U_SExt, (U_atom _ 564%nat (u_at T0 392 4) E564 ltac:(lia)) in H22.
  rewrite Z.mod_small in H22 by (change (2 ^ Z.of_N 32) with (2 ^ 32); exact R392).
  destruct HrL as (Hsp & Hgp & Htp & Hr8 & Hr9 & Hr19 & Hr18 & Hr20 & Hr27).
  apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx AF_both3_reac_disco_table_age
    (EV_HEAD i) h i n n now _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs (e_ex T0))) _ ms
    (d_A cx + 192) (d_A cx + 208) Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc' Hi ltac:(lia) Hnow Hbody HSp eq_refl).
  + cbn [ss_pc setpc]. rewrite pa_sigma_reac_disco_table_age. lia.
  + exact (d_E_env cx E _ HdE).
  + exact (d_env_fl cx E _).
  + vm_compute. reflexivity.
  + unfold LLVMF_STK. lia.
  + lia.
  + exact HK.
  + intros a _. exact (a3_present_grows (w_H W) mem3 (ms_mem ms) HG a).
  + unfold a3_hsw. intros a Ha. lia.
  + split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
    rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
      (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
      (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
      (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
    repeat split; assumption.
  + split; [unfold w64, P_AGE_RA; exact Hra|].
    split; [rewrite H10; unfold w64, d_obj, dobj_off; reflexivity|].
    split; [rewrite (RG 11%bv 26%bv ltac:(vm_compute; reflexivity)); exact R26|].
    split; [rewrite H23; unfold a3_stale; rewrite HZ; cbn [Z.to_nat age_count]; unfold w64; reflexivity|].
    split; [rewrite H22; unfold w64, s32_at; apply e_zbv_zcanon|].
    split; [rewrite H25; unfold w64; reflexivity|].
    split; [rewrite H24; unfold w64, d_obj, dobj_off; reflexivity|].
    split; [rewrite (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)); exact R26|].
    rewrite (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)). exact Hr27.
  + destruct Hsp0 as (H208 & H320). destruct HOP as (H360 & H352).
    refine (conj (conj (conj _ _) (conj V192 V200)) (conj (conj HTl (conj HTok _)) (conj _ _))).
    * e_vk HK H208.
    * e_vk HK H320.
    * e_gk HK HTl HTg.
    * e_vk HK H360.
    * e_vk HK H352.
  + destruct Hsp0 as (H208 & H320). split; [e_vk HK H208 | e_vk HK H320].
- pose proof (st_ok_pi_add_fact _ _ _ 563%nat (mkAF 1 8 0) HS
    (e_afact _ 563%nat (n_of T0) 1 8 E563 ltac:(lia) ltac:(lia))) as HS2.
  clear HS. rename HS2 into HS. norm_ss HS.
  paj_run_to_sh RUNTOP HS HJ LH_OFF.
  { e_awr EA60u. }
  apply SRr_ret. exists T0. right. split; [exact Hfrom|]. split; [lia|].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssF (restrict _ ?msx) =>
    assert (RG : forall r r0 : bv 5, sr_get (ss_regs ssF) r = sr_get a3_sr r0 ->
      getr (ms_regs msx) r = getr regs r0)
      by (intros r r0 Heq; rewrite (st_ok_pi_restrict_reg (w_H W) _ ssF msx r HS), Heq; symmetry; exact (HRO r0))
  end.
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 192 <= a < d_A cx + 208) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
      apply (a3_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) (d_A cx + 192) (d_A cx + 208) HFr);
      intros a Ha; pose proof (e_in_wrange_win Ex rsx a ltac:(vm_compute; reflexivity) Ha) as Hb;
      rewrite EA60u in Hb; lia end. }
  e_regok HS 60%nat RA60.
  assert (V192 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 192) 8 n).
  { rewrite <- EA60u. apply (e_chunk_in_val _ _ _ 192 (SOff 545 0) n RA60 eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))).
    rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0) 14%bv 545%nat eq_refl) R14). }
  assert (V200 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 200) 8 (d_cur cx n)).
  { rewrite <- EA60u. apply (e_chunk_in_val _ _ _ 200 (SOff 556 0) (d_cur cx n) RA60 eq_refl
      ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))).
    rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0) 25%bv 556%nat eq_refl) R25). }
  e_grg HS (10%bv : bv 5) H10. cbn [sv_denot] in H10. rewrite EFu in H10.
  e_grg HS (13%bv : bv 5) H13. cbn [sv_denot] in H13. rewrite EFu in H13.
  e_grg HS (11%bv : bv 5) H11. cbn [sv_denot] in H11.
  e_grg HS (12%bv : bv 5) H12. cbn [sv_denot] in H12. rewrite E563 in H12.
  rewrite unsigned_lit_small in H12 by lia. rewrite Z.add_0_r in H12.
  e_grg HS (23%bv : bv 5) H23. cbn [sv_denot] in H23.
  e_grg HS (25%bv : bv 5) H25. cbn [sv_denot] in H25. rewrite E563 in H25.
  rewrite unsigned_lit_small in H25 by lia. rewrite Z.add_0_r in H25.
  e_grg HS (22%bv : bv 5) H22.
  rewrite denot_lit_U, U_SExt, (U_atom _ 564%nat (u_at T0 392 4) E564 ltac:(lia)) in H22.
  rewrite Z.mod_small in H22 by (change (2 ^ Z.of_N 32) with (2 ^ 32); exact R392).
  destruct HrL as (Hsp & Hgp & Htp & Hr8 & Hr9 & Hr19 & Hr18 & Hr20 & Hr27).
  apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx LH_OFF
    (EV_HEAD i) h i n n now _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs (e_ex T0))) _ ms
    (d_A cx + 192) (d_A cx + 208) Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc' Hi ltac:(lia) Hnow Hbody HS eq_refl).
  + vm_compute. reflexivity.
  + exact (d_E_env cx E _ HdE).
  + exact (d_env_fl cx E _).
  + vm_compute. reflexivity.
  + unfold LLVMF_STK. lia.
  + lia.
  + exact HK.
  + intros a _. exact (a3_present_grows (w_H W) mem3 (ms_mem ms) HG a).
  + unfold a3_hsw. intros a Ha. lia.
  + split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
    rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
      (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
      (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
      (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
    repeat split; assumption.
  + split; [rewrite H10; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|].
    split; [rewrite H13; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|].
    split; [rewrite H11; unfold w64; apply e_lit_eq; vm_compute; reflexivity|].
    split; [rewrite H12; unfold w64; apply e_lit_eq; f_equal; lia|].
    split; [rewrite (RG 15%bv 15%bv ltac:(vm_compute; reflexivity)); exact R15|].
    split; [rewrite H23; unfold e_cnt, w64; cbn [Z.to_nat age_count]; reflexivity|].
    split; [rewrite H22; unfold w64, s32_at; apply e_zbv_zcanon|].
    split; [rewrite H25; unfold w64; reflexivity|].
    rewrite (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)). exact R26.
  + destruct Hsp0 as (H208 & H320). destruct HOP as (H360 & H352).
    refine (conj (conj (conj _ _) (conj V192 V200)) (conj (conj HTl (conj HTok _)) (conj _ _))).
    * e_vk HK H208.
    * e_vk HK H320.
    * e_gk HK HTl HTg.
    * e_vk HK H360.
    * e_vk HK H352.
  + destruct Hsp0 as (H208 & H320). split; [e_vk HK H208 | e_vk HK H320].
Qed.

Ltac e_pre j :=
intros cx h i n now op T0 W0 c0 W c HEX HP;
destruct HP as (Hfrom & Hjn & Hst);
destruct Hst as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hcfg & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody);
subst c;
destruct HR as (R10 & R13 & R11 & R12 & R15 & R23 & R22 & R25 & R26);
destruct HX as (HSP1 & HT0 & HOP);
pose proof HT0 as (HTl & HTok & HTg);
destruct HSP1 as ((V208 & V320) & V192 & V200);
destruct HOP as (V360 & V352);
destruct Hsp0 as (W208 & W320);
pose proof HrL as HrLc;
destruct HrLc as (Hsp & Hgp & Htp & Hr8 & Hr9 & Hr19 & Hr18 & Hr20 & Hr27);
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs));
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3);
pose proof alloc_ceiling_val as Hac;
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA & GA32);
unfold MFRAME in GA; unfold LLVMF_STK in GSlo;
assert (HN8 : 0 <= n_of T0 <= 8) by (pose proof (proj1 HTok) as Q; unfold tbl_T1 in Q; lia);
assert (HTg' : garr8 SEGS (rd W mem3) (d_FB cx + 2160) (map (fun b : byte => bv_unsigned b) T0)) by exact HTg;
assert (HF8 : d_FB cx mod 8 = 0)
  by (pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)) as Q; rewrite GF32, Z.add_0_r in Q; rewrite Q;
      replace (32 * (d_FB cx / 32)) with (4 * (d_FB cx / 32) * 8) by lia; apply Z_mod_mult);
assert (HLR : forall x, 0 <= x <= 7 -> 0 <= last_of T0 x < 2 ^ 64)
  by (intros x Hx; unfold last_of; pose proof (e_u_rng T0 (48 * x + 40) 8 ltac:(lia) ltac:(lia)) as Q;
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Q; lia);
assert (CHJ : forall (x : Z) E0, 0 <= x <= 7 -> d_E cx E0 ->
  Forall (YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs [Z_to_bv 64 (last_of T0 x)])) (rd W mem3) (d_FB cx))
    [YP09.mkChunk (2200 + 48 * x) (CVal 8 (SOff 563 0))])
  by (intros x E0 Hx HE0; apply Forall_cons; [|apply Forall_nil];
      replace (2200 + 48 * x) with (2160 + (48 * x + 40)) by lia;
      apply (e_t_chunk _ _ T0 _ 563%nat 8 (48 * x + 40) HTg' HTl); [| lia | lia | lia];
      rewrite (e_atom cx E0 regs [Z_to_bv 64 (last_of T0 x)] 0 563%nat eq_refl ltac:(cbn; lia)); cbn [nth];
      reflexivity);
assert (HCN : 0 <= e_cnt T0 now j <= j) by (apply e_cnt_rng; lia);
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS);
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS);
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS);
pose proof (paj_branch (fx := fq) (PI := PI)) as BR;
unfold cfg_at; change (w64 (BASE + LH_OFF)) with (Z_to_bv 64 (BASE + LH_OFF)).

Ltac e_leaf xl j :=
let fq := ident:(fq) in let cx := ident:(cx) in let h := ident:(h) in let i := ident:(i) in let n := ident:(n) in
let now := ident:(now) in let T0 := ident:(T0) in let W := ident:(W) in let regs := ident:(regs) in
let mem3 := ident:(mem3) in let md3 := ident:(md3) in let ly3 := ident:(ly3) in let S3 := ident:(S3) in
let k := ident:(k) in let acc := ident:(acc) in let HC := ident:(HC) in let HrL := ident:(HrL) in
let Hbody := ident:(Hbody) in let CHJ := ident:(CHJ) in let R10 := ident:(R10) in let R11 := ident:(R11) in
let R12 := ident:(R12) in let R13 := ident:(R13) in let R15 := ident:(R15) in let R22 := ident:(R22) in
let R23 := ident:(R23) in let R25 := ident:(R25) in let R26 := ident:(R26) in let HF8 := ident:(HF8) in
let HLR := ident:(HLR) in let Hnow := ident:(Hnow) in let Hfrom := ident:(Hfrom) in let Hfrm := ident:(Hfrm) in
let Hbase := ident:(Hbase) in let HJ := ident:(HJ) in let Hfrs := ident:(Hfrs) in let Hk := ident:(Hk) in
let Hnev := ident:(Hnev) in let Hmo := ident:(Hmo) in let Hacc := ident:(Hacc) in let Hi := ident:(Hi) in
let Hsp := ident:(Hsp) in let Hr27 := ident:(Hr27) in let HTl := ident:(HTl) in let HTok := ident:(HTok) in
let HEX := ident:(HEX) in let RUNP := ident:(RUNP) in let RUNC := ident:(RUNC) in let RUNTOP := ident:(RUNTOP) in
let BR := ident:(BR) in let E := ident:(E) in let HdE := ident:(HdE) in let HS := ident:(HS) in
let HRO := ident:(HRO) in let HEIE := ident:(HEIE) in let EFu := ident:(EFu) in let E543 := ident:(E543) in
let E554 := ident:(E554) in let E563 := ident:(E563) in let E557 := ident:(E557) in let KA := ident:(KA) in
let PA := ident:(PA) in let HST := ident:(HST) in let Hc := ident:(Hc) in let Hc0 := ident:(Hc0) in
let RG := ident:(RG) in let HSp := ident:(HSp) in let G10 := ident:(G10) in let G11 := ident:(G11) in
let G12 := ident:(G12) in let G13 := ident:(G13) in let G15 := ident:(G15) in let G23 := ident:(G23) in
let A10 := ident:(A10) in let A23 := ident:(A23) in let A24 := ident:(A24) in
let seatj j :=
  (destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx LH_OFF h n [] dsh_loop ly3 S3 W regs mem3
      md3 k [Z_to_bv 64 (last_of T0 j)] [] [YP09.mkChunk (2200 + 48 * j) (CVal 8 (SOff 563 0))] [] [] []
      HC HrL Hbody
      (fun E0 HE0 => conj I (conj I (conj (Forall_nil _) (conj (CHJ j E0 ltac:(lia) HE0)
         (conj (Forall_nil _) (conj I (Forall_nil _)))))))
      ltac:(vm_compute; reflexivity)) as (E & HdE & HS);
   pose proof (a3_regs_ok B cx E regs [Z_to_bv 64 (last_of T0 j)] HdE HrL) as HRO;
   pose proof (a3_env_img cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)]) HdE) as HEI;
   pose proof (proj1 (proj2 (proj2 HdE))) as HEIE;
   pose proof (d_E_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)]) HdE) as HdEx;
   pose proof HdEx as (EER & E32x & EIMGx & E60 & EF & ESHx);
   change AT_A with 60%nat in E60; change AT_F with 516%nat in EF; change AT_SH with 529%nat in ESHx;
   assert (EA60u : bv_unsigned (ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 60) = d_A cx)
     by (rewrite E60; unfold w64; apply unsigned_lit_small; lia);
   assert (EFu : bv_unsigned (ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 516) = d_FB cx)
     by (rewrite EF; unfold w64; apply unsigned_lit_small; lia);
   assert (E563 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 563 = Z_to_bv 64 (last_of T0 j))
     by (rewrite (e_atom cx E regs [Z_to_bv 64 (last_of T0 j)] 0 563%nat eq_refl ltac:(cbn; lia)); reflexivity);
   assert (E543 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 543 = Z_to_bv 64 (n_of T0 - j))
     by (rewrite (a3_env_reg cx E regs _ (12%bv : bv 5) 543%nat eq_refl); exact R12);
   assert (E554 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 554 = Z_to_bv 64 (e_cnt T0 now j))
     by (rewrite (a3_env_reg cx E regs _ (23%bv : bv 5) 554%nat eq_refl); exact R23);
   assert (E557 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) 557 = Z_to_bv 64 now)
     by (rewrite (a3_env_reg cx E regs _ (26%bv : bv 5) 557%nat eq_refl); exact R26);
   unfold ss_d in HS;
   e_win HS 516%nat 0 0; e_win HS 529%nat 0 0; e_win HS 60%nat 0 0;
   pose proof (st_ok_pi_add_alias _ _ _ _ _ HS
     (e_shal (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) (d_FB cx) j EF E32x ESHx
        ltac:(lia) ltac:(lia) HF8 ltac:(lia))) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) (SOff 516 (2200 + 48 * j)) HS
     ltac:(vm_compute; reflexivity)
     ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite EFu, R10; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia)) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (ast_ok_pi_set_reg_fp _ _ _ (13%bv : bv 5) (SOff 516 (2200 + 48 * j)) HS
     ltac:(vm_compute; reflexivity)
     ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite EFu, R13; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia)) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (ast_ok_pi_set_reg_fp _ _ _ (11%bv : bv 5) (SLit (48 * j - 384)) HS
     ltac:(vm_compute; reflexivity)
     ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite R11; unfold w64; apply e_lit_eq; f_equal; lia)) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (ast_ok_pi_set_reg_fp _ _ _ (15%bv : bv 5) (SLit 5000000001) HS
     ltac:(vm_compute; reflexivity)
     ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite R15; unfold w64, STALE_NS; apply e_lit_eq; f_equal; lia)) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (st_ok_pi_add_fact _ _ _ 554%nat (mkAF 0 j 0) HS
     (e_afact _ 554%nat (e_cnt T0 now j) 0 j E554 ltac:(lia) ltac:(lia))) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   pose proof (HLR j ltac:(lia)) as HLRj;
   assert (KA : forall x, aview SEGS (w_H W) mem3 x = aview SEGS (w_H W) mem3 x) by (intros x; reflexivity);
   assert (PA : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a Hp; exact Hp)) in
let geuf j :=
  (rewrite branch_geu_U, (U_atom _ 563%nat (last_of T0 j) E563 ltac:(apply HLR; lia)),
     (U_atom _ 557%nat now E557 Hnow) in Hc) in
let ltuf j Hx :=
  (rewrite branch_ltu_U, (e_sub_U _ 563%nat 557%nat (last_of T0 j) now E563 E557 ltac:(apply HLR; lia) Hnow),
     U_SLit in Hx;
   change (zcanon 5000000001) with 5000000001 in Hx;
   rewrite (Z.mod_small (now - last_of T0 j)) in Hx by lia) in
let lhland j :=
  (apply SRr_ret; right; split; [exact Hfrom|]; split; [lia|];
   lazymatch type of HS with st_ok_pi _ _ _ ?ssF (restrict _ ?msx) =>
     assert (RG : forall r r0 : bv 5, sr_get (ss_regs ssF) r = sr_get a3_sr r0 ->
       getr (ms_regs msx) r = getr regs r0)
       by (intros r r0 Heq; rewrite (st_ok_pi_restrict_reg (w_H W) _ ssF msx r HS), Heq; symmetry; exact (HRO r0))
   end;
   e_grg HS (10%bv : bv 5) G10; cbn [sv_denot] in G10; rewrite EFu in G10;
   e_grg HS (13%bv : bv 5) G13; cbn [sv_denot] in G13; rewrite EFu in G13;
   e_grg HS (11%bv : bv 5) G11; cbn [sv_denot] in G11;
   e_grg HS (12%bv : bv 5) G12; cbn [sv_denot] in G12; rewrite E543 in G12;
   rewrite unsigned_lit_small in G12 by lia;
   e_grg HS (23%bv : bv 5) G23; cbn [sv_denot] in G23; rewrite E554 in G23;
   rewrite unsigned_lit_small in G23 by lia;
   e_grg HS (15%bv : bv 5) G15; cbn [sv_denot] in G15;
   apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx LH_OFF (EV_HEAD i) h i n n now
     _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)])) _ _ (d_S cx) (d_S cx)
      Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HS eq_refl);
   [ vm_compute; reflexivity
   | exact (d_E_env cx E _ HdE)
   | exact (d_env_fl cx E _)
   | vm_compute; reflexivity
   | unfold LLVMF_STK; lia
   | lia
   | intros aa _ _; exact (KA aa)
   | intros aa _; exact (PA aa)
   | intros aa _; lia
   | split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|];
     rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
       (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
       (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
       (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity));
     repeat split; assumption
   | split; [rewrite G10; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|];
     split; [rewrite G13; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|];
     split; [rewrite G11; unfold w64; apply e_lit_eq; vm_compute; reflexivity|];
     split; [rewrite G12; unfold w64; apply e_lit_eq; f_equal; lia|];
     split; [rewrite G15; unfold w64, STALE_NS; apply e_lit_eq; f_equal; lia|];
     split; [rewrite G23, (e_cnt_S T0 now j ltac:(lia)), HST; unfold w64; apply e_lit_eq; reflexivity|];
     split; [rewrite (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)); exact R22|];
     split; [rewrite (RG 25%bv 25%bv ltac:(vm_compute; reflexivity)); exact R25|];
     rewrite (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)); exact R26
   | refine (conj (conj (conj _ _) (conj _ _)) (conj (conj HTl (conj HTok _)) (conj _ _)));
     first [ eapply (a3_val_mem_all W mem3); [exact KA | eassumption]
           | eapply (a3_garr8_all W mem3); [exact KA | eassumption] ]
   | split; (eapply (a3_val_mem_all W mem3); [exact KA | eassumption]) ]) in
let ageland j :=
  (apply SRr_ret; left; split; [exact Hfrom|];
   lazymatch type of HS with st_ok _ ?Ex (setpc ?ssF (SIGMA ?s)) (restrict ?HH ?msx) =>
     pose proof (a3_pcall_pi fq Ex ssF (restrict HH msx) s HS) as HSp;
     assert (RG : forall r r0 : bv 5, sr_get (ss_regs (setpc ssF (SIGMA s))) r = sr_get a3_sr r0 ->
       getr (ms_regs msx) r = getr regs r0)
       by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS HH Ex _ msx r HS), Heq; symmetry; exact (HRO r0))
   end;
   pose proof (st_ok_pi_restrict_reg (w_H W) _ _ _ (1%bv : bv 5) HSp) as Hra;
   lazymatch type of Hra with _ = sv_denot _ (sr_get ?sr _) =>
     let v := eval vm_compute in (sr_get sr (1%bv : bv 5)) in change (sr_get sr (1%bv : bv 5)) with v in Hra end;
   cbn [sv_denot] in Hra; rewrite d_env_old in Hra by (cbv; lia);
   rewrite (HEIE 240%nat ltac:(cbv; lia)) in Hra;
   e_grg HSp (10%bv : bv 5) A10; cbn [sv_denot] in A10; rewrite EFu in A10;
   e_grg HSp (24%bv : bv 5) A24; cbn [sv_denot] in A24; rewrite EFu in A24;
   e_grg HSp (23%bv : bv 5) A23; cbn [sv_denot] in A23; rewrite E554 in A23;
   rewrite unsigned_lit_small in A23 by lia;
   apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx AF_both3_reac_disco_table_age
     (EV_HEAD i) h i n n now _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T0 j)]))
     _ _ (d_S cx) (d_S cx)
      Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSp eq_refl);
   [ cbn [ss_pc setpc]; rewrite pa_sigma_reac_disco_table_age; lia
   | exact (d_E_env cx E _ HdE)
   | exact (d_env_fl cx E _)
   | vm_compute; reflexivity
   | unfold LLVMF_STK; lia
   | lia
   | intros aa _ _; exact (KA aa)
   | intros aa _; exact (PA aa)
   | intros aa _; lia
   | split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|];
     rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
       (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
       (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
       (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity));
     repeat split; assumption
   | replace (a3_stale T0 now) with (e_cnt T0 now (j + 1))
       by (unfold a3_stale, e_cnt; rewrite HEX; reflexivity);
     split; [unfold w64, P_AGE_RA; exact Hra|];
     split; [rewrite A10; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|];
     split; [rewrite (RG 11%bv 26%bv ltac:(vm_compute; reflexivity)); exact R26|];
     split; [rewrite A23, (e_cnt_S T0 now j ltac:(lia)), HST; unfold w64; apply e_lit_eq; reflexivity|];
     split; [rewrite (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)); exact R22|];
     split; [rewrite (RG 25%bv 25%bv ltac:(vm_compute; reflexivity)); exact R25|];
     split; [rewrite A24; unfold w64, d_obj, dobj_off; apply e_lit_eq; f_equal; lia|];
     split; [rewrite (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)); exact R26|];
     rewrite (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)); exact Hr27
   | refine (conj (conj (conj _ _) (conj _ _)) (conj (conj HTl (conj HTok _)) (conj _ _)));
     first [ eapply (a3_val_mem_all W mem3); [exact KA | eassumption]
           | eapply (a3_garr8_all W mem3); [exact KA | eassumption] ]
   | split; (eapply (a3_val_mem_all W mem3); [exact KA | eassumption]) ]) in
let cleaf j :=
  (seatj j;
   pose proof (st_ok_pi_add_fact _ _ _ 543%nat (mkAF 2 (8 - j) 0) HS
     (e_afact _ 543%nat (n_of T0 - j) 2 (8 - j) E543 ltac:(lia) ltac:(lia))) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   paj_run_sh RUNP HS HJ;
   [ e_nowin
   | e_kacc; e_pacc; psrr_branch_pi RUNP BR HS;
     [ geuf j; apply negb_true_iff in Hc; apply Z.ltb_ge in Hc;
       assert (HST : disco_stale T0 j now = false) by (apply e_stale_ge; lia);
       paj_run_to_sh RUNTOP HS HJ LH_OFF; [ e_nowin | e_kacc; e_pacc; lhland j ]
     | geuf j; apply negb_false_iff in Hc; apply Z.ltb_lt in Hc;
       paj_run_sh RUNP HS HJ;
       [ e_nowin
       | e_kacc; e_pacc; psrr_branch_pi RUNP BR HS;
         [ ltuf j Hc0; apply Z.ltb_lt in Hc0;
           assert (HST : disco_stale T0 j now = false) by (apply e_stale_near; unfold REAC_DISCO_STALE_NS; lia);
           paj_run_to_sh RUNTOP HS HJ LH_OFF; [ e_nowin | e_kacc; e_pacc; lhland j ]
         | ltuf j Hc0; apply Z.ltb_ge in Hc0;
           assert (HST : disco_stale T0 j now = true)
             by (apply e_stale_yes; [lia | unfold REAC_DISCO_STALE_NS; lia]);
           paj_run_to_sh RUNTOP HS HJ LH_OFF; [ e_nowin | e_kacc; e_pacc; lhland j ] ] ] ] ]) in
let xleaf j :=
  (seatj j;
   pose proof (ast_ok_pi_set_reg_fp _ _ _ (12%bv : bv 5) (SLit 1) HS
     ltac:(vm_compute; reflexivity)
     ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite R12; unfold w64; apply e_lit_eq; f_equal; lia)) as HSA;
   clear HS; rename HSA into HS; norm_ss HS;
   paj_run_sh RUNP HS HJ;
   [ e_nowin
   | e_kacc; e_pacc; psrr_branch_pi RUNP BR HS;
     [ geuf j; apply negb_true_iff in Hc; apply Z.ltb_ge in Hc;
       assert (HST : disco_stale T0 j now = false) by (apply e_stale_ge; lia);
       paj_run_shc RUNP RUNC HS HJ; [ e_nowin | e_kacc; e_pacc; ageland j ]
     | geuf j; apply negb_false_iff in Hc; apply Z.ltb_lt in Hc;
       paj_run_sh RUNP HS HJ;
       [ e_nowin
       | e_kacc; e_pacc; psrr_branch_pi RUNP BR HS;
         [ ltuf j Hc0; apply Z.ltb_lt in Hc0;
           assert (HST : disco_stale T0 j now = false) by (apply e_stale_near; unfold REAC_DISCO_STALE_NS; lia);
           paj_run_shc RUNP RUNC HS HJ; [ e_nowin | e_kacc; e_pacc; ageland j ]
         | ltuf j Hc0; apply Z.ltb_ge in Hc0;
           assert (HST : disco_stale T0 j now = true)
             by (apply e_stale_yes; [lia | unfold REAC_DISCO_STALE_NS; lia]);
           paj_run_shc RUNP RUNC HS HJ; [ e_nowin | e_kacc; e_pacc; ageland j ] ] ] ] ]) in
lazymatch xl with true => xleaf j | false => cleaf j end.

Definition e_cx (j : Z) : Prop := forall cx h i n now op T0 W0 c0 (W : world SEGS) c,
  n_of T0 = j + 1 -> p_lh cx h i n now op T0 W0 c0 j W c ->
  SRr SEGS W c (fun W' c' => p_age B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 W' c' \/
    p_lh cx h i n now op T0 W0 c0 (j + 1) W' c').

Definition e_cc (j : Z) : Prop := forall cx h i n now op T0 W0 c0 (W : world SEGS) c,
  n_of T0 <> j + 1 -> p_lh cx h i n now op T0 W0 c0 j W c ->
  SRr SEGS W c (fun W' c' => p_age B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 W' c' \/
    p_lh cx h i n now op T0 W0 c0 (j + 1) W' c').

Lemma e_lx0 : e_cx 0.
Proof. e_pre 0. e_leaf true 0. Qed.
Lemma e_lx1 : e_cx 1.
Proof. e_pre 1. e_leaf true 1. Qed.
Lemma e_lx2 : e_cx 2.
Proof. e_pre 2. e_leaf true 2. Qed.
Lemma e_lx3 : e_cx 3.
Proof. e_pre 3. e_leaf true 3. Qed.
Lemma e_lx4 : e_cx 4.
Proof. e_pre 4. e_leaf true 4. Qed.
Lemma e_lx5 : e_cx 5.
Proof. e_pre 5. e_leaf true 5. Qed.
Lemma e_lx6 : e_cx 6.
Proof. e_pre 6. e_leaf true 6. Qed.
Lemma e_lx7 : e_cx 7.
Proof. e_pre 7. e_leaf true 7. Qed.
Lemma e_lc0 : e_cc 0.
Proof. e_pre 0. e_leaf false 0. Qed.
Lemma e_lc1 : e_cc 1.
Proof. e_pre 1. e_leaf false 1. Qed.
Lemma e_lc2 : e_cc 2.
Proof. e_pre 2. e_leaf false 2. Qed.
Lemma e_lc3 : e_cc 3.
Proof. e_pre 3. e_leaf false 3. Qed.
Lemma e_lc4 : e_cc 4.
Proof. e_pre 4. e_leaf false 4. Qed.
Lemma e_lc5 : e_cc 5.
Proof. e_pre 5. e_leaf false 5. Qed.
Lemma e_lc6 : e_cc 6.
Proof. e_pre 6. e_leaf false 6. Qed.
Lemma e_lc7 : e_cc 7.
Proof. e_pre 7. e_leaf false 7. Qed.

Lemma e_step : forall cx h i n now op T0 W0 c0 jz (W : world SEGS) c,
  p_lh cx h i n now op T0 W0 c0 jz W c ->
  SRr SEGS W c (fun W' c' => p_age B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 W' c' \/
    p_lh cx h i n now op T0 W0 c0 (jz + 1) W' c').
Proof.
intros cx h i n now op T0 W0 c0 jz W c HP.
assert (HJ8 : jz = 0 \/ jz = 1 \/ jz = 2 \/ jz = 3 \/ jz = 4 \/ jz = 5 \/ jz = 6 \/ jz = 7).
{ pose proof HP as (_ & Hjn & Hst).
  destruct Hst as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hcfg & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo &
    Hacc & Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
  destruct HX as (_ & (_ & HTok & _) & _).
  pose proof (proj1 HTok) as Q. unfold tbl_T1 in Q. clear - Hjn Q. lia. }
destruct (Z.eq_dec (n_of T0) (jz + 1)) as [HB | HB];
  destruct HJ8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- exact (e_lx0 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx1 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx2 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx3 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx4 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx5 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx6 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lx7 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc0 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc1 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc2 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc3 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc4 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc5 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc6 cx h i n now op T0 W0 c0 W c HB HP).
- exact (e_lc7 cx h i n now op T0 W0 c0 W c HB HP).
Qed.

Lemma e_loop : forall (ff : nat) cx h i n now op T0 W0 c0 jz (W : world SEGS) c,
  (Z.to_nat (n_of T0 - jz) <= ff)%nat -> p_lh cx h i n now op T0 W0 c0 jz W c ->
  SRr SEGS W c (p_age B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0).
Proof.
induction ff as [|ff IH]; intros cx h i n now op T0 W0 c0 jz W c Hf HP.
- exfalso. destruct HP as (_ & Hjn & _). lia.
- eapply SRr_bind; [exact (e_step cx h i n now op T0 W0 c0 jz W c HP)|].
  intros W' c' Hle HD. destruct HD as [HA | HB]; [apply SRr_ret; exact HA|].
  apply (IH cx h i n now op T0 W0 c0 (jz + 1) W' c'); [|exact HB].
  destruct HP as (_ & Hjn & _). destruct HB as (_ & Hjn2 & _). lia.
Qed.

Theorem a3_e_ent : e_ent_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W c HIN.
eapply SRr_bind; [exact (e_entry cx h i n now op W c HIN)|].
intros W1 c1 Hle HD. destruct HD as (T0 & [HA | HB]).
- apply SRr_ret. exists T0. exact HA.
- eapply SRr_mono; [exact (e_loop (Z.to_nat (n_of T0)) cx h i n now op T0 W c 0 W1 c1 ltac:(lia) HB)|].
  intros W2 c2 _ H2. exists T0. exact H2.
Qed.

End h.
End f.
End d.
