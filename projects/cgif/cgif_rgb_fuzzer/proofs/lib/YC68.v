(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac lg_branchF tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (st_okF_branch segs E ss ms _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "lg_branchF: state is not stuck at a branch:" why
end
end
end.
Lemma lg_kept_win : forall E0 rs (H : word -> bool) (m m' : word -> option byte) (n : nat) b lo hi,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some n /\ lo <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= hi)) ->
bv_unsigned (ew E0 n) = b ->
forall x, 0 <= x < 2 ^ 64 -> ~ (b + lo <= x < b + hi) -> aview trasegs H m' x = aview trasegs H m x.
Proof.
intros E0 rs H m m' n b lo hi HF Hrs Hb x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hbs & Hlo & Hhi)]; [lia|].
rewrite Hbs in Hr. cbn [base_val] in Hr. rewrite Hb in Hr. lia.
Qed.
Lemma lg_kept_ro : forall E0 rs (H : word -> bool) (m m' : word -> option byte),
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr) ->
forall x, 0 <= x < 2 ^ 64 -> aview trasegs H m' x = aview trasegs H m x.
Proof.
intros E0 rs H m m' HF Hrs x Hx. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). pose proof (Hrs rr Hin). lia.
Qed.
Lemma lg_fle_cvt_test : forall md (bw mw : word) (b mean s m : Z),
bw = Z_to_bv 64 b -> mw = Z_to_bv 64 mean -> 0 <= b < 256 -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
fpop2_denot (FP2_cmp F_LE FMT_D) (fpop1_denot (FP1_cvt FC_D FC_WU md) bw) mw = if b * s <=? m then w1 else w0.
Proof.
intros md bw mw b mean s m -> -> Hb Hm Hq. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
rewrite fp_arg_fcvt_d_wu, fp_arg_D, !unsigned_lit_small by lia.
rewrite (crawl_scan_le md b mean m s ltac:(lia) Hq). reflexivity.
Qed.
Lemma lg_flt_cvt_test : forall md (bw mw : word) (b mean s m : Z),
bw = Z_to_bv 64 b -> mw = Z_to_bv 64 mean -> 0 <= b < 256 -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
fpop2_denot (FP2_cmp F_LT FMT_D) mw (fpop1_denot (FP1_cvt FC_D FC_WU md) bw) = if b * s <=? m then w0 else w1.
Proof.
intros md bw mw b mean s m -> -> Hb Hm Hq. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
rewrite fp_arg_fcvt_d_wu, fp_arg_D, !unsigned_lit_small by lia.
rewrite (crawl_scan_gt md b mean m s ltac:(lia) Hq).
destruct (Z.leb_spec (b * s) m); destruct (Z.ltb_spec m (b * s)); try reflexivity; lia.
Qed.
Lemma lg_bne_bool_w : forall t : bool, branch_taken BC_NE (if t then w1 else w0) (Z_to_bv 64 0) = t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma lg_bne_bool_w_neg : forall t : bool, branch_taken BC_NE (if t then w0 else w1) (Z_to_bv 64 0) = negb t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma lg_denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma lg_addw1_pred : forall E a x, sv_denot E a = Z_to_bv 64 (x - 1) -> 0 <= x < 2 ^ 31 ->
sv_denot E (SAluw ALU_ADD a (SLit 1)) = Z_to_bv 64 x.
Proof.
intros E a x Ha Hx. apply lg_denot_of_U. rewrite U_SAluw. cbn [zalu_raw]. unfold U at 1. rewrite Ha, U_SLit.
rewrite Z_to_bv_unsigned. unfold bv_wrap at 2, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (zcanon_id 1) by (unfold M64; lia). change (1 mod 2 ^ 32) with 1.
assert (E1 : ((x - 1) mod 2 ^ 64) mod 2 ^ 32 = (x - 1) mod 2 ^ 32).
{ change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Zaux.Zmod_mod_mult by lia. reflexivity. }
rewrite E1.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (4294967296 `div` 2) with 2147483648. change (2 ^ 32) with 4294967296.
destruct (Z.eq_dec x 0) as [-> | Hne].
- reflexivity.
- rewrite (Z.mod_small (x - 1)) by lia. replace (x - 1 + 1) with x by lia.
rewrite (Z.mod_small (x + 2147483648)) by lia.
replace (x + 2147483648 - 2147483648) with x by lia. apply Z.mod_small. lia.
Qed.
Lemma lg_subw1_succ : forall E a y, sv_denot E a = Z_to_bv 64 (y + 1) -> 0 <= y < 2 ^ 31 - 1 ->
sv_denot E (SAluw ALU_ADD a (SLit (-1))) = Z_to_bv 64 y.
Proof.
intros E a y Ha Hy. apply lg_denot_of_U. rewrite U_SAluw. cbn [zalu_raw]. unfold U at 1. rewrite Ha, U_SLit.
rewrite Z_to_bv_unsigned. unfold bv_wrap at 2, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (y + 1)) by lia. rewrite (Z.mod_small (y + 1)) by lia.
change (zcanon (-1) mod 2 ^ 32) with 4294967295.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (4294967296 `div` 2) with 2147483648. change (2 ^ 32) with 4294967296.
replace ((y + 1 + 4294967295 + 2147483648) mod 4294967296) with (y + 2147483648) by (apply (Zmod_unique _ _ 1); lia).
replace (y + 2147483648 - 2147483648) with y by lia. apply Z.mod_small. lia.
Qed.
