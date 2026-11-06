(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Reals Lra.
From Flocq Require Import Core.Raux Core.Defs Core.Float_prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ00 YQ0h YQ09 YQ04 YQ0a YQ07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM07 YM05 YM04 YM01 YM02 YM03 YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition C2P52 : word := Z_to_bv 64 4841369599423283200.
Definition CHALF : word := Z_to_bv 64 4602678819172646912.
Definition CMHALF : word := Z_to_bv 64 13826050856027422720.
Definition CONE : word := Z_to_bv 64 4607182418800017408.
Definition faddD (a b : word) : word := fpop2_denot (FP2_ari F_ADD FMT_D RNE) a b.
Definition fsubD (a b : word) : word := fpop2_denot (FP2_ari F_SUB FMT_D RNE) a b.
Definition fmulD (a b : word) : word := fpop2_denot (FP2_ari F_MUL FMT_D RNE) a b.
Definition fabsD (a : word) : word := fpop2_denot (FP2_sgnj F_SGNJX FMT_D) a a.
Definition fnegD (a : word) : word := fpop2_denot (FP2_sgnj F_SGNJN FMT_D) a a.
Definition fltD (a b : word) : word := fpop2_denot (FP2_cmp F_LT FMT_D) a b.
Definition fleD (a b : word) : word := fpop2_denot (FP2_cmp F_LE FMT_D) a b.
Definition round_exp (x : word) : word := alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 1)) (Z_to_bv 64 53).
Definition round_bits (x : word) : word :=
let e := round_exp x in
if bv_ltu (Z_to_bv 64 1074) e then x
else if negb (bv_ltu (Z_to_bv 64 1021) e) then fmulD (Z_to_bv 64 0) x
else
let ax := fabsD x in
let y := fsubD (fsubD (faddD ax C2P52) C2P52) ax in
let r := if negb (bv_eqb (fltD CHALF y) (Z_to_bv 64 0)) then fsubD (faddD y ax) CONE
else if negb (bv_eqb (fleD y CMHALF) (Z_to_bv 64 0)) then faddD (faddD y ax) CONE
else faddD y ax in
if bv_lts x (Z_to_bv 64 0) then fnegD r else r.
Local Open Scope R_scope.
Local Abbreviation D := fmt_double.
Lemma round_exp_field : forall x : word, bv_unsigned (round_exp x) = fp_exp_field D (bv_unsigned x).
Proof.
intros x. unfold round_exp. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by lia. change (Z.land 1 63) with 1%Z. change (Z.land 53 63) with 53%Z.
pose proof (word_range x) as Hx.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (_ / _)).
2:{ split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|].
apply Z.div_lt_upper_bound; [lia|]. eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia|].
rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
apply dexp_field_word.
Qed.
Theorem round_bits_mean : forall (x : word) (q : R),
dval (bv_unsigned x) q -> 0 <= q <= 255 ->
exists n : Z, is_intd (bv_unsigned (round_bits x)) n /\ (0 <= n <= 255)%Z.
Proof.
intros x q Hx Hq.
pose proof (word_range x) as Hxr.
destruct (musl_round_branches (bv_unsigned x) q Hx Hq Hxr) as (He1 & He2 & Hmain).
pose proof (round_exp_field x) as He.
unfold round_bits.
assert (Hb1 : bv_ltu (Z_to_bv 64 1074) (round_exp x) = false).
{ unfold bv_ltu. rewrite unsigned_lit_small by lia. rewrite He. apply Z.ltb_ge. lia. }
rewrite Hb1.
destruct (Z.le_gt_cases (fp_exp_field D (bv_unsigned x)) 1021) as [Hsmall | Hbig].
-
assert (Hb2 : bv_ltu (Z_to_bv 64 1021) (round_exp x) = false).
{ unfold bv_ltu. rewrite unsigned_lit_small by lia. rewrite He. apply Z.ltb_ge. lia. }
rewrite Hb2. cbn [negb].
exists 0%Z. split; [|lia]. apply dval0_is_intd.
unfold fmulD. rewrite <- fp_arg_D, fp_arg_ari. cbn [fari_sem fp_format]. rewrite !fp_arg_D, unsigned_lit_small by lia.
exact (proj1 (musl_round_small (bv_unsigned x) q 0 RNE Hx is_intd_zero)).
-
assert (Hb2 : bv_ltu (Z_to_bv 64 1021) (round_exp x) = true).
{ unfold bv_ltu. rewrite unsigned_lit_small by lia. rewrite He. apply Z.ltb_lt. lia. }
rewrite Hb2. cbn [negb].
assert (Hhalf : / 2 <= q) by (destruct (Rle_or_lt (/ 2) q) as [H|H]; [exact H | apply He2 in H; lia]).
destruct (Hmain Hhalf) as (Hx63 & Habs & Hq51).
destruct (musl_round_main (bv_unsigned x) q C2p52 Chalf Cmhalf Cone Hx (conj Hhalf Hq51) C2p52_val Chalf_val Cmhalf_val Cone_val)
as (N & Ht & Ht1 & Hy & HyN & Hlt & Hr0 & HN & Hle1 & Hle2).
set (ax := fabsD x). set (y := fsubD (fsubD (faddD ax C2P52) C2P52) ax).
assert (Hax : fp_arg FMT_D ax = bv_unsigned x) by (unfold ax, fabsD; rewrite fp_arg_fabs_d, fp_arg_D; exact Habs).
assert (HC52 : fp_arg FMT_D C2P52 = C2p52) by reflexivity.
assert (HCH : fp_arg FMT_D CHALF = Chalf) by reflexivity.
assert (HCMH : fp_arg FMT_D CMHALF = Cmhalf) by reflexivity.
assert (HC1 : fp_arg FMT_D CONE = Cone) by reflexivity.
assert (Hyv : fp_arg FMT_D y =
fst (fp_sub D RNE (fst (fp_sub D RNE (fst (fp_add D RNE (bv_unsigned x) C2p52)) C2p52)) (bv_unsigned x))).
{ unfold y, fsubD, faddD. rewrite fp_arg_ari. cbn [fari_sem fp_format]. rewrite fp_arg_ari. cbn [fari_sem fp_format].
rewrite fp_arg_ari. cbn [fari_sem fp_format]. rewrite Hax, HC52. reflexivity. }
assert (Hflt : fltD CHALF y = w0).
{ unfold fltD. rewrite fcmp_denot. cbn [fcmp_sem fp_format]. rewrite HCH, Hyv, Hlt. reflexivity. }
rewrite Hflt. change (bv_eqb w0 (Z_to_bv 64 0)) with true. cbn [negb].
assert (Hsgn : bv_lts x (Z_to_bv 64 0) = false).
{ unfold bv_lts. apply Z.ltb_ge. change (bv_signed (Z_to_bv 64 0)) with 0%Z.
apply (dval_pos_signed x q Hx). lra. }
rewrite Hsgn.
assert (Hr0v : fp_arg FMT_D (faddD y ax) = fst (fp_add D RNE (fp_arg FMT_D y) (bv_unsigned x))).
{ unfold faddD. rewrite fp_arg_ari. cbn [fari_sem fp_format]. rewrite Hax. reflexivity. }
pose proof (floor_half_range q Hq) as Hfl.
destruct (fst (fp_le D (fp_arg FMT_D y) Cmhalf)) eqn:Hle.
+ assert (Hfle : fleD y CMHALF = w1).
{ unfold fleD. rewrite fcmp_denot. cbn [fcmp_sem fp_format]. rewrite HCMH, Hle. reflexivity. }
rewrite Hfle. change (bv_eqb w1 (Z_to_bv 64 0)) with false. cbn [negb].
rewrite Hyv in Hle. destruct (Hle1 Hle) as [Hi HN1].
exists (N + 1)%Z. split; [|lia].
rewrite <- fp_arg_D. unfold faddD at 1. rewrite fp_arg_ari. cbn [fari_sem fp_format]. fold (faddD y ax).
rewrite Hr0v, Hyv, HC1. exact Hi.
+ assert (Hfle : fleD y CMHALF = w0).
{ unfold fleD. rewrite fcmp_denot. cbn [fcmp_sem fp_format]. rewrite HCMH, Hle. reflexivity. }
rewrite Hfle. change (bv_eqb w0 (Z_to_bv 64 0)) with true. cbn [negb].
rewrite Hyv in Hle. pose proof (Hle2 Hle) as HN2.
exists N. split; [|lia].
rewrite <- fp_arg_D, Hr0v, Hyv. exact Hr0.
Qed.
Corollary round_checks : forall (x : word) (q : R) (md : rmode),
dval (bv_unsigned x) q -> 0 <= q <= 255 ->
fst (fp_lt D Cm1 (bv_unsigned (round_bits x))) = true /\
fst (fp_lt D (bv_unsigned (round_bits x)) C256) = true /\
exists n : Z, fp_to_int D md false 64 (bv_unsigned (round_bits x)) = (n, no_flags) /\ (0 <= n <= 255)%Z.
Proof.
intros x q md Hx Hq. destruct (round_bits_mean x q Hx Hq) as (n & Hn & Hr).
destruct (round_result_checks _ n Cm1 C256 md Hn Hr Cm1_val C256_val) as (H1 & H2 & H3).
rewrite H1, H2. split; [reflexivity|]. split; [reflexivity|]. exists n. split; [exact H3 | exact Hr].
Qed.
Corollary round_checks_mean : forall (m : Z) (md : rmode),
mean_ok m -> (0 <= m < 2 ^ 64)%Z ->
fst (fp_lt D Cm1 (bv_unsigned (round_bits (Z_to_bv 64 m)))) = true /\
fst (fp_lt D (bv_unsigned (round_bits (Z_to_bv 64 m))) C256) = true.
Proof.
intros m md (mm & s & Hq & Hle) Hm.
destruct (mean_dval_range m mm s Hq Hle) as (q & Hd & Hr & _).
destruct (round_checks (Z_to_bv 64 m) q md) as (H1 & H2 & _); [rewrite unsigned_lit_small by lia; exact Hd | exact Hr |].
split; assumption.
Qed.
