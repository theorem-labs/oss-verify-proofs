(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03.
Unset Lia Cache. Unset Nia Cache.
Local Abbreviation D := fmt_double.
Local Abbreviation S := fmt_single.
Local Open Scope Z_scope.
Lemma fp_arg_D w : fp_arg FMT_D w = bv_unsigned w.
Proof. reflexivity. Qed.
Lemma fp_arg_S w : fp_arg FMT_S w = bv_unsigned (unbox_s w).
Proof. reflexivity. Qed.


Lemma fp_arg_res_D v : 0 <= v < 2 ^ 64 -> fp_arg FMT_D (fp_res FMT_D v) = v.
Proof. apply unsigned_Z_to_bv64. Qed.
Lemma fp_arg_res_S v : 0 <= v < 2 ^ 32 -> fp_arg FMT_S (fp_res FMT_S v) = v.
Proof. apply unsigned_unbox_nan_box. Qed.


Lemma fp_format_ok fmt : format_ok (fp_format fmt).
Proof. destruct fmt; [apply fmt_single_ok|apply fmt_double_ok]. Qed.
Lemma fp_arg_res fmt v :
0 <= v < 2 ^ fp_width (fp_format fmt) -> fp_arg fmt (fp_res fmt v) = v.
Proof. destruct fmt; [apply fp_arg_res_S|apply fp_arg_res_D]. Qed.
Lemma fari_sem_range o fmt md a b :
0 <= fst (fari_sem o (fp_format fmt) md a b) < 2 ^ fp_width (fp_format fmt).
Proof.
destruct o; cbn [fari_sem].
- apply (fp_add_range _ (fp_format_ok fmt)).
- apply (fp_sub_range _ (fp_format_ok fmt)).
- apply (fp_mul_range _ (fp_format_ok fmt)).
- apply (fp_div_range _ (fp_format_ok fmt)).
Qed.
Theorem fp_arg_ari o fmt md a b :
fp_arg fmt (fpop2_denot (FP2_ari o fmt md) a b)
= fst (fari_sem o (fp_format fmt) md (fp_arg fmt a) (fp_arg fmt b)).
Proof. cbn [fpop2_denot]. apply fp_arg_res. apply fari_sem_range. Qed.
Theorem fp_arg_fma o fmt md a b c :
fp_arg fmt (fpop3_denot (FP3_fma o fmt md) a b c)
= fst (fp_fma (fp_format fmt) md (fst (fma_args o (fp_format fmt) (fp_arg fmt a) (fp_arg fmt c)))
(fp_arg fmt b)
(snd (fma_args o (fp_format fmt) (fp_arg fmt a) (fp_arg fmt c)))).
Proof.
cbn [fpop3_denot]. destruct (fma_args o _ _ _) as [a' c']. cbn [fst snd].
apply fp_arg_res. apply (fp_fma_range _ (fp_format_ok fmt)).
Qed.
Corollary fp_arg_fmadd fmt md a b c :
fp_arg fmt (fpop3_denot (FP3_fma F_MADD fmt md) a b c)
= fst (fp_fma (fp_format fmt) md (fp_arg fmt a) (fp_arg fmt b) (fp_arg fmt c)).
Proof. apply fp_arg_fma. Qed.
Theorem fcmp_denot o fmt a b :
fpop2_denot (FP2_cmp o fmt) a b
= if fst (fcmp_sem o (fp_format fmt) (fp_arg fmt a) (fp_arg fmt b)) then w1 else w0.
Proof. reflexivity. Qed.
Theorem fp_arg_cvt_of_int fmt dst src md sg bits a :
fcvt_fty dst = Some fmt -> fcvt_fty src = None -> fcvt_ity src = Some (sg, bits) ->
fp_arg fmt (fpop1_denot (FP1_cvt dst src md) a)
= fst (fp_of_int (fp_format fmt) md sg bits (bv_unsigned a)).
Proof.
intros H1 H2 H3. cbn [fpop1_denot]. unfold fcvt_denot. rewrite H1, H2, H3.
apply fp_arg_res. apply (fp_of_int_range _ (fp_format_ok fmt)).
Qed.
Corollary fp_arg_fcvt_d_wu md a :
fp_arg FMT_D (fpop1_denot (FP1_cvt FC_D FC_WU md) a) = fst (fp_of_int D md false 32 (bv_unsigned a)).
Proof. apply fp_arg_cvt_of_int; reflexivity. Qed.

Corollary fp_arg_fcvt_s_wu md a :
fp_arg FMT_S (fpop1_denot (FP1_cvt FC_S FC_WU md) a) = fst (fp_of_int S md false 32 (bv_unsigned a)).
Proof. apply fp_arg_cvt_of_int; reflexivity. Qed.




Corollary fcvt_w_s_denot md a :
fpop1_denot (FP1_cvt FC_W FC_S md) a = sext 64 (Z_to_bv 32 (fst (fp_to_int S md true 32 (fp_arg FMT_S a)))).
Proof. reflexivity. Qed.

Theorem fp_arg_nanbox a : fp_arg FMT_S (fpop1_denot FP1_nanbox a) = bv_unsigned (low32 a).
Proof. cbn [fpop1_denot fp_arg]. rewrite unbox_nan_box. reflexivity. Qed.

Theorem fmv_d_denot a : fpop2_denot (FP2_sgnj F_SGNJ FMT_D) a a = a.
Proof. cbn [fpop2_denot]. apply fmv_d_word. Qed.
Theorem fmv_s_denot a :
fpop2_denot (FP2_sgnj F_SGNJ FMT_S) a a = nan_box (unbox_s a).
Proof. cbn [fpop2_denot]. rewrite (sgnj_same (n:=32%N)) by reflexivity. reflexivity. Qed.

Theorem fp_arg_fabs_d a :
fp_arg FMT_D (fpop2_denot (FP2_sgnj F_SGNJX FMT_D) a a) = fp_abs D (fp_arg FMT_D a).
Proof.
cbn [fpop2_denot fp_arg]. rewrite fabs_d_word. apply unsigned_Z_to_bv64.
apply (fp_abs_range D fmt_double_ok).
Qed.

