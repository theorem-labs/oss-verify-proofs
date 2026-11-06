(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool Reals Lra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ02 YQ04 YI00 YI01 YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06.
Unset Lia Cache. Unset Nia Cache.
Local Abbreviation S := fmt_single.
Local Open Scope Z_scope.
Definition SloB : Z := 18446744072887468033.
Lemma fp_arg_SloB : fp_arg FMT_S (Z_to_bv 64 SloB) = Slo.
Proof. vm_compute. reflexivity. Qed.
Lemma fp_arg_nanbox_val : forall (w : word) c, w = Z_to_bv 64 c -> 0 <= c < 2 ^ 32 ->
fp_arg FMT_S (fpop1_denot FP1_nanbox w) = c.
Proof.
intros w c -> Hc. rewrite fp_arg_nanbox. unfold low32. rewrite bv_extract_unsigned, Z_to_bv_unsigned.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small c (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma fp_arg_boxed32 : forall v, 0 <= v < 2 ^ 32 -> fp_arg FMT_S (nan_box (Z_to_bv 32 v)) = v.
Proof. intros v Hv. rewrite fp_arg_S. apply unsigned_unbox_nan_box. exact Hv. Qed.
Section KL.
Variable E : env.
Variables (nc np : nat) (c p : Z).
Hypothesis Hc : ew E nc = Z_to_bv 64 c. Hypothesis Rc : 0 <= c < 2 ^ 32.
Hypothesis Hp : ew E np = Z_to_bv 64 p. Hypothesis Rp : 0 <= p < 256.
Hypothesis Hin : s_in c 0 255.
Definition KDIFF : sv := SF2 (FP2_ari F_SUB FMT_S RNE) (SF1 FP1_nanbox (SOff nc 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff np 0)).
Definition kdiff : Z := fst (fp_sub S RNE c (fst (fp_of_int S RNE false 32 p))).
Lemma kl_diff_arg : fp_arg FMT_S (sv_denot E KDIFF) = kdiff.
Proof.
unfold KDIFF, kdiff. cbn [sv_denot]. rewrite fp_arg_ari. cbn [fari_sem fp_format].
rewrite (fp_arg_nanbox_val _ c) by first [rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hc; reflexivity | exact Rc].
rewrite fp_arg_fcvt_s_wu. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hp, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma kl_facts : exists e, -255 <= e <= 255 /\
fst (fp_lt S Slo kdiff) = true /\ fst (fp_lt S kdiff Shi) = true /\ fst (fp_to_int S RTZ true 32 kdiff) = int_wrap 32 e.
Proof.
destruct (dither_err RNE c p Slo Shi Hin Rp Slo_val Shi_val) as (rd & e & _ & _ & _ & H1 & H2 & H3 & _ & He & _).
exists e. split; [exact He|]. unfold kdiff. rewrite H1, H2. cbn [fst]. split; [reflexivity|]. split; [reflexivity|]. exact H3.
Qed.
Lemma kl_chk1 : U E (SF2 (FP2_cmp F_LT FMT_S) (SLit SloB) KDIFF) = 1.
Proof.
destruct kl_facts as (e & _ & H1 & _ & _).
unfold U. cbn [sv_denot]. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
rewrite fp_arg_SloB, kl_diff_arg, H1. vm_compute. reflexivity.
Qed.
Lemma kl_chk2 : forall nf, ew E nf = nan_box (Z_to_bv 32 Shi) -> U E (SF2 (FP2_cmp F_LT FMT_S) KDIFF (SOff nf 0)) = 1.
Proof.
intros nf Hf. destruct kl_facts as (e & _ & _ & H2 & _).
unfold U. cbn [sv_denot]. rewrite fcmp_denot. cbn [fcmp_sem fp_format]. rewrite Z.add_0_r, Hf, Z_to_bv_bv_unsigned.
rewrite kl_diff_arg, (fp_arg_boxed32 Shi) by (unfold Shi; lia). rewrite H2. vm_compute. reflexivity.
Qed.
Definition KERR : sv := SF1 (FP1_cvt FC_W FC_S RTZ) KDIFF.
Lemma kl_err : exists e, -255 <= e <= 255 /\ sv_denot E KERR = Z_to_bv 64 e.
Proof.
destruct kl_facts as (e & He & _ & _ & H3). exists e. split; [exact He|].
unfold KERR. cbn [sv_denot]. rewrite fcvt_w_s_denot, kl_diff_arg, H3.
unfold int_wrap. rewrite Z.land_ones by lia.
replace (Z_to_bv 32 (e mod 2 ^ 32)) with (bv_extract 0 32 (Z_to_bv 64 e)).
2:{ apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r, Z.mul_comm, Z.mod_add, Z.mod_mod by lia. reflexivity. }
apply sext32_small. lia.
Qed.
End KL.
Lemma mod64_32 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite Z.rem_mul_r, Z.mul_comm, Z.mod_add, Z.mod_mod by lia. reflexivity. Qed.
Lemma swrap32_mod : forall z, bv_swrap 32 (z mod 2 ^ 32) = bv_swrap 32 z.
Proof. intros z. change (z mod 2 ^ 32) with (bv_wrap 32 z). apply bv_swrap_wrap. Qed.
Section a.
Variable E : env. Variable T : sv. Variable e : Z.
Hypothesis HT : sv_denot E T = Z_to_bv 64 e. Hypothesis He : -2 ^ 20 <= e <= 2 ^ 20.
Lemma UT : U E T = e mod 2 ^ 64.
Proof. unfold U. rewrite HT, Z_to_bv_unsigned. reflexivity. Qed.
Lemma shl_small : forall k, 0 <= k <= 3 -> U E (SAlu ALU_SLL T (SLit k)) = (e * 2 ^ k) mod 2 ^ 64.
Proof.
intros k Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite UT, U_SLit.
replace (Z.land (zcanon k) 63) with k.
2:{ rewrite zcanon_id by (unfold M64; lia). assert (X : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia. destruct X as [-> |[-> |[-> | ->]]]; reflexivity. }
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64. rewrite Zdiv.Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma sov32_sub3 : U E (SAluw ALU_SUB (SAlu ALU_SLL T (SLit 3)) T) = U E (SAlu ALU_SUB (SAlu ALU_SLL T (SLit 3)) T).
Proof.
rewrite U_SAluw, (U_SAlu E ALU_SUB). cbn [zalu_raw]. rewrite (shl_small 3) by lia. rewrite UT. change (2 ^ 3) with 8.
rewrite !mod64_32. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (swrap32_mod (e * 8 mod 2 ^ 32 - e mod 2 ^ 32)). rewrite <- Zdiv.Zminus_mod. rewrite swrap32_mod.
rewrite swrap32_id by lia. rewrite <- Zdiv.Zminus_mod. reflexivity.
Qed.
Lemma sov32_add2 : U E (SAluw ALU_ADD (SAlu ALU_SLL T (SLit 2)) T) = U E (SAlu ALU_ADD (SAlu ALU_SLL T (SLit 2)) T).
Proof.
rewrite U_SAluw, (U_SAlu E ALU_ADD). cbn [zalu_raw]. rewrite (shl_small 2) by lia. rewrite UT. change (2 ^ 2) with 4.
rewrite !mod64_32. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (swrap32_mod (e * 4 mod 2 ^ 32 + e mod 2 ^ 32)). rewrite <- Zdiv.Zplus_mod. rewrite swrap32_mod.
rewrite swrap32_id by lia. rewrite <- Zdiv.Zplus_mod. reflexivity.
Qed.
End a.
Lemma shiftr_mod_low : forall w k, 0 <= w -> 0 <= k <= 3 ->
(Z.shiftr w (8 * k)) mod 256 = (Z.shiftr (w mod 2 ^ 32) (8 * k)) mod 256.
Proof.
intros w k Hw Hk. rewrite !Z.shiftr_div_pow2 by lia.
assert (Hp : 0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
rewrite (Z.div_mod w (2 ^ 32)) at 1 by lia.
replace (2 ^ 32) with (2 ^ (8 * k) * (256 * 2 ^ (24 - 8 * k))) at 1.
2:{ change 256 with (2 ^ 8). rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
replace (2 ^ (8 * k) * (256 * 2 ^ (24 - 8 * k)) * (w / 2 ^ 32) + w mod 2 ^ 32)
with (w mod 2 ^ 32 + (w / 2 ^ 32 * (256 * 2 ^ (24 - 8 * k))) * 2 ^ (8 * k)) by lia.
rewrite Z.div_add by lia.
replace (w / 2 ^ 32 * (256 * 2 ^ (24 - 8 * k))) with ((w / 2 ^ 32 * 2 ^ (24 - 8 * k)) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma val_mem_of_cval4 : forall segs E m base off e,
chunk_ok segs E m base (mkChunk off (CVal 4 e)) -> val_mem segs m (base + off) 4 (U E e mod 2 ^ 32).
Proof.
intros segs E m base off e H k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
rewrite (le_byte_small (U E e mod 2 ^ 32) 4 k) by first [apply Z.mod_pos_bound; lia | lia].
unfold byte_of_word, U. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply shiftr_mod_low; [pose proof (bv_unsigned_in_range 64 (sv_denot E e)); lia | lia].
Qed.
Lemma U_fmv_s_mod : forall E X, U E (SF2 (FP2_sgnj F_SGNJ FMT_S) X X) mod 2 ^ 32 = fp_arg FMT_S (sv_denot E X).
Proof.
intros E X. unfold U. cbn [sv_denot]. rewrite fmv_s_denot. rewrite fp_arg_S.
rewrite <- (low32_nan_box (unbox_s (sv_denot E X))) at 2. unfold low32. rewrite bv_extract_unsigned.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Section CL.
Variable E : env.
Variables (nv f0 f1 : nat) (v : Z).
Hypothesis Hv : ew E nv = Z_to_bv 64 v. Hypothesis Rv : 0 <= v < 2 ^ 32.
Hypothesis H0 : ew E f0 = nan_box (Z_to_bv 32 0). Hypothesis H1 : ew E f1 = nan_box (Z_to_bv 32 S255).
Definition LEV (f : nat) : sv := SF2 (FP2_cmp F_LE FMT_S) (SF1 FP1_nanbox (SOff nv 0)) (SOff f 0).
Definition cb0 : bool := fst (fp_le S v 0).
Definition cb1 : bool := fst (fp_le S v S255).
Lemma fp_arg_v : fp_arg FMT_S (sv_denot E (SF1 FP1_nanbox (SOff nv 0))) = v.
Proof. cbn [sv_denot]. apply (fp_arg_nanbox_val _ v); [rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hv; reflexivity | exact Rv]. Qed.
Lemma fp_arg_f0 : fp_arg FMT_S (sv_denot E (SOff f0 0)) = 0.
Proof. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H0. apply fp_arg_boxed32. lia. Qed.
Lemma fp_arg_f1 : fp_arg FMT_S (sv_denot E (SOff f1 0)) = S255.
Proof. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H1. apply fp_arg_boxed32. unfold S255. lia. Qed.
Lemma U_LE0 : U E (LEV f0) = Z.b2z cb0.
Proof.
unfold U, LEV, cb0. cbn [sv_denot]. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
pose proof fp_arg_v as X. cbn [sv_denot] in X. rewrite X. pose proof fp_arg_f0 as Y. cbn [sv_denot] in Y. rewrite Y.
destruct (fst (fp_le S v 0)); vm_compute; reflexivity.
Qed.
Lemma U_LE1 : U E (LEV f1) = Z.b2z cb1.
Proof.
unfold U, LEV, cb1. cbn [sv_denot]. rewrite fcmp_denot. cbn [fcmp_sem fp_format].
pose proof fp_arg_v as X. cbn [sv_denot] in X. rewrite X. pose proof fp_arg_f1 as Y. cbn [sv_denot] in Y. rewrite Y.
destruct (fst (fp_le S v S255)); vm_compute; reflexivity.
Qed.
Lemma U_cl_and : U E (SAlu ALU_AND (LEV f0) (LEV f1)) = Z.b2z (cb0 && cb1).
Proof. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_LE0, U_LE1. destruct cb0, cb1; reflexivity. Qed.
Lemma U_cl_or : U E (SAlu ALU_OR (LEV f0) (SAlu ALU_XOR (LEV f1) (SLit 1))) = Z.b2z (cb0 || negb cb1).
Proof. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_LE0, U_LE1, U_SLit. destruct cb0, cb1; reflexivity. Qed.
Lemma cl_mid : cb0 || negb cb1 = false -> s_in v 0 255.
Proof.
unfold cb0, cb1. intros Hb. apply Bool.orb_false_iff in Hb as [Hb0 Hb1]. apply Bool.negb_false_iff in Hb1.
destruct (clamp_mid v 0 S255 is_ints_zero S255_val Hb1 Hb0) as (r & Hr & Hrr).
exists r. split; [exact Hr|]. change (IZR 0) with 0%R. change (IZR 255) with 255%R. lra.
Qed.
Lemma s_in_0 : s_in 0 0 255. Proof. apply (is_ints_s_in _ 0); [exact is_ints_zero | lia]. Qed.
Lemma s_in_255 : s_in S255 0 255. Proof. apply (is_ints_s_in _ 255); [exact S255_val | lia]. Qed.
End CL.
