(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool SpecFloat.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import FpBound.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition GC_05f : Z := 0x3f000000.            (* [comment removed for export] *)
Definition GC_03f : Z := 0x3e99999a.            (* [comment removed for export] *)
Definition GC_02f : Z := 0x3e4ccccd.            (* [comment removed for export] *)
Definition GC_05d : Z := 0x3fe0000000000000.    (* [comment removed for export] *)
Definition GC_m1d : Z := 0xbff0000000000000.    (* [comment removed for export] *)
Definition GC_2p32d : Z := 0x41f0000000000000.  (* [comment removed for export] *)

Lemma GC_05f_FB : FB fmt_single 0 GC_05f. Proof. apply FB_const. vm_compute. reflexivity. Qed.
Lemma GC_03f_FB : FB fmt_single (-1) GC_03f. Proof. apply FB_const. vm_compute. reflexivity. Qed.
Lemma GC_02f_FB : FB fmt_single (-2) GC_02f. Proof. apply FB_const. vm_compute. reflexivity. Qed.
Lemma GC_05d_FB : FB fmt_double 0 GC_05d. Proof. apply FB_const. vm_compute. reflexivity. Qed.
Lemma GC_m1d_dec : fp_decode fmt_double GC_m1d = S754_finite true 4503599627370496 (-52). Proof. vm_compute. reflexivity. Qed.
Lemma GC_2p32d_dec : fp_decode fmt_double GC_2p32d = S754_finite false 4503599627370496 (-20). Proof. vm_compute. reflexivity. Qed.

Section Gray.
Variable md : rmode.

(* [comment removed for export] *)
Definition gray_i (v : Z) : Z := fst (fp_of_int fmt_single md true 32 v).
Definition gray_1 (g : Z) : Z := fst (fp_mul fmt_single md (gray_i g) GC_05f).
Definition gray_2 (r g : Z) : Z := fst (fp_fma fmt_single md (gray_i r) GC_03f (gray_1 g)).
Definition gray_3 (r g b : Z) : Z := fst (fp_fma fmt_single md (gray_i b) GC_02f (gray_2 r g)).
Definition gray_4 (r g b : Z) : Z := fst (fp_convert fmt_single fmt_double md (gray_3 r g b)).
Definition gray_5 (r g b : Z) : Z := fst (fp_add fmt_double md (gray_4 r g b) GC_05d).

Lemma gray_i_FB : forall v, 0 <= v < 256 -> FB fmt_single 9 (gray_i v).
Proof. intros v Hv. apply (fb_of_int fmt_single fmt_ok2_single md true 32 v 8); cbn; lia. Qed.

Lemma gray_1_FB : forall g, 0 <= g < 256 -> FB fmt_single 10 (gray_1 g).
Proof. intros g Hg. apply (fb_mul fmt_single fmt_ok2_single md 9 0 _ _ (gray_i_FB g Hg) GC_05f_FB); cbn; lia. Qed.

Lemma gray_2_FB : forall r g, 0 <= r < 256 -> 0 <= g < 256 -> FB fmt_single 12 (gray_2 r g).
Proof. intros r g Hr Hg. apply (fb_fma fmt_single fmt_ok2_single md 9 (-1) 10 _ _ _ (gray_i_FB r Hr) GC_03f_FB (gray_1_FB g Hg)); cbn; lia. Qed.

Lemma gray_3_FB : forall r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> FB fmt_single 14 (gray_3 r g b).
Proof. intros r g b Hr Hg Hb. apply (fb_fma fmt_single fmt_ok2_single md 9 (-2) 12 _ _ _ (gray_i_FB b Hb) GC_02f_FB (gray_2_FB r g Hr Hg)); cbn; lia. Qed.

Lemma gray_4_FB : forall r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> FB fmt_double 15 (gray_4 r g b).
Proof. intros r g b Hr Hg Hb. apply (fb_convert fmt_single fmt_double md 14 _ fmt_ok2_single fmt_ok2_double (gray_3_FB r g b Hr Hg Hb)); cbn; lia. Qed.

Lemma gray_5_FB : forall r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> FB fmt_double 17 (gray_5 r g b).
Proof. intros r g b Hr Hg Hb. apply (fb_add fmt_double fmt_ok2_double md 15 0 _ _ (gray_4_FB r g b Hr Hg Hb) GC_05d_FB); cbn; lia. Qed.

(* [comment removed for export] *)
Theorem gray_guard_lo : forall r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> fst (fp_lt fmt_double GC_m1d (gray_5 r g b)) = true.
Proof. intros r g b Hr Hg Hb. exact (fb_lt_lo fmt_double 17 _ _ _ _ (gray_5_FB r g b Hr Hg Hb) GC_m1d_dec). Qed.

Theorem gray_guard_hi : forall r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> fst (fp_lt fmt_double (gray_5 r g b) GC_2p32d) = true.
Proof.
  intros r g b Hr Hg Hb. apply (fb_lt_hi fmt_double fmt_ok2_double 17 _ _ _ _ (gray_5_FB r g b Hr Hg Hb) GC_2p32d_dec); [reflexivity | cbn; lia].
Qed.

Theorem gray_cast : forall mdc r g b, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 ->
  0 <= fst (fp_to_int fmt_double mdc false 32 (gray_5 r g b)) <= 2 ^ 17.
Proof. intros mdc r g b Hr Hg Hb. apply (fb_to_int fmt_double fmt_ok2_double mdc false 32 17 _ (gray_5_FB r g b Hr Hg Hb)); lia. Qed.
End Gray.

(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec StepTac FPSteps FPStepsV.
Local Open Scope Z_scope.

Definition gray_m5 (r g b : Z) : Z :=
  let wi := fun v : Z => bv_unsigned (Z_to_bv 32 (fst (fp_of_int (fp_format FMT_S) RNE true 32 v))) in
  let m1 := bv_unsigned (Z_to_bv 32 (fst (fpv_ari F_MUL FMT_S RNE (wi g) GC_05f))) in
  let m2 := bv_unsigned (Z_to_bv 32 (fst (fpv_fma F_MADD FMT_S RNE (wi r) GC_03f m1))) in
  let m3 := bv_unsigned (Z_to_bv 32 (fst (fpv_fma F_MADD FMT_S RNE (wi b) GC_02f m2))) in
  let m4 := bv_unsigned (Z_to_bv 64 (fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE m3))) in
  bv_unsigned (Z_to_bv 64 (fst (fpv_ari F_ADD FMT_D RNE m4 GC_05d))).

Lemma gray_m5_eq : forall r g b : Z, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> gray_m5 r g b = gray_5 RNE r g b.
Proof.
  intros r g b Hr Hg Hb. unfold gray_m5, fpv_ari, fpv_fma, fpv_fma_args. cbv zeta beta. cbn [fp_format].
  change (fst (fp_of_int fmt_single RNE true 32 g)) with (gray_i RNE g).
  change (fst (fp_of_int fmt_single RNE true 32 r)) with (gray_i RNE r).
  change (fst (fp_of_int fmt_single RNE true 32 b)) with (gray_i RNE b).
  rewrite !(fp_u_Z2bv32 (gray_i RNE _)) by (first [exact (FB_range_single _ _ (gray_i_FB RNE g Hg)) | exact (FB_range_single _ _ (gray_i_FB RNE r Hr)) | exact (FB_range_single _ _ (gray_i_FB RNE b Hb))]).
  change (fst (fp_mul fmt_single RNE (gray_i RNE g) GC_05f)) with (gray_1 RNE g).
  rewrite (fp_u_Z2bv32 (gray_1 RNE g)) by (exact (FB_range_single _ _ (gray_1_FB RNE g Hg))).
  change (fst (fp_fma fmt_single RNE (gray_i RNE r) GC_03f (gray_1 RNE g))) with (gray_2 RNE r g).
  rewrite (fp_u_Z2bv32 (gray_2 RNE r g)) by (exact (FB_range_single _ _ (gray_2_FB RNE r g Hr Hg))).
  change (fst (fp_fma fmt_single RNE (gray_i RNE b) GC_02f (gray_2 RNE r g))) with (gray_3 RNE r g b).
  rewrite (fp_u_Z2bv32 (gray_3 RNE r g b)) by (exact (FB_range_single _ _ (gray_3_FB RNE r g b Hr Hg Hb))).
  change (fst (fp_convert fmt_single fmt_double RNE (gray_3 RNE r g b))) with (gray_4 RNE r g b).
  rewrite (u_Z2bv (gray_4 RNE r g b)) by (pose proof (FB_range_double _ _ (gray_4_FB RNE r g b Hr Hg Hb)); lia).
  change (fst (fp_add fmt_double RNE (gray_4 RNE r g b) GC_05d)) with (gray_5 RNE r g b).
  pose proof (FB_range_double _ _ (gray_5_FB RNE r g b Hr Hg Hb)). apply u_Z2bv; lia.
Qed.

(* [comment removed for export] *)
Lemma gray_m_guard_lo : forall r g b : Z, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> fst (fpv_cmp F_LT FMT_D GC_m1d (gray_m5 r g b)) = true.
Proof. intros r g b Hr Hg Hb. rewrite gray_m5_eq by assumption. exact (gray_guard_lo RNE r g b Hr Hg Hb). Qed.
Lemma gray_m_guard_hi : forall r g b : Z, 0 <= r < 256 -> 0 <= g < 256 -> 0 <= b < 256 -> fst (fpv_cmp F_LT FMT_D (gray_m5 r g b) GC_2p32d) = true.
Proof. intros r g b Hr Hg Hb. rewrite gray_m5_eq by assumption. exact (gray_guard_hi RNE r g b Hr Hg Hb). Qed.
