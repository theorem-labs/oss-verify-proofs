(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YChv YChx YChi YChn YChg YCf6 YCft YCi1 YCie YCph YCrr YCrd YCrc YCr3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 250.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_or_zero : forall E a b, U E (SAlu ALU_OR a b) = 0 -> U E a = 0 /\ U E b = 0.
Proof.
intros E a b H. rewrite U_SAlu in H. cbn [zalu_raw] in H.
pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold zcanon, M64 in *.
rewrite <- Z.land_ones in H by lia. rewrite Z.land_lor_distr_l in H. rewrite !Z.land_ones in H by lia.
rewrite (Z.mod_small (U E a)), (Z.mod_small (U E b)) in H by lia. apply Z.lor_eq_0_iff in H. exact H.
Qed.
Lemma rtb_val_mem_byte1 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> exists v, 0 <= v < 256 /\ val_mem trbsegs (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [b Hb]]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R. change (2 ^ 8) with 256 in R.
split; [lia|]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh. cbn. rewrite Hb. f_equal.
unfold YP0g.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rtb_val_mem_byte2 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> apresent H m (a + 1) -> exists v, 0 <= v < 65536 /\ val_mem trbsegs (mrestrict H m) a 2 v.
Proof.
intros H m a Ha0 Ha1.
destruct (rtb_val_mem_byte1 H m a Ha0) as (v0 & R0 & V0). destruct (rtb_val_mem_byte1 H m (a + 1) Ha1) as (v1 & R1 & V1).
exists (v0 + 256 * v1). split; [lia|]. intros k Hk.
assert (L0 : YP0g.le_byte v0 1 0 = v0) by (unfold YP0g.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v0 256) by lia; reflexivity).
assert (L1 : YP0g.le_byte v1 1 0 = v1) by (unfold YP0g.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v1 256) by lia; reflexivity).
assert (M0 : YP0g.le_byte (v0 + 256 * v1) 2 0 = v0).
{ unfold YP0g.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.shiftr_0_r, (Z.mod_small _ 65536) by lia.
replace (256 * v1) with (v1 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (M1 : YP0g.le_byte (v0 + 256 * v1) 2 1 = v1).
{ unfold YP0g.le_byte. change (8 * Z.of_nat 1) with 8. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite (Z.mod_small _ 65536) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. replace (v0 + 256 * v1) with (v1 * 256 + v0) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small v0 256) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia. }
destruct k as [|[|k]]; [| |lia].
- specialize (V0 0%nat ltac:(lia)). cbn [Z.of_nat] in *. rewrite V0, L0, M0. reflexivity.
- specialize (V1 0%nat ltac:(lia)). change (Z.of_nat 1) with 1. cbn [Z.of_nat] in V1. rewrite Z.add_0_r in V1. rewrite V1, L1, M1. reflexivity.
Qed.
End c.
Ltac upd_aboveF2 HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in let Heq := fresh "Heq" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Heq | Hin]; [rewrite <- Heq in Hrg; clear Heq; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac idx_of_baseLoR rs n lo :=
lazymatch rs with
| YQ0b.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baseLoR tl n lo in constr:(S i)
end.
