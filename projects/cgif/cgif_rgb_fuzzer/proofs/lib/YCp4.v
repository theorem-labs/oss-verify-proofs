(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YI08 YI0c YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCjo YM01 YM02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjc.
Lemma q_denot_off : forall E n p c, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (p + c).
Proof. intros E n p c Hn Hp. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma q_denot_off0 : forall E n p, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 p.
Proof. intros E n p Hn Hp. rewrite (q_denot_off E n p 0 Hn Hp), Z.add_0_r. reflexivity. Qed.
Lemma q_denot_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. rewrite denot_lit_U. f_equal. apply U_sext32_small; assumption. Qed.
Lemma q_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U. f_equal. exact H. Qed.
Lemma q_slot_of_state : forall {fx : YK11.FPState} E ss ms (H : word -> bool) idx lo hi wlo whi cs sp0 off e v,
st_ok trbsegs E ss (restrict H ms) -> nth_error (ss_mem ss) idx = Some (YQ0b.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
In (YQ0b.mkChunk (off - 576) (CVal 8 e)) cs -> bv_unsigned (ew E 2) = sp0 -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trbsegs (mrestrict H (ms_mem ms)) (sp0 - 576 + off) 8 v.
Proof.
intros fx E ss ms H idx lo hi wlo whi cs sp0 off e v HS Hnth Hin U2 He Hv.
destruct (st_ok_mem_ok trbsegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hnth)) as HR. cbn [ms_mem restrict] in HR.
replace (sp0 - 576 + off) with (sp0 + (off - 576)) by lia.
exact (field_of_region E _ 2 sp0 cs lo hi wlo whi (off - 576) 8%N e v HR U2 Hin He Hv ltac:(lia)).
Qed.
Definition trb_rol_const (B : asyms) : Prop :=
forall a, LDK_ROL <= a < LDK_ROL + 4 -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Lemma q_rol_in_ro : forall a, LDK_ROL <= a < LDK_ROL + 4 -> in_ro_tfa a.
Proof.
intros a Ha. left. exists (nth 0 trbsegs seg_dummy). split; [apply nth_In; vm_compute; lia|]. split; [vm_compute; reflexivity|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold LDK_ROL in Ha. lia.
Qed.
Lemma q_rol_val : forall (B : asyms) (H : word -> bool) mem, trb_rol_const B -> arodata_ok B (aview trbsegs H mem) ->
val_mem trbsegs (mrestrict H mem) LDK_ROL 4 Slo.
Proof.
intros B H mem RC HR k Hk.
assert (Ha : LDK_ROL <= LDK_ROL + Z.of_nat k < LDK_ROL + 4) by lia.
destruct (RC _ Ha) as [Ho He].
pose proof (HR (LDK_ROL + Z.of_nat k) (q_rol_in_ro _ Ha) Ho He) as Hb.
assert (Hby : option_map (fun b : byte => bv_unsigned b) (seg_rom trbsegs (Z_to_bv 64 (LDK_ROL + Z.of_nat k))) = Some (le_byte Slo 4 k))
by (do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
rewrite Hby in Hb.
destruct (aview_byte trbsegs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
