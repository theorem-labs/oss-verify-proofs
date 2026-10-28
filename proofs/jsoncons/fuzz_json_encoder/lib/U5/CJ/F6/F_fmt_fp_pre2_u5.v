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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_lib_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_calls_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma prefix_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 68786 (zb PREFIX_STR).
Proof.
  intros m MI. unfold u8ro. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma zb_nth : forall l i, (0 <= i)%Z -> (Z.to_nat i < length l)%nat ->
  nth_error (zb l) (Z.to_nat i) = Some (Z_to_bv 8 (znth l i)).
Proof.
  intros l i Hi Hl. unfold zb, znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia.
  rewrite nth_error_map. rewrite (nth_error_nth' l 0%Z Hl). reflexivity.
Qed.

Lemma PREFIX_STR_range : forall i, (0 <= znth PREFIX_STR i <= 120)%Z.
Proof.
  intros i. unfold znth. destruct (i <? 0); [cbn; lia|].
  assert (HF : Forall (fun z => 0 <= z <= 120)%Z PREFIX_STR).
  { unfold PREFIX_STR. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  destruct (nth_in_or_default (Z.to_nat i) PREFIX_STR 0%Z) as [H|H]; [|rewrite H; cbn; lia].
  exact (proj1 (Forall_forall _ _) HF _ H).
Qed.

Lemma sext32_m1 : sext32 (-1) = 18446744073709551615%Z.
Proof. reflexivity. Qed.

Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma srliw1_small : forall i, (0 <= i < 2^31)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 i) 1) = (i / 2)%Z.
Proof.
  intros i Hi. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite swrap32_eq. mlia.
Qed.

(* [comment removed for export] *)
Lemma u32s_low_byte : forall ws k, (k < length ws)%nat ->
  nth_error (u32s ws) (4 * k) = Some (Z_to_bv 8 (bv_unsigned (nth k ws (Z_to_bv 64 0)))).
Proof.
  induction ws as [|w0 ws IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k].
  - cbn. reflexivity.
  - cbn [u32s nth]. replace (4 * S k)%nat with (4 + 4 * k)%nat by lia.
    rewrite nth_error_app2 by (rewrite length_le4; lia). rewrite length_le4. replace (4 + 4 * k - 4)%nat with (4 * k)%nat by lia.
    apply IH. cbn in Hk. lia.
Qed.

Lemma wnth_low_byte : forall ws k, (0 <= k)%Z -> (Z.to_nat k < length ws)%nat ->
  nth_error (u32s ws) (Z.to_nat (4 * k)) = Some (Z_to_bv 8 (wval ws k)).
Proof.
  intros ws k Hk Hl. replace (Z.to_nat (4 * k)) with (4 * Z.to_nat k)%nat by lia.
  rewrite (u32s_low_byte ws (Z.to_nat k) Hl). unfold wval, wnth. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
  rewrite <- (Z.mod_mod_divide _ 4294967296 256) by (exists 16777216%Z; reflexivity). reflexivity.
Qed.

Lemma land1_mod256 : forall v, (0 <= v)%Z -> Z.land (v mod 256) 1 = Z.land v 1.
Proof.
  intros v Hv. rewrite !land_bit0. change 256%Z with (2 * 128)%Z. rewrite Z.rem_mul_r, Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
