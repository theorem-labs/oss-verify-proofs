(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma land_mod32_mask : forall y m, 0 <= m < 2 ^ 32 -> Z.land y m = Z.land (y mod 2 ^ 32) m.
Proof.
  intros y m Hm. rewrite <- (Z.land_ones y 32) by lia.
  rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. symmetry. rewrite Z.land_ones_low; [reflexivity| lia |].
  destruct (Z.eq_dec m 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_mod_pow2 : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2 ^ n = Z.lxor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros k Hk.
  destruct (Z_lt_le_dec k n).
  - rewrite Z.mod_pow2_bits_low, !Z.lxor_spec, !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high, Z.lxor_spec, !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma szwrap32_mod : forall v, (szwrap 32 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite Zminus_mod, Z.mod_mod by lia.
  rewrite <- Zminus_mod. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. reflexivity.
Qed.

Lemma mod64_mod32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  rewrite Z.rem_mul_r by lia. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite (Z.mul_comm (2 ^ 32)), Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.


Lemma szwrap32_u64 : forall a, 0 <= a < 2 ^ 32 ->
  szwrap 32 a mod 2 ^ 64 = a + (if a <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite (Z.mod_small (a + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (a + 2 ^ 31) (-1) (2 ^ 32)) by lia.
    rewrite (Z.mod_small (a + 2 ^ 31 + -1 * 2 ^ 32)) by lia.
    rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma szwrap32_u64_zero : forall a, 0 <= a < 2 ^ 32 -> (szwrap 32 a mod 2 ^ 64 = 0 <-> a = 0).
Proof. intros a Ha. rewrite szwrap32_u64 by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. Qed.

Lemma lxor_m2_even : forall x, 0 <= x -> Z.land x 1 = 0 -> Z.lxor x (-2) = - x - 2.
Proof.
  intros x Hx He.
  assert (E1 : Z.lxor x 1 = x + 1) by (symmetry; apply Z.add_nocarry_lxor; exact He).
  change (-2) with (Z.lnot 1). rewrite <- Z.lnot_lxor_r, E1. unfold Z.lnot. lia.
Qed.

Lemma slide_end_ptr : forall B n, 1 <= n < 2 ^ 31 ->
  B + n * 2 + Z.lxor ((szwrap 32 (n + -1) * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31) (-2) = B.
Proof.
  intros B n Hn. rewrite szwrap_small by lia.
  rewrite Z.mod_small by lia.
  replace ((n + -1) * 2 ^ 32) with ((n - 1) * 2 * 2 ^ 31) by lia.
  rewrite Z.div_mul by lia.
  rewrite lxor_m2_even; [lia | lia |].
  change (Z.land ((n - 1) * 2) 1) with (Z.land ((n - 1) * 2) (Z.ones 1)).
  rewrite (Z.land_ones ((n - 1) * 2) 1) by lia. change (2 ^ 1) with 2.
  rewrite Z.mod_mul; lia.
Qed.

Section WithSegs.


Variables SL SD SB : Z.

End WithSegs.


Definition apart (r1 r2 : Z * Z) : Prop := fst r1 + snd r1 <= fst r2 \/ fst r2 + snd r2 <= fst r1.

Fixpoint apart_from (r : Z * Z) (l : list (Z * Z)) : Prop :=
  match l with [] => True | r' :: l' => apart r r' /\ apart_from r l' end.

Fixpoint apart_all (l : list (Z * Z)) : Prop :=
  match l with [] => True | r :: l' => apart_from r l' /\ apart_all l' end.

Lemma apart_from_nth : forall r l j d, apart_from r l -> (j < length l)%nat -> apart r (nth j l d).
Proof.
  intros r l. induction l as [|r' l IH]; intros j d H Hj; [cbn in Hj; lia|].
  destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn. apply IH; [exact H2|]. cbn in Hj. lia.
Qed.

Lemma apart_get : forall l i j d, apart_all l -> (i < j)%nat -> (j < length l)%nat ->
  apart (nth i l d) (nth j l d).
Proof.
  intros l. induction l as [|r l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|].
  destruct H as [H1 H2]. destruct i as [|i].
  - destruct j as [|j]; [lia|]. cbn. apply apart_from_nth; [exact H1|]. cbn in Hj. lia.
  - destruct j as [|j]; [lia|]. cbn. apply IH; [exact H2| lia |]. cbn in Hj. lia.
Qed.


Section Pre.
Variables SL SD SB : Z.

Definition fw_regions (FR S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : list (Z * Z) :=
  [(sp - FR, FR); (S, dsl_SIZE); (p_window p, 2 * ds_w_size ds); (p_prev p, 2 * ds_w_size ds);
   (p_head p, 2 * ds_hash_size ds); (p_strm p, zsl_SIZE); (zp_in zp, arr_len (cs_input (ds_strm ds)))].
End Pre.


Definition fam (w h pv inp : arr) : nat -> Z -> Z :=
  fun f => match f with 0%nat => wb w | 1%nat => pb h | 2%nat => pb pv | _ => wb inp end.

Ltac fam_bounds := cbn [fam]; intros; first [apply wb_range | apply pb_range].

Ltac open_wf H :=
  pose proof (wf_ws _ _ _ H) as Vws; pose proof (wf_wl _ _ _ H) as Vwl; pose proof (wf_wsz _ _ _ H) as Vwsz;
  pose proof (wf_pl _ _ _ H) as Vpl; pose proof (wf_wmask _ _ _ H) as Vwmask; pose proof (wf_hs _ _ _ H) as Vhs;
  pose proof (wf_hl _ _ _ H) as Vhl; pose proof (wf_hmask _ _ _ H) as Vhmask; pose proof (wf_hshift _ _ _ H) as Vhshift;
  pose proof (wf_ins _ _ _ H) as Vins; pose proof (wf_look _ _ _ H) as Vlook; pose proof (wf_sl _ _ _ H) as Vsl;
  pose proof (wf_ms _ _ _ H) as Vms; pose proof (wf_ih _ _ _ H) as Vih; pose proof (wf_hw _ _ _ H) as Vhw;
  pose proof (wf_ni _ _ _ H) as Vni; pose proof (wf_ai _ _ _ H) as Vai; pose proof (wf_inlen _ _ _ H) as Vinlen;
  pose proof (wf_ti _ _ _ H) as Vti; pose proof (wf_wrap _ _ _ H) as Vwrap.

Ltac cellS Hz acc name :=
  pose proof (acc _ _ _ _ _ _ _ _ (proj1 Hz)) as name.
