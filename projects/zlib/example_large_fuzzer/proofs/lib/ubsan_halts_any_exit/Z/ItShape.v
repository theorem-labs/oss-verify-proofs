(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItCover.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma nth_bounded : forall (l : list Z) lo hi k, forallb (fun v => (lo <=? v) && (v <? hi)) l = true ->
  lo <= 0 < hi -> lo <= nth k l 0 < hi.
Proof.
  intros l lo hi k H Hz. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
  - apply (proj1 (forallb_forall _ _)) with (x := nth k l 0) in H; [|apply nth_In; exact Hk].
    apply Bool.andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma lext_byte : forall k, 0 <= nth k lext_l 0 < 256.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma dext_byte : forall k, 0 <= nth k dext_l 0 < 256.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma lbase_short : forall k, 0 <= nth k lbase_l 0 < 65536.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.
Lemma dbase_short : forall k, 0 <= nth k dbase_l 0 < 65536.
Proof. intros k. apply nth_bounded; [vm_compute; reflexivity | lia]. Qed.

Lemma sym_entry_range : forall ty s, 0 <= s < nsyms ty ->
  0 <= fst (sym_entry ty s) < 256 /\ 0 <= snd (sym_entry ty s) < 65536.
Proof.
  intros ty s Hs. destruct ty; cbn [sym_entry nsyms] in *.
  - cbn. lia.
  - destruct (Z.ltb_spec s 256); [cbn; lia|]. destruct (Z.eqb_spec s 256); [cbn; lia|].
    cbn [fst snd]. pose proof (lext_byte (Z.to_nat (s - 257))). pose proof (lbase_short (Z.to_nat (s - 257))). lia.
  - cbn [fst snd]. pose proof (dext_byte (Z.to_nat s)). pose proof (dbase_short (Z.to_nat s)). lia.
Qed.

Lemma wrap8_idem : forall z, wrap8 (wrap8 z) = wrap8 z.
Proof.
  intros z. apply wrap8_small. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma entry_sym_entry : forall ty s, 0 <= s ->
  wrap8 (fst (entry ty s)) = fst (sym_entry ty s) /\ snd (entry ty s) = snd (sym_entry ty s).
Proof.
  intros ty s Hs. destruct ty; cbn [entry sym_entry].
  - cbn [fst snd]. rewrite wrap8_small by lia. split; reflexivity.
  - destruct (Z.ltb_spec (s + 1) 257), (Z.ltb_spec s 256); try lia.
    + cbn [fst snd]. rewrite wrap8_small by lia. split; reflexivity.
    + destruct (Z.leb_spec 257 s), (Z.eqb_spec s 256); try lia; cbn [fst snd].
      * rewrite wrap8_idem. rewrite wrap8_small by apply lext_byte. split; reflexivity.
      * rewrite wrap8_small by lia. split; reflexivity.
  - cbn [fst snd]. rewrite wrap8_idem. rewrite wrap8_small by apply dext_byte. split; reflexivity.
Qed.


Section Shape.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hns : NC ll <= nsyms ty.
  Hypothesis HU : used wl root (NZ wl - 1) < 65536.
  #[local] Set Default Proof Using "Hll Ewl Hroot HM1 HK Hns HU".

  Lemma HW' : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HL' : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Let HW := HW'.
  Let HL := HL'.

  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation len_at := (len_at wl).
  Local Notation used := (used wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation drop := (drop wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation wsym := (wsym wl ll).

  Lemma wsym_ok : forall k, 0 <= k < NZ -> 0 <= wsym k < nsyms ty /\ LofS ll (wsym k) = len_at k.
  Proof.
    intros k Hk. pose proof (wsym_spec ll Hll k) as WS. rewrite <- Ewl in WS. specialize (WS Hk). destruct WS as [A B].
    split; [lia | exact B].
  Qed.

  Lemma here_shape : forall k x, 0 <= k < NZ ->
    (islong k = false -> x < 2 ^ root) -> (islong k = true -> 2 ^ root <= x) ->
    entry_shape ty root (used (NZ - 1)) x (here wl ll root ty k).
  Proof.
    intros k x Hk Hs Hlg. pose proof (root_range wl HW HL root Hroot HM1) as RR.
    pose proof (wsym_ok k Hk) as [SR SL]. pose proof (len_at_spec wl HW HL k Hk) as [L _].
    unfold here. destruct (entry ty (wsym k)) as [op val] eqn:E.
    pose proof (entry_sym_entry ty (wsym k) ltac:(lia)) as [E1 E2]. rewrite E in E1, E2. cbn [fst snd] in E1, E2.
    pose proof (sym_entry_range ty (wsym k) SR) as [B1 B2].
    left. exists (wsym k), (len_at k). split; [exact SR|]. split; [exact L|].
    rewrite code_op_pack, code_val_pack, code_bits_pack. rewrite E1. split; [reflexivity|].
    rewrite <- E2. split; [apply wrap16_small; rewrite E2; lia|].
    unfold ItDefs.drop. destruct (islong k) eqn:HLg.
    - right. pose proof HLg as H'. unfold ItDefs.islong in H'. apply Z.ltb_lt in H'.
      rewrite wrap8_small by lia. specialize (Hlg eq_refl). repeat split; lia.
    - left. pose proof HLg as H'. unfold ItDefs.islong in H'. apply Z.ltb_ge in H'.
      rewrite Z.sub_0_r, wrap8_small by lia. specialize (Hs eq_refl). repeat split; lia.
  Qed.

  Lemma fill_shape : forall k i v, 0 <= k < NZ -> In (i, v) (fill_writes wl ll root ty table k) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros k i v Hk Hin. pose proof (fill_writes_range wl ll root ty table HW HL Hroot HM1 HK k i v Hk Hin) as R.
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as [C1 [C2 C3]].
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> _].
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LS LL].
    apply here_shape; [exact Hk| |].
    - intros HS. destruct (LS HS) as [En [Ec Eu]]. rewrite En, Ec in R. lia.
    - intros HLg. destruct (LL HLg) as [N1 _]. lia.
  Qed.

  Lemma link_shape : forall k i v, 0 <= k < NZ -> In (i, v) (link_writes wl root ty table k) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros k i v Hk Hin. pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    apply (In_link_writes wl root ty table HW HL Hroot HM1 HK) in Hin as (Hk1 & N & _ & -> & ->).
    pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) N) as Lg.
    pose proof (lay_inv wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as [_ LL]. destruct (LL Lg) as (N1 & N2 & N3 & N4 & N5).
    pose proof (used_mono wl HW HL root Hroot HM1 (k + 1) (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)). pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)).
    pose proof (rev_bound root (Pfx wl root (k + 1)) ltac:(lia)) as RB.
    pose proof (pow2_le_15 (curr (k + 1)) ltac:(lia)).
    right; left. rewrite code_op_pack, code_val_pack, code_bits_pack.
    rewrite !wrap8_small by lia. rewrite wrap16_small by lia. repeat split; lia.
  Qed.

  Lemma trips_shape : forall i v, In (i, v) (trips_writes wl ll root ty table NZ) ->
    entry_shape ty root (used (NZ - 1)) (i - table) v.
  Proof.
    intros i v Hin. pose proof (NZ_pos wl HW HL HM1).
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin as [Hin|Hin]; [eapply fill_shape | eapply link_shape]; eauto.
  Qed.
End Shape.
