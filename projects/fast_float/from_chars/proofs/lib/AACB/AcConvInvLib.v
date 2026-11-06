(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tget_is (o : Z) (c : tree bval) (v : bval) : bool :=
  match tget (okey o) c with Some v' => bval_eqb v' v | None => match v with BK 0 => true | _ => false end end.
Fixpoint bk_list (o : Z) (bs : list Z) : list (Z * bval) := match bs with [] => [] | b :: bs' => (o, BK b) :: bk_list (o + 1) bs' end.
Definition bv_list (o : Z) (l : lin) (w : nat) : list (Z * bval) := List.map (fun j => (o + Z.of_nat j, BV l (Z.of_nat j))) (seq 0 w).
Definition fb (c : tree bval) (l : list (Z * bval)) : bool := forallb (fun e => tget_is (fst e) c (snd e)) l.
Lemma tget_is_sound : forall o c v, tget_is o c v = true -> tget (okey o) c = Some v \/ (tget (okey o) c = None /\ v = BK 0).
Proof.
  intros o c v H. unfold tget_is in H. destruct (tget (okey o) c) as [v'|].
  - left. apply bval_eqb_eq in H. subst. reflexivity.
  - right. split; [reflexivity|]. destruct v as [b|l j]; [|discriminate]. destruct b; [reflexivity | discriminate | discriminate].
Qed.

(* [comment removed for export] *)
Section Bytes.
Variable E : valu.
Variable m : word -> option byte.

#[using="Type"] Lemma byte_tracked : forall bl zl k c o v, rg_ok SEGS E m (RG bl zl k c) -> 0 <= o -> tget (okey o) c = Some v ->
  rd1 SEGS m (Z_to_bv 64 (uE E bl + o)) = Some (bden E v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl k c o v HR Ho Ht. destruct HR as (_ & _ & _ & HT). destruct (HT _ _ Ht) as [_ X]. cbn [rg_base] in X.
  unfold okey in X. rewrite Z2Pos.id in X by lia. replace (o + 1 - 1) with o in X by lia. exact X.
Qed.

#[using="Type"] Lemma byte_rz : forall bl zl c o, rg_ok SEGS E m (RG bl zl RZ c) -> 0 <= o < rsz E (RG bl zl RZ c) -> tget (okey o) c = None ->
  rd1 SEGS m (Z_to_bv 64 (uE E bl + o)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl c o HR Ho Ht. destruct HR as (_ & _ & HB & _). specialize (HB o Ho). cbn [rg_kind rg_cont rg_base] in HB.
  destruct HB as [_ X]. exact (X Ht).
Qed.

#[using="Type"] Lemma rd_of_rd1 : forall a w v, 0 <= a -> a + Z.of_nat w <= two64 ->
  (forall j, (j < w)%nat -> rd1 SEGS m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error (word_to_le_bytes w (wa v)) j) -> rd m a w v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a w v Ha Hw H. unfold rd.
  assert (Hl : length (word_to_le_bytes w (wa v)) = w) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
  rewrite <- Hl at 1. unfold wa at 1. apply rdn_of_rd1; [exact Ha | rewrite Hl; exact Hw |]. rewrite Hl. exact H.
Qed.
End Bytes.

Section Words.
Variable E : valu.
Variable m : word -> option byte.

#[using="Type"] Lemma in_bk_list : forall bs o j, (j < length bs)%nat -> In (o + Z.of_nat j, BK (nth j bs 0)) (bk_list o bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; intros o j Hj; cbn [length] in Hj; [lia|]. destruct j as [|j].
  - left. cbn [nth]. rewrite Z.add_0_r. reflexivity.
  - right. cbn [nth]. replace (o + Z.of_nat (Datatypes.S j)) with (o + 1 + Z.of_nat j) by lia. apply IH. lia.
Qed.

#[using="Type"] Lemma in_bv_list : forall o l w j, (j < w)%nat -> In (o + Z.of_nat j, BV l (Z.of_nat j)) (bv_list o l w).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros o l w j Hj. unfold bv_list. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd_bk : forall bl zl c o bs v, rg_ok SEGS E m (RG bl zl RZ c) -> 0 <= o -> o + Z.of_nat (length bs) <= rsz E (RG bl zl RZ c) ->
  uE E bl + o + Z.of_nat (length bs) <= two64 ->
  forallb (fun e => tget_is (fst e) c (snd e)) (bk_list o bs) = true -> word_to_le_bytes (length bs) (wa v) = List.map (Z_to_bv 8) bs ->
  rd m (uE E bl + o) (length bs) v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl c o bs v HR Ho Hz Hw Hf Hv. assert (Rb : 0 <= uE E bl) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E bl)) as X; unfold bv_modulus in X; lia).
  apply rd_of_rd1; [lia | exact Hw |]. intros j Hj. rewrite forallb_forall in Hf.
  rewrite Hv. rewrite nth_error_map. rewrite (nth_error_nth' bs 0 Hj). rewrite <- Z.add_assoc.
  destruct (tget_is_sound _ _ _ (Hf _ (in_bk_list bs o j Hj))) as [Ht|(Ht & Hz0)]; cbn [fst snd] in Ht.
  - rewrite (byte_tracked E m bl zl RZ c (o + Z.of_nat j) _ HR ltac:(lia) Ht). reflexivity.
  - injection Hz0 as Hz0. rewrite Hz0. exact (byte_rz E m bl zl c (o + Z.of_nat j) HR ltac:(lia) Ht).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd_bv : forall bl zl k c o l, rg_ok SEGS E m (RG bl zl k c) -> 0 <= o -> uE E bl + o + 8 <= two64 ->
  forallb (fun e => tget_is (fst e) c (snd e)) (bv_list o l 8) = true -> rd m (uE E bl + o) 8 (uE E l).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl k c o l HR Ho Hw Hf. assert (Rb : 0 <= uE E bl) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E bl)) as X; unfold bv_modulus in X; lia).
  apply rd_of_rd1; [lia | exact Hw |]. intros j Hj. rewrite forallb_forall in Hf.
  destruct (tget_is_sound _ _ _ (Hf _ (in_bv_list o l 8 j Hj))) as [Ht|(_ & X)]; [|discriminate]. cbn [fst snd] in Ht.
  rewrite <- Z.add_assoc. rewrite (byte_tracked E m bl zl k c (o + Z.of_nat j) _ HR ltac:(lia) Ht). cbn [bden].
  unfold word_to_le_bytes, uE. rewrite wa_u. rewrite nth_Z_to_le_bytes by exact Hj. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd_rz0 : forall bl zl c o w, rg_ok SEGS E m (RG bl zl RZ c) -> 0 <= o -> o + Z.of_nat w <= rsz E (RG bl zl RZ c) ->
  uE E bl + o + Z.of_nat w <= two64 -> (forall j, (j < w)%nat -> tget (okey (o + Z.of_nat j)) c = None) -> rd m (uE E bl + o) w 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bl zl c o w HR Ho Hz Hw Hn. assert (Rb : 0 <= uE E bl) by (unfold uE; pose proof (bv_unsigned_in_range _ (lden E bl)) as X; unfold bv_modulus in X; lia).
  apply rd_of_rd1; [lia | exact Hw |]. intros j Hj.
  rewrite <- Z.add_assoc. rewrite (byte_rz E m bl zl c (o + Z.of_nat j) HR ltac:(lia) (Hn j Hj)).
  unfold word_to_le_bytes, wa. rewrite u_small64 by (unfold two64; lia). rewrite nth_Z_to_le_bytes by exact Hj.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.
End Words.

Lemma uE_lconst' : forall E c, 0 <= c < two64 -> uE E (lconst c) = c.
Proof. intros E c Hc. unfold uE. rewrite lden_lconst. apply u_small64. exact Hc. Qed.
Lemma rsz_lconst' : forall E b c k cont, 0 <= c < two64 -> rsz E (RG b (lconst c) k cont) = c.
Proof. intros E b c k cont Hc. unfold rsz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. exact Hc. Qed.
(* [comment removed for export] *)
