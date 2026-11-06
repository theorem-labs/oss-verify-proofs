(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanHexScan FxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Module FXH.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Local Open Scope Z_scope.

Section Leaf.
Variable leaf : int -> bool.
(* [comment removed for export] *)
Fixpoint scan_pow (k : nat) (base w : int) : bool :=
  match k with
  | O => leaf base
  | S k' => let h := PrimInt63.lsr w 1%uint63 in if scan_pow k' base h then scan_pow k' (PrimInt63.add base h) h else false
  end.
(* [comment removed for export] *)
Fixpoint scanP (p : positive) (k : nat) (base w : int) : bool :=
  match p with
  | xH => scan_pow k base w
  | xO q => scanP q (S k) base (PrimInt63.add w w)
  | xI q => if scan_pow k base w then scanP q (S k) (PrimInt63.add base w) (PrimInt63.add w w) else false
  end.

Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma pow2_pos : forall k : nat, 0 < 2 ^ Z.of_nat k. Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma scan_pow_spec : forall k base w, φ w = 2 ^ Z.of_nat k -> φ base + 2 ^ Z.of_nat k <= 2 ^ 62 ->
  scan_pow k base w = true -> forall i, φ base <= i < φ base + 2 ^ Z.of_nat k -> leaf (Uint63.of_Z i) = true.
Proof.
  induction k as [|k IH]; intros base w Hw Hb H i Hi; cbn [scan_pow] in H.
  - change (2 ^ Z.of_nat 0) with 1 in Hi. assert (i = φ base) by lia. subst i. rewrite Uint63.of_to_Z. exact H.
  - cbv zeta in H. pose proof (pow2_pos k) as Pk.
    assert (P2 : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
    assert (Hh : φ (PrimInt63.lsr w 1%uint63) = 2 ^ Z.of_nat k).
    { rewrite Uint63.lsr_spec, Hw, P2. change (φ 1%uint63) with 1. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    pose proof (Uint63.to_Z_bounded base) as Bb.
    assert (Ha : φ (PrimInt63.add base (PrimInt63.lsr w 1%uint63)) = φ base + 2 ^ Z.of_nat k).
    { rewrite Uint63.add_spec, Hh, wB63. apply Z.mod_small. lia. }
    destruct (scan_pow k base (PrimInt63.lsr w 1%uint63)) eqn:E1; [|discriminate].
    destruct (Z.lt_ge_cases i (φ base + 2 ^ Z.of_nat k)) as [L|G].
    + apply (IH base _ Hh ltac:(lia) E1). lia.
    + apply (IH _ _ Hh ltac:(rewrite Ha; lia) H). rewrite Ha. lia.
Qed.
Lemma scanP_spec : forall p k base w, φ w = 2 ^ Z.of_nat k -> φ base + Zpos p * 2 ^ Z.of_nat k <= 2 ^ 62 ->
  scanP p k base w = true -> forall i, φ base <= i < φ base + Zpos p * 2 ^ Z.of_nat k -> leaf (Uint63.of_Z i) = true.
Proof.
  induction p as [q IH|q IH|]; intros k base w Hw Hb H i Hi; cbn [scanP] in H; pose proof (pow2_pos k) as Pk;
    assert (P2 : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity);
    pose proof (Uint63.to_Z_bounded base) as Bb.
  - change (Z.pos q~1) with (2 * Z.pos q + 1) in *. pose proof (Z.mul_pos_pos _ _ (Pos2Z.is_pos q) Pk) as QX.
    set (X := 2 ^ Z.of_nat k) in *.
    destruct (scan_pow k base w) eqn:E1; [|discriminate].
    assert (Hww : φ (PrimInt63.add w w) = 2 * X) by (rewrite Uint63.add_spec, Hw, wB63; rewrite Z.mod_small by lia; lia).
    assert (Ha : φ (PrimInt63.add base w) = φ base + X) by (rewrite Uint63.add_spec, Hw, wB63; apply Z.mod_small; lia).
    destruct (Z.lt_ge_cases i (φ base + X)) as [L|G].
    + apply (scan_pow_spec k base w Hw ltac:(fold X; lia) E1). fold X. lia.
    + apply (IH (S k) (PrimInt63.add base w) (PrimInt63.add w w) ltac:(rewrite P2; exact Hww) ltac:(rewrite Ha, P2; fold X; lia) H). rewrite Ha, P2. fold X. lia.
  - change (Z.pos q~0) with (2 * Z.pos q) in *. pose proof (Z.mul_pos_pos _ _ (Pos2Z.is_pos q) Pk) as QX.
    set (X := 2 ^ Z.of_nat k) in *. assert (QX1 : X <= Z.pos q * X) by (pose proof (Pos2Z.is_pos q); nia).
    assert (Hww : φ (PrimInt63.add w w) = 2 * X) by (rewrite Uint63.add_spec, Hw, wB63; rewrite Z.mod_small by lia; lia).
    apply (IH (S k) base (PrimInt63.add w w) ltac:(rewrite P2; exact Hww) ltac:(rewrite P2; fold X; lia) H). rewrite P2. fold X. lia.
  - apply (scan_pow_spec k base w Hw ltac:(lia) H). lia.
Qed.
End Leaf.

(* [comment removed for export] *)
Definition scanG (leaf : int -> bool) (base n : N) : bool :=
  match n with
  | N0 => true
  | Npos p => match IMGF.z61 (Z.of_N base) with Some b => scanP leaf p 0 b 1%uint63 | None => false end
  end.
Lemma scanG_spec : forall leaf base n, Z.of_N base + Z.of_N n <= 2 ^ 62 -> scanG leaf base n = true ->
  forall i, (i < n)%N -> leaf (Uint63.of_Z (Z.of_N (base + i))) = true.
Proof.
  intros leaf base n Hb H i Hi. destruct n as [|p]; [lia|]. cbn [scanG] in H.
  destruct (IMGF.z61 (Z.of_N base)) as [b|] eqn:E; [|discriminate]. apply IMGF.z61_spec in E. destruct E as [E1 E2].
  apply (scanP_spec leaf p 0 b 1%uint63); [reflexivity|change (2 ^ Z.of_nat 0) with 1; lia|exact H|]. change (2 ^ Z.of_nat 0) with 1. lia.
Qed.

(* [comment removed for export] *)
Definition leaf_ok (s : PrimString.string) (o : int) : bool := match IMGF.hex_byte_atI s o with Some _ => true | None => false end.
Definition scanF (s : PrimString.string) (base n : N) : bool := scanG (leaf_ok s) base n.
Lemma leaf_ok_spec : forall s i, Z.of_N i < 2 ^ 62 -> leaf_ok s (Uint63.of_Z (Z.of_N i)) = true -> byte_ok s i = true.
Proof.
  intros s i Hi H. unfold leaf_ok in H. rewrite (IMGF.hex_byte_atI_spec s _ i) in H; [|rewrite Uint63.of_Z_spec, wB63; apply Z.mod_small; lia|exact Hi].
  unfold byte_ok. destruct (hex_byte_at s i); [reflexivity|discriminate].
Qed.
Lemma scanN_complete : forall s f base n, (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> byte_ok s (base + i) = true) ->
  scanN s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H;
    [cbn [scanN]|change (scanN s (S (S f)) base n) with (if N.eqb n 0 then true else if N.eqb n 1 then byte_ok s base else (scanN s (S f) base (N.div2 n) && scanN s (S f) (base + N.div2 n) (n - N.div2 n))%bool)].
  - change (2 ^ N.of_nat 0)%N with 1%N in Hn. destruct (N.eqb_spec n 0); [reflexivity|]. assert (n = 1%N) by lia. subst n. cbn [N.eqb Pos.eqb].
    specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
  - destruct (N.eqb_spec n 0); [reflexivity|]. destruct (N.eqb_spec n 1).
    + subst n. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
    + assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
      pose proof (N.div2_odd n) as D. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      assert (Hb : (N.b2n (N.odd n) <= 1)%N) by (destruct (N.odd n); cbn; lia).
      rewrite (IH base h) by (try lia; intros i Hi; apply H; lia).
      rewrite (IH (base + h)%N (n - h)%N); [reflexivity|lia|]. intros i Hi. rewrite <- N.add_assoc. apply H. lia.
Qed.
Theorem scan_ok : forall s base n, scanF s base n = true -> Z.of_N base + Z.of_N n <= 2 ^ 62 -> scanN s 64 base n = true.
Proof.
  intros s base n H Hb. apply (scanN_complete s 63 base n).
  - apply N2Z.inj_le. rewrite N2Z.inj_pow. change (Z.of_N 2) with 2. change (Z.of_N (N.of_nat 63)) with 63. lia.
  - intros i Hi. apply leaf_ok_spec; [lia|]. exact (scanG_spec _ base n Hb H i Hi).
Qed.

(* [comment removed for export] *)
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Definition leaf_zero (s : PrimString.string) (o : int) : bool := match IMGF.hex_byte_atI s o with Some Z0 => true | _ => false end.
Definition zscanF (s : PrimString.string) (base n : N) : bool := scanG (leaf_zero s) base n.
Lemma leaf_zero_spec : forall s i, Z.of_N i < 2 ^ 62 -> leaf_zero s (Uint63.of_Z (Z.of_N i)) = true -> byte_zero s i = true.
Proof.
  intros s i Hi H. unfold leaf_zero in H. rewrite (IMGF.hex_byte_atI_spec s _ i) in H; [|rewrite Uint63.of_Z_spec, wB63; apply Z.mod_small; lia|exact Hi].
  unfold byte_zero. destruct (hex_byte_at s i) as [b|]; [|discriminate]. cbn [option_map] in H.
  destruct (bv_unsigned b); [reflexivity|discriminate|discriminate].
Qed.
Section ZS.
Variable zs : PrimString.string -> nat -> N -> N -> bool.
Variable bz : PrimString.string -> N -> bool.
Hypothesis ZS_eq : forall s f base n, zs s (S f) base n =
  if N.eqb n 0 then true else if N.eqb n 1 then bz s base else (zs s f base (N.div2 n) && zs s f (base + N.div2 n) (n - N.div2 n))%bool.
Hypothesis BZ : forall s i, byte_zero s i = true -> bz s i = true.
Lemma zs_complete : forall s f base n, (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> byte_zero s (base + i) = true) ->
  zs s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H; rewrite ZS_eq.
  - change (2 ^ N.of_nat 0)%N with 1%N in Hn. destruct (N.eqb_spec n 0); [reflexivity|]. assert (n = 1%N) by lia. subst n. cbn [N.eqb Pos.eqb].
    apply BZ. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
  - destruct (N.eqb_spec n 0); [reflexivity|]. destruct (N.eqb_spec n 1).
    + subst n. apply BZ. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
    + assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
      pose proof (N.div2_odd n) as D. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      assert (Hb : (N.b2n (N.odd n) <= 1)%N) by (destruct (N.odd n); cbn; lia).
      rewrite (IH base h) by (try lia; intros i Hi; apply H; lia).
      rewrite (IH (base + h)%N (n - h)%N); [reflexivity|lia|]. intros i Hi. rewrite <- N.add_assoc. apply H. lia.
Qed.
Theorem zscan_ok : forall s base n, zscanF s base n = true -> Z.of_N base + Z.of_N n <= 2 ^ 62 -> zs s 64 base n = true.
Proof.
  intros s base n H Hb. apply (zs_complete s 63 base n).
  - apply N2Z.inj_le. rewrite N2Z.inj_pow. change (Z.of_N 2) with 2. change (Z.of_N (N.of_nat 63)) with 63. lia.
  - intros i Hi. apply leaf_zero_spec; [lia|]. exact (scanG_spec _ base n Hb H i Hi).
Qed.
End ZS.
End FXH.
