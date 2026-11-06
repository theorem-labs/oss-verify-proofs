(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.
Definition byte_z (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

(* [comment removed for export] *)
Fixpoint scan (f : PrimString.string -> N -> bool) (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S g =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then f s base
      else let h := N.div2 n in (scan f s g base h && scan f s g (base + h) (n - h))%bool
  end.

Lemma scan_sound : forall f s fuel base n, scan f s fuel base n = true -> forall i, (i < n)%N -> f s (base + i)%N = true.
Proof.
  intros f s fuel. induction fuel as [|g IH]; intros base n H i Hi; cbn [scan] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. exact H.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

Lemma byte_ok_some : forall s off, byte_ok s off = true -> exists b, hex_byte_at s off = Some b.
Proof. intros s off H. unfold byte_ok in H. destruct (hex_byte_at s off) as [b|]; [exists b; reflexivity | discriminate]. Qed.

Lemma byte_z_zero : forall s off, byte_z s off = true -> hex_byte_at s off = Some (Z_to_bv 8 0).
Proof.
  intros s off H. unfold byte_z in H. destruct (hex_byte_at s off) as [b|]; [|discriminate].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint cscan (p : int -> bool) (s : PrimString.string) (fuel : nat) (k n : int) : bool :=
  match fuel with
  | O => (n =? 0)%uint63
  | S g =>
      if (n =? 0)%uint63 then true
      else if (n =? 1)%uint63 then p (PrimString.get s k)
      else let h := (n >> 1)%uint63 in if cscan p s g k h then cscan p s g (k + h)%uint63 (n - h)%uint63 else false
  end.
Lemma cscan_sound : forall p s fuel k n, cscan p s fuel k n = true -> to_Z k + to_Z n < wB ->
  forall j, 0 <= j < to_Z n -> p (PrimString.get s (of_Z (to_Z k + j))) = true.
Proof.
  intros p s fuel. induction fuel as [|g IH]; intros k n H Hb j Hj; cbn [cscan] in H.
  - apply Uint63.eqb_spec in H. subst n. change (to_Z 0) with 0 in Hj. lia.
  - destruct (n =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst n; change (to_Z 0) with 0 in Hj; lia|].
    destruct (n =? 1)%uint63 eqn:E1.
    + apply Uint63.eqb_spec in E1. subst n. change (to_Z 1) with 1 in Hj. replace j with 0 by lia. rewrite Z.add_0_r, of_to_Z. exact H.
    + pose proof (to_Z_bounded k) as Hk. pose proof (to_Z_bounded n) as Hn.
      assert (Hh : to_Z (n >> 1) = to_Z n / 2).
      { rewrite lsr_spec. change (to_Z 1) with 1. change (2 ^ 1) with 2. reflexivity. }
      assert (Hh2 : 0 <= to_Z n / 2 <= to_Z n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      destruct (cscan p s g k (n >> 1)) eqn:H1; [|discriminate].
      destruct (Z.lt_ge_cases j (to_Z n / 2)) as [Hl|Hge].
      * apply (IH _ _ H1); lia.
      * assert (Hk' : to_Z (k + (n >> 1)) = to_Z k + to_Z n / 2) by (rewrite add_spec, Hh; apply Z.mod_small; lia).
        assert (Hn' : to_Z (n - (n >> 1)) = to_Z n - to_Z n / 2) by (rewrite sub_spec, Hh; apply Z.mod_small; lia).
        pose proof (IH _ _ H ltac:(lia) (j - to_Z n / 2) ltac:(lia)) as Hg.
        rewrite Hk' in Hg. replace (to_Z k + to_Z n / 2 + (j - to_Z n / 2)) with (to_Z k + j) in Hg by lia. exact Hg.
Qed.
(* [comment removed for export] *)
Definition bscan (p : int -> bool) (s : PrimString.string) (lo n : N) : bool :=
  (Z.leb (Z.of_N (2 * (lo + n))) (to_Z (PrimString.length s)) && cscan p s 64 (of_Z (Z.of_N (2 * lo))) (of_Z (Z.of_N (2 * n))))%bool.
Lemma bscan_chars : forall p s lo n, bscan p s lo n = true -> forall i, (i < n)%N ->
  p (PrimString.get s (of_Z (Z.of_N (2 * (lo + i))))) = true /\ p (PrimString.get s (of_Z (Z.of_N (2 * (lo + i) + 1)))) = true /\
  PrimInt63.ltb (of_Z (Z.of_N (2 * (lo + i) + 1))) (PrimString.length s) = true.
Proof.
  intros p s lo n H i Hi. unfold bscan in H. apply andb_prop in H as [Hlen Hz]. apply Z.leb_le in Hlen.
  pose proof (to_Z_bounded (PrimString.length s)) as Hls.
  assert (Hlo : to_Z (of_Z (Z.of_N (2 * lo))) = Z.of_N (2 * lo)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (Hn : to_Z (of_Z (Z.of_N (2 * n))) = Z.of_N (2 * n)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (Hc : forall j, 0 <= j < Z.of_N (2 * n) -> p (PrimString.get s (of_Z (Z.of_N (2 * lo) + j))) = true).
  { intros j Hj. pose proof (cscan_sound p s 64 _ _ Hz ltac:(rewrite Hlo, Hn; lia) j ltac:(rewrite Hn; exact Hj)) as Hg. rewrite Hlo in Hg. exact Hg. }
  replace (Z.of_N (2 * (lo + i))) with (Z.of_N (2 * lo) + Z.of_N (2 * i)) by lia.
  replace (Z.of_N (2 * (lo + i) + 1)) with (Z.of_N (2 * lo) + (Z.of_N (2 * i) + 1)) by lia.
  split; [exact (Hc (Z.of_N (2 * i)) ltac:(lia))|]. split; [exact (Hc (Z.of_N (2 * i) + 1) ltac:(lia))|].
  apply ltb_spec. rewrite of_Z_spec, Z.mod_small by lia. lia.
Qed.
Definition ch_zero (c : int) : bool := (c =? 48)%uint63.
Definition ch_hex (c : int) : bool := (N.ltb (hex_nybble c) 16).
Definition scanz (s : PrimString.string) (lo n : N) : bool := bscan ch_zero s lo n.
Definition scank (s : PrimString.string) (lo n : N) : bool := bscan ch_hex s lo n.
Lemma scanz_sound : forall s lo n, scanz s lo n = true -> forall i, (i < n)%N -> byte_z s (lo + i)%N = true.
Proof.
  intros s lo n H i Hi. destruct (bscan_chars _ _ _ _ H i Hi) as (H0 & H1 & Hlt). unfold ch_zero in H0, H1.
  apply Uint63.eqb_spec in H0. apply Uint63.eqb_spec in H1.
  unfold byte_z, hex_byte_at. cbv zeta. rewrite Hlt, H0, H1. cbn [orb]. reflexivity.
Qed.
Lemma scank_sound : forall s lo n, scank s lo n = true -> forall i, (i < n)%N -> byte_ok s (lo + i)%N = true.
Proof.
  intros s lo n H i Hi. destruct (bscan_chars _ _ _ _ H i Hi) as (H0 & H1 & Hlt). unfold ch_hex in H0, H1.
  unfold byte_ok, hex_byte_at. cbv zeta. rewrite Hlt. cbn [orb]. rewrite H0, H1. reflexivity.
Qed.
Lemma scanz_at : forall c lo n base x, scanz c lo n = true -> base + Z.of_N lo <= x < base + Z.of_N lo + Z.of_N n ->
  byte_z c (Z.to_N (x - base)) = true.
Proof.
  intros c lo n base x Hs Hx. pose proof (scanz_sound c lo n Hs (Z.to_N (x - base) - lo)%N ltac:(lia)) as H.
  replace (lo + (Z.to_N (x - base) - lo))%N with (Z.to_N (x - base)) in H by lia. exact H.
Qed.
Lemma scank_at : forall c lo n base x, scank c lo n = true -> base + Z.of_N lo <= x < base + Z.of_N lo + Z.of_N n ->
  byte_ok c (Z.to_N (x - base)) = true.
Proof.
  intros c lo n base x Hs Hx. pose proof (scank_sound c lo n Hs (Z.to_N (x - base) - lo)%N ltac:(lia)) as H.
  replace (lo + (Z.to_N (x - base) - lo))%N with (Z.to_N (x - base)) in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma scan_S : forall f s g base n, scan f s (S g) base n =
  if N.eqb n 0 then true else if N.eqb n 1 then f s base else (scan f s g base (N.div2 n) && scan f s g (base + N.div2 n) (n - N.div2 n))%bool.
Proof. reflexivity. Qed.
Lemma scan_complete : forall f s g base n, (n <= 2 ^ N.of_nat g)%N -> (forall i, (i < n)%N -> f s (base + i)%N = true) -> scan f s (S g) base n = true.
Proof.
  intros f s g. induction g as [|g IH]; intros base n Hn H; rewrite scan_S.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [reflexivity|]. destruct (N.eqb_spec n 1) as [E1|Hn1].
    + rewrite <- (N.add_0_r base). apply H. lia.
    + change (2 ^ N.of_nat 0)%N with 1%N in Hn. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [reflexivity|]. destruct (N.eqb_spec n 1) as [E1|Hn1].
    + rewrite <- (N.add_0_r base). apply H. lia.
    + rewrite N.div2_div. assert (Hp : (2 ^ N.of_nat (S g) = 2 * 2 ^ N.of_nat g)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
      assert (Hd : (n = 2 * (n / 2) + n mod 2)%N) by (apply N.div_mod'; lia). pose proof (N.mod_upper_bound n 2 ltac:(lia)) as Hm.
      assert (Hh : (n / 2 <= 2 ^ N.of_nat g)%N) by lia.
      rewrite (IH base (n / 2)%N Hh) by (intros i Hi; apply H; lia). cbn [andb].
      apply IH; [lia|]. intros i Hi. rewrite <- N.add_assoc. apply H. lia.
Qed.
Lemma scan_of_scanz : forall c lo n, N.leb n 9223372036854775808 = true -> scanz c lo n = true -> scan byte_z c 64 lo n = true.
Proof. intros c lo n Hn H. apply N.leb_le in Hn. apply (scan_complete byte_z c 63 lo n); [exact Hn | exact (scanz_sound c lo n H)]. Qed.
Lemma scan_of_scank : forall c lo n, N.leb n 9223372036854775808 = true -> scank c lo n = true -> scan byte_ok c 64 lo n = true.
Proof. intros c lo n Hn H. apply N.leb_le in Hn. apply (scan_complete byte_ok c 63 lo n); [exact Hn | exact (scank_sound c lo n H)]. Qed.

(* [comment removed for export] *)
Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Definition c0 : PrimString.string := AsanUbsan_seg_bytes_000.
Definition c2 : PrimString.string := AsanUbsan_seg_bytes_002.
Definition c3 : PrimString.string := AsanUbsan_seg_bytes_003.
(* [comment removed for export] *)
