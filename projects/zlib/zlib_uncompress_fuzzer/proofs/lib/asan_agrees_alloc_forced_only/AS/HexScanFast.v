(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition hexc (c : PrimInt63.int) : bool :=
  ((Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63) || (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63))%bool.

Definition byte_okI (s : PrimString.string) (b : PrimInt63.int) : bool :=
  let ci := PrimInt63.lsl b 1%uint63 in
  let ci1 := PrimInt63.add ci 1%uint63 in
  (Uint63.ltb ci1 (PrimString.length s) && hexc (PrimString.get s ci) && hexc (PrimString.get s ci1))%bool.

Fixpoint scanI (s : PrimString.string) (fuel : nat) (base n : PrimInt63.int) : bool :=
  match fuel with
  | O => Uint63.eqb n 0%uint63
  | S f =>
      if Uint63.eqb n 0%uint63 then true
      else if Uint63.eqb n 1%uint63 then byte_okI s base
      else let h := PrimInt63.lsr n 1%uint63 in
           (scanI s f base h && scanI s f (PrimInt63.add base h) (PrimInt63.sub n h))%bool
  end.

Lemma to_Z_48 : Uint63.to_Z 48%uint63 = 48. Proof. reflexivity. Qed.
Lemma to_Z_57 : Uint63.to_Z 57%uint63 = 57. Proof. reflexivity. Qed.
Lemma to_Z_97 : Uint63.to_Z 97%uint63 = 97. Proof. reflexivity. Qed.
Lemma to_Z_102 : Uint63.to_Z 102%uint63 = 102. Proof. reflexivity. Qed.

Lemma hexc_nybble : forall c, hexc c = true -> (hex_nybble c <? 16)%N = true.
Proof.
  intros c H. unfold hexc in H. unfold hex_nybble.
  destruct (Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63)%bool eqn:E1.
  - apply andb_prop in E1 as [A B]. apply Uint63.leb_spec in A, B. pose proof to_Z_48 as T1. pose proof to_Z_57 as T2.
    apply N.ltb_lt. lia.
  - cbn [orb] in H. rewrite H. apply andb_prop in H as [A B]. apply Uint63.leb_spec in A, B. pose proof to_Z_97 as T1. pose proof to_Z_102 as T2.
    apply N.ltb_lt. lia.
Qed.

Lemma byte_okI_sound : forall s b, byte_okI s b = true -> hex_byte_at s (Z.to_N (Uint63.to_Z b)) <> None.
Proof.
  intros s b H. unfold byte_okI in H. cbv zeta in H.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  pose proof (Uint63.to_Z_bounded b) as Bb.
  assert (Eci : Uint63.of_Z (Z.of_N (2 * Z.to_N (Uint63.to_Z b))) = PrimInt63.lsl b 1%uint63).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.lsl_spec, Uint63.to_Z_1, Z.pow_1_r. f_equal. lia. }
  assert (Eci1 : Uint63.of_Z (Z.of_N (2 * Z.to_N (Uint63.to_Z b) + 1)) = PrimInt63.add (PrimInt63.lsl b 1%uint63) 1%uint63).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, Uint63.lsl_spec, Uint63.to_Z_1, Z.pow_1_r, Zplus_mod_idemp_l. f_equal. lia. }
  unfold hex_byte_at. cbv zeta. rewrite Eci, Eci1, H0. cbn [orb].
  rewrite (hexc_nybble _ H1), (hexc_nybble _ H2). cbn [andb]. discriminate.
Qed.

Lemma scanI_sound : forall s fuel base n,
  scanI s fuel base n = true -> Uint63.to_Z base + Uint63.to_Z n < Uint63.wB ->
  forall i, 0 <= i < Uint63.to_Z n -> byte_okI s (Uint63.of_Z (Uint63.to_Z base + i)) = true.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H Hb i Hi; cbn [scanI] in H.
  - apply Uint63.eqb_spec in H. subst n. rewrite Uint63.to_Z_0 in Hi. lia.
  - destruct (Uint63.eqb n 0%uint63) eqn:E0.
    { apply Uint63.eqb_spec in E0. subst n. rewrite Uint63.to_Z_0 in Hi. lia. }
    destruct (Uint63.eqb n 1%uint63) eqn:E1.
    { apply Uint63.eqb_spec in E1. subst n. rewrite Uint63.to_Z_1 in Hi. replace i with 0 by lia.
      rewrite Z.add_0_r, Uint63.of_to_Z. exact H. }
    cbv zeta in H. apply andb_prop in H as [H1 H2].
    pose proof (Uint63.to_Z_bounded base) as Bb. pose proof (Uint63.to_Z_bounded n) as Bn.
    assert (Eh : Uint63.to_Z (PrimInt63.lsr n 1%uint63) = Uint63.to_Z n / 2).
    { rewrite Uint63.lsr_spec, Uint63.to_Z_1, Z.pow_1_r. reflexivity. }
    set (q := Uint63.to_Z n / 2) in *.
    assert (Hq : 0 <= q <= Uint63.to_Z n) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Ea : Uint63.to_Z (PrimInt63.add base (PrimInt63.lsr n 1%uint63)) = Uint63.to_Z base + q).
    { rewrite Uint63.add_spec, Eh. apply Z.mod_small. lia. }
    assert (Es : Uint63.to_Z (PrimInt63.sub n (PrimInt63.lsr n 1%uint63)) = Uint63.to_Z n - q).
    { rewrite Uint63.sub_spec, Eh. apply Z.mod_small. lia. }
    destruct (Z.lt_ge_cases i q) as [Hl|Hge].
    + apply (IH _ _ H1); rewrite Eh; lia.
    + specialize (IH _ _ H2). rewrite Ea, Es in IH. specialize (IH ltac:(lia) (i - q) ltac:(lia)).
      replace (Uint63.to_Z base + q + (i - q)) with (Uint63.to_Z base + i) in IH by lia. exact IH.
Qed.

Lemma segment_byte_at_some1I : forall s (n : N) (off : N),
  scanI s 64 0%uint63 (Uint63.of_Z (Z.of_N n)) = true ->
  Z.of_N n < Uint63.wB ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  Z.of_N off < Z.of_N n ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hlen Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
  assert (En : Uint63.to_Z (Uint63.of_Z (Z.of_N n)) = Z.of_N n) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; lia).
  pose proof (scanI_sound s 64 0%uint63 _ Hs) as S. rewrite Uint63.to_Z_0, En in S.
  specialize (S ltac:(lia) (Z.of_N off) ltac:(lia)). rewrite Z.add_0_l in S.
  apply byte_okI_sound in S.
  rewrite Uint63.of_Z_spec, Z.mod_small, N2Z.id in S by lia. exact S.
Qed.

Section GenericN.
  Variable leaf : N -> bool.
  Fixpoint gscanN (fuel : nat) (base n : N) : bool :=
    match fuel with
    | O => N.eqb n 0
    | S f =>
        if N.eqb n 0 then true
        else if N.eqb n 1 then leaf base
        else let h := N.div2 n in (gscanN f base h && gscanN f (base + h) (n - h))%bool
    end.

  Lemma gscanN_complete : forall f base n,
    (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> leaf (base + i)%N = true) -> gscanN (S f) base n = true.
  Proof.
    induction f as [|f IH]; intros base n Hn Hl; cbn [gscanN].
    - destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1]; [|exfalso; cbn in Hn; lia].
      specialize (Hl 0%N ltac:(lia)). rewrite N.add_0_r in Hl. exact Hl.
    - destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1].
      { specialize (Hl 0%N ltac:(lia)). rewrite N.add_0_r in Hl. exact Hl. }
      cbv zeta. rewrite N.div2_div.
      rewrite Nat2N.inj_succ, N.pow_succ_r' in Hn. set (P := (2 ^ N.of_nat f)%N) in *.
      pose proof (N.div_mod n 2 ltac:(lia)) as DM. pose proof (N.mod_upper_bound n 2 ltac:(lia)) as MB.
      set (h := (n / 2)%N) in *. set (r := (n mod 2)%N) in *.
      apply andb_true_intro; split.
      + apply IH; [lia|]. intros i Hi. apply Hl. lia.
      + apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply Hl. lia.
  Qed.
End GenericN.

Section GenericI.
  Variable leafI : PrimInt63.int -> bool.
  Fixpoint scanP (fuel : nat) (base n : PrimInt63.int) : bool :=
    match fuel with
    | O => Uint63.eqb n 0%uint63
    | S f =>
        if Uint63.eqb n 0%uint63 then true
        else if Uint63.eqb n 1%uint63 then leafI base
        else let h := PrimInt63.lsr n 1%uint63 in
             (scanP f base h && scanP f (PrimInt63.add base h) (PrimInt63.sub n h))%bool
    end.

  Lemma scanP_sound : forall fuel base n,
    scanP fuel base n = true -> Uint63.to_Z base + Uint63.to_Z n < Uint63.wB ->
    forall i, 0 <= i < Uint63.to_Z n -> leafI (Uint63.of_Z (Uint63.to_Z base + i)) = true.
  Proof.
    induction fuel as [|f IH]; intros base n H Hb i Hi; cbn [scanP] in H.
    - apply Uint63.eqb_spec in H. subst n. rewrite Uint63.to_Z_0 in Hi. lia.
    - destruct (Uint63.eqb n 0%uint63) eqn:E0.
      { apply Uint63.eqb_spec in E0. subst n. rewrite Uint63.to_Z_0 in Hi. lia. }
      destruct (Uint63.eqb n 1%uint63) eqn:E1.
      { apply Uint63.eqb_spec in E1. subst n. rewrite Uint63.to_Z_1 in Hi. replace i with 0 by lia.
        rewrite Z.add_0_r, Uint63.of_to_Z. exact H. }
      cbv zeta in H. apply andb_prop in H as [H1 H2].
      pose proof (Uint63.to_Z_bounded base) as Bb. pose proof (Uint63.to_Z_bounded n) as Bn.
      assert (Eh : Uint63.to_Z (PrimInt63.lsr n 1%uint63) = Uint63.to_Z n / 2).
      { rewrite Uint63.lsr_spec, Uint63.to_Z_1, Z.pow_1_r. reflexivity. }
      set (q := Uint63.to_Z n / 2) in *.
      assert (Hq : 0 <= q <= Uint63.to_Z n) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      assert (Ea : Uint63.to_Z (PrimInt63.add base (PrimInt63.lsr n 1%uint63)) = Uint63.to_Z base + q).
      { rewrite Uint63.add_spec, Eh. apply Z.mod_small. lia. }
      assert (Es : Uint63.to_Z (PrimInt63.sub n (PrimInt63.lsr n 1%uint63)) = Uint63.to_Z n - q).
      { rewrite Uint63.sub_spec, Eh. apply Z.mod_small. lia. }
      destruct (Z.lt_ge_cases i q) as [Hl|Hge].
      + apply (IH _ _ H1); rewrite Eh; lia.
      + specialize (IH _ _ H2). rewrite Ea, Es in IH. specialize (IH ltac:(lia) (i - q) ltac:(lia)).
        replace (Uint63.to_Z base + q + (i - q)) with (Uint63.to_Z base + i) in IH by lia. exact IH.
  Qed.
End GenericI.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

Lemma of_N_id : forall off : N, Z.of_N off < Uint63.wB -> Z.to_N (Uint63.to_Z (Uint63.of_Z (Z.of_N off))) = off.
Proof. intros off H. rewrite Uint63.of_Z_spec, Z.mod_small, N2Z.id by lia. reflexivity. Qed.

Lemma scanN_of_I : forall s (base n : N),
  scanP (byte_okI s) 64 (Uint63.of_Z (Z.of_N base)) (Uint63.of_Z (Z.of_N n)) = true ->
  Z.of_N base + Z.of_N n < Uint63.wB ->
  gscanN (byte_ok s) 64 base n = true.
Proof.
  intros s base n H Hb.
  assert (Eb : Uint63.to_Z (Uint63.of_Z (Z.of_N base)) = Z.of_N base) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; lia).
  assert (En : Uint63.to_Z (Uint63.of_Z (Z.of_N n)) = Z.of_N n) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; lia).
  apply (gscanN_complete (byte_ok s) 63).
  - change (2 ^ N.of_nat 63)%N with 9223372036854775808%N. change Uint63.wB with 9223372036854775808 in Hb. lia.
  - intros i Hi. pose proof (scanP_sound (byte_okI s) 64 _ _ H) as S. rewrite Eb, En in S.
    specialize (S Hb (Z.of_N i) ltac:(lia)). apply byte_okI_sound in S.
    replace (Z.of_N base + Z.of_N i) with (Z.of_N (base + i)) in S by lia.
    rewrite of_N_id in S by lia. unfold byte_ok. destruct (hex_byte_at s (base + i)); [reflexivity | contradiction].
Qed.

Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Definition byte_zeroI (s : PrimString.string) (b : PrimInt63.int) : bool :=
  let ci := PrimInt63.lsl b 1%uint63 in
  let ci1 := PrimInt63.add ci 1%uint63 in
  (Uint63.ltb ci1 (PrimString.length s) && Uint63.eqb (PrimString.get s ci) 48%uint63 && Uint63.eqb (PrimString.get s ci1) 48%uint63)%bool.

Lemma byte_zeroI_sound : forall s b, byte_zeroI s b = true -> hex_byte_at s (Z.to_N (Uint63.to_Z b)) = Some (Z_to_bv 8 0).
Proof.
  intros s b H. unfold byte_zeroI in H. cbv zeta in H.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Uint63.eqb_spec in H1, H2.
  pose proof (Uint63.to_Z_bounded b) as Bb.
  assert (Eci : Uint63.of_Z (Z.of_N (2 * Z.to_N (Uint63.to_Z b))) = PrimInt63.lsl b 1%uint63).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.lsl_spec, Uint63.to_Z_1, Z.pow_1_r. f_equal. lia. }
  assert (Eci1 : Uint63.of_Z (Z.of_N (2 * Z.to_N (Uint63.to_Z b) + 1)) = PrimInt63.add (PrimInt63.lsl b 1%uint63) 1%uint63).
  { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, Uint63.lsl_spec, Uint63.to_Z_1, Z.pow_1_r, Zplus_mod_idemp_l. f_equal. lia. }
  unfold hex_byte_at. cbv zeta. rewrite Eci, Eci1, H0, H1, H2. reflexivity.
Qed.

Lemma zscanN_of_I : forall s (base n : N),
  scanP (byte_zeroI s) 64 (Uint63.of_Z (Z.of_N base)) (Uint63.of_Z (Z.of_N n)) = true ->
  Z.of_N base + Z.of_N n < Uint63.wB ->
  gscanN (byte_zero s) 64 base n = true.
Proof.
  intros s base n H Hb.
  assert (Eb : Uint63.to_Z (Uint63.of_Z (Z.of_N base)) = Z.of_N base) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; lia).
  assert (En : Uint63.to_Z (Uint63.of_Z (Z.of_N n)) = Z.of_N n) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; lia).
  apply (gscanN_complete (byte_zero s) 63).
  - change (2 ^ N.of_nat 63)%N with 9223372036854775808%N. change Uint63.wB with 9223372036854775808 in Hb. lia.
  - intros i Hi. pose proof (scanP_sound (byte_zeroI s) 64 _ _ H) as S. rewrite Eb, En in S.
    specialize (S Hb (Z.of_N i) ltac:(lia)). apply byte_zeroI_sound in S.
    replace (Z.of_N base + Z.of_N i) with (Z.of_N (base + i)) in S by lia.
    rewrite of_N_id in S by lia. unfold byte_zero. rewrite S. reflexivity.
Qed.
