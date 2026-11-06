(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63 PString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ImgZero.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition is_hexc (c : int) : bool :=
  ((Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63) || (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63))%bool.

Lemma is_hexc_nybble : forall c, is_hexc c = true -> (hex_nybble c < 16)%N.
Proof.
  intros c H. unfold is_hexc in H. unfold hex_nybble.
  apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Uint63.leb_spec in H1, H2;
    change (φ%uint63 48%uint63) with 48%Z in *; change (φ%uint63 57%uint63) with 57%Z in *;
    change (φ%uint63 97%uint63) with 97%Z in *; change (φ%uint63 102%uint63) with 102%Z in *.
  - replace (Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63)%bool with true
      by (symmetry; apply andb_true_intro; split; apply Uint63.leb_spec; change (φ%uint63 48%uint63) with 48%Z;
          change (φ%uint63 57%uint63) with 57%Z; lia).
    lia.
  - destruct (Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63)%bool eqn:E.
    + apply andb_prop in E as [E1 E2]. apply Uint63.leb_spec in E1, E2. change (φ%uint63 57%uint63) with 57%Z in E2. lia.
    + replace (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63)%bool with true
        by (symmetry; apply andb_true_intro; split; apply Uint63.leb_spec; change (φ%uint63 97%uint63) with 97%Z;
            change (φ%uint63 102%uint63) with 102%Z; lia).
      lia.
Qed.

(* [comment removed for export] *)
Fixpoint scan_chars (s : string) (a : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => (is_hexc (PrimString.get s (Uint63.add a (Uint63.of_Z (Z.of_nat k')))) && scan_chars s a k')%bool
  end.

Lemma scan_chars_sound : forall s a k, scan_chars s a k = true ->
  forall i, (i < k)%nat -> is_hexc (PrimString.get s (Uint63.add a (Uint63.of_Z (Z.of_nat i)))) = true.
Proof.
  intros s a k. induction k as [|k IH]; intros H i Hi; [lia|].
  cbn [scan_chars] in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec i k) as [->|Hne]; [exact H1|]. apply IH; [exact H2|lia].
Qed.

(* [comment removed for export] *)
Fixpoint scan_from (s : string) (i : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => (is_hexc (PrimString.get s i) && scan_from s (Uint63.add i 1%uint63) k')%bool
  end.

Lemma int_add_0 : forall a : int, Uint63.add a (Uint63.of_Z 0) = a.
Proof.
  intros a. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, Uint63.of_Z_spec.
  pose proof (Uint63.to_Z_bounded a) as B. rewrite Z.mod_0_l by (unfold wB; cbn; lia). rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma int_add_S : forall (a : int) (i : nat), Uint63.add a (Uint63.of_Z (Z.of_nat (S i))) = Uint63.add (Uint63.add a 1%uint63) (Uint63.of_Z (Z.of_nat i)).
Proof.
  intros a i. apply Uint63.to_Z_inj. rewrite !Uint63.add_spec, !Uint63.of_Z_spec. change (φ%uint63 1%uint63) with 1%Z.
  rewrite Nat2Z.inj_succ. unfold Z.succ.
  rewrite Z.add_mod_idemp_r by (unfold wB; cbn; lia). rewrite Z.add_mod_idemp_l by (unfold wB; cbn; lia).
  rewrite Z.add_mod_idemp_r by (unfold wB; cbn; lia). f_equal. lia.
Qed.

Lemma scan_from_sound : forall s k a, scan_from s a k = true ->
  forall i, (i < k)%nat -> is_hexc (PrimString.get s (Uint63.add a (Uint63.of_Z (Z.of_nat i)))) = true.
Proof.
  intros s k. induction k as [|k IH]; intros a H i Hi; [lia|].
  cbn [scan_from] in H. apply andb_prop in H as [H1 H2].
  destruct i as [|i]; [change (Z.of_nat 0) with 0%Z; rewrite int_add_0; exact H1|].
  rewrite int_add_S. apply (IH _ H2). lia.
Qed.

Definition BLK : Z := 4096.
Definition ZBLK : string := PrimString.make 4096%uint63 48%uint63.

(* [comment removed for export] *)
Definition block_ok (s : string) (a : int) : bool :=
  match PrimString.compare (PrimString.sub s a 4096%uint63) ZBLK with
  | Eq => true
  | _ => scan_from s a 4096   (* [comment removed for export] *)
  end.

Lemma block_ok_sound : forall s a, block_ok s a = true -> (φ%uint63 a + 4096 < wB)%Z ->
  forall i, (0 <= i < 4096)%Z -> is_hexc (PrimString.get s (Uint63.add a (Uint63.of_Z i))) = true.
Proof.
  intros s a H Ha i Hi. unfold block_ok in H.
  destruct (PrimString.compare (PrimString.sub s a 4096%uint63) ZBLK) eqn:Hc.
  - apply compare_eq in Hc.
    assert (Hoi : φ%uint63 (Uint63.of_Z i) = i) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; unfold wB in *; cbn in *; lia).
    rewrite <- (sub_get_spec s a 4096%uint63 (Uint63.of_Z i)); [| rewrite Hoi; lia | rewrite Hoi; change (φ%uint63 4096%uint63) with 4096%Z; lia].
    rewrite Hc. unfold ZBLK. rewrite make_get_spec;
      [ reflexivity
      | rewrite Hoi; change (φ%uint63 max_length) with 16777211%Z; lia
      | rewrite Hoi; change (φ%uint63 4096%uint63) with 4096%Z; lia ].
  - replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (scan_from_sound s 4096 a H). lia.
  - replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (scan_from_sound s 4096 a H). lia.
Qed.

(* [comment removed for export] *)
Fixpoint blocks_ok (s : string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then block_ok s (Uint63.of_Z (Z.of_N (base * 4096)))
      else let h := N.div2 n in (blocks_ok s f base h && blocks_ok s f (base + h) (n - h))%bool
  end.

Lemma blocks_ok_sound : forall s fuel base n, blocks_ok s fuel base n = true ->
  forall b, (base <= b < base + n)%N -> block_ok s (Uint63.of_Z (Z.of_N (b * 4096))) = true.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H b Hb; cbn [blocks_ok] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace b with base by lia. exact H.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *.
      destruct (N.lt_ge_cases b (base + n / 2)) as [Hl|Hge].
      * exact (IH _ _ H1 b ltac:(lia)).
      * exact (IH _ _ H2 b ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_some3 : forall s (nblk : N) (off : N),
  blocks_ok s 64 0 nblk = true ->
  (Z.of_N nblk * 4096 <= 2 ^ 40)%Z ->
  (2 * off < nblk * 4096)%N ->
  hex_byte_at s off <> None.
Proof.
  intros s nblk off Hb Hsz Hoff.
  set (b := ((2 * off) / 4096)%N). set (i := Z.of_N ((2 * off) mod 4096)).
  assert (Hbl : block_ok s (Uint63.of_Z (Z.of_N (b * 4096))) = true).
  { apply (blocks_ok_sound s 64 0 nblk Hb b). split; [lia|]. unfold b.
    apply N.Div0.div_lt_upper_bound; lia. }
  assert (Hi : (0 <= i < 4096)%Z) by (unfold i; pose proof (N.mod_lt (2 * off) 4096 ltac:(lia)); lia).
  assert (Hi2 : i = (2 * (Z.of_N off mod 2048))%Z).
  { unfold i. rewrite N2Z.inj_mod by lia. rewrite N2Z.inj_mul. change (Z.of_N 2) with 2%Z.
    change (Z.of_N 4096) with (2 * 2048)%Z. apply Z.mul_mod_distr_l; lia. }
  assert (Hi1 : (0 <= i + 1 < 4096)%Z).
  { pose proof (Z.mod_pos_bound (Z.of_N off) 2048 ltac:(lia)). lia. }
  assert (HbZ : (Z.of_N (b * 4096) = Z.of_N (2 * off) - i)%Z).
  { unfold i, b. rewrite N2Z.inj_mod, N2Z.inj_mul, N2Z.inj_div by lia.
    change (Z.of_N 4096) with 4096%Z. rewrite Z.mod_eq by lia. lia. }
  assert (Hbnd : (Z.of_N (2 * off) + 1 < 2 ^ 41)%Z) by lia.
  assert (Ha : φ%uint63 (Uint63.of_Z (Z.of_N (b * 4096))) = Z.of_N (b * 4096)).
  { rewrite Uint63.of_Z_spec. apply Z.mod_small. unfold wB. cbn. (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi2; @Hi1; @HbZ; @Hbnd]); lia). }
  assert (Hsum : forall j, (0 <= j < 4096)%Z ->
            Uint63.add (Uint63.of_Z (Z.of_N (b * 4096))) (Uint63.of_Z j) = Uint63.of_Z (Z.of_N (b * 4096) + j)).
  { intros j Hj. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, Ha, !Uint63.of_Z_spec.
    rewrite (Z.mod_small j) by (unfold wB; cbn; (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi1; @HbZ; @Hbnd; @Ha; @Hj]); lia)). reflexivity. }
  assert (Hwb : (φ%uint63 (Uint63.of_Z (Z.of_N (b * 4096))) + 4096 < wB)%Z) by (rewrite Ha; unfold wB; cbn; (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi2; @Hi1; @HbZ; @Hbnd; @Ha]); lia)).
  pose proof (block_ok_sound s _ Hbl Hwb i Hi) as H0.
  pose proof (block_ok_sound s _ Hbl Hwb (i + 1) Hi1) as H1.
  rewrite Hsum in H0 by (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi1; @HbZ; @Hbnd; @Ha; @Hwb; @H0; @H1]); lia). rewrite Hsum in H1 by (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi1; @HbZ; @Hbnd; @Ha; @Hwb; @H0; @H1]); lia). rewrite HbZ in H0, H1.
  replace (Z.of_N (2 * off) - i + i)%Z with (Z.of_N (2 * off)) in H0 by (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi1; @HbZ; @Hbnd; @Ha; @Hwb; @H0; @H1]); lia).
  replace (Z.of_N (2 * off) - i + (i + 1))%Z with (Z.of_N (2 * off + 1)) in H1 by (ltac2:(LK.k [@Hb; @Hoff; @Hbl; @Hi; @Hi1; @HbZ; @Hbnd; @Ha; @Hwb; @H0; @H1]); lia).
  unfold hex_byte_at.
  (* [comment removed for export] *)
  assert (Hin : (φ%uint63 (Uint63.of_Z (Z.of_N (2 * off + 1))) < φ%uint63 (PrimString.length s))%Z).
  { destruct (Z.lt_ge_cases (φ%uint63 (Uint63.of_Z (Z.of_N (2 * off + 1)))) (φ%uint63 (PrimString.length s))) as [L|L];
      [exact L|].
    rewrite (get_spec_not_in_bounds s _ L) in H1. discriminate H1. }
  replace (Uint63.ltb (Uint63.of_Z (Z.of_N (2 * off + 1))) (PrimString.length s)) with true
    by (symmetry; apply Uint63.ltb_spec; exact Hin).
  cbn [orb].
  pose proof (is_hexc_nybble _ H0) as N0. pose proof (is_hexc_nybble _ H1) as N1.
  replace (N.ltb (hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off))))) 16) with true
    by (symmetry; apply N.ltb_lt; exact N0).
  replace (N.ltb (hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off + 1))))) 16) with true
    by (symmetry; apply N.ltb_lt; exact N1).
  discriminate.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some3 : forall s (nblk : N) (off : N),
  blocks_ok s 64 0 nblk = true ->
  (Z.of_N nblk * 4096 <= 2 ^ 40)%Z ->
  (nblk * 2048 <= Z.to_N (φ%uint63 (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N nblk * 2048)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s nblk off Hb Hsz Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (φ%uint63 (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
  apply (hex_byte_at_some3 s nblk off Hb Hsz). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zero_run_ok (s : string) (off n : N) : bool :=
  match PrimString.compare (PrimString.sub s (Uint63.of_Z (Z.of_N (2 * off))) (Uint63.of_Z (Z.of_N (2 * n))))
                           (PrimString.make (Uint63.of_Z (Z.of_N (2 * n))) 48%uint63) with
  | Eq => true
  | _ => false
  end.

Lemma sub_len_le : forall s a k, (φ%uint63 (PrimString.length (PrimString.sub s a k)) <= φ%uint63 (PrimString.length s) - φ%uint63 a)%Z
                                 \/ (φ%uint63 (PrimString.length s) < φ%uint63 a)%Z.
Proof.
  intros s a k. destruct (Z.lt_ge_cases (φ%uint63 (PrimString.length s)) (φ%uint63 a)) as [L|L]; [right; exact L|left].
  rewrite !length_spec_Z, sub_spec. rewrite List.length_firstn, List.length_skipn.
  pose proof (length_spec_Z s) as E. rewrite E in L. lia.
Qed.

Lemma zero_run_sound : forall s off n, zero_run_ok s off n = true ->
  (Z.of_N (2 * (off + n)) <= 2 ^ 40)%Z -> (Z.of_N (2 * n) <= 16777211)%Z ->
  forall j, (j < n)%N -> hex_byte_at s (off + j) = Some (Z_to_bv 8 0).
Proof.
  intros s off n H Hb Hm j Hj. unfold zero_run_ok in H.
  destruct (PrimString.compare _ _) eqn:Hc; try discriminate. apply compare_eq in Hc.
  set (a := Uint63.of_Z (Z.of_N (2 * off))) in *. set (k := Uint63.of_Z (Z.of_N (2 * n))) in *.
  assert (Ha : φ%uint63 a = Z.of_N (2 * off)) by (unfold a; rewrite Uint63.of_Z_spec; apply Z.mod_small; unfold wB; cbn; lia).
  assert (Hk : φ%uint63 k = Z.of_N (2 * n)) by (unfold k; rewrite Uint63.of_Z_spec; apply Z.mod_small; unfold wB; cbn; lia).
  (* [comment removed for export] *)
  assert (HL : (Z.of_N (2 * off) + Z.of_N (2 * n) <= φ%uint63 (PrimString.length s))%Z).
  { assert (Lm : φ%uint63 (PrimString.length (PrimString.make k 48%uint63)) = Z.of_N (2 * n)).
    { rewrite length_spec_Z, make_spec, List.repeat_length. change (φ%uint63 max_length) with 16777211%Z. rewrite Hk. lia. }
    rewrite <- Hc in Lm. destruct (sub_len_le s a k) as [L|L]; [rewrite Lm, Ha in L; lia|].
    exfalso. rewrite Ha in L.
    rewrite length_spec_Z, sub_spec, List.length_firstn, List.length_skipn in Lm. pose proof (length_spec_Z s) as E. rewrite Ha in *. lia. }
  assert (G : forall i, (0 <= i < Z.of_N (2 * n))%Z -> PrimString.get s (Uint63.of_Z (Z.of_N (2 * off) + i)) = 48%uint63).
  { intros i Hi.
    assert (Hoi : φ%uint63 (Uint63.of_Z i) = i) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; unfold wB; cbn; lia).
    replace (Uint63.of_Z (Z.of_N (2 * off) + i)) with (Uint63.add a (Uint63.of_Z i)).
    2:{ apply Uint63.to_Z_inj. rewrite Uint63.add_spec, Ha, Hoi, Uint63.of_Z_spec. reflexivity. }
    rewrite <- (sub_get_spec s a k (Uint63.of_Z i)); [| rewrite Ha, Hoi; unfold wB; cbn; (ltac2:(LK.k [@Hb; @Hm; @Hj; @Ha; @Hk; @HL; @Hi; @Hoi]); lia) | rewrite Hoi, Hk; (ltac2:(LK.k [@Hb; @Hm; @Hj; @Ha; @Hk; @HL; @Hi; @Hoi]); lia)].
    rewrite Hc. rewrite make_get_spec; [reflexivity | rewrite Hoi; change (φ%uint63 max_length) with 16777211%Z; (ltac2:(LK.k [@Hb; @Hm; @Hj; @Ha; @Hk; @HL; @Hi; @Hoi]); lia) | rewrite Hoi, Hk; (ltac2:(LK.k [@Hb; @Hm; @Hj; @Ha; @Hk; @HL; @Hi; @Hoi]); lia)]. }
  unfold hex_byte_at.
  pose proof (G (Z.of_N (2 * j)) ltac:(lia)) as G0. pose proof (G (Z.of_N (2 * j) + 1) ltac:(lia)) as G1.
  replace (Z.of_N (2 * off) + Z.of_N (2 * j))%Z with (Z.of_N (2 * (off + j))) in G0 by lia.
  replace (Z.of_N (2 * off) + (Z.of_N (2 * j) + 1))%Z with (Z.of_N (2 * (off + j) + 1)) in G1 by lia.
  rewrite G0, G1.
  replace (Uint63.ltb (Uint63.of_Z (Z.of_N (2 * (off + j) + 1))) (PrimString.length s)) with true.
  - reflexivity.
  - symmetry. apply Uint63.ltb_spec. rewrite Uint63.of_Z_spec, Z.mod_small by (unfold wB; cbn; lia). lia.
Qed.

(* [comment removed for export] *)
Definition img_zero3_chk (segs : list Segment) (lo n : Z) : bool :=
  match find_segment_excl segs lo n with
  | Some sg =>
      match seg_bytes sg with
      | [str] => (seg_readable sg && zero_run_ok str (Z.to_N (lo - Z.of_N (seg_base sg))) (Z.to_N n))%bool
      | _ => false
      end
  | None => false
  end.

Theorem img_zero3_chk_sound : forall segs lo n,
  img_zero3_chk segs lo n = true -> 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 39 -> 2 * n <= 16777211 ->
  forall x : word, lo <= bv_unsigned x < lo + n -> seg_rom segs x = Some (Z_to_bv 8 0).
Proof.
  intros segs lo n H Hlo Hn Hhi Hm x Hx. unfold img_zero3_chk in H.
  destruct (find_segment_excl segs lo n) as [sg|] eqn:Hf; [|discriminate].
  destruct (seg_bytes sg) as [|str [|? ?]] eqn:Hby; try discriminate.
  apply andb_prop in H as [Hr Hz].
  destruct (find_segment_excl_sound segs lo n sg (bv_unsigned x) Hf ltac:(lia) ltac:(lia)) as (F & B1 & B2).
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  rewrite Hby. cbn [segment_byte_at].
  set (off := Z.to_N (lo - Z.of_N (seg_base sg))) in *. set (j := Z.to_N (bv_unsigned x - lo)).
  replace (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg))) with (off + j)%N by (unfold off, j; lia).
  pose proof (zero_run_sound str off (Z.to_N n) Hz ltac:(unfold off; lia) ltac:(lia) j ltac:(unfold j; lia)) as Z0.
  (* [comment removed for export] *)
  assert (HL : (off + j < Z.to_N (φ%uint63 (PrimString.length str) / 2))%N).
  { unfold zero_run_ok in Hz. destruct (PrimString.compare _ _) eqn:Hc; try discriminate. apply compare_eq in Hc.
    assert (Lm : φ%uint63 (PrimString.length (PrimString.make (Uint63.of_Z (Z.of_N (2 * Z.to_N n))) 48%uint63)) = Z.of_N (2 * Z.to_N n)).
    { rewrite length_spec_Z, make_spec, List.repeat_length. change (φ%uint63 max_length) with 16777211%Z.
      rewrite Uint63.of_Z_spec, Z.mod_small by (unfold wB; cbn; lia). lia. }
    rewrite <- Hc in Lm.
    rewrite length_spec_Z, sub_spec, List.length_firstn, List.length_skipn in Lm. pose proof (length_spec_Z str) as E.
    rewrite Uint63.of_Z_spec, Z.mod_small in Lm by (unfold wB, off in *; cbn; (ltac2:(LK.k [@Hr; @Hhi; @Hm; @Hx; @Lm; @E]); lia)).
    rewrite Uint63.of_Z_spec, Z.mod_small in Lm by (unfold wB, off in *; cbn; (ltac2:(LK.k [@Hr; @Hn; @Hhi; @Hx; @Lm]); lia)).
    unfold j in *. (ltac2:(LK.k [@Hr; @Hx; @Lm; @E]); lia). }
  replace (off + j <? Z.to_N (φ%uint63 (PrimString.length str) / 2))%N with true by (symmetry; apply N.ltb_lt; exact HL).
  rewrite Z0. reflexivity.
Qed.
