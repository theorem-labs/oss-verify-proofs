(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hexbyte_ok (s : PrimString.string) (i : N) : bool :=
  match hex_byte_at s i with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint hexbytes_ok (s : PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => if hexbyte_ok s off then hexbytes_ok s (off + 1)%N n' else false
  end.

(* [comment removed for export] *)
Fixpoint chunks_ok (chunks : list PrimString.string) (off : N) (n : nat) : bool :=
  match chunks with
  | [] => false
  | c :: rest =>
      let cb := Z.to_N (Uint63.to_Z (PrimString.length c) / 2) in
      if (off + N.of_nat n <=? cb)%N then hexbytes_ok c off n
      else if (cb <=? off)%N then chunks_ok rest (off - cb)%N n
      else false
  end.

(* [comment removed for export] *)
Fixpoint find_segment_range (segs : list Segment) (lo hi : Z) : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
      let base := Z.of_N (seg_base seg) in
      let top  := (base + Z.of_N (seg_size seg))%Z in
      if (Z.leb base lo && Z.leb hi top)%bool then Some seg
      else if (Z.leb hi base || Z.leb top lo)%bool then find_segment_range rest lo hi
      else None
  end.

Definition wseg_fast (segs : list Segment) (a : word) (n : nat) : bool :=
  let lo := bv_unsigned a in
  let hi := (lo + Z.of_nat n)%Z in
  (Z.leb hi (2 ^ 64)
   && match find_segment_range segs lo hi with
      | Some seg =>
          seg_writable seg
          && chunks_ok (seg_bytes seg) (Z.to_N (lo - Z.of_N (seg_base seg))) n
      | None => false
      end)%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hexbyte_ok_sound : forall s i, hexbyte_ok s i = true -> hex_byte_at s i <> None.
Proof.
  intros s i H. unfold hexbyte_ok in H. destruct (hex_byte_at s i); [discriminate|discriminate H].
Qed.

Lemma hexbytes_ok_sound : forall s n off k,
  hexbytes_ok s off n = true -> (k < n)%nat -> hex_byte_at s (off + N.of_nat k)%N <> None.
Proof.
  intros s n; induction n as [|n IH]; intros off k H Hk; [lia|].
  cbn [hexbytes_ok] in H. destruct (hexbyte_ok s off) eqn:H0; [|discriminate]. rename H into Hr.
  destruct k as [|k].
  - rewrite N.add_0_r. apply hexbyte_ok_sound, H0.
  - replace (off + N.of_nat (S k))%N with (off + 1 + N.of_nat k)%N by lia.
    apply IH; [exact Hr | lia].
Qed.

Lemma chunks_ok_sound : forall chunks off n k,
  chunks_ok chunks off n = true -> (k < n)%nat ->
  segment_byte_at chunks (off + N.of_nat k)%N <> None.
Proof.
  induction chunks as [|c rest IH]; intros off n k H Hk; [discriminate|].
  cbn [chunks_ok] in H. cbn [segment_byte_at].
  set (cb := Z.to_N (Uint63.to_Z (PrimString.length c) / 2)) in *.
  destruct (off + N.of_nat n <=? cb)%N eqn:E1.
  - apply N.leb_le in E1.
    replace (off + N.of_nat k <? cb)%N with true by (symmetry; apply N.ltb_lt; lia).
    apply hexbytes_ok_sound with (n := n); assumption.
  - destruct (cb <=? off)%N eqn:E2; [|discriminate].
    apply N.leb_le in E2. apply N.leb_gt in E1.
    replace (off + N.of_nat k <? cb)%N with false by (symmetry; apply N.ltb_ge; lia).
    replace (off + N.of_nat k - cb)%N with (off - cb + N.of_nat k)%N by lia.
    apply IH with (n := n); assumption.
Qed.

Lemma find_segment_range_sound : forall segs lo hi seg x,
  find_segment_range segs lo hi = Some seg ->
  (lo <= x)%Z -> (x + 1 <= hi)%Z ->
  find_segment segs x 1 = Some seg
  /\ (Z.of_N (seg_base seg) <= lo)%Z /\ (hi <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction segs as [|s rest IH]; intros lo hi seg x H Hlo Hhi; [discriminate|].
  cbn [find_segment_range] in H. cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb hi (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E1.
  - injection H as <-. apply andb_true_iff in E1 as [Ea Eb].
    apply Z.leb_le in Ea. apply Z.leb_le in Eb.
    replace (Z.of_N (seg_base s) <=? x)%Z with true by (symmetry; apply Z.leb_le; lia).
    replace (x + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))%Z with true
      by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. repeat split; lia.
  - destruct (Z.leb hi (Z.of_N (seg_base s)) || Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo)%bool eqn:E2;
      [|discriminate].
    assert (Hdis : (hi <= Z.of_N (seg_base s) \/ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= lo)%Z).
    { apply orb_true_iff in E2 as [E|E]; apply Z.leb_le in E; lia. }
    replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
      with false.
    + apply IH; assumption.
    + symmetry. apply andb_false_iff.
      destruct Hdis as [Hd|Hd]; [left|right]; apply Z.leb_gt; lia.
Qed.

(* [comment removed for export] *)
Lemma wseg_fast_sound_aux : forall segs seg (lo : Z) (n : nat) (chunks_good :
    forall k, (k < n)%nat ->
      segment_byte_at (seg_bytes seg) (Z.to_N (lo - Z.of_N (seg_base seg)) + N.of_nat k)%N <> None),
  (lo + Z.of_nat n <= 2 ^ 64)%Z ->
  seg_writable seg = true ->
  (forall x, (lo <= x)%Z -> (x + 1 <= lo + Z.of_nat n)%Z ->
     find_segment segs x 1 = Some seg /\ (Z.of_N (seg_base seg) <= lo)%Z /\
     (lo + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z) ->
  forall m (a : word) k, bv_unsigned a = (lo + Z.of_nat k)%Z -> (k + m <= n)%nat ->
  wseg_ok segs a m = true.
Proof.
  intros segs seg lo n Hbytes Hnw Hw Hfind m.
  induction m as [|m IH]; intros a k Ha Hkm; [reflexivity|].
  cbn [wseg_ok].
  destruct (Hfind (bv_unsigned a)) as [Hf [Hb1 Hb2]]; [lia|lia|].
  rewrite Hf, Hw.
  replace (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))
    with (Z.to_N (lo - Z.of_N (seg_base seg)) + N.of_nat k)%N by lia.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (lo - Z.of_N (seg_base seg)) + N.of_nat k)%N)
    as [b|] eqn:Eb.
  - cbn [andb]. destruct m as [|m']; [reflexivity|].
    apply (IH (a + 1) (S k)); [|lia].
    rewrite u_add1; [lia|]. pose proof (u64_range a). lia.
  - exfalso. apply (Hbytes k); [lia|exact Eb].
Qed.

Theorem wseg_fast_sound : forall segs a n,
  wseg_fast segs a n = true -> wseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold wseg_fast in H.
  apply andb_true_iff in H as [Hnw H]. apply Z.leb_le in Hnw.
  destruct (find_segment_range segs (bv_unsigned a) (bv_unsigned a + Z.of_nat n)) as [seg|] eqn:Hr;
    [|discriminate].
  apply andb_true_iff in H as [Hw Hc].
  apply (wseg_fast_sound_aux segs seg (bv_unsigned a) n) with (k := 0%nat).
  - intros k Hk. apply chunks_ok_sound with (n := n); assumption.
  - exact Hnw.
  - exact Hw.
  - intros x Hlo Hhi. eapply find_segment_range_sound; eassumption.
  - lia.
  - lia.
Qed.
