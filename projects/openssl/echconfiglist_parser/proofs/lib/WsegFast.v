(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require PrimString Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec StreamSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Fixpoint find_seg_rng (segs : list Segment) (lo n : Z) : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
      let base := Z.of_N (seg_base seg) in
      let top := (base + Z.of_N (seg_size seg))%Z in
      if (Z.leb base lo && Z.leb (lo + n) top)%bool then Some seg
      else if (Z.leb top lo || Z.leb (lo + n) base)%bool then find_seg_rng rest lo n
      else None
  end.

Lemma find_seg_rng_byte : forall segs lo n seg, find_seg_rng segs lo n = Some seg ->
  forall x, (lo <= x < lo + n)%Z -> find_segment segs x 1 = Some seg.
Proof.
  induction segs as [|s rest IH]; intros lo n seg H x Hx; [discriminate|].
  cbn [find_seg_rng] in H. cbn [find_segment]. cbv zeta in H |- *.
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb (lo + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:Hc.
  - injection H as <-. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - destruct (Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo || Z.leb (lo + n) (Z.of_N (seg_base s)))%bool eqn:Hd; [|discriminate].
    apply orb_prop in Hd.
    assert (Hf : (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = false).
    { apply andb_false_iff. destruct Hd as [Hd|Hd]; apply Z.leb_le in Hd; [right | left]; apply Z.leb_gt; lia. }
    rewrite Hf. exact (IH lo n seg H x Hx).
Qed.

Definition chunk_bytes (c : PrimString.string) : N := Z.to_N (Uint63.to_Z (PrimString.length c) / 2).

(* [comment removed for export] *)
Fixpoint hex_ok (c : PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match hex_byte_at c off with Some _ => hex_ok c (off + 1) n' | None => false end
  end.

Lemma hex_ok_at : forall c n off, hex_ok c off n = true ->
  forall j, (j < N.of_nat n)%N -> hex_byte_at c (off + j) <> None.
Proof.
  induction n as [|n IH]; intros off H j Hj; [lia|].
  cbn [hex_ok] in H. destruct (hex_byte_at c off) as [b|] eqn:Hb; [|discriminate].
  destruct (N.eq_dec j 0) as [->|Hne].
  - rewrite N.add_0_r, Hb. discriminate.
  - replace (off + j)%N with (off + 1 + (j - 1))%N by lia. apply (IH (off + 1)%N H). lia.
Qed.

(* [comment removed for export] *)
Fixpoint chunks_ok (chunks : list PrimString.string) (off n : N) : bool :=
  match chunks with
  | [] => N.eqb n 0
  | c :: rest =>
      let cb := chunk_bytes c in
      if (cb <=? off)%N then chunks_ok rest (off - cb) n
      else let k := N.min n (cb - off) in
           (hex_ok c off (N.to_nat k) && chunks_ok rest 0 (n - k))%bool
  end.

Lemma chunks_ok_at : forall chunks off n, chunks_ok chunks off n = true ->
  forall i, (i < n)%N -> segment_byte_at chunks (off + i) <> None.
Proof.
  induction chunks as [|c rest IH]; intros off n H i Hi.
  - cbn [chunks_ok] in H. apply N.eqb_eq in H. lia.
  - cbn [chunks_ok] in H. cbn [segment_byte_at]. fold (chunk_bytes c). cbv zeta in H |- *.
    destruct (chunk_bytes c <=? off)%N eqn:Hc.
    + apply N.leb_le in Hc. rewrite (proj2 (N.ltb_ge _ _)) by lia.
      replace (off + i - chunk_bytes c)%N with (off - chunk_bytes c + i)%N by lia. exact (IH _ _ H i Hi).
    + apply N.leb_gt in Hc. apply andb_prop in H as [Hh Hr].
      destruct (N.lt_ge_cases i (N.min n (chunk_bytes c - off))) as [Hlt|Hge].
      * rewrite (proj2 (N.ltb_lt _ _)) by lia. apply (hex_ok_at c _ off Hh). rewrite N2Nat.id. exact Hlt.
      * assert (Hk : N.min n (chunk_bytes c - off) = (chunk_bytes c - off)%N) by lia.
        rewrite Hk in Hr, Hge. rewrite (proj2 (N.ltb_ge _ _)) by lia.
        replace (off + i - chunk_bytes c)%N with (0 + (i - (chunk_bytes c - off)))%N by lia.
        apply (IH _ _ Hr). lia.
Qed.

Definition wseg_fast (segs : list Segment) (a : word) (n : nat) : bool :=
  let lo := bv_unsigned a in
  match find_seg_rng segs lo (Z.of_nat n) with
  | Some seg =>
      (seg_writable seg && Z.leb (lo + Z.of_nat n) (2 ^ 64)
       && chunks_ok (seg_bytes seg) (Z.to_N (lo - Z.of_N (seg_base seg))) (N.of_nat n))%bool
  | None => false
  end.

Lemma wseg_ok_bytes : forall segs seg n (a : word),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  seg_writable seg = true ->
  (forall x, (bv_unsigned a <= x < bv_unsigned a + Z.of_nat n)%Z ->
     find_segment segs x 1 = Some seg /\ segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) <> None) ->
  wseg_ok segs a n = true.
Proof.
  intros segs seg. induction n as [|n IH]; intros a Hn Hw Hb; [reflexivity|].
  cbn [wseg_ok]. destruct (Hb (bv_unsigned a) ltac:(lia)) as [Hf Hs]. rewrite Hf, Hw.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|]; [|contradiction].
  cbn [andb].
  destruct n as [|n']; [reflexivity|].
  assert (Hu : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
  apply IH; [rewrite Hu; lia | exact Hw |]. intros x Hx. rewrite Hu in Hx. apply Hb. lia.
Qed.

Theorem wseg_fast_ok : forall segs (a : word) n, wseg_fast segs a n = true -> wseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold wseg_fast in H. cbv zeta in H.
  destruct (find_seg_rng segs (bv_unsigned a) (Z.of_nat n)) as [seg|] eqn:Hf; [|discriminate].
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hw H64]. apply Z.leb_le in H64.
  apply (wseg_ok_bytes segs seg n a H64 Hw). intros x Hx. split.
  - exact (find_seg_rng_byte segs _ _ seg Hf x Hx).
  - pose proof (find_seg_rng_byte segs _ _ seg Hf (bv_unsigned a) ltac:(lia)) as Hfa.
    assert (Hbase : (Z.of_N (seg_base seg) <= bv_unsigned a)%Z).
    { clear - Hfa. induction segs as [|s rest IH]; [discriminate|]. cbn [find_segment] in Hfa. cbv zeta in Hfa.
      destruct (Z.leb (Z.of_N (seg_base s)) (bv_unsigned a) && Z.leb (bv_unsigned a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:Hc.
      - injection Hfa as <-. apply andb_prop in Hc as [H1 _]. apply Z.leb_le in H1. exact H1.
      - exact (IH Hfa). }
    replace (Z.to_N (x - Z.of_N (seg_base seg))) with (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)) + Z.to_N (x - bv_unsigned a))%N by lia.
    apply (chunks_ok_at _ _ _ Hc). lia.
Qed.
