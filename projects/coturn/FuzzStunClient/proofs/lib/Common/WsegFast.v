(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition nyb_ok (c : int) : bool :=
  ((Uint63.leb 48 c && Uint63.leb c 57) || (Uint63.leb 97 c && Uint63.leb c 102))%bool.

Lemma hex_nybble_ok : forall c, nyb_ok c = true -> (hex_nybble c <? 16)%N = true.
Proof.
  intros c H. unfold nyb_ok in H. unfold hex_nybble.
  destruct (Uint63.leb 48 c && Uint63.leb c 57)%bool eqn:H1.
  - apply andb_prop in H1. destruct H1 as [A B]. apply Uint63.leb_spec in A, B.
    change (Uint63.to_Z 48) with 48%Z in A. change (Uint63.to_Z 57) with 57%Z in B.
    apply N.ltb_lt. lia.
  - cbn [orb] in H. rewrite H. apply andb_prop in H. destruct H as [A B]. apply Uint63.leb_spec in A, B.
    change (Uint63.to_Z 97) with 97%Z in A. change (Uint63.to_Z 102) with 102%Z in B.
    apply N.ltb_lt. lia.
Qed.

Definition byte_ok (s : string) (k : int) : bool :=
  let k1 := Uint63.add k 1 in
  ((Uint63.ltb k1 (PrimString.length s) || Uint63.eqb k1 (Uint63.sub (PrimString.length s) 1))
   && nyb_ok (PrimString.get s k) && nyb_ok (PrimString.get s k1))%bool.

Lemma of_Z_succ : forall z, Uint63.of_Z (z + 1) = Uint63.add (Uint63.of_Z z) 1.
Proof.
  intros z. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec.
  change (Uint63.to_Z 1) with 1%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma of_Z_plus2 : forall z, Uint63.of_Z (z + 2) = Uint63.add (Uint63.of_Z z) 2.
Proof.
  intros z. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec.
  change (Uint63.to_Z 2) with 2%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hex_byte_at_ok : forall s i, byte_ok s (Uint63.of_Z (Z.of_N (2 * i))) = true -> exists b, hex_byte_at s i = Some b.
Proof.
  intros s i H. unfold byte_ok in H. cbv zeta in H.
  replace (Z.of_N (2 * i + 1)) with (Z.of_N (2 * i) + 1)%Z in * by lia.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  unfold hex_byte_at. cbv zeta.
  replace (Z.of_N (2 * i + 1)) with (Z.of_N (2 * i) + 1)%Z by lia.
  rewrite of_Z_succ, H1, (hex_nybble_ok _ H2), (hex_nybble_ok _ H3). cbn [andb]. eexists. reflexivity.
Qed.

Fixpoint hex_ok (f : nat) (s : string) (k : int) : bool :=
  match f with
  | O => true
  | S f' => if byte_ok s k then hex_ok f' s (Uint63.add k 2) else false
  end.

Lemma hex_ok_sound : forall f s i, hex_ok f s (Uint63.of_Z (Z.of_N (2 * i))) = true ->
  forall j, (j < f)%nat -> exists b, hex_byte_at s (i + N.of_nat j) = Some b.
Proof.
  induction f as [|f IH]; intros s i H j Hj; [lia|].
  cbn [hex_ok] in H. destruct (byte_ok s (Uint63.of_Z (Z.of_N (2 * i)))) eqn:Hb; [|discriminate].
  destruct j as [|j].
  - rewrite N.add_0_r. apply hex_byte_at_ok. exact Hb.
  - replace (i + N.of_nat (S j))%N with ((i + 1) + N.of_nat j)%N by lia.
    apply IH; [|lia]. replace (Z.of_N (2 * (i + 1))) with (Z.of_N (2 * i) + 2)%Z by lia.
    rewrite of_Z_plus2. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint bytes_ok (chunks : list string) (off : N) (n : nat) : bool :=
  match chunks with
  | [] => match n with O => true | S _ => false end
  | c :: rest =>
      let cb := Z.to_N (Uint63.to_Z (PrimString.length c) / 2) in
      if (off <? cb)%N then
        let avail := N.to_nat (cb - off) in
        if (n <=? avail)%nat then hex_ok n c (Uint63.of_Z (Z.of_N (2 * off)))
        else (hex_ok avail c (Uint63.of_Z (Z.of_N (2 * off))) && bytes_ok rest 0 (n - avail))%bool
      else bytes_ok rest (off - cb) n
  end.

Lemma bytes_ok_sound : forall chunks off n, bytes_ok chunks off n = true ->
  forall j, (j < n)%nat -> exists b, segment_byte_at chunks (off + N.of_nat j) = Some b.
Proof.
  induction chunks as [|c rest IH]; intros off n H j Hj; cbn [bytes_ok] in H.
  - destruct n; [lia|discriminate].
  - cbn [segment_byte_at]. cbv zeta in H |- *.
    set (cb := Z.to_N (Uint63.to_Z (PrimString.length c) / 2)) in *.
    destruct (off <? cb)%N eqn:Hlt.
    + apply N.ltb_lt in Hlt.
      destruct (n <=? N.to_nat (cb - off))%nat eqn:Hle.
      * apply Nat.leb_le in Hle.
        assert (Hin : (off + N.of_nat j <? cb)%N = true) by (apply N.ltb_lt; lia).
        rewrite Hin. exact (hex_ok_sound _ _ _ H j Hj).
      * apply Nat.leb_gt in Hle. apply andb_prop in H. destruct H as [H1 H2].
        destruct (Nat.lt_ge_cases j (N.to_nat (cb - off))) as [Hj1|Hj1].
        -- assert (Hin : (off + N.of_nat j <? cb)%N = true) by (apply N.ltb_lt; lia).
           rewrite Hin. exact (hex_ok_sound _ _ _ H1 j Hj1).
        -- assert (Hout : (off + N.of_nat j <? cb)%N = false) by (apply N.ltb_ge; lia).
           rewrite Hout.
           replace (off + N.of_nat j - cb)%N with (0 + N.of_nat (j - N.to_nat (cb - off)))%N by lia.
           apply (IH 0%N (n - N.to_nat (cb - off))%nat H2). lia.
    + apply N.ltb_ge in Hlt.
      assert (Hout : (off + N.of_nat j <? cb)%N = false) by (apply N.ltb_ge; lia).
      rewrite Hout. replace (off + N.of_nat j - cb)%N with ((off - cb) + N.of_nat j)%N by lia.
      exact (IH _ _ H j Hj).
Qed.

(* [comment removed for export] *)
Fixpoint find_seg_range (segs : list Segment) (lo n : Z) : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
      let base := Z.of_N (seg_base seg) in
      let top := (base + Z.of_N (seg_size seg))%Z in
      if (Z.leb base lo && Z.leb (lo + n) top)%bool then Some seg
      else if (Z.leb (lo + n) base || Z.leb top lo)%bool then find_seg_range rest lo n
      else None
  end.

Lemma find_seg_range_sound : forall segs lo n seg, find_seg_range segs lo n = Some seg ->
  forall x, (lo <= x < lo + n)%Z -> find_segment segs x 1 = Some seg.
Proof.
  induction segs as [|s rest IH]; intros lo n seg H x Hx; cbn [find_seg_range] in H; [discriminate|].
  cbv zeta in H. cbn [find_segment]. cbv zeta.
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb (lo + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:H1.
  - injection H as <-. apply andb_prop in H1. destruct H1 as [A B]. apply Z.leb_le in A, B.
    assert (T : (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = true)
      by (apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite T. reflexivity.
  - destruct (Z.leb (lo + n) (Z.of_N (seg_base s)) || Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo)%bool eqn:H2; [|discriminate].
    assert (F : (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = false).
    { apply orb_prop in H2. destruct H2 as [A|A]; apply Z.leb_le in A; apply andb_false_iff; [left|right]; apply Z.leb_gt; lia. }
    rewrite F. exact (IH _ _ _ H x Hx).
Qed.

Definition wseg_ok_fast (segs : list Segment) (lo : Z) (n : nat) : bool :=
  (Z.leb 0 lo && Z.leb (lo + Z.of_nat n) (2 ^ 64) &&
   match find_seg_range segs lo (Z.of_nat n) with
   | Some seg => seg_writable seg && bytes_ok (seg_bytes seg) (Z.to_N (lo - Z.of_N (seg_base seg))) n
   | None => false
   end)%bool.

Lemma wseg_ok_intro : forall segs n (a : bv 64),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x, (bv_unsigned a <= x < bv_unsigned a + Z.of_nat n)%Z ->
     exists seg, find_segment segs x 1 = Some seg /\ seg_writable seg = true /\
                 exists b, segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) = Some b) ->
  wseg_ok segs a n = true.
Proof.
  intros segs. induction n as [|n IH]; intros a Hb H; [reflexivity|].
  cbn [wseg_ok]. destruct (H (bv_unsigned a)) as (seg & -> & -> & b & ->); [lia|]. cbn [andb].
  destruct n as [|n']; [reflexivity|].
  pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha.
  assert (E : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
  { rewrite bv_add_unsigned. change (bv_unsigned (1 : bv 64)) with 1%Z. apply bv_wrap_small. unfold bv_modulus. lia. }
  apply IH; rewrite E; [lia|]. intros x Hx. apply H. lia.
Qed.

Theorem wseg_ok_fast_sound : forall segs (a : bv 64) n,
  wseg_ok_fast segs (bv_unsigned a) n = true -> wseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold wseg_ok_fast in H.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1, H2.
  destruct (find_seg_range segs (bv_unsigned a) (Z.of_nat n)) as [seg|] eqn:Hf; [|discriminate].
  apply andb_prop in H3. destruct H3 as [Hw Hby].
  apply wseg_ok_intro; [exact H2|]. intros x Hx.
  exists seg. split; [exact (find_seg_range_sound _ _ _ _ Hf x Hx)|]. split; [exact Hw|].
  (* [comment removed for export] *)
  assert (Hbase : (Z.of_N (seg_base seg) <= bv_unsigned a)%Z).
  { destruct n as [|n']; [lia|].
    pose proof (find_seg_range_sound _ _ _ _ Hf (bv_unsigned a) ltac:(lia)) as Hs.
    clear - Hs. induction segs as [|s rest IHs]; cbn [find_segment] in Hs; [discriminate|]. cbv zeta in Hs.
    destruct (Z.leb (Z.of_N (seg_base s)) (bv_unsigned a) && Z.leb (bv_unsigned a + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:T.
    - injection Hs as <-. apply andb_prop in T. destruct T as [A _]. apply Z.leb_le in A. exact A.
    - exact (IHs Hs). }
  destruct (bytes_ok_sound _ _ _ Hby (Z.to_nat (x - bv_unsigned a)) ltac:(lia)) as [b Hbb].
  exists b. rewrite <- Hbb. f_equal. lia.
Qed.
