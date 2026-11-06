(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint bytes_zero_b (chunks : list PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match segment_byte_at chunks off with
            | Some b => (Z.eqb (bv_unsigned b) 0 && bytes_zero_b chunks (off + 1)%N n')%bool
            | None => false
            end
  end.

Lemma bytes_zero_b_sound : forall chunks n off j,
  bytes_zero_b chunks off n = true -> (j < n)%nat ->
  segment_byte_at chunks (off + N.of_nat j)%N = Some (Z_to_bv 8 0).
Proof.
  induction n as [|n IH]; intros off j H Hj; [lia|].
  cbn [bytes_zero_b] in H. destruct (segment_byte_at chunks off) as [b|] eqn:Hb; [|discriminate].
  apply andb_prop in H as [H0 H]. apply Z.eqb_eq in H0.
  destruct j as [|j].
  - rewrite N.add_0_r. rewrite Hb. f_equal. apply bv_eq. rewrite H0. reflexivity.
  - replace (off + N.of_nat (S j))%N with (off + 1 + N.of_nat j)%N by lia. apply IH; [exact H | lia].
Qed.

(* [comment removed for export] *)
Fixpoint find_segment_excl (segs : list Segment) (lo n : Z) : option Segment :=
  match segs with
  | [] => None
  | s :: rest =>
      let b := Z.of_N (seg_base s) in let t := Z.of_N (seg_base s) + Z.of_N (seg_size s) in
      if (Z.leb b lo && Z.leb (lo + n) t)%bool then Some s
      else if (Z.leb t lo || Z.leb (lo + n) b)%bool then find_segment_excl rest lo n
      else None
  end.

Lemma find_segment_excl_sound : forall segs lo n s x,
  find_segment_excl segs lo n = Some s -> lo <= x -> x + 1 <= lo + n ->
  find_segment segs x 1 = Some s /\ Z.of_N (seg_base s) <= lo /\ lo + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 rest IH]; intros lo n s x H H1 H2; [discriminate|].
  cbn [find_segment_excl] in H. cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s0)) lo && Z.leb (lo + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:C.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    replace (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    split; [reflexivity | lia].
  - destruct (Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) lo || Z.leb (lo + n) (Z.of_N (seg_base s0)))%bool eqn:D; [|discriminate].
    assert (OUT : (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool = false).
    { apply Bool.orb_prop in D. destruct D as [D|D]; apply Z.leb_le in D; apply andb_false_iff;
        [right | left]; apply Z.leb_gt; lia. }
    rewrite OUT. exact (IH lo n s x H H1 H2).
Qed.

Definition img_zero_chk (segs : list Segment) (lo n : Z) : bool :=
  match find_segment_excl segs lo n with
  | Some s => (seg_readable s && bytes_zero_b (seg_bytes s) (Z.to_N (lo - Z.of_N (seg_base s))) (Z.to_nat n))%bool
  | None => false
  end.

Theorem img_zero_chk_sound : forall segs lo n,
  img_zero_chk segs lo n = true -> 0 <= lo -> lo + n <= 2 ^ 64 ->
  forall x : word, lo <= bv_unsigned x < lo + n -> seg_rom segs x = Some (Z_to_bv 8 0).
Proof.
  intros segs lo n H Hlo Hn x Hx. unfold img_zero_chk in H.
  destruct (find_segment_excl segs lo n) as [s|] eqn:Hf; [|discriminate].
  apply andb_prop in H as [Hr Hz].
  destruct (find_segment_excl_sound segs lo n s (bv_unsigned x) Hf ltac:(lia) ltac:(lia)) as (F & B1 & B2).
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite F, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  pose proof (bytes_zero_b_sound (seg_bytes s) (Z.to_nat n) (Z.to_N (lo - Z.of_N (seg_base s))) (Z.to_nat (bv_unsigned x - lo)) Hz ltac:(lia)) as Z0.
  replace (Z.to_N (bv_unsigned x - Z.of_N (seg_base s))) with (Z.to_N (lo - Z.of_N (seg_base s)) + N.of_nat (Z.to_nat (bv_unsigned x - lo)))%N by lia.
  rewrite Z0. reflexivity.
Qed.
