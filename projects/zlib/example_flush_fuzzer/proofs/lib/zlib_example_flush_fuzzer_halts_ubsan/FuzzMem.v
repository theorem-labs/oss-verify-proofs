(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec StoreOk Frame RefMemcpyLib Hoare AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section BYTES.
  Variable segs : list Segment.

  Definition byte_at (m : word -> option byte) (a : Z) : Z :=
    match rdn segs m (Z_to_bv 64 a) 1 with Some [b] => bv_unsigned b | _ => 0 end.

  Fixpoint bytes_at (m : word -> option byte) (a : Z) (n : nat) : list Z :=
    match n with
    | O => []
    | S n' => byte_at m a :: bytes_at m (a + 1) n'
    end.



  Lemma bytes_at_length : forall m n a, length (bytes_at m a n) = n.
  Proof. intros m n; induction n as [|n IH]; intros a; cbn; [reflexivity | now rewrite IH]. Qed.


  Lemma bytes_at_app : forall m n1 n2 a,
    bytes_at m a (n1 + n2) = bytes_at m a n1 ++ bytes_at m (a + Z.of_nat n1) n2.
  Proof.
    intros m n1; induction n1 as [|n1 IH]; intros n2 a; cbn [bytes_at Nat.add app].
    - now rewrite Z.add_0_r.
    - rewrite IH. do 2 f_equal. f_equal. lia.
  Qed.


  Lemma bytes_at_snoc : forall m n a,
    bytes_at m a (S n) = bytes_at m a n ++ [byte_at m (a + Z.of_nat n)].
  Proof. intros m n a. rewrite <- Nat.add_1_r, bytes_at_app. reflexivity. Qed.

  Lemma byte_at_range : forall m a, 0 <= byte_at m a < 256.
  Proof.
    intros m a. unfold byte_at.
    destruct (rdn segs m (Z_to_bv 64 a) 1) as [[|b [|]]|]; try lia.
    pose proof (u8_range b). lia.
  Qed.

  Lemma bytes_at_range : forall m n a, Forall (fun b => 0 <= b < 256) (bytes_at m a n).
  Proof.
    intros m n; induction n as [|n IH]; intros a; cbn; constructor; [apply byte_at_range | apply IH].
  Qed.



  Lemma byte_at_rdn : forall m a (b : byte),
    rdn segs m (Z_to_bv 64 a) 1 = Some [b] -> byte_at m a = bv_unsigned b.
  Proof. intros m a b H. unfold byte_at. now rewrite H. Qed.


  Lemma rdn_byte_at_v : forall m a (b : byte),
    rdn segs m (Z_to_bv 64 a) 1 = Some [b] -> Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (byte_at m a).
  Proof. intros m a b H. now rewrite (byte_at_rdn m a b H). Qed.

  Lemma byte_at_ext : forall m m' a,
    m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> byte_at m' a = byte_at m a.
  Proof. intros m m' a H. unfold byte_at. cbn [rdn]. now rewrite H. Qed.

  Lemma bytes_at_ext : forall m m' n a,
    (forall i, 0 <= i < Z.of_nat n -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
    bytes_at m' a n = bytes_at m a n.
  Proof.
    intros m m' n; induction n as [|n IH]; intros a H; [reflexivity|]. cbn [bytes_at]. f_equal.
    - apply byte_at_ext. rewrite <- (Z.add_0_r a). apply H. lia.
    - apply IH. intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia.
  Qed.

  Lemma bytes_at_frame : forall m m' rs n a,
    frame_mod m m' rs ->
    (forall i, 0 <= i < Z.of_nat n -> outside (Z_to_bv 64 (a + i)) rs) ->
    bytes_at m' a n = bytes_at m a n.
  Proof.
    intros m m' rs n a [Hout _] Hrs. apply bytes_at_ext. intros i Hi. apply Hout, Hrs, Hi.
  Qed.


  Lemma bytes_at_wbytes : forall m n a (wa : word) bs,
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    bv_unsigned wa + Z.of_nat (length bs) <= 2 ^ 64 ->
    (a + Z.of_nat n <= bv_unsigned wa \/ bv_unsigned wa + Z.of_nat (length bs) <= a) ->
    bytes_at (wbytes m wa bs) a n = bytes_at m a n.
  Proof.
    intros m n a wa bs Ha Hn Hwa Hap. apply bytes_at_ext. intros i Hi.
    apply wbytes_outside; [|exact Hwa]. unfold in_rng. rewrite u64_lit by lia. lia.
  Qed.

  Lemma readable_grows : forall m m' a len,
    mem_grows m m' ->
    (forall i, 0 <= i < len -> exists b : byte, rdn segs m (Z_to_bv 64 (a + i)) 1 = Some [b]) ->
    (forall i, 0 <= i < len -> exists b : byte, rdn segs m' (Z_to_bv 64 (a + i)) 1 = Some [b]).
  Proof.
    intros m m' a len Hg H i Hi. destruct (H i Hi) as [b Hb].
    cbn [rdn] in *. destruct (m (Z_to_bv 64 (a + i))) as [b0|] eqn:Hm.
    - assert (Hm' : m' (Z_to_bv 64 (a + i)) <> None) by (apply Hg; congruence).
      destruct (m' (Z_to_bv 64 (a + i))) as [b1|]; [exists b1; reflexivity | congruence].
    - destruct (m' (Z_to_bv 64 (a + i))) as [b1|]; [exists b1; reflexivity|].
      destruct (seg_rom segs (Z_to_bv 64 (a + i))) as [b2|]; [exists b2; reflexivity | discriminate].
  Qed.



  Lemma bv_succ_lit : forall a, 0 <= a -> a + 1 < 2 ^ 64 ->
    (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
  Proof.
    intros a H0 H1. rewrite word_succ_at. unfold at_. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma rdn_bytes_at : forall m n a,
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat n -> exists b : byte, rdn segs m (Z_to_bv 64 (a + i)) 1 = Some [b]) ->
    exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ map (fun b : byte => bv_unsigned b) bs = bytes_at m a n.
  Proof.
    intros m n; induction n as [|n IH]; intros a Ha Hn H.
    - exists []. split; reflexivity.
    - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
      pose proof (byte_at_rdn m a b Hb) as Eb.
      cbn [rdn] in Hb |- *.
      destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 a) end)
        as [b0|]; [|discriminate]. injection Hb as ->.
      destruct n as [|n'].
      + exists [b]. split; [reflexivity | cbn; now rewrite Eb].
      + rewrite bv_succ_lit by lia.
        destruct (IH (a + 1) ltac:(lia) ltac:(lia)
                    ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia))
          as (bs & Hbs & Hmap).
        rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn [map bytes_at]; now rewrite Eb, Hmap].
  Qed.



End BYTES.

Arguments byte_at segs m a : simpl never.
