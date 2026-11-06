(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition meets (a n : Z) (q : word * word) : bool := (bas q <? a + n) && (a <? bas q + bsz q).

Lemma meets_false (a n : Z) (q : word * word) : meets a n q = false <-> iv_disj a (a + n) q.
Proof. unfold meets, iv_disj. rewrite andb_false_iff, !Z.ltb_ge. tauto. Qed.

Definition round_up (z : Z) : Z := (z + 4095) / 4096 * 4096.

Lemma round_up_spec (z : Z) : z <= round_up z <= z + 4095 /\ round_up z mod 4096 = 0.
Proof.
  unfold round_up. pose proof (Z.div_mod (z + 4095) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (z + 4095) 4096 ltac:(lia)) as B.
  split; [lia | apply Z_mod_mult].
Qed.

Lemma live_bytes_split (l1 l2 : list (word * word)) (q : word * word) :
  live_bytes (l1 ++ q :: l2) = bsz q + live_bytes (l1 ++ l2).
Proof. rewrite !live_bytes_app, live_bytes_cons. lia. Qed.

Lemma pack_free_aux (n : Z) : 0 < n -> forall (k : nat) (l : list (word * word)) (lo : Z),
  length l = k -> lo mod 4096 = 0 ->
  exists a, lo <= a <= lo + live_bytes l + Z.of_nat k * (n + 4096) /\ a mod 4096 = 0 /\ forall q, In q l -> iv_disj a (a + n) q.
Proof.
  intros Hn. induction k as [|k IH]; intros l lo Hlen Hal.
  - destruct l; [|discriminate Hlen]. exists lo. cbn [live_bytes]. split; [lia|]. split; [exact Hal | intros q []].
  - destruct (find (meets lo n) l) as [q|] eqn:Ef.
    + apply find_some in Ef as [Hin Hm]. unfold meets in Hm. apply andb_prop in Hm as [M1 M2]. apply Z.ltb_lt in M1. apply Z.ltb_lt in M2.
      apply in_split in Hin as [l1 [l2 ->]].
      destruct (round_up_spec (bas q + bsz q)) as [[R1 R2] R3].
      assert (Hlen' : length (l1 ++ l2) = k) by (rewrite length_app in *; cbn [length] in Hlen; lia).
      destruct (IH (l1 ++ l2) (round_up (bas q + bsz q)) Hlen' R3) as [a [[A1 A2] [A3 A4]]].
      exists a. rewrite live_bytes_split. split; [|split; [exact A3|]].
      * rewrite Nat2Z.inj_succ. pose proof (bsz_range q). nia.
      * intros q' Hq'. apply in_app_or in Hq' as [Hq'|[<-|Hq']].
        -- apply A4. apply in_or_app. left. exact Hq'.
        -- unfold iv_disj. right. lia.
        -- apply A4. apply in_or_app. right. exact Hq'.
    + exists lo. pose proof (live_bytes_nonneg l). split; [nia|]. split; [exact Hal|].
      intros q Hq. apply meets_false. exact (find_none _ _ Ef q Hq).
Qed.

Theorem pack_free (l : list (word * word)) (n lo top : Z) :
  0 < n -> lo mod 4096 = 0 -> lo + live_bytes l + Z.of_nat (length l) * (n + 4096) + n <= top ->
  exists a, lo <= a /\ a mod 4096 = 0 /\ a + n <= top /\ forall q, In q l -> iv_disj a (a + n) q.
Proof.
  intros Hn Hal Hb. destruct (pack_free_aux n Hn (length l) l lo eq_refl Hal) as [a [[A1 A2] [A3 A4]]].
  exists a. repeat split; [exact A1 | exact A3 | lia | exact A4].
Qed.

(* [comment removed for export] *)
Theorem grant_exists (l : list (word * word)) (nZ top : Z) :
  0 < nZ -> top <= two64 ->
  4096 + live_bytes l + Z.of_nat (length l) * (nZ + 4096) + nZ <= top ->
  exists a : word, bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= top
                   /\ region_free l a (Z_to_bv 64 nZ) = true.
Proof.
  intros Hn Ht Hb. destruct (pack_free l nZ 4096 top Hn eq_refl Hb) as [a [A1 [A2 [A3 A4]]]].
  assert (Hr : 0 <= a < two64) by lia.
  exists (Z_to_bv 64 a). rewrite (u_Z_to_bv a Hr). repeat split; [exact A2 | lia | exact A3|].
  apply region_free_disj. intros q Hq. rewrite (u_Z_to_bv a Hr), (u_Z_to_bv nZ) by lia. exact (A4 q Hq).
Qed.
