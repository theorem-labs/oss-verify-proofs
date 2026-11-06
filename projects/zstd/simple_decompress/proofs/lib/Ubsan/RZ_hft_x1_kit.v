(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuildThm.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition x1pref (tl cur : Z) (dt : list Z) : Prop :=
  Znth 0 dt = 12 /\ Znth 1 dt = 0 /\ Znth 2 dt = tl /\ forall u, 0 <= u < cur -> 0 <= Znth (4 + 2 * u) dt <= tl.

Definition x1prf (tl c : Z) (ks : list Z) (dt : list Z) : Prop :=
  x1pref tl c dt /\ forall k, In k ks -> 0 <= k /\ 0 <= Znth (4 + 2 * (c + k)) dt <= tl.

Lemma prf_open : forall tl c dt, x1pref tl c dt -> x1prf tl c [] dt.
Proof. intros tl c dt P. split; [exact P|]. intros k []. Qed.

(* [comment removed for export] *)
Lemma prf_st_nb : forall tl c ks dt k i v, x1prf tl c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 2 * (c + k) -> i < Z.of_nat (length dt) -> 0 <= v <= tl ->
  x1prf tl c (k :: ks) (Zupd i v dt).
Proof.
  intros tl c ks dt k i v ((H0 & H1 & H2 & HP) & HK) Hc Hk -> HL Hv. unfold FseNCount.Zlength.
  split; [split; [|split; [|split]]|].
  - rewrite Znth_Zupd_other by lia. exact H0.
  - rewrite Znth_Zupd_other by lia. exact H1.
  - rewrite Znth_Zupd_other by lia. exact H2.
  - intros u Hu. destruct (Z.eq_dec (4 + 2 * u) (4 + 2 * (c + k))) as [E|NE]; [lia|].
    rewrite Znth_Zupd_other by lia. apply HP; lia.
  - intros k' [<-|IN]; [split; [lia|]; rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia); exact Hv|].
    destruct (HK k' IN) as (K0 & KV). split; [exact K0|].
    destruct (Z.eq_dec k' k) as [->|NE]; [rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia); exact Hv|].
    rewrite Znth_Zupd_other by lia. exact KV.
Qed.

(* [comment removed for export] *)
Lemma prf_st_sy : forall tl c ks dt k i v, x1prf tl c ks dt -> 0 <= c -> 0 <= k -> i = 4 + 2 * (c + k) + 1 ->
  x1prf tl c ks (Zupd i v dt).
Proof.
  intros tl c ks dt k i v ((H0 & H1 & H2 & HP) & HK) Hc Hk ->.
  split; [split; [|split; [|split]]|].
  - rewrite Znth_Zupd_other by lia. exact H0.
  - rewrite Znth_Zupd_other by lia. exact H1.
  - rewrite Znth_Zupd_other by lia. exact H2.
  - intros u Hu. rewrite Znth_Zupd_other by lia. apply HP; lia.
  - intros k' IN. destruct (HK k' IN) as (K0 & KV). split; [exact K0|]. rewrite Znth_Zupd_other by lia. exact KV.
Qed.

(* [comment removed for export] *)
Lemma prf_close : forall tl c ks dt L, x1prf tl c ks dt -> 0 <= c -> (forall k, 0 <= k < L -> In k ks) -> x1pref tl (c + L) dt.
Proof.
  intros tl c ks dt L ((H0 & H1 & H2 & HP) & HK) Hc COV.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros u Hu. destruct (Z.lt_ge_cases u c) as [LT|GE]; [apply HP; lia|].
  replace u with (c + (u - c)) by lia. apply HK. apply COV. lia.
Qed.

(* [comment removed for export] *)
Definition cover (L : nat) (ks : list Z) : bool := forallb (fun k => existsb (Z.eqb k) ks) (zseq L 0).
Lemma cover_ok : forall L ks, cover L ks = true -> forall k, 0 <= k < Z.of_nat L -> In k ks.
Proof.
  intros L ks C k Hk. unfold cover in C. rewrite forallb_forall in C.
  specialize (C k ltac:(apply zseq_In_iff; lia)). apply existsb_exists in C. destruct C as (x & IN & E).
  apply Z.eqb_eq in E. subst x. exact IN.
Qed.
Lemma prf_close_c : forall tl c ks dt (L : nat), x1prf tl c ks dt -> 0 <= c -> cover L ks = true -> x1pref tl (c + Z.of_nat L) dt.
Proof. intros tl c ks dt L P Hc C. apply (prf_close tl c ks dt); [exact P | exact Hc | apply cover_ok; exact C]. Qed.

(* [comment removed for export] *)
Lemma lxor_sign_small : forall a, 0 <= a < 2^63 -> Z.lxor a 9223372036854775808 = a + 9223372036854775808.
Proof. intros a Ha. change 9223372036854775808 with (2^63). rewrite zb_lxor_sign by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
