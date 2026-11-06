(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), ROOM WITH HEADROOM.
   ARGUMENT ORDER: ROOM_cf_k S k -- STATE FIRST, then the headroom k (a nat: the number of allocator calls
   still to be paid for). ROOM_cf_k S 0 is ROOM_cf S (YGcfRoomPre.v). Per-call charges: RK_malloc = 1,
   RK_free = 1 (a free may allocate one quarantine batch from class kBatchClass), RK_realloc = 2 (a malloc
   and a free). These charges are fixed: consumers build expressions on them.
   The keep / step lemmas over malloc_cf / free_cf / the realloc tree are in YGcfRoomStep.v; the
   secondary count can also be rebuilt from state at any time with ROOM_cf_count_of_live (YGcfSecBound.v).
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YGcfRoomPre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section K. Context {cp : CfParams}.

(* ERRB_ROOM (YG00cf.v) with 100 bytes of headroom per remaining call: one class-full report
   appends at most exh_len1 + exh_len2 c <= 33 + 60 + 2 + 5 = 100 bytes. *)
Definition ERRB_ROOM_k (S : astate) (k : nat) : Prop :=
errb_size_cf S + 100 * Z.of_nat k + 2 ^ 12 + kPage <= cf_nob.

Definition ROOM_cf_k (S : astate) (k : nat) : Prop :=
Z.of_nat (length (st_sec_arr S)) + Z.of_nat k < cf_sec_live_max /\ ERRB_ROOM_k S k /\
rg_mapped_user (reg S kBatchClass) + (Z.of_nat k + 1) * kUserMapSize <= kFreeArrayOffset.

Definition RK_malloc : nat := 1.
Definition RK_free : nat := 1.
Definition RK_realloc : nat := 2.

Lemma RK_zero : forall S, ROOM_cf_k S 0 <-> ROOM_cf S.
Proof.
intros S. unfold ROOM_cf_k, ERRB_ROOM_k, ROOM_cf, ERRB_ROOM, batch_room_cf. cbn [Z.of_nat].
split; intros (A & Bq & C); (split; [lia | split; lia]).
Qed.

Lemma ROOM_cf_k0 : forall S, ROOM_cf_k S 0 <-> ROOM_cf S.
Proof. exact RK_zero. Qed.

Lemma RK_mono : forall S k1 k2, (k2 <= k1)%nat -> ROOM_cf_k S k1 -> ROOM_cf_k S k2.
Proof.
intros S k1 k2 Hk (A & Bq & C). unfold ROOM_cf_k, ERRB_ROOM_k in *.
apply Nat2Z.inj_le in Hk. unfold kUserMapSize in *.
split; [lia | split; [lia | nia]].
Qed.

Lemma ROOM_cf_k_mono : forall s k k', (k <= k')%nat -> ROOM_cf_k s k' -> ROOM_cf_k s k.
Proof. intros s k k' Hk H. exact (RK_mono s k' k Hk H). Qed.

Lemma RK_room : forall S k, ROOM_cf_k S k -> ROOM_cf S.
Proof. intros S k H. apply RK_zero. exact (RK_mono S k 0 (Nat.le_0_l k) H). Qed.

(* A step that keeps every headroom level. *)
Definition room_kept (S S' : astate) : Prop := forall k, ROOM_cf_k S k -> ROOM_cf_k S' k.
Lemma room_kept_refl : forall S, room_kept S S.
Proof. intros S k H. exact H. Qed.
Lemma room_kept_trans : forall S1 S2 S3, room_kept S1 S2 -> room_kept S2 S3 -> room_kept S1 S3.
Proof. intros S1 S2 S3 H12 H23 k H. exact (H23 k (H12 k H)). Qed.

(* The headroom available at the allocator's initial state: no secondary, no errbuf, the batch
   class empty. Bounded by the secondary cap, the errbuf room and the batch class's room. *)
Definition K_INIT : nat :=
Z.to_nat (Z.min (cf_sec_live_max - 1) (Z.min ((cf_nob - 2 ^ 12 - kPage) / 100) (kFreeArrayOffset / kUserMapSize - 1))).

Theorem ROOM_cf_init_k : forall k, (k <= K_INIT)%nat -> ROOM_cf_k init_state k.
Proof.
intros k Hk. unfold K_INIT in Hk.
pose proof cf_sec_live_pos as P1. pose proof cf_nob_lo as P2.
assert (E3 : kFreeArrayOffset / kUserMapSize - 1 = 14335) by reflexivity.
rewrite E3 in Hk. unfold kPage in *. change (2 ^ 12) with 4096 in *.
assert (Hd : 0 <= (cf_nob - 4096 - 4096) / 100) by (apply Z.div_pos; lia).
assert (Hm : 0 <= Z.min (cf_sec_live_max - 1) (Z.min ((cf_nob - 4096 - 4096) / 100) 14335)) by lia.
apply Nat2Z.inj_le in Hk. rewrite Z2Nat.id in Hk by exact Hm.
pose proof (Z.mul_div_le (cf_nob - 4096 - 4096) 100 ltac:(lia)) as Hmd.
unfold ROOM_cf_k, ERRB_ROOM_k.
assert (Es : errb_size_cf init_state = 0) by reflexivity.
assert (Er : rg_mapped_user (reg init_state kBatchClass) = 0) by (rewrite reg_init; reflexivity).
rewrite Es, Er. cbn [st_sec_arr init_state length Z.of_nat]. unfold kPage, kUserMapSize, kFreeArrayOffset.
split; [lia | split; [lia | lia]].
Qed.

End K.
