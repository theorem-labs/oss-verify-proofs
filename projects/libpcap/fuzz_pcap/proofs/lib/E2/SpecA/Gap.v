(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import FreeRange.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FLOOR : Z := 0x2aaaaaaab000.
Definition CEIL : Z := 0x7fff7f800000.
Lemma FLOOR_val : FLOOR = 0x2aaaaaaab000. Proof. reflexivity. Qed.
Lemma CEIL_val : CEIL = 0x7fff7f800000. Proof. reflexivity. Qed.
Lemma FLOOR_eq : FLOOR = bottomup_floor. Proof. reflexivity. Qed.
Lemma CEIL_eq : CEIL = band_ceiling. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition in_band_b (e : word * word) : bool := inband e.

Lemma band_count_filter : forall l, band_count l = Z.of_nat (length (List.filter in_band_b l)).
Proof.
  induction l as [|e l IH]; [reflexivity|]. cbn [band_count List.filter]. unfold in_band_b at 1.
  destruct (inband e); cbn [length]; rewrite IH; lia.
Qed.

Lemma length_filter_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros f l. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

(* [comment removed for export] *)
Corollary vm_gap_available_intro_N : forall h nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4096) + T <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ N R T HnZ _ maps HN HT HB.
  apply (vm_gap_available_of_bound h nZ N T); [lia| | |].
  - fold maps. rewrite band_count_filter. exact HN.
  - fold maps. pose proof (band_bytes_le_live maps). lia.
  - change (band_ceiling - bottomup_floor) with (CEIL - FLOOR). change page_size with 4096.
    pose proof (band_count_nonneg maps) as P. rewrite band_count_filter in P.
    assert (0 <= N) by lia. nia.
Qed.
