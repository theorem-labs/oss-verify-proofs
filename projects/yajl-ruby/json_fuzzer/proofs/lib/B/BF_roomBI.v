(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanBudget AsanBudget2 AsanBudget3.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_rtok5 BF_refill_iface BF_refill_room.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma class_maps_bound_BI : forall nd F a c, BI nd F a -> 1 <= c <= kLargestClassID ->
  8 * (rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c))
  <= 9 * (class_size c * (as_nprim_ever a + 8 + b24 c * kNB) + kUserMapSize) + 8 * kFreeArrayMapSize.
Proof.
  intros nd F a c HBI Hc. destruct (BI_c nd F a c Hc HBI) as [X NDp]. unfold BIc_raw in X.
  destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; lia)) as [_ SZ]. pose proof (b24_range c) as R24.
  set (size := class_size c) in *. set (r := get_region a c) in *.
  assert (D : 32 * (rg_alloc_user r / size) <= rg_alloc_user r).
  { transitivity (size * (rg_alloc_user r / size)); [apply Z.mul_le_mono_nonneg_r; [apply Z.div_pos; lia| lia]| apply Z.mul_div_le; lia]. }
  assert (M : size * (everc a c + 8 + b24 c * kNB) <= size * (as_nprim_ever a + 8 + b24 c * kNB)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold kNB in *. lia.
Qed.

Theorem M2_sharp_BI : forall nd F a, BI nd F a -> regions_bytes a + 2^26 <= 4096 * (160 * as_nprim_ever a + 100000).
Proof.
  intros nd F a HBI. rewrite regions_bytes_sumZ.
  set (f := fun c => rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c)).
  set (g := fun c => (9 * (as_nprim_ever a + 8)) * class_size c + (9 * kNB) * (b24 c * class_size c) + (9 * kUserMapSize + 8 * kFreeArrayMapSize)).
  assert (LE : sumZ (fun c => 8 * f c) classes30 <= sumZ g classes30).
  { apply sumZ_le. intros c Hc. subst f g. cbn beta. pose proof (class_maps_bound_BI nd F a c HBI (In_classes30 c Hc)). lia. }
  rewrite sumZ_scale in LE. subst g. rewrite !sumZ_add, !sumZ_scale, sumZ_const, sum_class_size, sum_b24_class_size, zlen_classes30 in LE.
  assert (NP : 0 <= as_nprim_ever a).
  { destruct (BI_c nd F a 1 ltac:(unfold kLargestClassID; lia) HBI) as [X _]. unfold BIc_raw in X. lia. }
  unfold kNB, kUserMapSize, kFreeArrayMapSize in LE. rewrite ?sumZ_const, ?zlen_classes30 in LE. subst f. rewrite ?sumZ_add. clear -LE NP. lia.
Qed.

Lemma rooms_of_BI : forall E P D nd F a c, AWf E P D a -> BI nd F a -> 1 <= c <= kLargestClassID -> 0 <= as_nprim_ever a <= 12000 ->
  let r := get_region a c in
     rg_mapped_user r + kUserMapSize <= kFreeArrayOffset
  /\ 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) + kFreeArrayMapSize <= kFreeArraySize
  /\ 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) <= rg_mapped_fa r + kFreeArrayMapSize
  /\ rg_mapped_fa r + kFreeArrayMapSize <= kFreeArraySize.
Proof.
  intros E P D nd F a c WF HBI Hc NP. pose proof (proj2 (proj1 (proj2 WF)) c Hc) as WR. cbv zeta in WR. destruct WR as (_ & _ & _ & _ & _ & _ & _ & WFA & _). unfold region_of in WFA.
  destruct (BI_c nd F a c Hc HBI) as [X NDp]. unfold BIc_raw in X. cbv zeta.
  destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; lia)) as [SM SZ]. pose proof (b24_range c) as R24.
  pose proof (zlen_nonneg (get_cache a c)) as C0. pose proof (zlen_nonneg (as_tq a)) as Q1. pose proof (zlen_nonneg (as_gq a)) as Q2.
  unfold rg_num_freed. fold (zlen (rg_free (get_region a c))). unfold ncache, nbatch, fzero, kNB, kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArraySize, kMaxSize in *.
  set (size := class_size c) in *. set (mu := rg_mapped_user (get_region a c)) in *. set (au := rg_alloc_user (get_region a c)) in *.
  set (mfa := rg_mapped_fa (get_region a c)) in *. set (nf := zlen (rg_free (get_region a c))) in *.
  assert (K0 : everc a c + 8 + b24 c * 32896 <= 44904) by (clear -R24 A9 NP; lia).
  assert (K : size * (everc a c + 8 + b24 c * 32896) <= 65536 * 44904) by (clear -SZ K0 A9 R24; nia).
  assert (MU : mu <= size * 44904 + 2 ^ 18) by (clear -A6 K0 SZ A9 R24; nia).
  split; [clear -MU SZ; nia|].
  set (q2 := (mu + 2 ^ 18 - au) / size) in *.
  assert (Q2B : size * q2 <= mu + 2 ^ 18 - au) by (subst q2; clear -SZ A1; Z.div_mod_to_equations; nia).
  assert (Q2N : 0 <= q2) by (subst q2; apply Z.div_pos; clear -SZ A1; lia).
  assert (NF1 : nf <= au / size) by (clear -A7 A11 C0 Q1 Q2 R24 A10 NDp; nia).
  assert (AUQ : size * (au / size) = au) by (clear -A3 SZ; Z.div_mod_to_equations; nia).
  assert (SUM : size * (nf + q2) <= mu + 2 ^ 18) by (clear -Q2B NF1 AUQ SZ A1 Q2N C0; nia).
  assert (SUM2 : nf + q2 <= 44904 + 8192 + 8192).
  { assert (size * (nf + q2) <= size * (44904 + 16384)) by (clear -SUM MU SZ; nia). clear -H SZ. nia. }
  split; [clear -SUM2; lia|].
  unfold rg_num_freed in WFA. change (Z.of_nat (length (rg_free (get_region a c)))) with nf in WFA. fold mfa in WFA.
  assert (Q2S : q2 <= 18432).
  { assert (size * q2 <= 32 * 18432) by (clear -Q2B A12 SZ; lia). clear -H SZ Q2N. nia. }
  split; [clear -WFA Q2S Q2N; lia|].
  assert (CV : au / size <= 44904 + 8192).
  { assert (size * (au / size) <= size * (44904 + 8192)) by (rewrite AUQ; clear -A1 MU SZ; nia). clear -H SZ. nia. }
  clear -A5 CV. lia.
Qed.

Lemma refill_room_of_BI : forall E (Pq : list Z) (Dq : list batch) nd F a c,
  AWf E Pq Dq a -> BI nd F a -> 1 <= c <= kLargestClassID -> 0 <= as_nprim_ever a <= 12000 ->
  refill_room a c /\ room a c.
Proof.
  intros E Pq Dq nd F a c WF HBI Hc NP.
  pose proof (rooms_of_BI E Pq Dq nd F a c WF HBI Hc NP) as (R1 & R2 & R3 & R5). pose proof (M2_sharp_BI nd F a HBI) as M.
  split; [| exact R1].
  unfold refill_room. cbv zeta. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [| exact R5].
  unfold gapR, kBatchPages, kUserMapSize, kFreeArrayMapSize. clear -M NP. lia.
Qed.

End RC__1.
