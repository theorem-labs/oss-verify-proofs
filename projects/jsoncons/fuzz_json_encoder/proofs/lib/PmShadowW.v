(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIfaceA PmHeapIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition sbw_idx (n j : Z) : Prop := j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0).

Lemma sbw_idx_iff : forall n j, 0 <= n -> (sbw_idx n j <-> j < (n + 7) / 8).
Proof.
  intros n j Hn. unfold sbw_idx. pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as R.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as R7. split; intros H; lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_cont_tr : forall (M M' : word -> option byte) u n mid, 0 <= mid <= n ->
  (forall j v, 0 <= j -> sbw_idx n j -> byte_at M (S u + j) v -> byte_at M' (S u + j) v) ->
  shadow_cont M u n mid -> shadow_cont M' u n mid.
Proof.
  intros M M' u n mid Hm T (Z0 & P0 & F0).
  pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as R.
  pose proof (Z.div_mod mid 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mid 8 ltac:(lia)) as Rm.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as R7.
  pose proof (Z.div_mod (mid + 7) 8 ltac:(lia)) as Dm7. pose proof (Z.mod_pos_bound (mid + 7) 8 ltac:(lia)) as Rm7.
  split; [|split].
  - intros j Hj. apply T; [lia|unfold sbw_idx; lia|exact (Z0 j Hj)].
  - intros Hne. apply T; [lia|unfold sbw_idx; lia|exact (P0 Hne)].
  - intros j Hj. apply T; [lia|unfold sbw_idx; lia|exact (F0 j Hj)].
Qed.

(* [comment removed for export] *)
Lemma shadow_blk_w_tr : forall (M M' : word -> option byte) u n,
  (forall j v, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> byte_at M (S u + j) v -> byte_at M' (S u + j) v) ->
  shadow_blk_w M u n -> shadow_blk_w M' u n.
Proof. intros M M' u n T (mid & Hm & SC). exists mid. split; [exact Hm|]. exact (shadow_cont_tr M M' u n mid Hm T SC). Qed.

(* [comment removed for export] *)
Lemma shadow_blk_w_trB : forall (M M' : word -> option byte) u n,
  (forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> forall v, byte_at M (S u + j) v -> byte_at M' (S u + j) v) ->
  shadow_blk_w M u n -> shadow_blk_w M' u n.
Proof. intros M M' u n T. apply shadow_blk_w_tr. intros j v H0 Hj B. exact (T j H0 Hj v B). Qed.

(* [comment removed for export] *)
Lemma shadow_blk_w_eq : forall (M M' : word -> option byte) u n,
  (forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> M' (Z_to_bv 64 (S u + j)) = M (Z_to_bv 64 (S u + j))) ->
  shadow_blk_w M u n -> shadow_blk_w M' u n.
Proof. intros M M' u n E. apply shadow_blk_w_tr. intros j v H0 Hj B. unfold byte_at in *. rewrite (E j H0 Hj). exact B. Qed.

(* [comment removed for export] *)
Lemma shadow_blk_w_def : forall (M : word -> option byte) u n, shadow_blk_w M u n ->
  forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> exists v, byte_at M (S u + j) v.
Proof.
  intros M u n (mid & Hm & Z0 & P0 & F0) j Hj0 Hj.
  pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as R.
  pose proof (Z.div_mod mid 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mid 8 ltac:(lia)) as Rm.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as R7.
  pose proof (Z.div_mod (mid + 7) 8 ltac:(lia)) as Dm7. pose proof (Z.mod_pos_bound (mid + 7) 8 ltac:(lia)) as Rm7.
  destruct (Z_lt_ge_dec j (mid / 8)) as [Lo|Hi]; [eexists; exact (Z0 j ltac:(lia))|].
  destruct (Z_lt_ge_dec j ((mid + 7) / 8)) as [Lo2|Hi2].
  - assert (E : j = mid / 8) by lia. assert (Ne : mid mod 8 <> 0) by lia. rewrite E. eexists. exact (P0 Ne).
  - eexists. apply (F0 j). destruct Hj as [Hj|[Hj Hne]]; lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_blk_w_frame : forall (M M1 : word -> option byte) u n, 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shadow_blk_w M u n -> shadow_blk_w M1 u n.
Proof.
  intros M M1 u n Hu H8 Hn AG. apply shadow_blk_w_eq. intros j Hj0 Hj. apply AG. unfold in_shadow_of, S.
  pose proof (Z.div_mod u 8 ltac:(lia)) as DU. rewrite H8, Z.add_0_r in DU.
  pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as RN.
  assert (HI : u / 8 + j <= (u + n - 1) / 8). { apply Z.div_le_lower_bound; [lia|]. destruct Hj as [Hj|[Hj Hne]]; lia. }
  lia.
Qed.
