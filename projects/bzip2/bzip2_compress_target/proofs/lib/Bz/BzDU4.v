(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zget_clear256 : forall n k a i,
  zget (clear256 n k a) i = if (k <=? i) && (i <? k + Z.of_nat n) then 0 else zget a i.
Proof.
  induction n as [|n IH]; intros k a i; cbn [clear256].
  - destruct (Z.leb_spec k i), (Z.ltb_spec i (k + Z.of_nat 0)); cbn; try reflexivity; exfalso; cbn in *; lia.
  - rewrite IH. rewrite zget_zset. rewrite Nat2Z.inj_succ.
    destruct (Z.leb_spec (k + 1) i), (Z.ltb_spec i (k + 1 + Z.of_nat n)), (Z.eqb_spec i k),
             (Z.leb_spec k i), (Z.ltb_spec i (k + Z.succ (Z.of_nat n))); cbn; try reflexivity; exfalso; lia.
Qed.
Lemma zget_clear256_in : forall a i, 0 <= i < 256 -> zget (clear256 256 0 a) i = 0.
Proof.
  intros a i Hi. rewrite zget_clear256.
  replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i <? 0 + Z.of_nat 256) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map2_outer_fuel : forall n m i L d s, (Z.max 1 (17 - i) <= Z.of_nat n) -> (Z.max 1 (17 - i) <= Z.of_nat m) ->
  map2_outer n i L d s = map2_outer m i L d s.
Proof.
  induction n as [|n IH]; intros m i L d s Hn Hm; [cbn in Hn; lia|].
  destruct m as [|m]; [cbn in Hm; lia|]. cbn [map2_outer].
  destruct (Z.leb_spec 16 i); [reflexivity|].
  destruct (negb (zget (d_inUse16 d) i =? 0)); [reflexivity|].
  apply IH; rewrite Nat2Z.inj_succ in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mm_fin (L : dsv) (d : dst) (s : dstrm) : dres :=
  let L1 := sv_set_i L 16 in
  if d_nInUse d =? 0 then DRet BZ_DATA_ERROR L1 d s
  else DGo 30 (sv_set_alphaSize L1 (d_nInUse d + 2)) d s.

(* [comment removed for export] *)
Definition K_L4M (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  let '(s2u, n) := mkmaps (Z.to_nat (256 - i)) i (d_inUse d) (d_s2u d) (d_nInUse d) in
  dgo F (mm_fin L (d_set_nInUse (d_set_s2u d s2u) n) s).

(* [comment removed for export] *)
Definition K_HMK (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres :=
  dgo F (mm_fin L (makeMaps_d d) s).

(* [comment removed for export] *)
Definition K_L4O (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  dgo F (map2_outer (Z.to_nat (17 - i)) i L d s).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_set_s2u_nInUse_id : forall d, d_set_nInUse (d_set_s2u d (d_s2u d)) (d_nInUse d) = d.
Proof. intros []; reflexivity. Qed.
Lemma d_set_s2u_nInUse_twice : forall d a n a' n',
  d_set_nInUse (d_set_s2u (d_set_nInUse (d_set_s2u d a) n) a') n' = d_set_nInUse (d_set_s2u d a') n'.
Proof. intros []; reflexivity. Qed.
Lemma d_inUse_set_s2u_nInUse : forall d a n, d_inUse (d_set_nInUse (d_set_s2u d a) n) = d_inUse d.
Proof. intros []; reflexivity. Qed.
Lemma d_s2u_set_s2u_nInUse : forall d a n, d_s2u (d_set_nInUse (d_set_s2u d a) n) = a.
Proof. intros []; reflexivity. Qed.
Lemma d_nInUse_set_s2u_nInUse : forall d a n, d_nInUse (d_set_nInUse (d_set_s2u d a) n) = n.
Proof. intros []; reflexivity. Qed.
Lemma d_inUse_set_nInUse : forall d n, d_inUse (d_set_nInUse d n) = d_inUse d.
Proof. intros []; reflexivity. Qed.
Lemma d_s2u_set_nInUse : forall d n, d_s2u (d_set_nInUse d n) = d_s2u d.
Proof. intros []; reflexivity. Qed.
Lemma d_nInUse_set_nInUse : forall d n, d_nInUse (d_set_nInUse d n) = n.
Proof. intros []; reflexivity. Qed.
Lemma d_set_s2u_nInUse_over : forall d n0 a n,
  d_set_nInUse (d_set_s2u (d_set_nInUse d n0) a) n = d_set_nInUse (d_set_s2u d a) n.
Proof. intros []; reflexivity. Qed.
Lemma makeMaps_d_eq : forall d,
  makeMaps_d d = let '(s2u, n) := mkmaps 256 0 (d_inUse d) (d_s2u d) 0 in d_set_nInUse (d_set_s2u d s2u) n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma edge_28 : forall F v L d s,
  dgo F (gb_after 28 v L d s) =
  if sv_i L + 1 <? 16
  then drun F 28 (sv_set_i L (sv_i L + 1)) (d_set_inUse16 d (zset (d_inUse16 d) (sv_i L) (if v =? 1 then 1 else 0))) s
  else K_L4O F (sv_set_i L 256)
         (d_set_inUse (d_set_inUse16 d (zset (d_inUse16 d) (sv_i L) (if v =? 1 then 1 else 0)))
                      (clear256 256 0 (d_inUse d))) s 0.
Proof.
  intros F v L d s. rewrite gb_after_28. cbv zeta. rewrite dgo_if, dgo_DGo. unfold K_L4O.
  destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma edge_29 : forall F v L d s, 0 <= sv_i L < 16 ->
  dgo F (gb_after 29 v L d s) =
  if sv_j L + 1 <? 16
  then drun F 29 (sv_set_j L (sv_j L + 1)) (if v =? 1 then d_set_inUse d (zset (d_inUse d) (sv_i L * 16 + sv_j L) 1) else d) s
  else K_L4O F (sv_set_j L (sv_j L + 1)) (if v =? 1 then d_set_inUse d (zset (d_inUse d) (sv_i L * 16 + sv_j L) 1) else d) s
         (sv_i L + 1).
Proof.
  intros F v L d s Hi. rewrite gb_after_29. cbv zeta. rewrite dgo_if, dgo_DGo. unfold K_L4O.
  rewrite (map2_outer_fuel 17 (Z.to_nat (17 - (sv_i L + 1))) (sv_i L + 1)) by lia. reflexivity.
Qed.

Lemma K_L4O_step : forall F L d s i, 0 <= i < 16 ->
  K_L4O F L d s i =
  if negb (zget (d_inUse16 d) i =? 0) then drun F 29 (sv_set_j (sv_set_i L i) 0) d s
  else K_L4O F L d s (i + 1).
Proof.
  intros F L d s i Hi. unfold K_L4O.
  replace (Z.to_nat (17 - i)) with (S (Z.to_nat (17 - (i + 1)))) by lia. cbn [map2_outer].
  replace (16 <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite dgo_if, dgo_DGo. reflexivity.
Qed.
Lemma K_L4O_set : forall F L d s i, 0 <= i < 16 -> zget (d_inUse16 d) i <> 0 ->
  K_L4O F L d s i = drun F 29 (sv_set_j (sv_set_i L i) 0) d s.
Proof.
  intros F L d s i Hi Hz. rewrite K_L4O_step by exact Hi.
  replace (zget (d_inUse16 d) i =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). reflexivity.
Qed.
Lemma K_L4O_clear : forall F L d s i, 0 <= i < 16 -> zget (d_inUse16 d) i = 0 ->
  K_L4O F L d s i = K_L4O F L d s (i + 1).
Proof. intros F L d s i Hi Hz. rewrite K_L4O_step by exact Hi. rewrite Hz. reflexivity. Qed.

Lemma K_L4O_exit : forall F L d s, K_L4O F L d s 16 = K_HMK F L d s.
Proof.
  intros F L d s. unfold K_L4O, K_HMK, mm_fin. change (Z.to_nat (17 - 16)) with 1%nat. cbn [map2_outer].
  change (16 <=? 16) with true. cbv iota. rewrite dgo_if, dgo_DGo, dgo_DRet. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma K_HMK_L4M : forall F L d s, K_HMK F L d s = K_L4M F L (d_set_nInUse d 0) s 0.
Proof.
  intros F L d s. unfold K_HMK, K_L4M. rewrite makeMaps_d_eq. change (Z.to_nat (256 - 0)) with 256%nat.
  rewrite d_inUse_set_nInUse, d_s2u_set_nInUse, d_nInUse_set_nInUse.
  destruct (mkmaps 256 0 _ _ 0) as [a n]. rewrite d_set_s2u_nInUse_over. reflexivity.
Qed.

Lemma K_L4M_step : forall F L d s i, 0 <= i < 256 ->
  K_L4M F L d s i =
  if negb (zget (d_inUse d) i =? 0)
  then K_L4M F L (d_set_nInUse (d_set_s2u d (zset (d_s2u d) (d_nInUse d) i)) (d_nInUse d + 1)) s (i + 1)
  else K_L4M F L d s (i + 1).
Proof.
  intros F L d s i Hi. unfold K_L4M.
  replace (Z.to_nat (256 - i)) with (S (Z.to_nat (256 - (i + 1)))) by lia. cbn [mkmaps].
  rewrite d_inUse_set_s2u_nInUse, d_s2u_set_s2u_nInUse, d_nInUse_set_s2u_nInUse.
  destruct (negb (zget (d_inUse d) i =? 0)); [|reflexivity].
  destruct (mkmaps _ _ _ _ _) as [a n]. rewrite d_set_s2u_nInUse_twice. reflexivity.
Qed.
Lemma K_L4M_set : forall F L d s i, 0 <= i < 256 -> zget (d_inUse d) i <> 0 ->
  K_L4M F L d s i = K_L4M F L (d_set_nInUse (d_set_s2u d (zset (d_s2u d) (d_nInUse d) i)) (d_nInUse d + 1)) s (i + 1).
Proof.
  intros F L d s i Hi Hz. rewrite K_L4M_step by exact Hi.
  replace (zget (d_inUse d) i =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). reflexivity.
Qed.
Lemma K_L4M_skip : forall F L d s i, 0 <= i < 256 -> zget (d_inUse d) i = 0 ->
  K_L4M F L d s i = K_L4M F L d s (i + 1).
Proof. intros F L d s i Hi Hz. rewrite K_L4M_step by exact Hi. rewrite Hz. reflexivity. Qed.

Lemma K_L4M_exit : forall F L d s, K_L4M F L d s 256 = dgo F (mm_fin L d s).
Proof.
  intros F L d s. unfold K_L4M. change (Z.to_nat (256 - 256)) with 0%nat. cbn [mkmaps].
  rewrite d_set_s2u_nInUse_id. reflexivity.
Qed.
Lemma K_L4M_exit_ret : forall F L d s, d_nInUse d = 0 ->
  K_L4M F L d s 256 = DRet BZ_DATA_ERROR (sv_set_i L 16) d s.
Proof. intros F L d s Hn. rewrite K_L4M_exit. unfold mm_fin. rewrite Hn. cbn [Z.eqb]. apply dgo_DRet. Qed.
Lemma K_L4M_exit_go : forall F L d s, d_nInUse d <> 0 ->
  K_L4M F L d s 256 = drun F 30 (sv_set_alphaSize (sv_set_i L 16) (d_nInUse d + 2)) d s.
Proof.
  intros F L d s Hn. rewrite K_L4M_exit. unfold mm_fin.
  replace (d_nInUse d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn). apply dgo_DGo.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in16_ok (d : dst) : Prop := forall k, 0 <= k < 16 -> 0 <= zget (d_inUse16 d) k <= 1.
Definition inUse_ok (d : dst) : Prop := forall k, 0 <= k < 256 -> 0 <= zget (d_inUse d) k <= 1.

(* [comment removed for export] *)
Lemma inUse_ok_clear : forall d iu, inUse_ok (d_set_inUse d (clear256 256 0 iu)).
Proof. intros d iu k Hk. destruct d. cbn -[clear256]. rewrite zget_clear256_in by exact Hk. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma inUse_ok_set1' : forall d a k, (forall j, 0 <= j < 256 -> 0 <= zget a j <= 1) ->
  inUse_ok (d_set_inUse d (zset a k 1)).
Proof.
  intros d a k H j Hj. destruct d. cbn. rewrite zget_zset.
  destruct (Z.eqb_spec j k); [lia|]. apply H. exact Hj.
Qed.
Lemma in16_ok_frame_inUse : forall d a, in16_ok d -> in16_ok (d_set_inUse d a).
Proof. intros [] a H; exact H. Qed.
Lemma inUse_ok_frame_s2u : forall d a n, inUse_ok d -> inUse_ok (d_set_nInUse (d_set_s2u d a) n).
Proof. intros [] a n H; exact H. Qed.

(* [comment removed for export] *)
Definition dinv_HMAP2 (L : dsv) (d : dst) : Prop :=
  nb_ok L /\ hdr_ok d /\ 0 <= sv_i L < 16 /\ 0 <= sv_j L < 16 /\ in16_ok d /\ inUse_ok d.
(* [comment removed for export] *)
Definition dinv_L4O (L : dsv) (d : dst) (i : Z) : Prop :=
  nb_ok L /\ hdr_ok d /\ 0 <= i <= 16 /\ in16_ok d /\ inUse_ok d /\ d_state d <> 2.
(* [comment removed for export] *)
Definition dinv_HMK (L : dsv) (d : dst) : Prop := nb_ok L /\ hdr_ok d /\ inUse_ok d /\ d_state d <> 2.
(* [comment removed for export] *)
Definition dinv_L4M (L : dsv) (d : dst) (i : Z) : Prop :=
  nb_ok L /\ hdr_ok d /\ inUse_ok d /\ 0 <= i <= 256 /\ 0 <= d_nInUse d <= i /\ d_state d <> 2.

(* [comment removed for export] *)
Lemma hdr_ok_frame : forall d d', hdr_ok d ->
  d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d -> hdr_ok d'.
Proof. intros d d' H E1 E2 E3. unfold hdr_ok in *. rewrite E1, E2, E3. exact H. Qed.
