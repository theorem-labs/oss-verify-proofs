(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb BzLemmasT BzLemmasT2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Strategy 10 [cf_copy cf_accum cf_dup].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_set_cftab_cftab : forall d a b, d_set_cftab (d_set_cftab d a) b = d_set_cftab d b.
Proof. intros []; reflexivity. Qed.
Lemma d_set_cftab_id : forall d, d_set_cftab d (d_cftab d) = d.
Proof. intros []; reflexivity. Qed.
Lemma d_cftab_set_cftab : forall d a, d_cftab (d_set_cftab d a) = a.
Proof. intros []; reflexivity. Qed.
Lemma d_unzftab_set_cftab : forall d a, d_unzftab (d_set_cftab d a) = d_unzftab d.
Proof. intros []; reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition be_cf2 (d : dst) : zarr := cf_accum 256 1 (cf_copy 256 1 (d_unzftab d) (zset (d_cftab d) 0 0)).
Definition be_d1 (d : dst) : dst := d_set_cftab d (be_cf2 d).
(* [comment removed for export] *)
Definition dT (d : dst) : dst := d_set_state (d_set_cbcrc (d_set_out_ch (d_set_out_len d 0) 0) crc_init) BZ_X_OUTPUT.

(* [comment removed for export] *)
Definition be_fast (L : dsv) (d2 : dst) (s : dstrm) : dres :=
  let nblock := sv_nblock L in
  let cap := 100000 * d_bs100k d2 in
  let '(tt1, cf3) := tinv_fast (Z.to_nat nblock) 0 (d_tt d2) (d_cftab d2) in
  let d3 := d_set_cftab (d_set_tt d2 tt1) cf3 in
  let L3 := sv_set_i L nblock in
  let d4 := d_set_nused (d_set_tPos d3 (Z.shiftr (zget tt1 (d_origPtr d3)) 8)) 0 in
  let d5 := if d_rand d4 =? 0 then d4 else d_set_rTPos (d_set_rNToGo d4 0) 0 in
  if cap <=? d_tPos d5 then DRetNoSave 1 L3 d5 s else
  let w := zget tt1 (d_tPos d5) in
  let d6 := d_set_nused (d_set_tPos (d_set_k0 d5 (Z.land w 255)) (Z.shiftr w 8)) 1 in
  let d7 := if d_rand d6 =? 0 then d6
            else let d' := rand_upd d6 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
  DRet BZ_OK L3 d7 s.

(* [comment removed for export] *)
Definition be_small (L : dsv) (d2 : dst) (s : dstrm) : dres :=
  let nblock := sv_nblock L in
  let cap := 100000 * d_bs100k d2 in
  let d3 := d_set_cftabCopy d2 (cf_dup 257 0 (d_cftab d2) (d_cftabCopy d2)) in
  let d4 := tvec_small (Z.to_nat nblock) 0 d3 in
  let i0 := d_origPtr d4 in
  let j0 := get_ll d4 i0 in
  let '(i5, j5, d5) := prev_loop (S (Z.to_nat nblock)) i0 j0 d4 in
  let L5 := sv_set_j (sv_set_i L i5) j5 in
  let d6 := d_set_nused (d_set_tPos d5 (d_origPtr d5)) 0 in
  let d7 := if d_rand d6 =? 0 then d6 else d_set_rTPos (d_set_rNToGo d6 0) 0 in
  if cap <=? d_tPos d7 then DRetNoSave 1 L5 d7 s else
  let k0 := indexIntoF (d_tPos d7) (d_cftab d7) in
  let d8 := d_set_nused (d_set_tPos (d_set_k0 d7 k0) (get_ll d7 (d_tPos d7))) 1 in
  let d9 := if d_rand d8 =? 0 then d8
            else let d' := rand_upd d8 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
  DRet BZ_OK L5 d9 s.

Lemma block_end_eq : forall L d s,
  block_end L d s =
  let nblock := sv_nblock L in
  if (d_origPtr d <? 0) || (nblock <=? d_origPtr d) then DRet BZ_DATA_ERROR L d s else
  let i1 := unz_check 256 0 (d_unzftab d) nblock in
  if i1 <? 256 then DRet BZ_DATA_ERROR (sv_set_i L i1) d s else
  let i2 := cf_check1 257 0 (be_cf2 d) nblock in
  if i2 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i2) (be_d1 d) s else
  let i3 := cf_check2 256 1 (be_cf2 d) in
  if i3 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i3) (be_d1 d) s else
  if smallb (dT (be_d1 d)) then be_small L (dT (be_d1 d)) s else be_fast L (dT (be_d1 d)) s.
Proof. intros L d s. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_HFAST (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (be_fast L d s).
Definition K_HSMALL (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (be_small L d s).

(* [comment removed for export] *)
Definition K_T (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres :=
  if smallb (dT d) then K_HSMALL F L (dT d) s else K_HFAST F L (dT d) s.
(* [comment removed for export] *)
Definition K_L25 (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  let i3 := cf_check2 (Z.to_nat (257 - i)) i (d_cftab d) in
  if i3 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i3) d s else K_T F L d s.
(* [comment removed for export] *)
Definition K_L24 (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  let i2 := cf_check1 (Z.to_nat (257 - i)) i (d_cftab d) (sv_nblock L) in
  if i2 <? 257 then DRet BZ_DATA_ERROR (sv_set_i L i2) d s else K_L25 F L d s 1.
(* [comment removed for export] *)
Definition K_L23 (F : nat) (L : dsv) (d : dst) (s : dstrm) (k : Z) : dres :=
  K_L24 F L (d_set_cftab d (cf_accum (Z.to_nat (257 - k)) k (d_cftab d))) s 0.
(* [comment removed for export] *)
Definition K_L22 (F : nat) (L : dsv) (d : dst) (s : dstrm) (k : Z) : dres :=
  K_L23 F L (d_set_cftab d (cf_copy (Z.to_nat (257 - k)) k (d_unzftab d) (d_cftab d))) s 1.
(* [comment removed for export] *)
Definition K_L21 (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  let i1 := unz_check (Z.to_nat (256 - i)) i (d_unzftab d) (sv_nblock L) in
  if i1 <? 256 then DRet BZ_DATA_ERROR (sv_set_i L i1) d s
  else K_L22 F L (d_set_cftab d (zset (d_cftab d) 0 0)) s 1.

(* [comment removed for export] *)
Lemma K_HEOB_eq : forall F L d s,
  dgo F (block_end L d s) =
  if (d_origPtr d <? 0) || (sv_nblock L <=? d_origPtr d) then DRet BZ_DATA_ERROR L d s else K_L21 F L d s 0.
Proof.
  intros F L d s. rewrite block_end_eq. cbv zeta.
  destruct ((d_origPtr d <? 0) || (sv_nblock L <=? d_origPtr d)); [reflexivity|].
  unfold K_L21. rewrite Z.sub_0_r. change (Z.to_nat 256) with 256%nat.
  destruct (unz_check 256 0 (d_unzftab d) (sv_nblock L) <? 256); [reflexivity|].
  unfold K_L22, K_L23, K_L24, K_L25, K_T, K_HSMALL, K_HFAST, be_d1, be_cf2.
  rewrite !d_cftab_set_cftab, !d_unzftab_set_cftab, !d_set_cftab_cftab.
  change (Z.to_nat (257 - 1)) with 256%nat. rewrite !Z.sub_0_r. change (Z.to_nat 257) with 257%nat.
  rewrite dgo_if. destruct (cf_check1 257 0 _ _ <? 257); [reflexivity|].
  rewrite dgo_if. destruct (cf_check2 256 1 _ <? 257); [reflexivity|].
  rewrite dgo_if. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma unz_check_S : forall n i unz nb,
  unz_check (S n) i unz nb = (let u := zget unz i in if (u <? 0) || (nb <? u) then i else unz_check n (i + 1) unz nb).
Proof. reflexivity. Qed.

Lemma K_L21_pass : forall F L d s i, 0 <= i < 256 ->
  0 <= zget (d_unzftab d) i <= sv_nblock L ->
  K_L21 F L d s i = K_L21 F L d s (i + 1).
Proof.
  intros F L d s i Hi Hu. unfold K_L21.
  replace (Z.to_nat (256 - i)) with (S (Z.to_nat (256 - (i + 1)))) by lia. rewrite unz_check_S. cbv zeta.
  replace ((zget (d_unzftab d) i <? 0) || (sv_nblock L <? zget (d_unzftab d) i)) with false by (symmetry; blia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma K_L21_exit : forall F L d s, K_L21 F L d s 256 = K_L22 F L (d_set_cftab d (zset (d_cftab d) 0 0)) s 1.
Proof. intros. unfold K_L21. rewrite Z.sub_diag. cbn [Z.to_nat unz_check]. rewrite Z.ltb_irrefl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_L22_step : forall F L d s k, 1 <= k <= 256 ->
  K_L22 F L d s k = K_L22 F L (d_set_cftab d (zset (d_cftab d) k (zget (d_unzftab d) (k - 1)))) s (k + 1).
Proof.
  intros F L d s k Hk. unfold K_L22.
  replace (Z.to_nat (257 - k)) with (S (Z.to_nat (257 - (k + 1)))) by lia. cbn [cf_copy].
  rewrite d_cftab_set_cftab, d_unzftab_set_cftab, d_set_cftab_cftab. reflexivity.
Qed.
Lemma K_L22_exit : forall F L d s, K_L22 F L d s 257 = K_L23 F L d s 1.
Proof. intros. unfold K_L22. rewrite Z.sub_diag. cbn [Z.to_nat cf_copy]. rewrite d_set_cftab_id. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_L23_step : forall F L d s k, 1 <= k <= 256 ->
  K_L23 F L d s k = K_L23 F L (d_set_cftab d (zset (d_cftab d) k (zget (d_cftab d) k + zget (d_cftab d) (k - 1)))) s (k + 1).
Proof.
  intros F L d s k Hk. unfold K_L23.
  replace (Z.to_nat (257 - k)) with (S (Z.to_nat (257 - (k + 1)))) by lia. cbn [cf_accum].
  rewrite d_cftab_set_cftab, d_set_cftab_cftab. reflexivity.
Qed.
Lemma K_L23_exit : forall F L d s, K_L23 F L d s 257 = K_L24 F L d s 0.
Proof. intros. unfold K_L23. rewrite Z.sub_diag. cbn [Z.to_nat cf_accum]. rewrite d_set_cftab_id. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cf_check1_S : forall n i cf nb,
  cf_check1 (S n) i cf nb = (let c := zget cf i in if (c <? 0) || (nb <? c) then i else cf_check1 n (i + 1) cf nb).
Proof. reflexivity. Qed.
Lemma K_L24_pass : forall F L d s i, 0 <= i < 257 ->
  0 <= zget (d_cftab d) i <= sv_nblock L ->
  K_L24 F L d s i = K_L24 F L d s (i + 1).
Proof.
  intros F L d s i Hi Hc. unfold K_L24.
  replace (Z.to_nat (257 - i)) with (S (Z.to_nat (257 - (i + 1)))) by lia. rewrite cf_check1_S. cbv zeta.
  replace ((zget (d_cftab d) i <? 0) || (sv_nblock L <? zget (d_cftab d) i)) with false by (symmetry; blia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma K_L24_exit : forall F L d s, K_L24 F L d s 257 = K_L25 F L d s 1.
Proof. intros. unfold K_L24. rewrite Z.sub_diag. cbn [Z.to_nat cf_check1]. rewrite Z.ltb_irrefl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cf_check2_S : forall n i cf,
  cf_check2 (S n) i cf = (if zget cf i <? zget cf (i - 1) then i else cf_check2 n (i + 1) cf).
Proof. reflexivity. Qed.
Lemma K_L25_pass : forall F L d s i, 1 <= i < 257 ->
  zget (d_cftab d) (i - 1) <= zget (d_cftab d) i ->
  K_L25 F L d s i = K_L25 F L d s (i + 1).
Proof.
  intros F L d s i Hi Hc. unfold K_L25.
  replace (Z.to_nat (257 - i)) with (S (Z.to_nat (257 - (i + 1)))) by lia. rewrite cf_check2_S.
  replace (zget (d_cftab d) i <? zget (d_cftab d) (i - 1)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma K_L25_exit : forall F L d s, K_L25 F L d s 257 = K_T F L d s.
Proof. intros. unfold K_L25. rewrite Z.sub_diag. cbn [Z.to_nat cf_check2]. rewrite Z.ltb_irrefl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_T_small : forall F L d s, d_small d <> 0 -> K_T F L d s = K_HSMALL F L (dT d) s.
Proof. intros F L d s H. unfold K_T. rewrite smallb_true; [reflexivity|]. destruct d; exact H. Qed.
Lemma K_T_fast : forall F L d s, d_small d = 0 -> K_T F L d s = K_HFAST F L (dT d) s.
Proof. intros F L d s H. unfold K_T. rewrite smallb_false; [reflexivity|]. destruct d; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cf_copied (unz cf : zarr) (k : Z) : Prop :=
  zget cf 0 = 0 /\ forall j, 1 <= j < k -> zget cf j = zget unz (j - 1).
Lemma cf_copied_1 : forall unz cf, cf_copied unz (zset cf 0 0) 1.
Proof. intros. split; [apply zget_zset_same| intros; lia]. Qed.
Lemma cf_copied_step : forall unz cf k, 1 <= k -> cf_copied unz cf k -> cf_copied unz (zset cf k (zget unz (k - 1))) (k + 1).
Proof.
  intros unz cf k Hk [C0 C]. split.
  - rewrite zget_zset_other by lia. exact C0.
  - intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j k) as [->|]; [reflexivity|]. apply C. lia.
Qed.
(* [comment removed for export] *)
Definition cf_summed (unz cf : zarr) (k : Z) : Prop :=
  (forall j, 0 <= j < k -> zget cf j = psum (zget unz) j) /\ (forall j, k <= j <= 256 -> zget cf j = zget unz (j - 1)).
Lemma cf_summed_1 : forall unz cf, cf_copied unz cf 257 -> cf_summed unz cf 1.
Proof.
  intros unz cf [C0 C]. split.
  - intros j Hj. replace j with 0 by lia. rewrite C0. reflexivity.
  - intros j Hj. apply C. lia.
Qed.
(* [comment removed for export] *)
Lemma cf_summed_val : forall unz cf k, 1 <= k <= 256 -> cf_summed unz cf k ->
  zget cf k + zget cf (k - 1) = psum (zget unz) k.
Proof.
  intros unz cf k Hk [P C]. rewrite C, P by lia. replace k with (k - 1 + 1) at 3 by lia. rewrite psum_succ by lia. lia.
Qed.
Lemma cf_summed_step : forall unz cf k, 1 <= k <= 256 -> cf_summed unz cf k ->
  cf_summed unz (zset cf k (zget cf k + zget cf (k - 1))) (k + 1).
Proof.
  intros unz cf k Hk CS. pose proof (cf_summed_val unz cf k Hk CS) as V. destruct CS as [P C]. split.
  - intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j k) as [->|]; [exact V| apply P; lia].
  - intros j Hj. rewrite zget_zset_other by lia. apply C. lia.
Qed.
Lemma cf_summed_exit : forall unz cf, cf_summed unz cf 257 -> forall j, 0 <= j <= 256 -> zget cf j = psum (zget unz) j.
Proof. intros unz cf [P _] j Hj. apply P. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eobF (L : dsv) (d : dst) : Prop :=
  0 <= sv_nblock L <= 100000 * d_bs100k d /\ sv_nblock L <= 900000 /\
  (forall i, 0 <= i < sv_nblock L -> 0 <= bsym d i < 256) /\
  hist_ok (zget (d_unzftab d)) (bsym d) (Z.to_nat (sv_nblock L)) /\
  hdr_ok d.
(* [comment removed for export] *)
Definition cfps (d : dst) : Prop := forall j, 0 <= j <= 256 -> zget (d_cftab d) j = psum (zget (d_unzftab d)) j.
(* [comment removed for export] *)
Definition tset (d : dst) : Prop := d_state d = BZ_X_OUTPUT /\ d_out_len d = 0 /\ d_out_ch d = 0 /\ d_cbcrc d = crc_init.

(* [comment removed for export] *)
Definition dinv_L21 (L : dsv) (d : dst) (i : Z) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ 0 <= i <= 256.
Definition dinv_L22 (L : dsv) (d : dst) (k : Z) : Prop :=
  eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ 1 <= k <= 257 /\ cf_copied (d_unzftab d) (d_cftab d) k.
Definition dinv_L23 (L : dsv) (d : dst) (k : Z) : Prop :=
  eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ 1 <= k <= 257 /\ cf_summed (d_unzftab d) (d_cftab d) k.
Definition dinv_L24 (L : dsv) (d : dst) (i : Z) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ 0 <= i <= 257 /\ cfps d.
Definition dinv_L25 (L : dsv) (d : dst) (i : Z) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ 1 <= i <= 257 /\ cfps d.
Definition dinv_T (L : dsv) (d : dst) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ cfps d.
(* [comment removed for export] *)
Definition dinv_HFAST (L : dsv) (d : dst) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ cfps d /\ tset d /\ d_small d = 0.
Definition dinv_HSMALL (L : dsv) (d : dst) : Prop := eobF L d /\ 0 <= d_origPtr d < sv_nblock L /\ cfps d /\ tset d /\ d_small d = 1.

(* [comment removed for export] *)
Lemma eobF_frame : forall L d d', eobF L d ->
  d_bs100k d' = d_bs100k d -> d_small d' = d_small d -> d_tt d' = d_tt d -> d_ll16 d' = d_ll16 d -> d_unzftab d' = d_unzftab d ->
  d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d ->
  eobF L d'.
Proof.
  (intros L d d'; cps_intros (A & B & C & D & E); intros E1 E2 E3 E4 E5 E6 E7 E8). unfold eobF, hdr_ok in *. rewrite E1, E5, E6, E7, E8.
  pose proof (bsym_frame d d' E2 E3 E4) as BS.
  split; [exact A|]. split; [exact B|]. split; [intros i Hi; rewrite BS; apply C; exact Hi|]. split; [| exact E].
  intros b Hb. rewrite (occ_ext _ (bsym d)) by (intros; apply BS). apply D. exact Hb.
Qed.
Lemma eobF_set_cftab : forall L d a, eobF L d -> eobF L (d_set_cftab d a).
Proof. intros L d a H. apply (eobF_frame L d); [exact H | ..]; destruct d; reflexivity. Qed.
Lemma eobF_dT : forall L d, eobF L d -> eobF L (dT d).
Proof. intros L d H. apply (eobF_frame L d); [exact H | ..]; destruct d; reflexivity. Qed.
Lemma cfps_dT : forall d, cfps d -> cfps (dT d).
Proof. intros d H. unfold cfps in *. destruct d; exact H. Qed.
Lemma tset_dT : forall d, tset (dT d).
Proof. intros d. unfold tset. destruct d; repeat split; reflexivity. Qed.
Lemma dT_origPtr : forall d, d_origPtr (dT d) = d_origPtr d. Proof. intros []; reflexivity. Qed.
Lemma dT_small : forall d, d_small (dT d) = d_small d. Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Lemma eobF_unz_range : forall L d c, eobF L d -> 0 <= c < 256 -> 0 <= zget (d_unzftab d) c <= sv_nblock L.
Proof.
  (intros L d c; cps_intros (A & _ & C & D & _); intros Hc).
  pose proof (unz_range (bsym d) (zget (d_unzftab d)) (Z.to_nat (sv_nblock L)) D c Hc). lia.
Qed.
Lemma eobF_psum_range : forall L d j, eobF L d -> 0 <= j <= 256 -> 0 <= psum (zget (d_unzftab d)) j <= sv_nblock L.
Proof.
  (intros L d j; cps_intros (A & _ & C & D & _); intros Hj).
  pose proof (psum_range (bsym d) (zget (d_unzftab d)) (Z.to_nat (sv_nblock L)) ltac:(intros k Hk; apply C; lia) D j Hj). lia.
Qed.

Lemma dinv_HFAST_T : forall L d, eobF L d -> 0 <= d_origPtr d < sv_nblock L -> cfps d -> d_small d = 0 -> dinv_HFAST L (dT d).
Proof.
  intros L d E O C SM. unfold dinv_HFAST. rewrite dT_origPtr, dT_small.
  split; [apply eobF_dT; exact E|]. split; [exact O|]. split; [apply cfps_dT; exact C|]. split; [apply tset_dT| exact SM].
Qed.
Lemma dinv_HSMALL_T : forall L d, eobF L d -> 0 <= d_origPtr d < sv_nblock L -> cfps d -> d_small d = 1 -> dinv_HSMALL L (dT d).
Proof.
  intros L d E O C SM. unfold dinv_HSMALL. rewrite dT_origPtr, dT_small.
  split; [apply eobF_dT; exact E|]. split; [exact O|]. split; [apply cfps_dT; exact C|]. split; [apply tset_dT| exact SM].
Qed.

(* [comment removed for export] *)
Lemma cf_summed_step' : forall unz cf k v, 1 <= k <= 256 -> cf_summed unz cf k -> v = zget cf k + zget cf (k - 1) ->
  cf_summed unz (zset cf k v) (k + 1).
Proof. intros unz cf k v Hk CS ->. apply cf_summed_step; assumption. Qed.
Lemma cf_copied_step' : forall unz cf k v, 1 <= k -> cf_copied unz cf k -> v = zget unz (k - 1) ->
  cf_copied unz (zset cf k v) (k + 1).
Proof. intros unz cf k v Hk CC ->. apply cf_copied_step; assumption. Qed.

(* [comment removed for export] *)
Lemma eobF_of_ML : forall L d, dinv_ML L d -> eobF L d.
Proof.
  (intros L d; cps_intros (AL & GR & _ & _ & (B1 & B2 & B3) & _)). unfold eobF.
  pose proof (alpha_ok_hdr L d AL) as HDR.
  assert (NBL : 0 <= sv_nblock L <= 900000) by (unfold alpha_ok in AL; tauto).
  cps_destruct GR as (_ & _ & _ & _ & NBM). rewrite NBM in B1.
  split; [exact B1|]. split; [lia|]. split; [exact B2|]. split; [exact B3| exact HDR].
Qed.
