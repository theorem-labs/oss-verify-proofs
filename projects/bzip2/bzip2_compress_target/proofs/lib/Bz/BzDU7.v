(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU4 BzDU6 BzDUM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM.   (* [comment removed for export] *)
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
Definition zrow (a : zarr) (off : Z) : Z -> Z := fun i => zget a (off + i).

(* [comment removed for export] *)
Lemma zrow_zset_pt : forall a off k v i, zrow (zset a (off + k) v) off i = zfupd (zrow a off) k v i.
Proof.
  intros a off k v i. unfold zrow. rewrite zget_zset, zfupd_eq.
  destruct (Z.eqb_spec (off + i) (off + k)), (Z.eqb_spec i k); try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Definition feq (f g : Z -> Z) : Prop := forall i, f i = g i.
Lemma feq_set : forall a off f k v v', feq (zrow a off) f -> v = v' ->
  feq (zrow (zset a (off + k) v) off) (zfupd f k v').
Proof. intros a off f k v v' H <- i. rewrite zrow_zset_pt, !zfupd_eq, (H i). reflexivity. Qed.
Lemma feq_at : forall a off f k, feq (zrow a off) f -> zget a (off + k) = f k.
Proof. intros a off f k H. exact (H k). Qed.

Lemma bridge_permJ : forall n j i len perm off pp (lenf permf : Z -> Z),
  feq (zrow len off) lenf -> feq (zrow perm off) permf ->
  let '(p1, pp1) := hbd_permJ n j i len perm off pp in
  let '(p2, pp2) := BzModel.hb_permJ lenf i j n permf pp in
  feq (zrow p1 off) p2 /\ pp1 = pp2 /\ pp <= pp1 /\
  (forall k, (k < off + pp \/ off + pp1 <= k) -> zget p1 k = zget perm k).
Proof.
  induction n as [|n IH]; intros j i len perm off pp lenf permf HL HP; cbn [hbd_permJ BzModel.hb_permJ].
  - split; [exact HP|]. split; [reflexivity|]. split; [lia|]. intros; reflexivity.
  - unfold zrow in HL. rewrite <- (HL j).
    destruct (zget len (off + j) =? i) eqn:E.
    + pose proof (feq_set perm off permf pp j j HP eq_refl) as HP'.
      specialize (IH (j + 1) i len (zset perm (off + pp) j) off (pp + 1) lenf (zfupd permf pp j) HL HP').
      destruct (hbd_permJ n (j + 1) i len (zset perm (off + pp) j) off (pp + 1)) as [p1 pp1].
      destruct (BzModel.hb_permJ lenf i (j + 1) n (zfupd permf pp j) (pp + 1)) as [p2 pp2].
      cps_destruct IH as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [lia|].
      intros k Hk. rewrite F4 by lia. rewrite zget_zset.
      destruct (Z.eqb_spec k (off + pp)); [exfalso; lia| reflexivity].
    + specialize (IH (j + 1) i len perm off pp lenf permf HL HP).
      destruct (hbd_permJ n (j + 1) i len perm off pp) as [p1 pp1].
      destruct (BzModel.hb_permJ lenf i (j + 1) n permf pp) as [p2 pp2].
      cps_destruct IH as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [lia|].
      intros k Hk. apply F4; lia.
Qed.

Lemma bridge_permI : forall n i len perm off pp alpha (lenf permf : Z -> Z),
  feq (zrow len off) lenf -> feq (zrow perm off) permf ->
  let '(p1, pp1) := hbd_permI n i len perm off pp alpha in
  let '(p2, pp2) := BzModel.hb_permI lenf alpha i n permf pp in
  feq (zrow p1 off) p2 /\ pp1 = pp2 /\ pp <= pp1 /\
  (forall k, (k < off + pp \/ off + pp1 <= k) -> zget p1 k = zget perm k).
Proof.
  induction n as [|n IH]; intros i len perm off pp alpha lenf permf HL HP; cbn [hbd_permI BzModel.hb_permI].
  - split; [exact HP|]. split; [reflexivity|]. split; [lia|]. intros; reflexivity.
  - pose proof (bridge_permJ (Z.to_nat alpha) 0 i len perm off pp lenf permf HL HP) as J.
    destruct (hbd_permJ (Z.to_nat alpha) 0 i len perm off pp) as [pa ppa].
    destruct (BzModel.hb_permJ lenf i 0 (Z.to_nat alpha) permf pp) as [pb ppb]. cbn [fst snd].
    cps_destruct J as (J1 & J2 & J3 & J4). subst ppb.
    specialize (IH (i + 1) len pa off ppa alpha lenf pb HL J1).
    destruct (hbd_permI n (i + 1) len pa off ppa alpha) as [p1 pp1].
    destruct (BzModel.hb_permI lenf alpha (i + 1) n pb ppa) as [p2 pp2].
    cps_destruct IH as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [lia|].
    intros k Hk. rewrite F4 by lia. apply J4. lia.
Qed.

Lemma bridge_zero : forall n i a off (f : Z -> Z), feq (zrow a off) f ->
  feq (zrow (hbd_zero n i a off) off) (fill0 f i n) /\
  (forall k, (k < off + i \/ off + i + Z.of_nat n <= k) -> zget (hbd_zero n i a off) k = zget a k).
Proof.
  induction n as [|n IH]; intros i a off f HF; cbn [hbd_zero fill0].
  - split; [exact HF|]. intros; reflexivity.
  - pose proof (feq_set a off f i 0 0 HF eq_refl) as HF'.
    destruct (IH (i + 1) (zset a (off + i) 0) off (zfupd f i 0) HF') as [F1 F2].
    split; [exact F1|]. intros k Hk. rewrite F2 by lia. rewrite zget_zset.
    destruct (Z.eqb_spec k (off + i)); [exfalso; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma bridge_count : forall n i len base off (lenf basef : Z -> Z),
  feq (zrow len off) lenf -> feq (zrow base off) basef ->
  (forall j, i <= j < i + Z.of_nat n -> 0 <= zget len (off + j) + 1 < 258) ->
  feq (zrow (hbd_count n i len base off) off) (hb_count lenf i n basef) /\
  (forall k, (k < off \/ off + 258 <= k) -> zget (hbd_count n i len base off) k = zget base k).
Proof.
  induction n as [|n IH]; intros i len base off lenf basef HL HB HR; cbn [hbd_count hb_count].
  - split; [exact HB|]. intros; reflexivity.
  - unfold zincr. rewrite <- (feq_at len off lenf i HL).
    replace (off + zget len (off + i) + 1) with (off + (zget len (off + i) + 1)) by lia.
    pose proof (feq_set base off basef (zget len (off + i) + 1) (zget base (off + (zget len (off + i) + 1)) + 1)
                  (basef (zget len (off + i) + 1) + 1) HB ltac:(rewrite (feq_at base off basef _ HB); reflexivity)) as HB'.
    destruct (IH (i + 1) len _ off lenf _ HL HB' ltac:(intros; apply HR; lia)) as [F1 F2].
    split; [exact F1|]. intros k Hk. rewrite F2 by exact Hk. rewrite zget_zset.
    pose proof (HR i ltac:(lia)).
    destruct (Z.eqb_spec k (off + (zget len (off + i) + 1))); [exfalso; lia| reflexivity].
Qed.

Lemma bridge_accum : forall n i base off (basef : Z -> Z), feq (zrow base off) basef -> 1 <= i ->
  feq (zrow (hbd_accum n i base off) off) (hb_accum i n basef) /\
  (forall k, (k < off + i \/ off + i + Z.of_nat n <= k) -> zget (hbd_accum n i base off) k = zget base k).
Proof.
  induction n as [|n IH]; intros i base off basef HB Hi; cbn [hbd_accum hb_accum].
  - split; [exact HB|]. intros; reflexivity.
  - pose proof (feq_set base off basef i (zget base (off + i) + zget base (off + i - 1)) (basef i + basef (i - 1)) HB
                  ltac:(rewrite <- (feq_at base off basef i HB), <- (feq_at base off basef (i - 1) HB);
                        replace (off + (i - 1)) with (off + i - 1) by lia; reflexivity)) as HB'.
    destruct (IH (i + 1) _ off _ HB' ltac:(lia)) as [F1 F2].
    split; [exact F1|]. intros k Hk. rewrite F2 by lia. rewrite zget_zset.
    destruct (Z.eqb_spec k (off + i)); [exfalso; lia| reflexivity].
Qed.

Lemma bridge_limit : forall n i base limit off vec (basef limitf : Z -> Z),
  feq (zrow base off) basef -> feq (zrow limit off) limitf ->
  let '(l1, v1) := hbd_limit n i base limit off vec in
  let '(l2, v2) := hb_limit basef i n limitf vec in
  feq (zrow l1 off) l2 /\ v1 = v2 /\
  (forall k, (k < off + i \/ off + i + Z.of_nat n <= k) -> zget l1 k = zget limit k).
Proof.
  induction n as [|n IH]; intros i base limit off vec basef limitf HB HL; cbn [hbd_limit hb_limit].
  - split; [exact HL|]. split; [reflexivity|]. intros; reflexivity.
  - rewrite <- (feq_at base off basef (i + 1) HB), <- (feq_at base off basef i HB).
    replace (off + (i + 1)) with (off + i + 1) by lia.
    set (vec1 := vec + (zget base (off + i + 1) - zget base (off + i))).
    pose proof (feq_set limit off limitf i (vec1 - 1) (vec1 - 1) HL eq_refl) as HL'.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. replace (vec1 * 2) with (2 * vec1) by lia.
    specialize (IH (i + 1) base (zset limit (off + i) (vec1 - 1)) off (2 * vec1) basef (zfupd limitf i (vec1 - 1)) HB HL').
    destruct (hbd_limit n (i + 1) base (zset limit (off + i) (vec1 - 1)) off (2 * vec1)) as [l1 v1].
    destruct (hb_limit basef (i + 1) n (zfupd limitf i (vec1 - 1)) (2 * vec1)) as [l2 v2].
    cps_destruct IH as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|].
    intros k Hk. rewrite F3 by lia. rewrite zget_zset.
    destruct (Z.eqb_spec k (off + i)); [exfalso; lia| reflexivity].
Qed.

Lemma bridge_base : forall n i limit base off (limitf basef : Z -> Z),
  feq (zrow limit off) limitf -> feq (zrow base off) basef -> 1 <= i ->
  feq (zrow (hbd_base n i limit base off) off) (hb_base limitf i n basef) /\
  (forall k, (k < off + i \/ off + i + Z.of_nat n <= k) -> zget (hbd_base n i limit base off) k = zget base k).
Proof.
  induction n as [|n IH]; intros i limit base off limitf basef HL HB Hi; cbn [hbd_base hb_base].
  - split; [exact HB|]. intros; reflexivity.
  - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    pose proof (feq_set base off basef i (2 * (zget limit (off + i - 1) + 1) - zget base (off + i)) ((limitf (i - 1) + 1) * 2 - basef i) HB
                  ltac:(rewrite <- (feq_at limit off limitf (i - 1) HL), <- (feq_at base off basef i HB);
                        replace (off + (i - 1)) with (off + i - 1) by lia; lia)) as HB'.
    destruct (IH (i + 1) limit _ off limitf _ HL HB' ltac:(lia)) as [F1 F2].
    split; [exact F1|]. intros k Hk. rewrite F2 by lia. rewrite zget_zset.
    destruct (Z.eqb_spec k (off + i)); [exfalso; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Theorem hbd_bridge : forall limit base perm len off mn mx alpha,
  1 <= mn -> mx <= 20 -> 0 <= alpha -> (forall j, 0 <= j < alpha -> 0 <= zget len (off + j) + 1 < 258) ->
  let '(li, ba, pe) := hbCreateDecodeTables limit base perm len off mn mx alpha in
  let '(lim, bas, per) := hb_create (zrow limit off) (zrow base off) (zrow perm off) (zrow len off) mn mx alpha in
  feq (zrow li off) lim /\ feq (zrow ba off) bas /\ feq (zrow pe off) per /\
  snd (hbd_permI (zspan mn mx) mn len perm off 0 alpha) = snd (BzModel.hb_permI (zrow len off) alpha mn (span mn mx) (zrow perm off) 0) /\
  (forall k, (k < off \/ off + 258 <= k) -> zget li k = zget limit k /\ zget ba k = zget base k) /\
  (forall k, (k < off \/ off + snd (hbd_permI (zspan mn mx) mn len perm off 0 alpha) <= k) -> zget pe k = zget perm k).
Proof.
  intros limit base perm len off mn mx alpha Hmn Hmx Ha HR.
  unfold hbCreateDecodeTables, hb_create. rewrite BZ_MAX_CODE_LEN_eq. unfold OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff.BZ_MAX_CODE_LEN.
  replace (zspan mn mx) with (span mn mx) by reflexivity.
  replace (zspan (mn + 1) mx) with (span (mn + 1) mx) by reflexivity.
  pose proof (bridge_permI (span mn mx) mn len perm off 0 alpha (zrow len off) (zrow perm off)
                ltac:(intros k; reflexivity) ltac:(intros k; reflexivity)) as P.
  destruct (hbd_permI (span mn mx) mn len perm off 0 alpha) as [pe pp1].
  destruct (BzModel.hb_permI (zrow len off) alpha mn (span mn mx) (zrow perm off) 0) as [per pp2]. cbn [fst snd].
  cps_destruct P as (P1 & P2 & P3 & P4).
  destruct (bridge_zero (Z.to_nat 23) 0 base off (zrow base off) ltac:(intros k; reflexivity)) as [B1 B1f].
  destruct (bridge_count (Z.to_nat alpha) 0 len _ off (zrow len off) _ ltac:(intros k; reflexivity) B1
              ltac:(intros; apply HR; lia)) as [B2 B2f].
  destruct (bridge_accum (Z.to_nat (23 - 1)) 1 _ off _ B2 ltac:(lia)) as [B3 B3f].
  destruct (bridge_zero (Z.to_nat 23) 0 limit off (zrow limit off) ltac:(intros k; reflexivity)) as [L1 L1f].
  pose proof (bridge_limit (span mn mx) mn _ _ off 0 _ _ B3 L1) as LM.
  destruct (hbd_limit (span mn mx) mn _ _ off 0) as [li v1].
  destruct (hb_limit _ mn (span mn mx) _ 0) as [lim v2]. cbn [fst snd].
  cps_destruct LM as (L2 & _ & L2f).
  destruct (bridge_base (span (mn + 1) mx) (mn + 1) li _ off lim _ L2 B3 ltac:(lia)) as [B4 B4f].
  split; [exact L2|]. split; [exact B4|]. split; [exact P1|]. split; [exact P2|].
  split.
  - intros k Hk. split.
    + rewrite L2f by (unfold span in *; lia). apply L1f. lia.
    + rewrite B4f by (unfold span in *; lia). rewrite B3f by lia. rewrite B2f by lia. apply B1f. lia.
  - intros k Hk. apply P4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mt_rows (t alpha : Z) (d : dst) (mn mx : Z) : dst :=
  let '(li, ba, pe) := hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx alpha in
  d_set_perm (d_set_base (d_set_limit d li) ba) pe.
Definition mt_fin (t alpha : Z) (d : dst) (mnmx : Z * Z) : dst :=
  let '(mn, mx) := mnmx in d_set_minLens (mt_rows t alpha d mn mx) (zset (d_minLens d) t mn).
Definition mt_step (t alpha : Z) (d : dst) : dst :=
  mt_fin t alpha d (minmax_len (Z.to_nat alpha) 0 (d_len d) (258 * t) 32 0).

Lemma d_minLens_mt_rows : forall t alpha d mn mx, d_minLens (mt_rows t alpha d mn mx) = d_minLens d.
Proof. intros. unfold mt_rows. destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe]. destruct d; reflexivity. Qed.

Lemma make_tables_S : forall n t alpha d,
  make_tables (S n) t alpha d = make_tables n (t + 1) alpha (mt_step t alpha d).
Proof.
  intros n t alpha d. cbn [make_tables]. unfold mt_step, mt_fin, mt_rows.
  destruct (minmax_len _ _ _ _ _ _) as [mn mx].
  destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe].
  destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Definition L7loc (L : dsv) (d : dst) : dsv :=
  sv_set_groupPos (sv_set_groupNo (sv_set_nblockMAX (sv_set_EOB (sv_set_t (sv_set_i L (sv_alphaSize L)) (sv_nGroups L))
    (d_nInUse d + 1)) (100000 * d_bs100k d)) (-1)) 0.
(* [comment removed for export] *)
Definition mi_rest (L : dsv) (d : dst) (s : dstrm) : dres :=
  mtf_val_start BZ_X_MTF_1 (sv_set_nblock (sv_set_i (L7loc L d) 256) 0) d s.
Definition mi_fin (d : dst) (ab : zarr * zarr) : dst := let '(a, b) := ab in d_set_mtfbase (d_set_mtfa d a) b.
(* [comment removed for export] *)
Definition at_rest (L : dsv) (d : dst) (s : dstrm) : dres :=
  mi_rest L (mi_fin (d_set_unzftab d (clear256 256 0 (d_unzftab d)))
                  (mtfinit_i 16 15 4095 (d_mtfa d) (d_mtfbase d))) s.

Lemma L7loc_frame : forall L d d', d_nInUse d' = d_nInUse d -> d_bs100k d' = d_bs100k d -> L7loc L d' = L7loc L d.
Proof. intros L d d' E1 E2. unfold L7loc. rewrite E1, E2. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma after_tables_eq : forall L d s,
  after_tables L d s = at_rest L (make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d) s.
Proof.
  intros L d s. unfold after_tables, at_rest, mi_rest, mtf_init, BZ_X_MTF_1.
  set (d1 := make_tables _ _ _ _). clearbody d1.
  set (d2 := d_set_unzftab d1 _).
  assert (E1 : d_mtfa d2 = d_mtfa d1) by (subst d2; destruct d1; reflexivity).
  assert (E2 : d_mtfbase d2 = d_mtfbase d1) by (subst d2; destruct d1; reflexivity).
  rewrite <- E1, <- E2. unfold mi_fin. destruct (mtfinit_i _ _ _ _ _) as [a b].
  rewrite (L7loc_frame L d1 (d_set_mtfbase (d_set_mtfa d2 a) b)); [reflexivity| |]; subst d2; destruct d1; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_L7T (F : nat) (L : dsv) (d : dst) (s : dstrm) (t : Z) : dres :=
  dgo F (at_rest L (make_tables (Z.to_nat (sv_nGroups L - t)) t (sv_alphaSize L) d) s).
Definition K_H7M (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (at_rest L d s).
(* [comment removed for export] *)
Definition K_L7I (F : nat) (L : dsv) (d : dst) (s : dstrm) (t i mn mx : Z) : dres :=
  K_L7T F L (mt_fin t (sv_alphaSize L) d (minmax_len (Z.to_nat (sv_alphaSize L - i)) i (d_len d) (258 * t) mn mx)) s (t + 1).
(* [comment removed for export] *)
Definition K_L7C (F : nat) (L : dsv) (d : dst) (s : dstrm) (t mn mx : Z) : dres :=
  K_L7T F L (mt_fin t (sv_alphaSize L) d (mn, mx)) s (t + 1).
(* [comment removed for export] *)
Definition K_L7D (F : nat) (L : dsv) (d : dst) (s : dstrm) (t mn : Z) : dres :=
  K_L7T F L (d_set_minLens d (zset (d_minLens d) t mn)) s (t + 1).

Lemma K_HHB_L7T : forall F L d s, K_HHB F L d s = K_L7T F L d s 0.
Proof. intros. unfold K_HHB, K_L7T. rewrite after_tables_eq, Z.sub_0_r. reflexivity. Qed.
Lemma K_L7T_exit : forall F L d s t, t = sv_nGroups L -> K_L7T F L d s t = K_H7M F L d s.
Proof. intros F L d s t ->. unfold K_L7T, K_H7M. rewrite Z.sub_diag. reflexivity. Qed.
Lemma K_L7T_scan : forall F L d s t, t < sv_nGroups L -> K_L7T F L d s t = K_L7I F L d s t 0 32 0.
Proof.
  intros F L d s t Ht. unfold K_L7I, K_L7T.
  replace (Z.to_nat (sv_nGroups L - t)) with (S (Z.to_nat (sv_nGroups L - (t + 1)))) by lia.
  rewrite make_tables_S. rewrite Z.sub_0_r. reflexivity.
Qed.
Lemma K_L7I_step : forall F L d s t i mn mx, i < sv_alphaSize L ->
  K_L7I F L d s t i mn mx =
  K_L7I F L d s t (i + 1) (if zget (d_len d) (258 * t + i) <? mn then zget (d_len d) (258 * t + i) else mn)
                          (if mx <? zget (d_len d) (258 * t + i) then zget (d_len d) (258 * t + i) else mx).
Proof.
  intros F L d s t i mn mx Hi. unfold K_L7I.
  replace (Z.to_nat (sv_alphaSize L - i)) with (S (Z.to_nat (sv_alphaSize L - (i + 1)))) by lia.
  cbn [minmax_len]. reflexivity.
Qed.
Lemma K_L7I_exit : forall F L d s t i mn mx, i = sv_alphaSize L -> K_L7I F L d s t i mn mx = K_L7C F L d s t mn mx.
Proof. intros F L d s t i mn mx ->. unfold K_L7I, K_L7C. rewrite Z.sub_diag. reflexivity. Qed.
Lemma K_L7C_call : forall F L d s t mn mx,
  K_L7C F L d s t mn mx = K_L7D F L (mt_rows t (sv_alphaSize L) d mn mx) s t mn.
Proof. intros. unfold K_L7C, K_L7D, mt_fin. rewrite d_minLens_mt_rows. reflexivity. Qed.
(* [comment removed for export] *)
Lemma K_L7C_D : forall F L d s t mn mx,
  K_L7C F L d s t mn mx = K_L7T F L (d_set_minLens (mt_rows t (sv_alphaSize L) d mn mx) (zset (d_minLens d) t mn)) s (t + 1).
Proof. intros. rewrite K_L7C_call. unfold K_L7D. rewrite d_minLens_mt_rows. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_L7G (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (mi_rest L d s).
(* [comment removed for export] *)
Definition K_L7K (F : nat) (L : dsv) (d : dst) (s : dstrm) (ii : Z) : dres :=
  dgo F (mi_rest L (mi_fin d (mtfinit_i (Z.to_nat (ii + 1)) ii (3855 + 16 * ii) (d_mtfa d) (d_mtfbase d))) s).
(* [comment removed for export] *)
Definition K_L7J (F : nat) (L : dsv) (d : dst) (s : dstrm) (ii dd : Z) : dres :=
  dgo F (mi_rest L (mi_fin d
    (let '(a, kk') := mtfinit_j (Z.to_nat (16 - dd)) (15 - dd) ii (3855 + 16 * ii - dd) (d_mtfa d) in
     mtfinit_i (Z.to_nat ii) (ii - 1) kk' a (zset (d_mtfbase d) ii (kk' + 1)))) s).

Lemma K_H7M_memset : forall F L d s,
  K_H7M F L d s = K_L7K F L (d_set_unzftab d (clear256 256 0 (d_unzftab d))) s 15.
Proof.
  intros. unfold K_H7M, K_L7K, at_rest. change (Z.to_nat (15 + 1)) with 16%nat. change (3855 + 16 * 15) with 4095.
  destruct d; reflexivity.
Qed.
Lemma K_L7K_in : forall F L d s ii, 0 <= ii -> K_L7K F L d s ii = K_L7J F L d s ii 0.
Proof.
  intros F L d s ii Hii. unfold K_L7K, K_L7J.
  replace (Z.to_nat (ii + 1)) with (S (Z.to_nat ii)) by lia. cbn [mtfinit_i].
  change (Z.to_nat (16 - 0)) with 16%nat. rewrite !Z.sub_0_r.
  destruct (mtfinit_j 16 15 ii _ _) as [a kk']. reflexivity.
Qed.
Lemma mtfinit_j_fuel : forall n jj ii kk a, mtfinit_j (S n) jj ii kk a = mtfinit_j n (jj - 1) ii (kk - 1) (zset a kk (ii * 16 + jj)).
Proof. reflexivity. Qed.
Lemma d_mtfa_set_mtfa : forall d a, d_mtfa (d_set_mtfa d a) = a. Proof. intros []; reflexivity. Qed.
Lemma d_mtfbase_set_mtfa : forall d a, d_mtfbase (d_set_mtfa d a) = d_mtfbase d. Proof. intros []; reflexivity. Qed.
Lemma d_mtfa_set_mtfbase : forall d b, d_mtfa (d_set_mtfbase d b) = d_mtfa d. Proof. intros []; reflexivity. Qed.
Lemma d_mtfbase_set_mtfbase : forall d b, d_mtfbase (d_set_mtfbase d b) = b. Proof. intros []; reflexivity. Qed.
Lemma mi_fin_set_mtfa : forall d a0 ab, mi_fin (d_set_mtfa d a0) ab = mi_fin d ab.
Proof. intros d a0 [a b]. destruct d; reflexivity. Qed.
Lemma mi_fin_set_mtfbase : forall d b0 ab, mi_fin (d_set_mtfbase d b0) ab = mi_fin d ab.
Proof. intros d b0 [a b]. destruct d; reflexivity. Qed.
Lemma K_L7J_step : forall F L d s ii dd, 0 <= dd < 16 ->
  K_L7J F L d s ii dd = K_L7J F L (d_set_mtfa d (zset (d_mtfa d) (3855 + 16 * ii - dd) (ii * 16 + (15 - dd)))) s ii (dd + 1).
Proof.
  intros F L d s ii dd Hdd. unfold K_L7J.
  rewrite d_mtfa_set_mtfa, d_mtfbase_set_mtfa, mi_fin_set_mtfa.
  replace (Z.to_nat (16 - dd)) with (S (Z.to_nat (16 - (dd + 1)))) by lia. rewrite mtfinit_j_fuel.
  replace (15 - dd - 1) with (15 - (dd + 1)) by lia. replace (3855 + 16 * ii - dd - 1) with (3855 + 16 * ii - (dd + 1)) by lia.
  reflexivity.
Qed.
Lemma K_L7J_exit : forall F L d s ii, 1 <= ii ->
  K_L7J F L d s ii 16 = K_L7K F L (d_set_mtfbase d (zset (d_mtfbase d) ii (3840 + 16 * ii))) s (ii - 1).
Proof.
  intros F L d s ii Hii. unfold K_L7J, K_L7K.
  rewrite d_mtfa_set_mtfbase, d_mtfbase_set_mtfbase, mi_fin_set_mtfbase.
  change (Z.to_nat (16 - 16)) with 0%nat. cbn [mtfinit_j].
  replace (3855 + 16 * ii - 16 + 1) with (3840 + 16 * ii) by lia.
  replace (Z.to_nat (ii - 1 + 1)) with (Z.to_nat ii) by lia.
  replace (3855 + 16 * (ii - 1)) with (3855 + 16 * ii - 16) by lia.
  reflexivity.
Qed.
Lemma K_L7J_last : forall F L d s,
  K_L7J F L d s 0 16 = K_L7G F L (d_set_mtfbase d (zset (d_mtfbase d) 0 3840)) s.
Proof.
  intros F L d s. unfold K_L7J, K_L7G. change (Z.to_nat (16 - 16)) with 0%nat. change (Z.to_nat 0) with 0%nat.
  cbn [mtfinit_j mtfinit_i]. change (3855 + 16 * 0 - 16 + 1) with 3840.
  unfold mi_fin. destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Definition L7fin (L : dsv) (d : dst) : dsv :=
  let L1 := sv_set_nblock (sv_set_i (L7loc L d) 256) 0 in
  let gSel := zget (d_sel d) 0 in
  let gMinlen := zget (d_minLens d) gSel in
  sv_set_zn (sv_set_gPtr (sv_set_gMinlen (sv_set_gSel (sv_set_groupPos (sv_set_groupNo L1 0) 49) gSel) gMinlen) true) gMinlen.
Lemma K_L7G_go : forall F L d s, 1 <= sv_nSelectors L -> K_L7G F L d s = K_HMTF1 F (L7fin L d) d s.
Proof.
  intros F L d s Hns. unfold K_L7G, K_HMTF1, mi_rest, mtf_val_start, L7fin, L7loc, BZ_X_MTF_1, BZ_G_SIZE.
  Lsplit L. cbn -[zget drun Z.add Z.mul Z.leb].
  replace (L_nSelectors <=? -1 + 1) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite dgo_DGo. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cong32 (f g : Z -> Z) : Prop := forall i, 0 <= i < 258 -> f i mod 4294967296 = g i mod 4294967296.

(* [comment removed for export] *)
Lemma cong32_upd : forall f g i v v', cong32 f g -> v mod 4294967296 = v' mod 4294967296 ->
  cong32 (zfupd f i v) (zfupd g i v').
Proof. intros f g i v v' H E k Hk. rewrite !zfupd_eq. destruct (k =? i); [exact E| apply H; exact Hk]. Qed.
Lemma cong32_add : forall a b a' b', a mod 4294967296 = a' mod 4294967296 -> b mod 4294967296 = b' mod 4294967296 ->
  (a + b) mod 4294967296 = (a' + b') mod 4294967296.
Proof. intros. rewrite Z.add_mod, H, H0, <- Z.add_mod by lia. reflexivity. Qed.
Lemma cong32_sub : forall a b a' b', a mod 4294967296 = a' mod 4294967296 -> b mod 4294967296 = b' mod 4294967296 ->
  (a - b) mod 4294967296 = (a' - b') mod 4294967296.
Proof. intros. rewrite Zminus_mod, H, H0, <- Zminus_mod. reflexivity. Qed.
Lemma cong32_mul2 : forall a a', a mod 4294967296 = a' mod 4294967296 ->
  (Z.shiftl a 1) mod 4294967296 = (Z.shiftl a' 1) mod 4294967296.
Proof.
  intros. rewrite !Z.shiftl_mul_pow2 by lia. rewrite Z.mul_mod, H, <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma cong_permJ : forall n len len' i j p p' pp, cong32 p p' ->
  (forall k, j <= k < j + Z.of_nat n -> len k = len' k) ->
  cong32 (fst (BzModel.hb_permJ len i j n p pp)) (fst (BzModel.hb_permJ len' i j n p' pp)) /\
  snd (BzModel.hb_permJ len i j n p pp) = snd (BzModel.hb_permJ len' i j n p' pp).
Proof.
  induction n as [|n IH]; intros len len' i j p p' pp H E; cbn [BzModel.hb_permJ fst snd].
  - split; [exact H| reflexivity].
  - rewrite <- (E j) by lia. destruct (len j =? i).
    + apply IH; [| intros; apply E; lia]. apply cong32_upd; [exact H| reflexivity].
    + apply IH; [exact H| intros; apply E; lia].
Qed.
Lemma cong_permI : forall n len len' alpha i p p' pp, cong32 p p' -> 0 <= alpha ->
  (forall k, 0 <= k < alpha -> len k = len' k) ->
  cong32 (fst (BzModel.hb_permI len alpha i n p pp)) (fst (BzModel.hb_permI len' alpha i n p' pp)) /\
  snd (BzModel.hb_permI len alpha i n p pp) = snd (BzModel.hb_permI len' alpha i n p' pp).
Proof.
  induction n as [|n IH]; intros len len' alpha i p p' pp H Ha E; cbn [BzModel.hb_permI fst snd].
  - split; [exact H| reflexivity].
  - destruct (cong_permJ (Z.to_nat alpha) len len' i 0 p p' pp H ltac:(intros; apply E; lia)) as [C X].
    destruct (BzModel.hb_permJ len i 0 (Z.to_nat alpha) p pp) as [q qq].
    destruct (BzModel.hb_permJ len' i 0 (Z.to_nat alpha) p' pp) as [q' qq']. cbn [fst snd] in *. subst qq'.
    apply IH; [exact C| exact Ha| exact E].
Qed.
Lemma cong_fill0 : forall n f g i, cong32 f g -> cong32 (fill0 f i n) (fill0 g i n).
Proof. induction n as [|n IH]; intros f g i H; cbn [fill0]; [exact H|]. apply IH. apply cong32_upd; [exact H| reflexivity]. Qed.
Lemma cong_count : forall n len len' i b b', cong32 b b' ->
  (forall j, i <= j < i + Z.of_nat n -> 0 <= len j + 1 < 258 /\ len j = len' j) ->
  cong32 (hb_count len i n b) (hb_count len' i n b').
Proof.
  induction n as [|n IH]; intros len len' i b b' H R; cbn [hb_count]; [exact H|].
  destruct (R i ltac:(lia)) as [R1 R2]. rewrite <- R2.
  apply IH; [| intros; apply R; lia]. apply cong32_upd; [exact H|]. apply cong32_add; [apply H; exact R1| reflexivity].
Qed.
Lemma cong_accum : forall n i b b', cong32 b b' -> 1 <= i -> i + Z.of_nat n <= 258 -> cong32 (hb_accum i n b) (hb_accum i n b').
Proof.
  induction n as [|n IH]; intros i b b' H Hi Hn; cbn [hb_accum]; [exact H|].
  apply IH; [| lia| lia]. apply cong32_upd; [exact H|]. apply cong32_add; apply H; lia.
Qed.
Lemma cong_limit : forall n b b' i l l' vec vec', cong32 b b' -> cong32 l l' -> vec mod 4294967296 = vec' mod 4294967296 ->
  0 <= i -> i + Z.of_nat n <= 257 ->
  cong32 (fst (hb_limit b i n l vec)) (fst (hb_limit b' i n l' vec')) /\
  snd (hb_limit b i n l vec) mod 4294967296 = snd (hb_limit b' i n l' vec') mod 4294967296.
Proof.
  induction n as [|n IH]; intros b b' i l l' vec vec' HB HL HV Hi Hn; cbn [hb_limit fst snd].
  - split; assumption.
  - assert (V1 : (vec + (b (i + 1) - b i)) mod 4294967296 = (vec' + (b' (i + 1) - b' i)) mod 4294967296).
    { apply cong32_add; [exact HV|]. apply cong32_sub; apply HB; lia. }
    apply IH; [exact HB| | | lia| lia].
    + apply cong32_upd; [exact HL|]. apply cong32_sub; [exact V1| reflexivity].
    + apply cong32_mul2. exact V1.
Qed.
Lemma cong_base : forall n l l' i b b', cong32 l l' -> cong32 b b' -> 1 <= i -> i + Z.of_nat n <= 258 ->
  cong32 (hb_base l i n b) (hb_base l' i n b').
Proof.
  induction n as [|n IH]; intros l l' i b b' HL HB Hi Hn; cbn [hb_base]; [exact HB|].
  apply IH; [exact HL| | lia| lia]. apply cong32_upd; [exact HB|].
  apply cong32_sub; [| apply HB; lia]. apply cong32_mul2. apply cong32_add; [apply HL; lia| reflexivity].
Qed.

Theorem hb_create_cong : forall lim0 lim0' base0 base0' perm0 perm0' len len' mn mx alpha,
  cong32 lim0 lim0' -> cong32 base0 base0' -> cong32 perm0 perm0' ->
  (forall j, 0 <= j < alpha -> len j = len' j) ->
  1 <= mn -> mn <= mx <= 20 -> 0 <= alpha -> (forall j, 0 <= j < alpha -> 0 <= len j + 1 < 258) ->
  let '(l, b, p) := hb_create lim0 base0 perm0 len mn mx alpha in
  let '(l', b', p') := hb_create lim0' base0' perm0' len' mn mx alpha in
  cong32 l l' /\ cong32 b b' /\ cong32 p p'.
Proof.
  intros lim0 lim0' base0 base0' perm0 perm0' len len' mn mx alpha HL HB HP HE Hmn Hmx Ha HR. unfold hb_create. cbv beta iota zeta.
  rewrite !BZ_MAX_CODE_LEN_eq.
  destruct (cong_permI (span mn mx) len len' alpha mn perm0 perm0' 0 HP Ha HE) as [CP _].
  pose proof (cong_accum (Z.to_nat (23 - 1)) 1 _ _
                (cong_count (Z.to_nat alpha) len len' 0 _ _ (cong_fill0 (Z.to_nat 23) base0 base0' 0 HB)
                   ltac:(intros; split; [apply HR| apply HE]; lia)) ltac:(lia) ltac:(lia)) as C3.
  pose proof (cong_fill0 (Z.to_nat 23) lim0 lim0' 0 HL) as CL1.
  assert (Hs : mn + Z.of_nat (span mn mx) = mx + 1) by (unfold span; lia).
  assert (Hs2 : mn + 1 + Z.of_nat (span (mn + 1) mx) = mx + 1) by (unfold span; lia).
  destruct (cong_limit (span mn mx) _ _ mn _ _ 0 0 C3 CL1 eq_refl ltac:(lia) ltac:(lia)) as [CL2 _].
  (* [comment removed for export] *)
  split; [exact CL2| split; [| exact CP]].
  apply cong_base; [exact CL2| exact C3| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tab_rowsF (d : dst) (alpha t mn mx : Z) : Prop :=
  exists (len lim0 base0 perm0 : Z -> Z),
    (1 <= mn /\ mn <= mx <= 20) /\
    (forall j, 0 <= j < alpha -> mn <= len j <= mx) /\
    (let '(lim, base, perm) := hb_create lim0 base0 perm0 len mn mx alpha in
     (forall i, 0 <= i < 258 -> zget (d_limit d) (258 * t + i) = lim i) /\
     (forall i, 0 <= i < 258 -> zget (d_base d) (258 * t + i) = base i) /\
     (forall i, 0 <= i < 258 -> zget (d_perm d) (258 * t + i) = perm i)).
Lemma tab_okF_of_rows : forall d alpha t mn mx, tab_rowsF d alpha t mn mx -> zget (d_minLens d) t = mn -> tab_okF d alpha t mn.
Proof.
  (intros d alpha t mn mx; cps_intros (len & lim0 & base0 & perm0 & H1 & H2 & H3); intros Hm).
  exists len, lim0, base0, perm0, mx. split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact Hm].
Qed.
(* [comment removed for export] *)
Lemma tab_okF_frame_pt : forall d d' alpha t mn, tab_okF d alpha t mn ->
  (forall i, 0 <= i < 258 -> zget (d_limit d') (258 * t + i) = zget (d_limit d) (258 * t + i)) ->
  (forall i, 0 <= i < 258 -> zget (d_base d') (258 * t + i) = zget (d_base d) (258 * t + i)) ->
  (forall i, 0 <= i < 258 -> zget (d_perm d') (258 * t + i) = zget (d_perm d) (258 * t + i)) ->
  zget (d_minLens d') t = zget (d_minLens d) t ->
  tab_okF d' alpha t mn.
Proof.
  (intros d d' alpha t mn; cps_intros (len & lim0 & base0 & perm0 & mx & H1 & H2 & H3 & H4); intros E1 E2 E3 E4).
  exists len, lim0, base0, perm0, mx. split; [exact H1|]. split; [exact H2|].
  destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm]. cps_destruct H3 as (A & B & C).
  split; [| rewrite E4; exact H4].
  split; [| split]; intros i Hi; [rewrite E1 | rewrite E2 | rewrite E3]; auto.
Qed.

(* [comment removed for export] *)
Definition tabs_upto (d : dst) (t alpha : Z) : Prop := forall t', 0 <= t' < t -> exists mn, tab_okF d alpha t' mn.
Lemma tabs_upto_0 : forall d alpha, tabs_upto d 0 alpha.
Proof. intros d alpha t' H. exfalso. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mt_rows_fields : forall t alpha d mn mx,
  let d' := mt_rows t alpha d mn mx in
  let '(li, ba, pe) := hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx alpha in
  d_limit d' = li /\ d_base d' = ba /\ d_perm d' = pe /\ d_len d' = d_len d /\ d_minLens d' = d_minLens d /\
  d_sel d' = d_sel d /\ d_nInUse d' = d_nInUse d /\ d_bs100k d' = d_bs100k d /\ d_state d' = d_state d /\
  d_rand d' = d_rand d /\ d_sbcrc d' = d_sbcrc d /\ d_origPtr d' = d_origPtr d /\ d_bsLive d' = d_bsLive d.
Proof.
  intros t alpha d mn mx. cbv zeta. unfold mt_rows. destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe].
  destruct d; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mt_rows_bridge : forall d t alpha mn mx,
  1 <= alpha <= 258 -> 0 <= t -> 1 <= mn /\ mn <= mx <= 20 ->
  (forall j, 0 <= j < alpha -> mn <= zget (d_len d) (258 * t + j) <= mx) ->
  let d' := mt_rows t alpha d mn mx in
  let '(lim, bas, per) := hb_create (zrow (d_limit d) (258 * t)) (zrow (d_base d) (258 * t)) (zrow (d_perm d) (258 * t))
                                     (zrow (d_len d) (258 * t)) mn mx alpha in
  (forall i, 0 <= i < 258 ->
     zget (d_limit d') (258 * t + i) = lim i /\ zget (d_base d') (258 * t + i) = bas i /\ zget (d_perm d') (258 * t + i) = per i) /\
  (forall k, (k < 258 * t \/ 258 * t + 258 <= k) ->
     zget (d_limit d') k = zget (d_limit d) k /\ zget (d_base d') k = zget (d_base d) k /\ zget (d_perm d') k = zget (d_perm d) k).
Proof.
  intros d t alpha mn mx Ha Ht Hmm Hlen. cbv zeta.
  pose proof (mt_rows_fields t alpha d mn mx) as FL. cbv zeta in FL.
  pose proof (hbd_bridge (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx alpha
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros j Hj; specialize (Hlen j Hj); lia)) as BR.
  destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe].
  cps_destruct FL as (E1 & E2 & E3 & _).
  pose proof (hb_perm_final (zrow (d_len d) (258 * t)) alpha mn mx Ha Hmm
                ltac:(intros j Hj; unfold zrow; apply Hlen; exact Hj) (zrow (d_perm d) (258 * t))) as PF. cbv zeta in PF.
  cps_destruct PF as (PP & _ & _).
  destruct (hb_create (zrow (d_limit d) (258 * t)) (zrow (d_base d) (258 * t)) (zrow (d_perm d) (258 * t))
                      (zrow (d_len d) (258 * t)) mn mx alpha) as [[lim bas] per] eqn:HC.
  cps_destruct BR as (B1 & B2 & B3 & B4 & B5 & B6).
  rewrite E1, E2, E3. split.
  - intros i Hi. split; [apply B1|]. split; [apply B2| apply B3].
  - intros k Hk. destruct (B5 k Hk) as [X Y]. split; [exact X|]. split; [exact Y|].
    apply B6. rewrite B4. rewrite PP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mtf_inv_ext : forall f g, (forall l, 0 <= l < 16 -> f l = g l) -> mtf_inv f -> mtf_inv g.
Proof.
  (intros f g E; cps_intros (A & B & C)). unfold mtf_inv.
  rewrite <- (E 0), <- (E 15) by lia. split; [exact A|]. split; [| exact C].
  intros l Hl. rewrite <- (E l), <- (E (l + 1)) by lia. apply B. exact Hl.
Qed.
Lemma mtf_inv_home : mtf_inv (fun l => 3840 + 16 * l).
Proof. unfold mtf_inv. split; [lia|]. split; [intros; lia| lia]. Qed.

(* [comment removed for export] *)
Definition unz0 (d : dst) : Prop := forall b, 0 <= b < 256 -> zget (d_unzftab d) b = 0.
Lemma unz0_clear : forall d a, unz0 (d_set_unzftab d (clear256 256 0 a)).
Proof. intros d a b Hb. destruct d. cbn -[clear256]. apply zget_clear256_in. exact Hb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u7com (L : dsv) (d : dst) : Prop :=
  sel_okF L d /\ (forall t i, 0 <= t < sv_nGroups L -> 0 <= i < sv_alphaSize L -> 1 <= zget (d_len d) (258 * t + i) <= 20).

Definition dinv_L7T (L : dsv) (d : dst) (t : Z) : Prop :=
  u7com L d /\ 0 <= t <= sv_nGroups L /\ tabs_upto d t (sv_alphaSize L).
Definition dinv_L7I (L : dsv) (d : dst) (t i mn mx : Z) : Prop :=
  u7com L d /\ 0 <= t < sv_nGroups L /\ 0 <= i <= sv_alphaSize L /\ 1 <= mn <= 32 /\ 0 <= mx <= 20 /\
  (forall j, 0 <= j < i -> mn <= zget (d_len d) (258 * t + j) <= mx) /\ (0 < i -> mn <= mx /\ mn <= 20) /\
  tabs_upto d t (sv_alphaSize L).
Definition dinv_L7C (L : dsv) (d : dst) (t mn mx : Z) : Prop :=
  u7com L d /\ 0 <= t < sv_nGroups L /\ (1 <= mn /\ mn <= mx <= 20) /\
  (forall j, 0 <= j < sv_alphaSize L -> mn <= zget (d_len d) (258 * t + j) <= mx) /\
  tabs_upto d t (sv_alphaSize L).
(* [comment removed for export] *)
Definition dinv_H7M (L : dsv) (d : dst) : Prop :=
  u7com L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L).
Definition dinv_L7K (L : dsv) (d : dst) (ii : Z) : Prop :=
  sel_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ unz0 d /\ -1 <= ii <= 15 /\
  (forall l, ii < l <= 15 -> zget (d_mtfbase d) l = 3840 + 16 * l) /\
  (forall k, 3856 + 16 * ii <= k < 4096 -> 0 <= zget (d_mtfa d) k < 256).
Definition dinv_L7J (L : dsv) (d : dst) (ii dd : Z) : Prop :=
  sel_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ unz0 d /\ 0 <= ii <= 15 /\ 0 <= dd <= 16 /\
  (forall l, ii < l <= 15 -> zget (d_mtfbase d) l = 3840 + 16 * l) /\
  (forall k, 3855 + 16 * ii - dd < k < 4096 -> 0 <= zget (d_mtfa d) k < 256).
Definition dinv_L7G (L : dsv) (d : dst) : Prop :=
  sel_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ unz0 d /\ mtf_okF d.

(* [comment removed for export] *)
Lemma dinv_HMTF1_intro : forall L d, dinv_L7G L d -> 1 <= d_bs100k d -> dinv_HMTF1 (L7fin L d) d.
Proof.
  (intros L d; cps_intros (SEL & TABS & U0 & MTF); intros Hn). cps_destruct SEL as ((AL & NBL) & NG & NSC & SOK).
  unfold dinv_HMTF1, dinv_ML, L7fin, L7loc. Lsplit L.
  assert (G0 : 0 <= zget (d_sel d) 0 < L_nGroups) by (apply SOK; lia).
  pose proof (TABS (zget (d_sel d) 0) G0) as [mn T].
  split; [| reflexivity]. split; [| split; [| split; [| split; [| split]]]].
  - unfold alpha_ok in *. cbn -[Z.mul Z.add Z.pow]. lia.
  - unfold grp_okF. cbn -[Z.mul Z.add]. split; [lia|]. split; [lia|]. split; [exact SOK| lia].
  - exact TABS.
  - exact MTF.
  - unfold blkF. cbn -[Z.mul Z.add]. split; [lia|]. split; [intros; lia|].
    intros b Hb. rewrite (U0 b Hb). reflexivity.
  - unfold cur_okF. cbn -[Z.mul Z.add zget]. repeat split; lia.
Qed.
