(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition d10 (junkD : dst) (small : Z) : dst := d_set_sv (dst_init junkD 0 small) dsv_zero.
Definition s10 (p : list Z) (dn : Z) : dstrm := dstrm_init p dn.

Lemma decompress_eq10 : forall junkD small p dn,
  decompress (dst_init junkD 0 small) (s10 p dn) = dfin (drun (9 * length p + 64) 10 dsv_zero (d10 junkD small) (s10 p dn)).
Proof.
  intros. unfold decompress, d10, s10, dfin. cbn [s_in dstrm_init].
  replace (d_state (dst_init junkD 0 small) =? BZ_X_MAGIC_1) with true by (destruct junkD; reflexivity).
  replace (d_sv (d_set_sv (dst_init junkD 0 small) dsv_zero)) with dsv_zero by (destruct junkD; reflexivity).
  replace (d_state (d_set_sv (dst_init junkD 0 small) dsv_zero)) with 10 by (destruct junkD; reflexivity).
  destruct (drun _ _ _ _ _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gb_bits_magic : forall lbl L, 10 <= lbl <= 13 -> gb_bits lbl L = 8.
Proof.
  intros lbl L H. assert (C : lbl = 10 \/ lbl = 11 \/ lbl = 12 \/ lbl = 13) by lia.
  destruct C as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.

Lemma lor_shl8_byte : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8) as [Lt|Ge].
    + replace (a * 256) with (a * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 b < 8); [|lia]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8) as [Lt|Ge].
    + replace (a * 256) with (a * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 b < 8); [|lia]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma gbval_byte : forall bb b, 0 <= bb -> 0 <= b < 256 -> gbval (u32 (Z.lor (Z.shiftl bb 8) b)) 8 8 = b.
Proof.
  intros bb b Hbb Hb. unfold gbval, u32. rewrite Z.sub_diag, Z.shiftr_0_r. change (Z.shiftl 1 8 - 1) with (Z.ones 8).
  rewrite Z.land_ones by lia. change (2 ^ 8) with 256. rewrite lor_shl8_byte by lia.
  rewrite (Z.mod_mod_divide (bb * 256 + b) 4294967296 256) by (exists 16777216; reflexivity).
  rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma mg_step : forall f lbl L d bb s b rest, 10 <= lbl <= 13 -> s_in s = b :: rest -> 0 <= bb -> 0 <= b < 256 ->
  drun (S (S f)) lbl L (gbst d lbl bb 0) s =
  dgo f (gb_after lbl b L (d_set_bsLive (gbst d lbl (u32 (Z.lor (Z.shiftl bb 8) b)) 8) 0) (s_set_tin (s_set_in s rest) (s_tin s + 1))).
Proof.
  intros f lbl L d bb s b rest Hl Hs Hbb Hb.
  rewrite (drun_pull' (S f) lbl L d s bb 0 8 b rest) by first [symmetry; apply gb_bits_magic; exact Hl | lia | exact Hs].
  rewrite (drun_bits' f lbl L d _ _ (0 + 8) 8) by first [symmetry; apply gb_bits_magic; exact Hl | lia].
  rewrite gbval_byte by lia. replace (0 + 8 - 8) with 0 by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma mg_eof : forall f lbl L d bb s, 10 <= lbl <= 13 -> s_in s = [] ->
  drun (S f) lbl L (gbst d lbl bb 0) s = DRet BZ_OK L (gbst d lbl bb 0) s.
Proof.
  intros f lbl L d bb s Hl Hs. apply (drun_eof' f lbl L d s bb 0 8); [symmetry; apply gb_bits_magic; exact Hl | lia | exact Hs].
Qed.

(* [comment removed for export] *)
Lemma d10_gbst : forall junkD small, d10 junkD small = gbst (d10 junkD small) 10 0 0.
Proof. intros. unfold d10, dst_init, gbst. destruct junkD; reflexivity. Qed.

(* [comment removed for export] *)
Lemma gb_after_10 : forall v L d s, gb_after 10 v L d s = (if v =? 66 then DGo 11 L d s else DRet BZ_DATA_ERROR_MAGIC L d s).
Proof. reflexivity. Qed.
Lemma gb_after_11 : forall v L d s, gb_after 11 v L d s = (if v =? 90 then DGo 12 L d s else DRet BZ_DATA_ERROR_MAGIC L d s).
Proof. reflexivity. Qed.
Lemma gb_after_12 : forall v L d s, gb_after 12 v L d s = (if v =? 104 then DGo 13 L d s else DRet BZ_DATA_ERROR_MAGIC L d s).
Proof. reflexivity. Qed.
Lemma gb_after_13 : forall v L d s, gb_after 13 v L d s =
  (if (v <? 49) || (57 <? v) then DRet BZ_DATA_ERROR_MAGIC L (d_set_bs100k d v) s
   else DGo 14 L (if smallb (d_set_bs100k (d_set_bs100k d v) (v - 48))
                   then d_set_ll_al (d_set_bs100k (d_set_bs100k d v) (v - 48)) true
                   else d_set_tt_al (d_set_bs100k (d_set_bs100k d v) (v - 48)) true) s).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition d13 (junkD : dst) (small v : Z) : dst :=
  d_set_bsLive (gbst (d_set_bsLive (gbst (d_set_bsLive (gbst (d_set_bsLive (gbst (d10 junkD small) 10 (u32 (Z.lor (Z.shiftl 0 8) 66)) 8) 0)
    11 (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl 0 8) 66)) 8) 90)) 8) 0)
    12 (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl 0 8) 66)) 8) 90)) 8) 104)) 8) 0)
    13 (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl 0 8) 66)) 8) 90)) 8) 104)) 8) v)) 8) 0.
Definition d14 (junkD : dst) (small v : Z) : dst :=
  let d := d_set_bs100k (d_set_bs100k (d13 junkD small v) v) (v - 48) in
  if smallb d then d_set_ll_al d true else d_set_tt_al d true.
Definition s14 (rest : list Z) (dn : Z) : dstrm := DSTRM rest [] dn 4 0.

Lemma u32_nonneg : forall x, 0 <= u32 x. Proof. intros. unfold u32. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma drun_regbst : forall f lbl lbl' L d bb bl x s,
  drun (S f) lbl' L (d_set_bsLive (gbst d lbl bb bl) x) s = drun (S f) lbl' L (gbst (d_set_bsLive (gbst d lbl bb bl) x) lbl' bb x) s.
Proof. intros. rewrite drun_gbst. destruct d; reflexivity. Qed.

Theorem dec10_ok : forall junkD small dn v rest,
  49 <= v <= 57 ->
  exists dd, 
  decompress (dst_init junkD 0 small) (s10 (66 :: 90 :: 104 :: v :: rest) dn) =
  dfin (drun (9 * length rest + 92) 14 dsv_zero dd (s14 rest dn)) /\ dd = d14 junkD small v.
Proof.
  intros junkD small dn v rest Hv. eexists. split; [| reflexivity].
  rewrite decompress_eq10. cbn [length].
  replace (9 * S (S (S (S (length rest)))) + 64)%nat with (S (S (S (S (S (S (S (S (9 * length rest + 92)))))))))%nat by lia.
  rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 (90 :: 104 :: v :: rest)) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ 90 (104 :: v :: rest)) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. change (90 =? 90) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 12 _ _ _ _ 104 (v :: rest)) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_12. change (104 =? 104) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 13 _ _ _ _ v rest) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_13. replace ((v <? 49) || (57 <? v)) with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; lia).
  rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  unfold d14, d13, s14. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem dec10_eof0 : forall junkD small dn,
  decompress (dst_init junkD 0 small) (s10 [] dn) = (BZ_OK, d_set_sv (d10 junkD small) dsv_zero, s10 [] dn).
Proof.
  intros. rewrite decompress_eq10. cbn [length]. change (9 * 0 + 64)%nat with (S 63). rewrite d10_gbst.
  rewrite mg_eof by first [lia | reflexivity]. rewrite dfin_DRet. rewrite <- d10_gbst. reflexivity.
Qed.
Theorem dec10_bad0 : forall junkD small dn b rest, 0 <= b < 256 -> b <> 66 ->
  decompress (dst_init junkD 0 small) (s10 (b :: rest) dn) =
  (BZ_DATA_ERROR_MAGIC, d_set_sv (d_set_bsLive (gbst (d10 junkD small) 10 (u32 (Z.lor (Z.shiftl 0 8) b)) 8) 0) dsv_zero,
   s_set_tin (s_set_in (s10 (b :: rest) dn) rest) (0 + 1)).
Proof.
  intros junkD small dn b rest Hb Hne. rewrite decompress_eq10. cbn [length].
  replace (9 * S (length rest) + 64)%nat with (S (S (9 * length rest + 71))) by lia. rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ b rest) by first [lia | reflexivity].
  rewrite gb_after_10. replace (b =? 66) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite dgo_DRet, dfin_DRet.
  reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma d14_fields : forall junkD small v, 0 <= v < 256 ->
  d_state (d14 junkD small v) = 13 /\ d_bsLive (d14 junkD small v) = 0 /\
  d_bsBuff (d14 junkD small v) = ((66 * 256 + 90) * 256 + 104) * 256 + v /\
  d_bs100k (d14 junkD small v) = v - 48 /\ d_small (d14 junkD small v) = small /\ d_sv (d14 junkD small v) = dsv_zero /\
  d_blockNo (d14 junkD small v) = 0 /\ d_verb (d14 junkD small v) = 0 /\ d_cccrc (d14 junkD small v) = 0 /\
  d_tt_al (d14 junkD small v) = (small =? 0) /\ d_ll_al (d14 junkD small v) = negb (small =? 0) /\
  (* [comment removed for export] *)
  d_out_ch (d14 junkD small v) = d_out_ch junkD /\ d_out_len (d14 junkD small v) = d_out_len junkD /\
  d_rand (d14 junkD small v) = d_rand junkD /\ d_rNToGo (d14 junkD small v) = d_rNToGo junkD /\ d_rTPos (d14 junkD small v) = d_rTPos junkD /\
  d_origPtr (d14 junkD small v) = d_origPtr junkD /\ d_tPos (d14 junkD small v) = d_tPos junkD /\ d_k0 (d14 junkD small v) = d_k0 junkD /\
  d_unzftab (d14 junkD small v) = d_unzftab junkD /\ d_nused (d14 junkD small v) = d_nused junkD /\ d_cftab (d14 junkD small v) = d_cftab junkD /\
  d_cftabCopy (d14 junkD small v) = d_cftabCopy junkD /\ d_tt (d14 junkD small v) = d_tt junkD /\ d_ll16 (d14 junkD small v) = d_ll16 junkD /\
  d_ll4 (d14 junkD small v) = d_ll4 junkD /\ d_sbcrc (d14 junkD small v) = d_sbcrc junkD /\ d_sccrc (d14 junkD small v) = d_sccrc junkD /\
  d_cbcrc (d14 junkD small v) = d_cbcrc junkD /\ d_nInUse (d14 junkD small v) = d_nInUse junkD /\ d_inUse (d14 junkD small v) = d_inUse junkD /\
  d_inUse16 (d14 junkD small v) = d_inUse16 junkD /\ d_s2u (d14 junkD small v) = d_s2u junkD /\ d_mtfa (d14 junkD small v) = d_mtfa junkD /\
  d_mtfbase (d14 junkD small v) = d_mtfbase junkD /\ d_sel (d14 junkD small v) = d_sel junkD /\ d_selMtf (d14 junkD small v) = d_selMtf junkD /\
  d_len (d14 junkD small v) = d_len junkD /\ d_limit (d14 junkD small v) = d_limit junkD /\ d_base (d14 junkD small v) = d_base junkD /\
  d_perm (d14 junkD small v) = d_perm junkD /\ d_minLens (d14 junkD small v) = d_minLens junkD.
Proof.
  intros junkD small v Hv.
  assert (BB : u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl (u32 (Z.lor (Z.shiftl 0 8) 66)) 8) 90)) 8) 104)) 8) v)
               = ((66 * 256 + 90) * 256 + 104) * 256 + v).
  { pose proof (lor_shl8_byte 0 66 ltac:(lia) ltac:(lia)) as E1. rewrite E1.
    assert (U1 : u32 (0 * 256 + 66) = 66) by reflexivity. rewrite U1.
    pose proof (lor_shl8_byte 66 90 ltac:(lia) ltac:(lia)) as E2. rewrite E2.
    assert (U2 : u32 (66 * 256 + 90) = 66 * 256 + 90) by reflexivity. rewrite U2.
    pose proof (lor_shl8_byte (66 * 256 + 90) 104 ltac:(lia) ltac:(lia)) as E3. rewrite E3.
    assert (U3 : u32 ((66 * 256 + 90) * 256 + 104) = (66 * 256 + 90) * 256 + 104) by reflexivity. rewrite U3.
    rewrite (lor_shl8_byte ((66 * 256 + 90) * 256 + 104) v) by lia. unfold u32. apply Z.mod_small. lia. }
  unfold d14, d13, d10, dst_init, gbst. destruct junkD. cbn -[u32 Z.lor Z.shiftl Z.mul Z.add Z.sub smallb].
  rewrite BB. unfold smallb. cbn -[Z.mul Z.add Z.sub Z.eqb]. destruct (small =? 0); cbn -[Z.mul Z.add Z.sub]; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition early10 (rc dn : Z) (R : Z * dst * dstrm) : Prop :=
  let '(rv, d1, s1) := R in
  rc = rv /\ (rv = BZ_OK \/ rv = BZ_DATA_ERROR_MAGIC) /\ 10 <= d_state d1 <= 13 /\ s_out s1 = [] /\ s_avail_out s1 = dn.

Lemma d_state_set_sv : forall d L, d_state (d_set_sv d L) = d_state d. Proof. intros []; reflexivity. Qed.
Lemma d_state_set_bsLive : forall d x, d_state (d_set_bsLive d x) = d_state d. Proof. intros []; reflexivity. Qed.
Lemma d_state_set_bs100k : forall d x, d_state (d_set_bs100k d x) = d_state d. Proof. intros []; reflexivity. Qed.
Lemma d_state_gbst : forall d lbl bb bl, d_state (gbst d lbl bb bl) = lbl. Proof. intros []; reflexivity. Qed.
Lemma d_state_d10 : forall junkD small, d_state (d10 junkD small) = 10. Proof. intros [] ?; reflexivity. Qed.

Local Ltac early_fin :=
  unfold early10;
  repeat first [rewrite d_state_set_sv | rewrite d_state_set_bsLive | rewrite d_state_set_bs100k | rewrite d_state_gbst | rewrite d_state_d10];
  cbn [s_out s_avail_out s_set_tin s_set_in s_tin s10 dstrm_init]; unfold BZ_OK, BZ_DATA_ERROR_MAGIC;
  repeat match goal with |- _ /\ _ => split end; first [reflexivity | lia | left; reflexivity | right; reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem dec10_eof0' : forall junkD small dn,
  early10 BZ_OK dn (decompress (dst_init junkD 0 small) (s10 [] dn)).
Proof. intros. rewrite dec10_eof0. early_fin. Qed.

Theorem dec10_bad0' : forall junkD small dn b rest, 0 <= b < 256 -> b <> 66 ->
  early10 BZ_DATA_ERROR_MAGIC dn (decompress (dst_init junkD 0 small) (s10 (b :: rest) dn)).
Proof. intros. rewrite dec10_bad0 by assumption. early_fin. Qed.

Theorem dec10_eof1 : forall junkD small dn,
  early10 BZ_OK dn (decompress (dst_init junkD 0 small) (s10 [66] dn)).
Proof.
  intros. rewrite decompress_eq10. cbn [length]. change (9 * 1 + 64)%nat with (S (S (S 70))). rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 []) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite mg_eof by first [lia | reflexivity]. rewrite dfin_DRet. early_fin.
Qed.

Theorem dec10_bad1 : forall junkD small dn b rest, 0 <= b < 256 -> b <> 90 ->
  early10 BZ_DATA_ERROR_MAGIC dn (decompress (dst_init junkD 0 small) (s10 (66 :: b :: rest) dn)).
Proof.
  intros junkD small dn b rest Hb Hne. rewrite decompress_eq10. cbn [length].
  replace (9 * S (S (length rest)) + 64)%nat with (S (S (S (S (9 * length rest + 78))))) by lia. rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 (b :: rest)) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ b rest) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. replace (b =? 90) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite dgo_DRet, dfin_DRet.
  early_fin.
Qed.

Theorem dec10_eof2 : forall junkD small dn,
  early10 BZ_OK dn (decompress (dst_init junkD 0 small) (s10 [66; 90] dn)).
Proof.
  intros. rewrite decompress_eq10. cbn [length]. change (9 * 2 + 64)%nat with (S (S (S (S (S 77))))). rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 [90]) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ 90 []) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. change (90 =? 90) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite mg_eof by first [lia | reflexivity]. rewrite dfin_DRet. early_fin.
Qed.

Theorem dec10_bad2 : forall junkD small dn b rest, 0 <= b < 256 -> b <> 104 ->
  early10 BZ_DATA_ERROR_MAGIC dn (decompress (dst_init junkD 0 small) (s10 (66 :: 90 :: b :: rest) dn)).
Proof.
  intros junkD small dn b rest Hb Hne. rewrite decompress_eq10. cbn [length].
  replace (9 * S (S (S (length rest))) + 64)%nat with (S (S (S (S (S (S (9 * length rest + 85))))))) by lia. rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 (90 :: b :: rest)) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ 90 (b :: rest)) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. change (90 =? 90) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 12 _ _ _ _ b rest) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_12. replace (b =? 104) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite dgo_DRet, dfin_DRet.
  early_fin.
Qed.

Theorem dec10_eof3 : forall junkD small dn,
  early10 BZ_OK dn (decompress (dst_init junkD 0 small) (s10 [66; 90; 104] dn)).
Proof.
  intros. rewrite decompress_eq10. cbn [length]. change (9 * 3 + 64)%nat with (S (S (S (S (S (S (S 84))))))). rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 [90; 104]) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ 90 [104]) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. change (90 =? 90) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 12 _ _ _ _ 104 []) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_12. change (104 =? 104) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite mg_eof by first [lia | reflexivity]. rewrite dfin_DRet. early_fin.
Qed.

Theorem dec10_bad3 : forall junkD small dn v rest, 0 <= v < 256 -> ~ (49 <= v <= 57) ->
  early10 BZ_DATA_ERROR_MAGIC dn (decompress (dst_init junkD 0 small) (s10 (66 :: 90 :: 104 :: v :: rest) dn)).
Proof.
  intros junkD small dn v rest Hv Hne. rewrite decompress_eq10. cbn [length].
  replace (9 * S (S (S (S (length rest)))) + 64)%nat with (S (S (S (S (S (S (S (S (9 * length rest + 92))))))))) by lia.
  rewrite d10_gbst.
  rewrite (mg_step _ 10 _ _ _ _ 66 (90 :: 104 :: v :: rest)) by first [lia | reflexivity].
  rewrite gb_after_10. change (66 =? 66) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin s10 dstrm_init].
  rewrite drun_regbst. rewrite (mg_step _ 11 _ _ _ _ 90 (104 :: v :: rest)) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_11. change (90 =? 90) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 12 _ _ _ _ 104 (v :: rest)) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_12. change (104 =? 104) with true. cbv iota. rewrite dgo_DGo. cbn [s_set_tin s_set_in s_tin].
  rewrite drun_regbst. rewrite (mg_step _ 13 _ _ _ _ v rest) by first [lia | reflexivity | apply u32_nonneg].
  rewrite gb_after_13. replace ((v <? 49) || (57 <? v)) with true.
  2: { symmetry. apply Bool.orb_true_intro. destruct (Z_lt_dec v 49); [left; apply Z.ltb_lt; lia | right; apply Z.ltb_lt; lia]. }
  rewrite dgo_DRet, dfin_DRet. early_fin.
Qed.

(* [comment removed for export] *)
Theorem dec10_ok' : forall junkD small dn v rest,
  49 <= v <= 57 ->
  decompress (dst_init junkD 0 small) (s10 (66 :: 90 :: 104 :: v :: rest) dn) =
  dfin (drun (9 * length rest + 92) 14 dsv_zero (d14 junkD small v) (s14 rest dn)).
Proof. intros. cps_destruct (dec10_ok junkD small dn v rest H) as (dd & E & ->). exact E. Qed.

(* [comment removed for export] *)
Definition dst_zero : dst :=
  DST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 znew 0 znew znew znew znew znew false false 0 0 0 0 0
      znew znew znew znew znew znew znew znew znew znew znew znew dsv_zero.
