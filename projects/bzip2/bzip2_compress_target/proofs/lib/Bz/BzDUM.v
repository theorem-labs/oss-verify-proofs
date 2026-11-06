(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5.   (* [comment removed for export] *)
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
Definition bsym (d : dst) (i : Z) : Z := if d_small d =? 0 then zget (d_tt d) i else zget (d_ll16 d) i.

(* [comment removed for export] *)
Definition dstore (d : dst) (nb uc : Z) : dst :=
  if smallb d then d_set_ll16 d (zset (d_ll16 d) nb uc) else d_set_tt d (zset (d_tt d) nb uc).

Lemma smallb_false : forall d, d_small d = 0 -> smallb d = false.
Proof. intros d H. unfold smallb. rewrite H. reflexivity. Qed.
Lemma smallb_true : forall d, d_small d <> 0 -> smallb d = true.
Proof. intros d H. unfold smallb. destruct (Z.eqb_spec (d_small d) 0); [contradiction| reflexivity]. Qed.

Lemma bsym_dstore : forall d nb uc i, bsym (dstore d nb uc) i = zfupd (bsym d) nb uc i.
Proof.
  intros d nb uc i. unfold bsym, dstore, smallb. rewrite zfupd_eq.
  destruct (d_small d =? 0) eqn:E; cbn [negb]; destruct d; cbn in E |- *; rewrite E, zget_zset; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsym_frame : forall d d', d_small d' = d_small d -> d_tt d' = d_tt d -> d_ll16 d' = d_ll16 d -> forall i, bsym d' i = bsym d i.
Proof. intros d d' E1 E2 E3 i. unfold bsym. rewrite E1, E2, E3. reflexivity. Qed.

Lemma dstore_small : forall d nb uc, d_small (dstore d nb uc) = d_small d.
Proof. intros d nb uc. unfold dstore. destruct (smallb d); destruct d; reflexivity. Qed.
Lemma dstore_unzftab : forall d nb uc, d_unzftab (dstore d nb uc) = d_unzftab d.
Proof. intros d nb uc. unfold dstore. destruct (smallb d); destruct d; reflexivity. Qed.
Lemma smallb_dstore : forall d nb uc, smallb (dstore d nb uc) = smallb d.
Proof. intros. unfold smallb. rewrite dstore_small. reflexivity. Qed.

(* [comment removed for export] *)
Lemma occ_ext : forall f g n b, (forall k, 0 <= k < Z.of_nat n -> f k = g k) -> occ f n b = occ g n b.
Proof. intros f g n b E. unfold occ. apply zcount_ext. intros k Hk. rewrite E by lia. reflexivity. Qed.

Lemma occ_dstore_old : forall d nb uc n b, Z.of_nat n <= nb -> occ (bsym (dstore d nb uc)) n b = occ (bsym d) n b.
Proof. intros d nb uc n b H. apply occ_ext. intros k Hk. rewrite bsym_dstore, zfupd_other by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma occ_dstore_new : forall d nb uc b, 0 <= nb ->
  occ (bsym (dstore d nb uc)) (Z.to_nat (nb + 1)) b = occ (bsym d) (Z.to_nat nb) b + (if uc =? b then 1 else 0).
Proof.
  intros d nb uc b H. replace (Z.to_nat (nb + 1)) with (S (Z.to_nat nb)) by lia.
  rewrite occ_S. rewrite (occ_dstore_old d nb uc (Z.to_nat nb) b) by lia.
  rewrite bsym_dstore. replace (Z.of_nat (Z.to_nat nb)) with nb by lia. rewrite zfupd_same. reflexivity.
Qed.

(* [comment removed for export] *)
Definition run_okF (N es : Z) : Prop := 1 <= N <= 4194304 /\ -1 <= es <= 2 * N.
Lemma run_okF_init : run_okF 1 (-1).
Proof. unfold run_okF. lia. Qed.
Lemma run_okF_step : forall N es dlt, run_okF N es -> N <= 2097151 -> (dlt = N \/ dlt = 2 * N) -> run_okF (2 * N) (es + dlt).
Proof. unfold run_okF. intros. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grp_okF (L : dsv) (d : dst) : Prop :=
  2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L <= 18002 /\
  belown (d_sel d) (sv_nSelectors L) (sv_nGroups L) /\
  sv_EOB L = d_nInUse d + 1 /\ sv_nblockMAX L = 100000 * d_bs100k d.

(* [comment removed for export] *)
Definition tab_okF (d : dst) (alpha t mn : Z) : Prop :=
  exists (len lim0 base0 perm0 : Z -> Z) (mx : Z),
    (1 <= mn /\ mn <= mx <= 20) /\
    (forall j, 0 <= j < alpha -> mn <= len j <= mx) /\
    (let '(lim, base, perm) := hb_create lim0 base0 perm0 len mn mx alpha in
     (forall i, 0 <= i < 258 -> zget (d_limit d) (258 * t + i) = lim i) /\
     (forall i, 0 <= i < 258 -> zget (d_base d) (258 * t + i) = base i) /\
     (forall i, 0 <= i < 258 -> zget (d_perm d) (258 * t + i) = perm i)) /\
    zget (d_minLens d) t = mn.
Definition tabs_okF (d : dst) (ng alpha : Z) : Prop :=
  forall t, 0 <= t < ng -> exists mn, tab_okF d alpha t mn.

(* [comment removed for export] *)
Definition mtfb (d : dst) : Z -> Z := fun l => zget (d_mtfbase d) l.
Definition mtf_okF (d : dst) : Prop :=
  mtf_inv (mtfb d) /\ (forall k, 0 <= k < 4096 -> 0 <= zget (d_mtfa d) k < 256).

(* [comment removed for export] *)
Definition blkF (L : dsv) (d : dst) : Prop :=
  0 <= sv_nblock L <= sv_nblockMAX L /\
  (forall i, 0 <= i < sv_nblock L -> 0 <= bsym d i < 256) /\
  hist_ok (zget (d_unzftab d)) (bsym d) (Z.to_nat (sv_nblock L)).

(* [comment removed for export] *)
Definition cur_okF (L : dsv) (d : dst) : Prop :=
  0 <= sv_groupNo L < sv_nSelectors L /\ 0 <= sv_groupPos L <= 49 /\
  sv_gSel L = zget (d_sel d) (sv_groupNo L) /\ 0 <= sv_gSel L < sv_nGroups L /\
  sv_gMinlen L = zget (d_minLens d) (sv_gSel L).

Definition dinv_ML (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ grp_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ mtf_okF d /\
  blkF L d /\ cur_okF L d.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dinv_HMTF1 (L : dsv) (d : dst) : Prop := dinv_ML L d /\ sv_zn L = sv_gMinlen L.
(* [comment removed for export] *)
Definition dinv_SYM (L : dsv) (d : dst) : Prop := dinv_ML L d /\ 0 <= sv_nextSym L < sv_alphaSize L.
(* [comment removed for export] *)
Definition dinv_HLIT (L : dsv) (d : dst) : Prop := dinv_ML L d /\ 2 <= sv_nextSym L < sv_EOB L.
(* [comment removed for export] *)
Definition dinv_HMTFC (L : dsv) (d : dst) : Prop := dinv_ML L d.
(* [comment removed for export] *)
Definition dinv_HRUN (L : dsv) (d : dst) : Prop :=
  dinv_ML L d /\ 0 <= sv_nextSym L <= 1 /\ run_okF (sv_N L) (sv_es L).
(* [comment removed for export] *)
Definition dinv_HMTFB (L : dsv) (d : dst) : Prop :=
  dinv_ML L d /\ run_okF (sv_N L) (sv_es L) /\ sv_N L <= 4194302.
(* [comment removed for export] *)
Definition dinv_HRUNEND (L : dsv) (d : dst) : Prop :=
  dinv_ML L d /\ 2 <= sv_nextSym L < sv_alphaSize L /\ -1 <= sv_es L <= 8388608.
(* [comment removed for export] *)
Definition dinv_HEOB (L : dsv) (d : dst) : Prop := dinv_ML L d /\ sv_nextSym L = sv_EOB L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_arm (L : dsv) (d : dst) (s : dstrm) : dres :=
  if sv_nblockMAX L <=? sv_nblock L then DRet BZ_DATA_ERROR L d s
  else
    let '(uc, d1) := mtf_decode d (sv_nextSym L - 1) in
    let u := zget (d_s2u d1) uc in
    let d2 := d_set_unzftab d1 (zincr (d_unzftab d1) u) in
    let nb := sv_nblock L in
    let d3 := if smallb d2 then d_set_ll16 d2 (zset (d_ll16 d2) nb u) else d_set_tt d2 (zset (d_tt d2) nb u) in
    mtf_val_start BZ_X_MTF_5 (sv_set_nblock L (nb + 1)) d3 s.

Definition K_HMTF1 (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := drun F 36 L d s.
Definition K_SYM (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (sym_dispatch L d s).
Definition K_HLIT (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (lit_arm L d s).
Definition K_HMTFC (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (mtf_val_start 40 L d s).
Definition K_HRUN (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (run_body L d s).
Definition K_HMTFB (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (mtf_val_start 38 L d s).
Definition K_HRUNEND (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (run_exit L d s).
Definition K_HEOB (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (block_end L d s).

(* [comment removed for export] *)
Lemma sym_dispatch_eob : forall L d s, sv_nextSym L = sv_EOB L -> sym_dispatch L d s = block_end L d s.
Proof. intros L d s H. unfold sym_dispatch. rewrite H, Z.eqb_refl. reflexivity. Qed.
Lemma sym_dispatch_run : forall L d s, sv_nextSym L <> sv_EOB L -> (sv_nextSym L = 0 \/ sv_nextSym L = 1) ->
  sym_dispatch L d s = run_body (sv_set_N (sv_set_es L (-1)) 1) d s.
Proof.
  intros L d s H R. unfold sym_dispatch. replace (sv_nextSym L =? sv_EOB L) with false by (symmetry; apply Z.eqb_neq; exact H).
  unfold BZ_RUNA, BZ_RUNB. destruct R as [-> | ->]; reflexivity.
Qed.
Lemma sym_dispatch_lit : forall L d s, sv_nextSym L <> sv_EOB L -> sv_nextSym L <> 0 -> sv_nextSym L <> 1 ->
  sym_dispatch L d s = lit_arm L d s.
Proof.
  intros L d s H H0 H1. unfold sym_dispatch, lit_arm, BZ_RUNA, BZ_RUNB, BZ_X_MTF_5.
  replace (sv_nextSym L =? sv_EOB L) with false by (symmetry; apply Z.eqb_neq; exact H).
  replace (sv_nextSym L =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace (sv_nextSym L =? 1) with false by (symmetry; apply Z.eqb_neq; exact H1). reflexivity.
Qed.
Lemma K_SYM_eob : forall F L d s, sv_nextSym L = sv_EOB L -> K_SYM F L d s = K_HEOB F L d s.
Proof. intros. unfold K_SYM, K_HEOB. rewrite sym_dispatch_eob by assumption. reflexivity. Qed.
Lemma K_SYM_run : forall F L d s, sv_nextSym L <> sv_EOB L -> (sv_nextSym L = 0 \/ sv_nextSym L = 1) ->
  K_SYM F L d s = K_HRUN F (sv_set_N (sv_set_es L (-1)) 1) d s.
Proof. intros. unfold K_SYM, K_HRUN. rewrite sym_dispatch_run by assumption. reflexivity. Qed.
Lemma K_SYM_lit : forall F L d s, sv_nextSym L <> sv_EOB L -> sv_nextSym L <> 0 -> sv_nextSym L <> 1 ->
  K_SYM F L d s = K_HLIT F L d s.
Proof. intros. unfold K_SYM, K_HLIT. rewrite sym_dispatch_lit by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grp_okF_frame : forall L L' d d', grp_okF L d ->
  sv_nGroups L' = sv_nGroups L -> sv_nSelectors L' = sv_nSelectors L -> sv_EOB L' = sv_EOB L ->
  sv_nblockMAX L' = sv_nblockMAX L -> d_sel d' = d_sel d -> d_nInUse d' = d_nInUse d -> d_bs100k d' = d_bs100k d ->
  grp_okF L' d'.
Proof. intros L L' d d' H E1 E2 E3 E4 E5 E6 E7. unfold grp_okF in *. rewrite E1, E2, E3, E4, E5, E6, E7. exact H. Qed.

Lemma tab_okF_frame : forall d d' alpha t mn, tab_okF d alpha t mn ->
  d_limit d' = d_limit d -> d_base d' = d_base d -> d_perm d' = d_perm d -> d_minLens d' = d_minLens d ->
  tab_okF d' alpha t mn.
Proof. intros d d' alpha t mn H E1 E2 E3 E4. unfold tab_okF in *. rewrite E1, E2, E3, E4. exact H. Qed.
Lemma tabs_okF_frame : forall d d' ng alpha, tabs_okF d ng alpha ->
  d_limit d' = d_limit d -> d_base d' = d_base d -> d_perm d' = d_perm d -> d_minLens d' = d_minLens d ->
  tabs_okF d' ng alpha.
Proof.
  intros d d' ng alpha H E1 E2 E3 E4 t Ht. destruct (H t Ht) as [mn T]. exists mn.
  apply (tab_okF_frame d d'); assumption.
Qed.

Lemma mtf_okF_frame : forall d d', mtf_okF d -> d_mtfbase d' = d_mtfbase d -> d_mtfa d' = d_mtfa d -> mtf_okF d'.
Proof. intros d d' H E1 E2. unfold mtf_okF, mtfb in *. rewrite E1, E2. exact H. Qed.

Lemma blkF_frame : forall L L' d d', blkF L d ->
  sv_nblock L' = sv_nblock L -> sv_nblockMAX L' = sv_nblockMAX L ->
  d_small d' = d_small d -> d_tt d' = d_tt d -> d_ll16 d' = d_ll16 d -> d_unzftab d' = d_unzftab d ->
  blkF L' d'.
Proof.
  (intros L L' d d'; cps_intros (B1 & B2 & B3); intros E1 E2 E3 E4 E5 E6). unfold blkF. rewrite E1, E2, E6.
  split; [exact B1|]. split.
  - intros i Hi. rewrite (bsym_frame d d' E3 E4 E5). apply B2. exact Hi.
  - intros b Hb. rewrite (B3 b Hb). apply occ_ext. intros k Hk. symmetry. apply (bsym_frame d d' E3 E4 E5).
Qed.

Lemma cur_okF_frame : forall L L' d d', cur_okF L d ->
  sv_groupNo L' = sv_groupNo L -> sv_groupPos L' = sv_groupPos L -> sv_gSel L' = sv_gSel L ->
  sv_gMinlen L' = sv_gMinlen L -> sv_nSelectors L' = sv_nSelectors L -> sv_nGroups L' = sv_nGroups L ->
  d_sel d' = d_sel d -> d_minLens d' = d_minLens d ->
  cur_okF L' d'.
Proof.
  intros L L' d d' H E1 E2 E3 E4 E5 E6 E7 E8. unfold cur_okF in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8. exact H.
Qed.

Lemma alpha_ok_frame : forall L L' d d', alpha_ok L d ->
  sv_alphaSize L' = sv_alphaSize L -> sv_nblock L' = sv_nblock L ->
  d_nInUse d' = d_nInUse d -> d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d ->
  d_state d' <> 2 ->
  alpha_ok L' d'.
Proof.
  intros L L' d d' H E1 E2 E3 E4 E5 E6 NS. unfold alpha_ok in *. rewrite E1, E2, E3, E4, E5, E6.
  destruct H as [(A1 & A2 & A3 & A4 & A5 & _) B]. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma dinv_ML_alpha : forall L d, dinv_ML L d -> 3 <= sv_alphaSize L <= 258 /\ sv_EOB L = sv_alphaSize L - 1.
Proof. (intros L d; cps_intros (AL & G & _)). unfold alpha_ok, grp_okF in *. lia. Qed.
Lemma dinv_ML_gmn : forall L d, dinv_ML L d -> 1 <= sv_gMinlen L <= 20.
Proof.
  (intros L d; cps_intros (AL & G & T & _ & _ & C)). cps_destruct C as (_ & _ & _ & Hs & Hm).
  destruct (T (sv_gSel L) Hs) as [mn (len & lim0 & base0 & perm0 & mx & Hmm & _ & _ & Hmn)].
  rewrite Hm, Hmn. lia.
Qed.
