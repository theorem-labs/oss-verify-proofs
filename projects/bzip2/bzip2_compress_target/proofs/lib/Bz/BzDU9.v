(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM.   (* [comment removed for export] *)
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
Definition run_delta (ns N : Z) : Z := if ns =? BZ_RUNA then N else if ns =? BZ_RUNB then 2 * N else 0.
Lemma run_delta_A : forall N, run_delta 0 N = N. Proof. reflexivity. Qed.
Lemma run_delta_B : forall N, run_delta 1 N = 2 * N. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma run_delta_shift : forall ns N, 0 <= ns <= 1 -> run_delta ns N = N * 2 ^ ns.
Proof.
  intros ns N H. assert (C : ns = 0 \/ ns = 1) by lia.
  destruct C as [-> | ->]; [rewrite run_delta_A, Z.pow_0_r | rewrite run_delta_B, Z.pow_1_r]; lia.
Qed.

Lemma run_body_ret : forall L d s, 2097152 <= sv_N L -> run_body L d s = DRet BZ_DATA_ERROR L d s.
Proof. intros L d s H. unfold run_body. replace (2097152 <=? sv_N L) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma run_body_go : forall L d s, sv_N L < 2097152 ->
  run_body L d s = mtf_val_start BZ_X_MTF_3 (sv_set_N (sv_set_es L (sv_es L + run_delta (sv_nextSym L) (sv_N L))) (2 * sv_N L)) d s.
Proof.
  intros L d s H. unfold run_body, run_delta. replace (2097152 <=? sv_N L) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (sv_nextSym L =? BZ_RUNA); [reflexivity|]. destruct (sv_nextSym L =? BZ_RUNB); [reflexivity|].
  rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma run_write_done : forall n small uc nb es nbMAX d, es <= 0 ->
  run_write n small uc nb es nbMAX d = (nb, es, d, false).
Proof. intros [|n] small uc nb es nbMAX d H; cbn [run_write]; [reflexivity|]. replace (0 <? es) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma run_write_fail : forall n small uc nb es nbMAX d, 0 < es -> nbMAX <= nb ->
  run_write (S n) small uc nb es nbMAX d = (nb, es, d, true).
Proof.
  intros n small uc nb es nbMAX d H1 H2. cbn [run_write].
  replace (0 <? es) with true by (symmetry; apply Z.ltb_lt; lia). replace (nbMAX <=? nb) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma run_write_step : forall n small uc nb es nbMAX d, 0 < es -> nb < nbMAX ->
  run_write (S n) small uc nb es nbMAX d =
  run_write n small uc (nb + 1) (es - 1) nbMAX (if small then d_set_ll16 d (zset (d_ll16 d) nb uc) else d_set_tt d (zset (d_tt d) nb uc)).
Proof.
  intros n small uc nb es nbMAX d H1 H2. cbn [run_write].
  replace (0 <? es) with true by (symmetry; apply Z.ltb_lt; lia). replace (nbMAX <=? nb) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_L9 (F : nat) (L : dsv) (d : dst) (s : dstrm) (uc nb es : Z) : dres :=
  let '(nb', es', d2, failed) := run_write (Z.to_nat es) (smallb d) uc nb es (sv_nblockMAX L) d in
  let L2 := sv_set_es (sv_set_nblock L nb') es' in
  if failed then DRet BZ_DATA_ERROR L2 d2 s else dgo F (sym_dispatch L2 d2 s).

(* [comment removed for export] *)
Definition run_uc (d : dst) : Z := zget (d_s2u d) (zget (d_mtfa d) (zget (d_mtfbase d) 0)).
Definition run_d1 (L : dsv) (d : dst) : dst :=
  let es := sv_es L + 1 in let uc := run_uc d in
  d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + es)).

Lemma smallb_set_unzftab : forall d a, smallb (d_set_unzftab d a) = smallb d.
Proof. intros [] a; reflexivity. Qed.

Lemma run_exit_K : forall F L d s,
  dgo F (run_exit L d s) = K_L9 F L (run_d1 L d) s (run_uc d) (sv_nblock L) (sv_es L + 1).
Proof.
  intros F L d s. unfold run_exit, K_L9, run_d1, run_uc. cbv zeta. rewrite smallb_set_unzftab.
  destruct (run_write _ _ _ _ _ _ _) as [[[nb' es'] d2] failed]. destruct failed; reflexivity.
Qed.

Lemma K_L9_exit : forall F L d s uc nb es, es <= 0 ->
  K_L9 F L d s uc nb es = dgo F (sym_dispatch (sv_set_es (sv_set_nblock L nb) es) d s).
Proof. intros F L d s uc nb es H. unfold K_L9. rewrite run_write_done by exact H. reflexivity. Qed.

Lemma K_L9_fail : forall F L d s uc nb es, 0 < es -> sv_nblockMAX L <= nb ->
  K_L9 F L d s uc nb es = DRet BZ_DATA_ERROR (sv_set_es (sv_set_nblock L nb) es) d s.
Proof.
  intros F L d s uc nb es H1 H2. unfold K_L9. replace (Z.to_nat es) with (S (Z.to_nat (es - 1))) by lia.
  rewrite run_write_fail by assumption. reflexivity.
Qed.

Lemma K_L9_step : forall F L d s uc nb es, 0 < es -> nb < sv_nblockMAX L ->
  K_L9 F L d s uc nb es = K_L9 F L (dstore d nb uc) s uc (nb + 1) (es - 1).
Proof.
  intros F L d s uc nb es H1 H2. unfold K_L9. replace (Z.to_nat es) with (S (Z.to_nat (es - 1))) by lia.
  rewrite run_write_step by assumption. rewrite smallb_dstore. unfold dstore. destruct (smallb d); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition run_inv (d : dst) (uc nb0 E j : Z) : Prop :=
  (forall i, 0 <= i < nb0 + j -> 0 <= bsym d i < 256) /\
  (forall c, 0 <= c < 256 -> zget (d_unzftab d) c = occ (bsym d) (Z.to_nat (nb0 + j)) c + (if c =? uc then E - j else 0)).

(* [comment removed for export] *)
Lemma run_inv_entry : forall d uc nb0 E,
  0 <= nb0 -> 0 <= uc < 256 ->
  (forall i, 0 <= i < nb0 -> 0 <= bsym d i < 256) ->
  (forall c, 0 <= c < 256 -> zget (d_unzftab d) c = occ (bsym d) (Z.to_nat nb0) c) ->
  run_inv (d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E))) uc nb0 E 0.
Proof.
  intros d uc nb0 E Hnb Huc SYM HIST.
  assert (BS : forall i, bsym (d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E))) i = bsym d i)
    by (apply bsym_frame; destruct d; reflexivity).
  split.
  - intros i Hi. rewrite BS. apply SYM. lia.
  - intros c Hc. rewrite Z.add_0_r, Z.sub_0_r. rewrite (occ_ext _ (bsym d)) by (intros; apply BS).
    replace (d_unzftab (d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)))) with (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)) by (destruct d; reflexivity).
    rewrite zget_zset. destruct (Z.eqb_spec c uc) as [->|NE]; rewrite HIST by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma run_inv_step : forall d uc nb0 E j, 0 <= nb0 -> 0 <= j -> 0 <= uc < 256 ->
  run_inv d uc nb0 E j -> run_inv (dstore d (nb0 + j) uc) uc nb0 E (j + 1).
Proof.
  intros d uc nb0 E j Hnb Hj Huc [SYM HIST]. split.
  - intros i Hi. rewrite bsym_dstore, zfupd_eq. destruct (Z.eqb_spec i (nb0 + j)); [lia|]. apply SYM. lia.
  - intros c Hc. rewrite dstore_unzftab. replace (nb0 + (j + 1)) with (nb0 + j + 1) by lia.
    rewrite occ_dstore_new by lia. rewrite HIST by lia. destruct (Z.eqb_spec uc c), (Z.eqb_spec c uc); lia.
Qed.

(* [comment removed for export] *)
Lemma run_inv_exit : forall d uc nb0 E,
  run_inv d uc nb0 E E ->
  (forall i, 0 <= i < nb0 + E -> 0 <= bsym d i < 256) /\
  (forall c, 0 <= c < 256 -> zget (d_unzftab d) c = occ (bsym d) (Z.to_nat (nb0 + E)) c).
Proof.
  intros d uc nb0 E [SYM HIST]. split; [exact SYM|]. intros c Hc. rewrite HIST by lia. rewrite Z.sub_diag. destruct (c =? uc); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dinv_ML_esN : forall L d e n, dinv_ML L d -> dinv_ML (sv_set_N (sv_set_es L e) n) d.
Proof.
  (intros L d e n; cps_intros (AL & GR & TB & MT & BL & CU)). unfold dinv_ML.
  split; [apply (alpha_ok_frame L _ d d AL); try reflexivity; exact (alpha_ok_state L d AL)|].
  split; [apply (grp_okF_frame L _ d d GR); reflexivity|].
  split; [exact TB|]. split; [exact MT|].
  split; [apply (blkF_frame L _ d d BL); reflexivity|].
  apply (cur_okF_frame L _ d d CU); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ml_restF (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ grp_okF L d /\ tabs_okF d (sv_nGroups L) (sv_alphaSize L) /\ mtf_okF d /\ cur_okF L d.
Lemma ml_restF_of_ML : forall L d, dinv_ML L d -> ml_restF L d.
Proof. (intros L d; cps_intros (A & G & T & M & _ & C)). unfold ml_restF. tauto. Qed.
Lemma ml_restF_set_unzftab : forall L d a, ml_restF L d -> ml_restF L (d_set_unzftab d a).
Proof.
  (intros L d a; cps_intros (A & G & T & M & C)). unfold ml_restF.
  split; [apply (alpha_ok_frame L L d); try assumption; try (destruct d; reflexivity); destruct d; exact (alpha_ok_state L _ A)|].
  split; [apply (grp_okF_frame L L d); try assumption; destruct d; reflexivity|].
  split; [apply (tabs_okF_frame d); try assumption; destruct d; reflexivity|].
  split; [apply (mtf_okF_frame d); try assumption; destruct d; reflexivity|].
  apply (cur_okF_frame L L d); try assumption; destruct d; reflexivity.
Qed.
Lemma ml_restF_dstore : forall L d nb uc, ml_restF L d -> ml_restF L (dstore d nb uc).
Proof.
  (intros L d nb uc; cps_intros (A & G & T & M & C)). unfold ml_restF, dstore.
  destruct (smallb d).
  - split; [apply (alpha_ok_frame L L d); try assumption; try (destruct d; reflexivity); destruct d; exact (alpha_ok_state L _ A)|].
    split; [apply (grp_okF_frame L L d); try assumption; destruct d; reflexivity|].
    split; [apply (tabs_okF_frame d); try assumption; destruct d; reflexivity|].
    split; [apply (mtf_okF_frame d); try assumption; destruct d; reflexivity|].
    apply (cur_okF_frame L L d); try assumption; destruct d; reflexivity.
  - split; [apply (alpha_ok_frame L L d); try assumption; try (destruct d; reflexivity); destruct d; exact (alpha_ok_state L _ A)|].
    split; [apply (grp_okF_frame L L d); try assumption; destruct d; reflexivity|].
    split; [apply (tabs_okF_frame d); try assumption; destruct d; reflexivity|].
    split; [apply (mtf_okF_frame d); try assumption; destruct d; reflexivity|].
    apply (cur_okF_frame L L d); try assumption; destruct d; reflexivity.
Qed.

(* [comment removed for export] *)
Definition dinv_L9 (L : dsv) (d : dst) (uc E j : Z) : Prop :=
  ml_restF L d /\ run_inv d uc (sv_nblock L) E j /\ 0 <= uc < 256 /\ 0 <= j /\ j + 1 <= E <= 8388609 /\
  sv_nblock L + j <= sv_nblockMAX L /\ 2 <= sv_nextSym L < sv_alphaSize L.

(* [comment removed for export] *)
Lemma dinv_ML_of_rest : forall L d nb e,
  ml_restF L d -> 0 <= nb <= sv_nblockMAX L -> nb <= 900000 ->
  (forall i, 0 <= i < nb -> 0 <= bsym d i < 256) -> hist_ok (zget (d_unzftab d)) (bsym d) (Z.to_nat nb) ->
  dinv_ML (sv_set_es (sv_set_nblock L nb) e) d.
Proof.
  (intros L d nb e; cps_intros (AL & GR & TB & MT & CU); intros NB NB9 SYM HIST). unfold dinv_ML. split.
  { unfold alpha_ok in *. destruct AL as [A B]. destruct L; cbn in *. split; [exact A| lia]. }
  split; [apply (grp_okF_frame L _ d d GR); try reflexivity; destruct L; reflexivity|].
  split; [destruct L; exact TB|]. split; [exact MT|].
  split; [| apply (cur_okF_frame L _ d d CU); destruct L; reflexivity].
  unfold blkF. destruct L; cbn in *. split; [exact NB|]. split; [exact SYM| exact HIST].
Qed.

(* [comment removed for export] *)
Lemma dstore_fast : forall d nb uc, d_small d = 0 -> dstore d nb uc = d_set_tt d (zset (d_tt d) nb uc).
Proof. intros d nb uc H. unfold dstore. rewrite (smallb_false d H). reflexivity. Qed.
Lemma dstore_smallm : forall d nb uc, d_small d <> 0 -> dstore d nb uc = d_set_ll16 d (zset (d_ll16 d) nb uc).
Proof. intros d nb uc H. unfold dstore. rewrite (smallb_true d H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma dinv_L9_entry : forall L d uc E,
  dinv_ML L d -> 0 <= uc < 256 -> 1 <= E <= 8388609 -> 2 <= sv_nextSym L < sv_alphaSize L ->
  dinv_L9 L (d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E))) uc E 0.
Proof.
  intros L d uc E ML UC HE NS. cps_pose ML as (AL & GR & _ & _ & (B1 & B2 & B3) & _).
  unfold dinv_L9. split; [apply ml_restF_set_unzftab; apply ml_restF_of_ML; exact ML|].
  split; [apply run_inv_entry; [lia | exact UC | exact B2 | exact B3]|].
  repeat split; try lia.
Qed.
Lemma run_hist0 : forall L d uc,
  dinv_ML L d -> 0 <= uc < 256 ->
  let d1 := d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0)) in
  (forall i, 0 <= i < sv_nblock L -> 0 <= bsym d1 i < 256) /\ hist_ok (zget (d_unzftab d1)) (bsym d1) (Z.to_nat (sv_nblock L)).
Proof.
  intros L d uc ML UC. cps_pose ML as (AL & GR & _ & _ & (B1 & B2 & B3) & _). cbv zeta.
  pose proof (run_inv_exit _ uc (sv_nblock L) 0 (run_inv_entry d uc (sv_nblock L) 0 ltac:(lia) UC B2 B3)) as [X Y].
  rewrite (Z.add_0_r (sv_nblock L)) in X, Y. split; [exact X | exact Y].
Qed.

(* [comment removed for export] *)
Lemma dinv_L9_step : forall L d uc E j, dinv_L9 L d uc E j -> j + 2 <= E -> sv_nblock L + j < sv_nblockMAX L ->
  dinv_L9 L (dstore d (sv_nblock L + j) uc) uc E (j + 1).
Proof.
  (intros L d uc E j; cps_intros (MR & RI & UCR & J0 & EJ & ROOM & NSR); intros HE HR). unfold dinv_L9.
  split; [apply ml_restF_dstore; exact MR|].
  split; [apply run_inv_step; [ | lia | exact UCR | exact RI] |]; [unfold ml_restF, alpha_ok in MR; lia|].
  repeat split; try lia.
Qed.
Lemma dinv_L9_exit : forall L d uc E j, dinv_L9 L d uc E j -> j + 1 = E -> sv_nblock L + j < sv_nblockMAX L -> sv_nblock L + E <= 900000 ->
  dinv_SYM (sv_set_es (sv_set_nblock L (sv_nblock L + E)) 0) (dstore d (sv_nblock L + j) uc).
Proof.
  (intros L d uc E j; cps_intros (MR & RI & UCR & J0 & EJ & ROOM & NSR); intros HE HR H9).
  assert (NB0 : 0 <= sv_nblock L) by (unfold ml_restF, alpha_ok in MR; lia).
  pose proof (run_inv_step d uc (sv_nblock L) E j NB0 J0 UCR RI) as RI'. replace (j + 1) with E in RI' by lia.
  destruct (run_inv_exit _ _ _ _ RI') as [SYM HIST].
  unfold dinv_SYM. split.
  - apply dinv_ML_of_rest; [apply ml_restF_dstore; exact MR | lia | lia | exact SYM | exact HIST].
  - destruct L; cbn in *; lia.
Qed.
Lemma dinv_L9_step_fast : forall L d uc E j, dinv_L9 L d uc E j -> d_small d = 0 -> j + 2 <= E -> sv_nblock L + j < sv_nblockMAX L ->
  dinv_L9 L (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc)) uc E (j + 1).
Proof. intros L d uc E j DI SM HE HR. rewrite <- (dstore_fast d _ _ SM). apply dinv_L9_step; assumption. Qed.
Lemma dinv_L9_step_small : forall L d uc E j, dinv_L9 L d uc E j -> d_small d <> 0 -> j + 2 <= E -> sv_nblock L + j < sv_nblockMAX L ->
  dinv_L9 L (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc)) uc E (j + 1).
Proof. intros L d uc E j DI SM HE HR. rewrite <- (dstore_smallm d _ _ SM). apply dinv_L9_step; assumption. Qed.
Lemma dinv_L9_exit_fast : forall L d uc E j, dinv_L9 L d uc E j -> d_small d = 0 -> j + 1 = E -> sv_nblock L + j < sv_nblockMAX L ->
  sv_nblock L + E <= 900000 ->
  dinv_SYM (sv_set_es (sv_set_nblock L (sv_nblock L + E)) 0) (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc)).
Proof. intros L d uc E j DI SM HE HR H9. rewrite <- (dstore_fast d _ _ SM). apply dinv_L9_exit; assumption. Qed.
Lemma dinv_L9_exit_small : forall L d uc E j, dinv_L9 L d uc E j -> d_small d <> 0 -> j + 1 = E -> sv_nblock L + j < sv_nblockMAX L ->
  sv_nblock L + E <= 900000 ->
  dinv_SYM (sv_set_es (sv_set_nblock L (sv_nblock L + E)) 0) (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc)).
Proof. intros L d uc E j DI SM HE HR H9. rewrite <- (dstore_smallm d _ _ SM). apply dinv_L9_exit; assumption. Qed.

(* [comment removed for export] *)
Lemma dinv_SYM_run0 : forall L d uc, dinv_ML L d -> 0 <= uc < 256 -> 2 <= sv_nextSym L < sv_alphaSize L ->
  dinv_SYM (sv_set_es (sv_set_nblock L (sv_nblock L)) 0) (d_set_unzftab d (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0))).
Proof.
  intros L d uc ML UC NS. destruct (run_hist0 L d uc ML UC) as [SYM HIST].
  cps_pose ML as (AL & GR & _ & _ & (B1 & _ & _) & _).
  unfold dinv_SYM. split.
  - apply dinv_ML_of_rest; [apply ml_restF_set_unzftab; apply ml_restF_of_ML; exact ML | exact B1 | unfold alpha_ok in AL; lia | exact SYM | exact HIST].
  - destruct L; cbn in *; lia.
Qed.
