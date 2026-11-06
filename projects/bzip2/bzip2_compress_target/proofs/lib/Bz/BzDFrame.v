(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition dk (d d' : dst) : Prop := d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\ d_state d' = d_state d.
(* [comment removed for export] *)
Definition dk2 (d d' : dst) : Prop := d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\ d_state d' = BZ_X_OUTPUT.

Lemma dk_refl : forall d, dk d d. Proof. intros d. repeat split; reflexivity. Qed.
Lemma dk_trans : forall d1 d2 d3, dk d1 d2 -> dk d2 d3 -> dk d1 d3.
Proof. (intros d1 d2 d3; cps_intros (A1 & A2 & A3); cps_intros (B1 & B2 & B3)). unfold dk. rewrite B1, B2, B3. auto. Qed.
Lemma dk_dk2 : forall d1 d2 d3, dk d1 d2 -> dk2 d2 d3 -> dk2 d1 d3.
Proof. (intros d1 d2 d3; cps_intros (A1 & A2 & A3); cps_intros (B1 & B2 & B3)). unfold dk2. rewrite B1, B2, B3. auto. Qed.

Ltac dk_setters := unfold dk, dk2; cbn [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
  d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
  d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
  d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
  d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
  d_set_base d_set_perm d_set_minLens d_set_sv]; repeat split; try reflexivity; try assumption.

(* [comment removed for export] *)
Ltac pcbn0 := cbn [fst snd d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
  d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
  d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
  d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
  d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
  d_set_base d_set_perm d_set_minLens d_set_sv].
(* [comment removed for export] *)
Ltac pcbn0_all := cbn [fst snd d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
  d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
  d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
  d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
  d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
  d_set_base d_set_perm d_set_minLens d_set_sv] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rand_upd_dk : forall d, dk d (rand_upd d).
Proof. intros d. unfold rand_upd. destruct (d_rNToGo d =? 0); dk_setters. Qed.
Lemma set_ll4_dk : forall d i n, dk d (set_ll4 d i n). Proof. intros. unfold set_ll4. dk_setters. Qed.
Lemma set_ll_dk : forall d i n, dk d (set_ll d i n).
Proof. intros. unfold set_ll. eapply dk_trans; [| apply set_ll4_dk]. dk_setters. Qed.
Lemma makeMaps_d_dk : forall d, dk d (makeMaps_d d).
Proof. intros d. unfold makeMaps_d. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0). dk_setters. Qed.
Lemma make_tables_dk : forall n t aS d, dk d (make_tables n t aS d).
Proof.
  induction n as [|n IH]; intros t aS d; cbn [make_tables]; [apply dk_refl|].
  destruct (minmax_len _ _ _ _ _ _) as [mn mx]. destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[lim bas] prm].
  eapply dk_trans; [| apply IH]. dk_setters.
Qed.
Lemma mtf_init_dk : forall d, dk d (mtf_init d).
Proof. intros d. unfold mtf_init. destruct (mtfinit_i _ _ _ _ _) as [a b]. dk_setters. Qed.
Lemma mtf_decode_dk : forall d nn, dk d (snd (mtf_decode d nn)).
Proof.
  intros d nn. unfold mtf_decode.
  repeat first [ destruct (mtf_pull _ _ _ _) as [? ?] | destruct (mtf_sh4 _ _ _ _) as [? ?] | destruct (mtfrb_i _ _ _ _ _) as [? ?]
               | match goal with |- context [if ?b then _ else _] => destruct b end ]; pcbn0; dk_setters.
Qed.
Lemma tvec_small_dk : forall n i d, dk d (tvec_small n i d).
Proof.
  induction n as [|n IH]; intros i d; cbn [tvec_small]; [apply dk_refl|].
  eapply dk_trans; [| apply IH]. eapply dk_trans; [apply set_ll_dk|]. dk_setters.
Qed.
Lemma prev_loop_dk : forall n i j d, dk d (snd (prev_loop n i j d)).
Proof.
  induction n as [|n IH]; intros i j d; cbn [prev_loop]; [apply dk_refl|].
  destruct (j =? d_origPtr d); pcbn0; [apply set_ll_dk|].
  specialize (IH j (get_ll d j) (set_ll d j i)). destruct (prev_loop n _ _ _) as [[i' j'] d']. pcbn0_all.
  eapply dk_trans; [apply set_ll_dk| exact IH].
Qed.
Lemma run_write_dk : forall n sm uc nb es mx d, dk d (snd (fst (run_write n sm uc nb es mx d))).
Proof.
  induction n as [|n IH]; intros sm uc nb es mx d; cbn [run_write]; [apply dk_refl|].
  destruct (0 <? es); [| apply dk_refl]. destruct (mx <=? nb); [apply dk_refl|].
  match goal with |- dk d (snd (fst (run_write n sm uc ?nb' ?es' mx ?d1))) => specialize (IH sm uc nb' es' mx d1) end.
  destruct (run_write n _ _ _ _ _ _) as [[[a b] d'] f']. pcbn0_all.
  eapply dk_trans; [| exact IH]. destruct sm; dk_setters.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shape (d : dst) (s : dstrm) (ok_lbl : Z -> Prop) (r : dres) : Prop :=
  match r with
  | DGo lbl' L' d' s' => s' = s /\ dk d d' /\ ok_lbl lbl'
  | DRet rv L' d' s' => s' = s /\ (dk d d' \/ dk2 d d')
  | DRetNoSave rv L' d' s' => s' = s /\ (dk d d' \/ dk2 d d')
  end.

(* [comment removed for export] *)
Ltac pcbn := cbn [fst snd shape d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
  d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
  d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
  d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
  d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
  d_set_base d_set_perm d_set_minLens d_set_sv].
Ltac pcbn_in H := cbn [fst snd shape d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
  d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
  d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
  d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
  d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
  d_set_base d_set_perm d_set_minLens d_set_sv] in H.
(* [comment removed for export] *)


Definition main_lbl (l : Z) : Prop := 36 <= l <= 41.

Lemma shape_mono : forall d s (P Q : Z -> Prop) r, (forall l, P l -> Q l) -> shape d s P r -> shape d s Q r.
Proof. intros d s P Q r H. destruct r; pcbn; intuition auto. Qed.
Lemma shape_dk : forall d0 d s P r, dk d0 d -> shape d s P r -> shape d0 s P r.
Proof.
  intros d0 d s P r K. destruct r; pcbn; intros (A & B); split; try exact A.
  - destruct B as [B C]. split; [eapply dk_trans; eassumption| exact C].
  - destruct B as [B|B]; [left; eapply dk_trans; eassumption| right; eapply dk_dk2; eassumption].
  - destruct B as [B|B]; [left; eapply dk_trans; eassumption| right; eapply dk_dk2; eassumption].
Qed.

Lemma shape_DRet : forall d s P rv L d', dk d d' \/ dk2 d d' -> shape d s P (DRet rv L d' s).
Proof. intros. pcbn. auto. Qed.
Lemma shape_DRetNoSave : forall d s P rv L d', dk d d' \/ dk2 d d' -> shape d s P (DRetNoSave rv L d' s).
Proof. intros. pcbn. auto. Qed.
Lemma dk_set_k0 : forall d v, dk d (d_set_k0 d v). Proof. intros. dk_setters. Qed.

Lemma mtf_val_start_shape : forall lbl1 L d s, shape d s (fun l => l = lbl1) (mtf_val_start lbl1 L d s).
Proof.
  intros. unfold mtf_val_start. destruct (sv_groupPos L =? 0); [destruct (sv_nSelectors L <=? sv_groupNo L + 1)|]; pcbn;
  repeat split; try reflexivity; left; apply dk_refl.
Qed.
Lemma run_body_shape : forall L d s, shape d s (fun l => l = 38) (run_body L d s).
Proof. intros. unfold run_body. destruct (2097152 <=? sv_N L); [pcbn; split; [reflexivity| left; apply dk_refl]| apply mtf_val_start_shape]. Qed.

Lemma dk2_dk : forall d1 d2 d3, dk2 d1 d2 -> dk d2 d3 -> dk2 d1 d3.
Proof. (intros d1 d2 d3; cps_intros (A1 & A2 & A3); cps_intros (B1 & B2 & B3)). unfold dk2. rewrite B1, B2, B3. auto. Qed.

(* [comment removed for export] *)
Lemma block_end_shape : forall L d s P, shape d s P (block_end L d s).
Proof.
  intros L d s P. unfold block_end.
  destruct ((d_origPtr d <? 0) || (sv_nblock L <=? d_origPtr d)); [pcbn; split; [reflexivity| left; apply dk_refl]|].
  destruct (unz_check _ _ _ _ <? 256); [pcbn; split; [reflexivity| left; apply dk_refl]|].
  destruct (cf_check1 _ _ _ _ <? 257); [pcbn; split; [reflexivity| left; dk_setters]|].
  destruct (cf_check2 _ _ _ <? 257); [pcbn; split; [reflexivity| left; dk_setters]|].
  cbv zeta.
  match goal with |- shape d s P (if smallb ?d2 then _ else _) => assert (K2 : dk2 d d2) by dk_setters; destruct (smallb d2) end.
  - match goal with |- context [tvec_small ?n ?i ?d3] =>
      assert (K4 : dk2 d (tvec_small n i d3)) by (eapply dk2_dk; [| apply tvec_small_dk]; dk_setters) end.
    match goal with |- context [prev_loop ?n ?i ?j ?d4] =>
      pose proof (prev_loop_dk n i j d4) as K5; destruct (prev_loop n i j d4) as [[i5 j5] d5] end.
    pcbn_in K5. assert (K5' : dk2 d d5) by (eapply dk2_dk; [exact K4| exact K5]). clear K4 K5.
    cbv zeta.
    match goal with |- shape d s P (if _ <=? d_tPos ?d7 then _ else _) =>
      assert (K7 : dk2 d d7) by (destruct (d_rand _ =? 0); eapply dk2_dk; [exact K5'| dk_setters| exact K5' | dk_setters]) end.
    destruct (d_rand _ =? 0);
      (destruct (_ <=? _); [apply shape_DRetNoSave; right; exact K7|]; cbv zeta; apply shape_DRet; right;
       match goal with |- dk2 d (if d_rand ?d8 =? 0 then _ else _) =>
         assert (K8 : dk2 d d8) by (eapply dk2_dk; [exact K7| dk_setters]);
         destruct (d_rand d8 =? 0); [exact K8| eapply dk2_dk; [exact K8| eapply dk_trans; [apply rand_upd_dk| apply dk_set_k0]]] end).
  - destruct (tinv_fast _ _ _ _) as [tt1 cf3]. cbv zeta.
    match goal with |- shape d s P (if _ <=? d_tPos ?d5 then _ else _) =>
      assert (K5 : dk2 d d5) by (destruct (d_rand _ =? 0); dk_setters) end.
    destruct (d_rand _ =? 0);
      (destruct (_ <=? _); [apply shape_DRetNoSave; right; exact K5|]; cbv zeta; apply shape_DRet; right;
       match goal with |- dk2 d (if d_rand ?d6 =? 0 then _ else _) =>
         assert (K6 : dk2 d d6) by (eapply dk2_dk; [exact K5| dk_setters]);
         destruct (d_rand d6 =? 0); [exact K6| eapply dk2_dk; [exact K6| eapply dk_trans; [apply rand_upd_dk| apply dk_set_k0]]] end).
Qed.

Lemma sym_dispatch_shape : forall L d s, shape d s main_lbl (sym_dispatch L d s).
Proof.
  intros L d s. unfold sym_dispatch.
  destruct (sv_nextSym L =? sv_EOB L); [apply block_end_shape|].
  destruct ((sv_nextSym L =? BZ_RUNA) || (sv_nextSym L =? BZ_RUNB)); [eapply shape_mono; [| apply run_body_shape]; unfold main_lbl; intros; lia|].
  destruct (sv_nblockMAX L <=? sv_nblock L); [pcbn; split; [reflexivity| left; apply dk_refl]|].
  pose proof (mtf_decode_dk d (sv_nextSym L - 1)) as K1. destruct (mtf_decode d _) as [uc d1]. pcbn_in K1.
  match goal with |- shape d s main_lbl (mtf_val_start _ ?L3 ?d3 s) =>
    eapply shape_dk with (d := d3); [| eapply shape_mono; [| apply mtf_val_start_shape]; unfold main_lbl; cbv beta; intros; subst; unfold BZ_X_MTF_5; lia] end.
  eapply dk_trans; [exact K1|]. destruct (smallb _); dk_setters.
Qed.

Lemma run_exit_shape : forall L d s, shape d s main_lbl (run_exit L d s).
Proof.
  intros L d s. unfold run_exit.
  match goal with |- context [run_write ?n ?sm ?uc ?nb ?es ?mx ?d1] =>
    pose proof (run_write_dk n sm uc nb es mx d1) as K; destruct (run_write n sm uc nb es mx d1) as [[[nb' es'] d2] failed] end.
  pcbn_in K. assert (K' : dk d d2) by (eapply dk_trans; [| exact K]; dk_setters).
  destruct failed; [pcbn; split; [reflexivity| left; exact K']|].
  eapply shape_dk; [exact K'| apply sym_dispatch_shape].
Qed.

Lemma mtf_val_loop_shape : forall which L d s, which = 1 \/ which = 3 \/ which = 5 ->
  shape d s main_lbl (mtf_val_loop which L d s).
Proof.
  intros which L d s Hw. unfold mtf_val_loop.
  destruct (20 <? sv_zn L); [pcbn; split; [reflexivity| left; apply dk_refl]|].
  destruct (sv_zvec L <=? _).
  - destruct ((_ <? 0) || (_ <=? _)); [pcbn; split; [reflexivity| left; apply dk_refl]|].
    destruct (which =? 3).
    + destruct ((_ =? BZ_RUNA) || (_ =? BZ_RUNB)); [eapply shape_mono; [| apply run_body_shape]; unfold main_lbl; intros; lia| apply run_exit_shape].
    + apply sym_dispatch_shape.
  - pcbn. split; [reflexivity|]. split; [apply dk_refl|]. unfold main_lbl. lia.
Qed.

Lemma map2_outer_shape : forall n i L d s, shape d s (fun l => l = 29 \/ l = 30) (map2_outer n i L d s).
Proof.
  induction n as [|n IH]; intros i L d s; cbn [map2_outer]; [pcbn; split; [reflexivity| left; apply dk_refl]|].
  destruct (16 <=? i).
  - pose proof (makeMaps_d_dk d) as K. destruct (d_nInUse (makeMaps_d d) =? 0); pcbn; (split; [reflexivity|]); [left; exact K| split; [exact K| right; reflexivity]].
  - destruct (negb _); [pcbn; split; [reflexivity| split; [apply dk_refl| left; reflexivity]]| apply IH].
Qed.

Lemma coding_check_shape : forall L d s, shape d s (fun l => l = 34) (coding_check L d s).
Proof. intros. unfold coding_check. destruct (_ || _); pcbn; repeat split; try reflexivity; left; apply dk_refl. Qed.

Lemma after_tables_shape : forall L d s, shape d s (fun l => l = 36) (after_tables L d s).
Proof.
  intros L d s. unfold after_tables.
  match goal with |- shape d s _ (mtf_val_start _ ?L3 ?d3 s) =>
    eapply shape_dk with (d := d3); [| eapply shape_mono; [| apply mtf_val_start_shape]; cbv beta; intros; subst; reflexivity] end.
  eapply dk_trans; [apply make_tables_dk|]. eapply dk_trans; [| apply mtf_init_dk]. dk_setters.
Qed.

(* [comment removed for export] *)
Definition next_ok (lbl lbl' : Z) : Prop :=
  10 <= lbl' <= 50 /\
  (lbl <= 18 -> lbl' = lbl + 1 \/ lbl' = 42) /\ (lbl = 19 -> lbl' = 20) /\ (20 <= lbl -> 20 <= lbl') /\ (42 <= lbl -> 42 <= lbl').

Lemma gb_after_shape : forall lbl v L d s, 10 <= lbl <= 50 ->
  match gb_after lbl v L d s with
  | DGo lbl' L' d' s' => s' = s /\ next_ok lbl lbl' /\ d_cccrc d' = d_cccrc d /\ d_state d' = d_state d /\
                         d_blockNo d' = d_blockNo d + (if lbl =? 19 then 1 else 0)
  | DRet rv L' d' s' => s' = s /\ d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\
                         (d_state d' = d_state d \/ (d_state d' = BZ_X_OUTPUT /\ 20 <= lbl <= 41) \/ d_state d' = BZ_X_IDLE)
  | DRetNoSave rv L' d' s' => s' = s /\ d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\
                         (d_state d' = d_state d \/ (d_state d' = BZ_X_OUTPUT /\ 20 <= lbl <= 41) \/ d_state d' = BZ_X_IDLE)
  end.
Proof.
  intros lbl v L d s Hl.
  (* [comment removed for export] *)
  assert (USE : forall P r, 20 <= lbl <= 41 -> (forall l, P l -> 20 <= l <= 41) -> shape d s P r ->
    match r with
    | DGo lbl' L' d' s' => s' = s /\ next_ok lbl lbl' /\ d_cccrc d' = d_cccrc d /\ d_state d' = d_state d /\
                           d_blockNo d' = d_blockNo d + (if lbl =? 19 then 1 else 0)
    | DRet rv L' d' s' => s' = s /\ d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\
                           (d_state d' = d_state d \/ (d_state d' = BZ_X_OUTPUT /\ 20 <= lbl <= 41) \/ d_state d' = BZ_X_IDLE)
    | DRetNoSave rv L' d' s' => s' = s /\ d_cccrc d' = d_cccrc d /\ d_blockNo d' = d_blockNo d /\
                           (d_state d' = d_state d \/ (d_state d' = BZ_X_OUTPUT /\ 20 <= lbl <= 41) \/ d_state d' = BZ_X_IDLE)
    end).
  { intros P r H20 HP SH. destruct r as [l' L' d' s'|rv L' d' s'|rv L' d' s']; pcbn_in SH.
    - cps_destruct SH as (-> & (K1 & K2 & K3) & Pl). pose proof (HP _ Pl). replace (lbl =? 19) with false by (symmetry; apply Z.eqb_neq; lia).
      repeat split; try assumption; unfold next_ok; try lia.
    - destruct SH as (-> & [[K1 [K2 K3]]|[K1 [K2 K3]]]); repeat split; try assumption; [left; exact K3| right; left; split; [exact K3| lia]].
    - destruct SH as (-> & [[K1 [K2 K3]]|[K1 [K2 K3]]]); repeat split; try assumption; [left; exact K3| right; left; split; [exact K3| lia]]. }
  unfold gb_after.
  assert (Hk : exists k, (k <= 40)%nat /\ lbl = Z.of_nat k + 10) by (exists (Z.to_nat (lbl - 10)); lia).
  cps_destruct Hk as (k & Hk40 & ->). clear Hl.
  Ltac fin_go := cbn [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
  d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
  d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv d_set_sbcrc d_set_blockNo d_set_bs100k d_set_tt_al d_set_ll_al d_set_origPtr d_set_rand
                      d_set_inUse16 d_set_inUse d_set_selMtf d_set_sel d_set_len d_set_minLens d_set_limit d_set_base d_set_perm d_set_sccrc d_set_state];
                 repeat split; try reflexivity; unfold next_ok, BZ_X_IDLE, BZ_X_OUTPUT; try lia.
  let rec splitk n := lazymatch n with O => exfalso; lia | S ?n' => destruct k as [|k]; [| splitk n'] end in
  splitk 41%nat.
  (* [comment removed for export] *)
  all: match goal with |- context [Z.of_nat ?kk + 10] => let v := eval cbv in (Z.of_nat kk + 10) in change (Z.of_nat kk + 10) with v in * end.
  all: match goal with |- context [Z.to_nat ?e] => let v := eval cbv in (Z.to_nat e) in change (Z.to_nat e) with v end.
  all: cbn [Z.eqb Pos.eqb].
  all: repeat match goal with |- context [if ?b then _ else _] => lazymatch b with context [gb_after] => fail | _ => destruct b end end.
  all: try match goal with |- context [sel_undo ?a1 ?a2 ?a3 ?a4 ?a5] => destruct (sel_undo a1 a2 a3 a4 a5) end.
  (* [comment removed for export] *)
  Ltac sub_shape_ok d0 d1 := first [ is_evar d0 | constr_eq d0 d1 ].
  Ltac sub_shape := lazymatch goal with
    | |- shape ?d0 _ _ (map2_outer _ _ _ ?d1 _) => sub_shape_ok d0 d1; apply map2_outer_shape
    | |- shape ?d0 _ _ (coding_check _ ?d1 _) => sub_shape_ok d0 d1; apply coding_check_shape
    | |- shape ?d0 _ _ (after_tables _ ?d1 _) => sub_shape_ok d0 d1; apply after_tables_shape
    | |- shape ?d0 _ _ (mtf_val_start _ _ ?d1 _) => sub_shape_ok d0 d1; apply mtf_val_start_shape
    | |- shape ?d0 _ _ (mtf_val_loop _ _ ?d1 _) => sub_shape_ok d0 d1; apply mtf_val_loop_shape; lia
    | |- shape ?d0 _ _ (run_body _ ?d1 _) => sub_shape_ok d0 d1; apply run_body_shape
    end.
  all: first [ lazymatch goal with
               | |- match ?r with DGo _ _ _ _ => _ | _ => _ end =>
                   eapply USE; [lia| | first [sub_shape | eapply shape_dk; [| sub_shape]; dk_setters]]; cbv beta; unfold main_lbl, BZ_X_MTF_1; intros; lia
               | |- _ /\ _ => fin_go
               end
             | idtac ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_out (s s' : dstrm) : Prop := s_out s' = s_out s /\ s_avail_out s' = s_avail_out s /\ s_tout s' = s_tout s.

Definition drun_post (lbl : Z) (d : dst) (s : dstrm) (d' : dst) (s' : dstrm) : Prop :=
  in_out s s' /\ d_cccrc d' = d_cccrc d /\
  (if 20 <=? lbl then d_blockNo d' = d_blockNo d else d_blockNo d' = d_blockNo d \/ d_blockNo d' = d_blockNo d + 1) /\
  (d_state d' = BZ_X_OUTPUT -> d_blockNo d' = d_blockNo d + (if lbl <=? 19 then 1 else 0)) /\
  (42 <= lbl -> d_state d' <> BZ_X_OUTPUT) /\ 1 <= d_state d' <= 50.

(* [comment removed for export] *)
Lemma drun_step_arith : forall lbl lbl' bn bn' bn2 st2 : Z,
  next_ok lbl lbl' -> bn' = bn + (if lbl =? 19 then 1 else 0) ->
  (if 20 <=? lbl' then bn2 = bn' else bn2 = bn' \/ bn2 = bn' + 1) ->
  (st2 = BZ_X_OUTPUT -> bn2 = bn' + (if lbl' <=? 19 then 1 else 0)) ->
  (42 <= lbl' -> st2 <> BZ_X_OUTPUT) ->
  (if 20 <=? lbl then bn2 = bn else bn2 = bn \/ bn2 = bn + 1) /\
  (st2 = BZ_X_OUTPUT -> bn2 = bn + (if lbl <=? 19 then 1 else 0)) /\
  (42 <= lbl -> st2 <> BZ_X_OUTPUT).
Proof.
  intros lbl lbl' bn bn' bn2 st2 NX B2 BB ST F42. unfold next_ok in NX.
  destruct (Z.leb_spec 20 lbl) as [G1|G1]; destruct (Z.leb_spec lbl 19) as [G2|G2]; try (exfalso; clear - G1 G2; lia);
  destruct (Z.leb_spec 20 lbl') as [G3|G3]; destruct (Z.leb_spec lbl' 19) as [G4|G4]; try (exfalso; clear - G3 G4; lia);
  destruct (Z.eqb_spec lbl 19) as [G5|G5]; try (exfalso; clear - G1 G2 G5; lia); repeat split; intros; try lia;
  try (specialize (ST ltac:(assumption)); lia);
  try (exfalso; apply F42; [lia| assumption]).
Qed.

Lemma drun_frame : forall fuel lbl L d s, 10 <= lbl <= 50 -> d_state d <> BZ_X_OUTPUT -> 1 <= d_state d <= 50 ->
  match drun fuel lbl L d s with
  | DGo _ _ d' s' | DRet _ _ d' s' | DRetNoSave _ _ d' s' => drun_post lbl d s d' s'
  end.
Proof.
  induction fuel as [|f IH]; intros lbl L d s Hl Hst Hsr.
  - cbn [drun]. unfold drun_post, in_out, BZ_X_OUTPUT in *. repeat split; try reflexivity; try lia.
    destruct (20 <=? lbl); lia.
  - cbn [drun].
    set (d0 := d_set_state d lbl).
    destruct (gb_bits lbl L <=? d_bsLive d0).
    + set (v := Z.land _ _). set (d1 := d_set_bsLive d0 _).
      pose proof (gb_after_shape lbl v L d1 s Hl) as SH.
      assert (F1 : d_cccrc d1 = d_cccrc d /\ d_blockNo d1 = d_blockNo d /\ d_state d1 = lbl) by (subst d1 d0; repeat split; reflexivity).
      cps_destruct F1 as (C1 & B1 & S1).
      destruct (gb_after lbl v L d1 s) as [lbl' L' d' s'|rv L' d' s'|rv L' d' s'].
      * cps_destruct SH as (-> & NX & C2 & S2 & B2).
        assert (Hl' : 10 <= lbl' <= 50) by (unfold next_ok in NX; lia).
        assert (Hst' : d_state d' <> BZ_X_OUTPUT) by (rewrite S2, S1; unfold BZ_X_OUTPUT; lia).
        specialize (IH lbl' L' d' s Hl' Hst' ltac:(rewrite S2, S1; lia)).
        destruct (drun f lbl' L' d' s) as [l2 L2 d2 s2|r2 L2 d2 s2|r2 L2 d2 s2];
          (cps_destruct IH as (IO & CC & BB & ST & F42 & SR); unfold drun_post; split; [exact IO|]; split; [rewrite CC, C2, C1; reflexivity|];
           rewrite B1 in B2;
           cps_pose (drun_step_arith lbl lbl' (d_blockNo d) (d_blockNo d') (d_blockNo d2) (d_state d2) NX B2 BB ST F42) as (Q1 & Q2 & Q3);
           split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3| exact SR]).
      * cps_destruct SH as (-> & C2 & B2 & S2). unfold drun_post, in_out. rewrite C2, C1, B2, B1, S1 in *.
        destruct (Z.leb_spec 20 lbl); destruct (Z.leb_spec lbl 19); repeat split; try reflexivity; try lia;
          unfold BZ_X_OUTPUT, BZ_X_IDLE in *; intros; lia.
      * cps_destruct SH as (-> & C2 & B2 & S2). unfold drun_post, in_out. rewrite C2, C1, B2, B1, S1 in *.
        destruct (Z.leb_spec 20 lbl); destruct (Z.leb_spec lbl 19); repeat split; try reflexivity; try lia;
          unfold BZ_X_OUTPUT, BZ_X_IDLE in *; intros; lia.
    + destruct (s_in s) as [|b rest].
      * unfold drun_post, in_out. subst d0. cbn [d_cccrc d_blockNo d_state d_set_state].
        destruct (Z.leb_spec 20 lbl); repeat split; try reflexivity; try lia; unfold BZ_X_OUTPUT; cbn [d_state]; intros; lia.
      * match goal with |- match drun f lbl L ?d1 ?s1 with _ => _ end =>
          specialize (IH lbl L d1 s1 Hl ltac:(subst d0; cbn; unfold BZ_X_OUTPUT; lia) ltac:(subst d0; cbn; lia));
          destruct (drun f lbl L d1 s1) as [l2 L2 d2 s2|r2 L2 d2 s2|r2 L2 d2 s2] end;
          (cps_destruct IH as (IO & CC & BB & ST & F42 & SR); unfold drun_post in *; subst d0; cbn [d_cccrc d_blockNo d_state d_set_state d_set_bsLive d_set_bsBuff] in *;
           unfold in_out in *; cbn [s_out s_avail_out s_tout s_set_tin s_set_in] in IO;
           split; [exact IO|]; split; [exact CC|]; split; [exact BB|]; split; [exact ST|]; split; [exact F42| exact SR]).
Qed.

Theorem decompress_frame : forall d s, d_state d <> BZ_X_OUTPUT -> 10 <= d_state d <= 50 ->
  let '(rv, d', s') := decompress d s in
  s_out s' = s_out s /\ s_avail_out s' = s_avail_out s /\ s_tout s' = s_tout s /\ d_cccrc d' = d_cccrc d /\
  (d_blockNo d' = d_blockNo d \/ d_blockNo d' = d_blockNo d + 1) /\
  (d_state d' = BZ_X_OUTPUT -> d_state d <= 19 -> d_blockNo d' = d_blockNo d + 1) /\ 1 <= d_state d' <= 50.
Proof.
  intros d s Hst Hl. unfold decompress.
  set (d0 := if d_state d =? BZ_X_MAGIC_1 then d_set_sv d dsv_zero else d).
  assert (E0 : d_state d0 = d_state d /\ d_cccrc d0 = d_cccrc d /\ d_blockNo d0 = d_blockNo d).
  { subst d0. destruct (d_state d =? BZ_X_MAGIC_1); repeat split; reflexivity. }
  cps_destruct E0 as (ES & EC & EB).
  pose proof (drun_frame (9 * length (s_in s) + 64) (d_state d0) (d_sv d0) d0 s ltac:(lia) ltac:(rewrite ES; exact Hst) ltac:(rewrite ES; lia)) as DF.
  destruct (drun _ _ _ _ _) as [l2 L2 d2 s2|r2 L2 d2 s2|r2 L2 d2 s2];
    cps_destruct DF as ((IO1 & IO2 & IO3) & CC & BB & ST & F42 & SR); cbn [d_cccrc d_blockNo d_state d_set_sv];
    rewrite ES, EC, EB in *;
    (split; [exact IO1|]); (split; [exact IO2|]); (split; [exact IO3|]); (split; [exact CC|]);
    destruct (Z.leb_spec 20 (d_state d)); destruct (Z.leb_spec (d_state d) 19); (split; [lia|]); (split; [intros A B; try lia; specialize (ST A); lia | exact SR]).
Qed.
