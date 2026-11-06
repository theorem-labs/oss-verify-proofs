(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import List. Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grp_decF (d : dst) (alpha t mn zn zvec : Z) : Prop :=
  exists (len lim0 base0 perm0 : Z -> Z) (mx : Z),
    (1 <= mn /\ mn <= mx <= 20) /\
    (forall j, 0 <= j < alpha -> mn <= len j <= mx) /\
    (let '(lim, base, perm) := hb_create lim0 base0 perm0 len mn mx alpha in
     (forall i, 0 <= i < 258 -> zget (d_limit d) (258 * t + i) = lim i) /\
     (forall i, 0 <= i < 258 -> zget (d_base d) (258 * t + i) = base i) /\
     (forall i, 0 <= i < 258 -> zget (d_perm d) (258 * t + i) = perm i) /\
     zget (d_minLens d) t = mn) /\
    decJ len alpha mn zn zvec.

Section D.
  Variables (d : dst) (alpha t mn : Z).
  Hypothesis Halpha : 1 <= alpha <= 258.

  Lemma grp_decF_init : forall zvec, tab_okF d alpha t mn -> 0 <= zvec < 2 ^ mn -> grp_decF d alpha t mn mn zvec.
  Proof.
    (intros zvec; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & M); intros Hz).
    exists len, lim0, base0, perm0, mx. split; [exact Hmm|]. split; [exact Hlen|]. split.
    - destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm]. cps_destruct G as (G1 & G2 & G3).
      repeat split; assumption.
    - apply (decJ_init len alpha mn mx Hmm). exact Hz.
  Qed.

  (* [comment removed for export] *)

  Lemma grp_decF_zn : forall zn zvec, grp_decF d alpha t mn zn zvec -> 1 <= mn /\ mn <= zn <= 21.
  Proof. (intros zn zvec; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & [J1 J2])). lia. Qed.

  (* [comment removed for export] *)

  Lemma grp_decF_zvec : forall zn zvec, grp_decF d alpha t mn zn zvec -> 0 <= zvec < 2097152.
  Proof.
    (intros zn zvec; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & J)).
    pose proof (decJ_zvec_range len alpha mn mx Halpha Hmm zn zvec J) as H. change (2 ^ 21) with 2097152 in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma grp_decF_limit : forall zn zvec, grp_decF d alpha t mn zn zvec -> zn <= 20 ->
    -1 <= zget (d_limit d) (258 * t + zn) < 268435456.
  Proof.
    (intros zn zvec; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & J); intros Hzn).
    pose proof (dec_limit_range len alpha mn mx Halpha Hmm Hlen lim0 base0 perm0 zn) as R.
    destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm]. cps_destruct G as (G1 & _ & _ & _).
    destruct J as [J1 _]. rewrite G1 by lia. change (2 ^ 28) with 268435456 in R. apply R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma grp_decF_step : forall zn zvec b, grp_decF d alpha t mn zn zvec -> zn <= 20 ->
    zget (d_limit d) (258 * t + zn) < zvec -> 0 <= b <= 1 ->
    grp_decF d alpha t mn (zn + 1) (2 * zvec + b) /\ Z.lor (Z.shiftl zvec 1) b = 2 * zvec + b.
  Proof.
    (intros zn zvec b; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & J); intros Hzn Hlt Hb).
    pose proof (decJ_step len alpha mn mx Halpha Hmm Hlen lim0 base0 perm0 zn zvec b) as ST.
    destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm] eqn:E. cps_destruct G as (G1 & G2 & G3 & G4).
    destruct J as [J1 J2].
    destruct (ST (conj J1 J2) Hzn ltac:(rewrite <- G1 by lia; exact Hlt) Hb) as [D EQ].
    split; [| exact EQ].
    exists len, lim0, base0, perm0, mx. split; [exact Hmm|]. split; [exact Hlen|]. rewrite E.
    split; [repeat split; assumption|]. rewrite <- EQ. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma grp_decF_break : forall zn zvec, grp_decF d alpha t mn zn zvec -> zn <= 20 ->
    zvec <= zget (d_limit d) (258 * t + zn) ->
    (mn <= zn <= 20) /\
    (0 <= zvec - zget (d_base d) (258 * t + zn) < alpha) /\
    (0 <= zget (d_perm d) (258 * t + (zvec - zget (d_base d) (258 * t + zn))) < alpha) /\
    (- 1073741824 < zget (d_base d) (258 * t + zn) < 1073741824).
  Proof.
    (intros zn zvec; cps_intros (len & lim0 & base0 & perm0 & mx & Hmm & Hlen & G & J); intros Hzn Hle).
    pose proof (decJ_break len alpha mn mx Halpha Hmm Hlen lim0 base0 perm0 zn zvec) as BR.
    destruct (hb_create lim0 base0 perm0 len mn mx alpha) as [[lim base] perm]. cps_destruct G as (G1 & G2 & G3 & G4).
    destruct J as [J1 J2].
    cps_destruct (BR (conj J1 J2) Hzn ltac:(rewrite <- G1 by lia; exact Hle)) as (B1 & B2 & B3 & B4).
    rewrite G2 by lia. rewrite G3 by lia.
    change (2 ^ 30) with 1073741824 in B4. repeat split; try lia.
  Qed.
End D.

(* [comment removed for export] *)
Lemma grp_decF_frame : forall d d' alpha t mn zn zvec, grp_decF d alpha t mn zn zvec ->
  d_limit d' = d_limit d -> d_base d' = d_base d -> d_perm d' = d_perm d -> d_minLens d' = d_minLens d ->
  grp_decF d' alpha t mn zn zvec.
Proof. intros d d' alpha t mn zn zvec G E1 E2 E3 E4. unfold grp_decF. rewrite E1, E2, E3, E4. exact G. Qed.

(* [comment removed for export] *)
Lemma dinv_ML_tab : forall L d, dinv_ML L d -> exists mn, tab_okF d (sv_alphaSize L) (sv_gSel L) mn /\ sv_gMinlen L = mn.
Proof.
  (intros L d; cps_intros (AL & GRP & TABS & MTF & BLK & CUR)). cps_destruct CUR as (C1 & C2 & C3 & C4 & C5).
  destruct (TABS (sv_gSel L) C4) as [mn T]. exists mn. split; [exact T|].
  cps_destruct T as (len & lim0 & base0 & perm0 & mx & _ & _ & _ & M). rewrite C5, M. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_L8 (F : nat) (w : Z) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (mtf_val_loop w L d s).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mvl_ret : forall w L d s, 20 < sv_zn L -> mtf_val_loop w L d s = DRet BZ_DATA_ERROR L d s.
Proof. intros w L d s H. unfold mtf_val_loop. destruct (Z.ltb_spec 20 (sv_zn L)); [reflexivity| lia]. Qed.

Lemma mvl_more : forall w L d s, sv_zn L <= 20 ->
  zget (d_limit d) (258 * sv_gSel L + sv_zn L) < sv_zvec L ->
  mtf_val_loop w L d s = DGo (w + 36) (sv_set_zn L (sv_zn L + 1)) d s.
Proof.
  intros w L d s H1 H2. unfold mtf_val_loop.
  destruct (Z.ltb_spec 20 (sv_zn L)); [lia|].
  destruct (Z.leb_spec (sv_zvec L) (zget (d_limit d) (258 * sv_gSel L + sv_zn L))); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mvl_sym (L : dsv) (d : dst) : Z :=
  zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))).

Lemma mvl_break : forall w L d s, sv_zn L <= 20 ->
  sv_zvec L <= zget (d_limit d) (258 * sv_gSel L + sv_zn L) ->
  0 <= sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L) < 258 ->
  mtf_val_loop w L d s =
  (if w =? 3 then
     (if (mvl_sym L d =? BZ_RUNA) || (mvl_sym L d =? BZ_RUNB) then run_body (sv_set_nextSym L (mvl_sym L d)) d s
      else run_exit (sv_set_nextSym L (mvl_sym L d)) d s)
   else sym_dispatch (sv_set_nextSym L (mvl_sym L d)) d s).
Proof.
  intros w L d s H1 H2 H3. unfold mtf_val_loop, mvl_sym, BZ_MAX_ALPHA_SIZE.
  destruct (Z.ltb_spec 20 (sv_zn L)); [lia|].
  destruct (Z.leb_spec (sv_zvec L) (zget (d_limit d) (258 * sv_gSel L + sv_zn L))); [|lia].
  destruct (Z.ltb_spec (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)) 0); [lia|].
  destruct (Z.leb_spec 258 (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma K_L8_sym1 : forall F L d s, sv_zn L <= 20 ->
  sv_zvec L <= zget (d_limit d) (258 * sv_gSel L + sv_zn L) ->
  0 <= sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L) < 258 ->
  K_L8 F 1 L d s = K_SYM F (sv_set_nextSym L (mvl_sym L d)) d s.
Proof. intros. unfold K_L8, K_SYM. rewrite mvl_break by assumption. replace (1 =? 3) with false by reflexivity. reflexivity. Qed.
Lemma K_L8_sym5 : forall F L d s, sv_zn L <= 20 ->
  sv_zvec L <= zget (d_limit d) (258 * sv_gSel L + sv_zn L) ->
  0 <= sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L) < 258 ->
  K_L8 F 5 L d s = K_SYM F (sv_set_nextSym L (mvl_sym L d)) d s.
Proof. intros. unfold K_L8, K_SYM. rewrite mvl_break by assumption. replace (5 =? 3) with false by reflexivity. reflexivity. Qed.
Lemma K_L8_run : forall F L d s, sv_zn L <= 20 ->
  sv_zvec L <= zget (d_limit d) (258 * sv_gSel L + sv_zn L) ->
  0 <= sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L) < 258 ->
  (mvl_sym L d = 0 \/ mvl_sym L d = 1) ->
  K_L8 F 3 L d s = K_HRUN F (sv_set_nextSym L (mvl_sym L d)) d s.
Proof.
  intros F L d s H1 H2 H3 H4. unfold K_L8, K_HRUN. rewrite mvl_break by assumption. rewrite Z.eqb_refl.
  unfold BZ_RUNA, BZ_RUNB. destruct H4 as [E|E]; rewrite E; reflexivity.
Qed.
Lemma K_L8_runend : forall F L d s, sv_zn L <= 20 ->
  sv_zvec L <= zget (d_limit d) (258 * sv_gSel L + sv_zn L) ->
  0 <= sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L) < 258 ->
  mvl_sym L d <> 0 -> mvl_sym L d <> 1 ->
  K_L8 F 3 L d s = K_HRUNEND F (sv_set_nextSym L (mvl_sym L d)) d s.
Proof.
  intros F L d s H1 H2 H3 H4 H5. unfold K_L8, K_HRUNEND. rewrite mvl_break by assumption. rewrite Z.eqb_refl.
  unfold BZ_RUNA, BZ_RUNB. destruct (Z.eqb_spec (mvl_sym L d) 0); [lia|]. destruct (Z.eqb_spec (mvl_sym L d) 1); [lia|]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma K_L8_ret : forall F w L d s, 20 < sv_zn L -> K_L8 F w L d s = DRet BZ_DATA_ERROR L d s.
Proof. intros. unfold K_L8. rewrite mvl_ret by assumption. reflexivity. Qed.
Lemma K_L8_more : forall F w L d s, sv_zn L <= 20 ->
  zget (d_limit d) (258 * sv_gSel L + sv_zn L) < sv_zvec L ->
  K_L8 F w L d s = drun F (w + 36) (sv_set_zn L (sv_zn L + 1)) d s.
Proof. intros. unfold K_L8. rewrite mvl_more by assumption. reflexivity. Qed.
(* [comment removed for export] *)
Lemma K_L8_enter36 : forall F v L d s, dgo F (gb_after 36 v L d s) = K_L8 F 1 (sv_set_zvec L v) d s. Proof. reflexivity. Qed.
Lemma K_L8_enter38 : forall F v L d s, dgo F (gb_after 38 v L d s) = K_L8 F 3 (sv_set_zvec L v) d s. Proof. reflexivity. Qed.
Lemma K_L8_enter40 : forall F v L d s, dgo F (gb_after 40 v L d s) = K_L8 F 5 (sv_set_zvec L v) d s. Proof. reflexivity. Qed.
Lemma K_L8_again37 : forall F v L d s zv, Z.lor (Z.shiftl (sv_zvec L) 1) v = zv ->
  dgo F (gb_after 37 v L d s) = K_L8 F 1 (sv_set_zvec (sv_set_zj L v) zv) d s.
Proof. intros F v L d s zv <-. reflexivity. Qed.
Lemma K_L8_again39 : forall F v L d s zv, Z.lor (Z.shiftl (sv_zvec L) 1) v = zv ->
  dgo F (gb_after 39 v L d s) = K_L8 F 3 (sv_set_zvec (sv_set_zj L v) zv) d s.
Proof. intros F v L d s zv <-. reflexivity. Qed.
Lemma K_L8_again41 : forall F v L d s zv, Z.lor (Z.shiftl (sv_zvec L) 1) v = zv ->
  dgo F (gb_after 41 v L d s) = K_L8 F 5 (sv_set_zvec (sv_set_zj L v) zv) d s.
Proof. intros F v L d s zv <-. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_HMTF1_drun : forall F L d s, K_HMTF1 F L d s = drun F 36 L d s. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mvs_L (L : dsv) (d : dst) : dsv :=
  if sv_groupPos L =? 0 then
    let gNo := sv_groupNo L + 1 in
    let gSel := zget (d_sel d) gNo in
    let gMinlen := zget (d_minLens d) gSel in
    sv_set_zn (sv_set_gPtr (sv_set_gMinlen (sv_set_gSel (sv_set_groupPos (sv_set_groupNo L gNo) (BZ_G_SIZE - 1)) gSel) gMinlen) true) gMinlen
  else sv_set_zn (sv_set_groupPos L (sv_groupPos L - 1)) (sv_gMinlen L).

Lemma mvs_go : forall lbl L d s, (sv_groupPos L =? 0) = false \/ sv_groupNo L + 1 < sv_nSelectors L ->
  mtf_val_start lbl L d s = DGo lbl (mvs_L L d) d s.
Proof.
  intros lbl L d s H. unfold mtf_val_start, mvs_L.
  destruct (Z.eqb_spec (sv_groupPos L) 0) as [E|E].
  - destruct H as [H|H]; [discriminate|]. destruct (Z.leb_spec (sv_nSelectors L) (sv_groupNo L + 1)); [lia|].
    cbv zeta. destruct L; reflexivity.
  - destruct L; reflexivity.
Qed.
Lemma mvs_ret : forall lbl L d s, sv_groupPos L = 0 -> sv_nSelectors L <= sv_groupNo L + 1 ->
  mtf_val_start lbl L d s = DRet BZ_DATA_ERROR (sv_set_groupNo L (sv_groupNo L + 1)) d s.
Proof.
  intros lbl L d s E H. unfold mtf_val_start. rewrite E. cbn [Z.eqb].
  destruct (Z.leb_spec (sv_nSelectors L) (sv_groupNo L + 1)); [reflexivity| lia].
Qed.
(* [comment removed for export] *)
Lemma K_HMTFB_go : forall F L d s, (sv_groupPos L =? 0) = false \/ sv_groupNo L + 1 < sv_nSelectors L ->
  K_HMTFB F L d s = drun F 38 (mvs_L L d) d s.
Proof. intros. unfold K_HMTFB. rewrite mvs_go by assumption. reflexivity. Qed.
Lemma K_HMTFC_go : forall F L d s, (sv_groupPos L =? 0) = false \/ sv_groupNo L + 1 < sv_nSelectors L ->
  K_HMTFC F L d s = drun F 40 (mvs_L L d) d s.
Proof. intros. unfold K_HMTFC. rewrite mvs_go by assumption. reflexivity. Qed.
Lemma K_HMTFB_ret : forall F L d s, sv_groupPos L = 0 -> sv_nSelectors L <= sv_groupNo L + 1 ->
  K_HMTFB F L d s = DRet BZ_DATA_ERROR (sv_set_groupNo L (sv_groupNo L + 1)) d s.
Proof. intros. unfold K_HMTFB. rewrite mvs_ret by assumption. reflexivity. Qed.
Lemma K_HMTFC_ret : forall F L d s, sv_groupPos L = 0 -> sv_nSelectors L <= sv_groupNo L + 1 ->
  K_HMTFC F L d s = DRet BZ_DATA_ERROR (sv_set_groupNo L (sv_groupNo L + 1)) d s.
Proof. intros. unfold K_HMTFC. rewrite mvs_ret by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mvs_L_pos : forall L d, sv_groupPos L <> 0 ->
  mvs_L L d = sv_set_zn (sv_set_groupPos L (sv_groupPos L - 1)) (sv_gMinlen L).
Proof. intros L d H. unfold mvs_L. destruct (Z.eqb_spec (sv_groupPos L) 0); [lia| reflexivity]. Qed.
Lemma mvs_L_zero : forall L d, sv_groupPos L = 0 ->
  mvs_L L d =
  sv_set_zn (sv_set_gPtr (sv_set_gMinlen (sv_set_gSel (sv_set_groupPos (sv_set_groupNo L (sv_groupNo L + 1)) 49)
    (zget (d_sel d) (sv_groupNo L + 1))) (zget (d_minLens d) (zget (d_sel d) (sv_groupNo L + 1)))) true)
    (zget (d_minLens d) (zget (d_sel d) (sv_groupNo L + 1))).
Proof. intros L d E. unfold mvs_L, BZ_G_SIZE. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dinv_L8 (w : Z) (L : dsv) (d : dst) : Prop :=
  dinv_ML L d /\ grp_decF d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) (sv_zn L) (sv_zvec L) /\
  (w = 3 -> run_okF (sv_N L) (sv_es L) /\ sv_N L <= 4194302).
(* [comment removed for export] *)
Definition dinv_L8G (L : dsv) (d : dst) : Prop := dinv_HMTFB L d /\ sv_zn L = sv_gMinlen L.
Definition dinv_L8CG (L : dsv) (d : dst) : Prop := dinv_HMTF1 L d.
Definition K_L8G (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := drun F 38 L d s.
Definition K_L8CG (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := drun F 40 L d s.

(* [comment removed for export] *)
Lemma dinv_L8_init : forall w L d v,
  dinv_ML L d -> sv_zn L = sv_gMinlen L -> 0 <= v < 2 ^ sv_gMinlen L ->
  (w = 3 -> run_okF (sv_N L) (sv_es L) /\ sv_N L <= 4194302) ->
  dinv_L8 w (sv_set_zvec L v) d.
Proof.
  intros w L d v ML Hzn Hv Hw. pose proof (dinv_ML_alpha L d ML) as [Ha _].
  destruct (dinv_ML_tab L d ML) as [mn [T M]].
  unfold dinv_L8. Lsplit L. split; [exact ML|]. split; [| exact Hw].
  rewrite Hzn, M. apply grp_decF_init; first [ lia | exact T | rewrite <- M; exact Hv ].
Qed.
(* [comment removed for export] *)
Lemma dinv_L8_step : forall w L d b, dinv_L8 w L d -> sv_zn L <= 20 ->
  zget (d_limit d) (258 * sv_gSel L + sv_zn L) < sv_zvec L -> 0 <= b <= 1 ->
  dinv_L8 w (sv_set_zvec (sv_set_zj (sv_set_zn L (sv_zn L + 1)) b) (2 * sv_zvec L + b)) d /\
  Z.lor (Z.shiftl (sv_zvec L) 1) b = 2 * sv_zvec L + b.
Proof.
  (intros w L d b; cps_intros (ML & G & Hw); intros Hzn Hlt Hb). pose proof (dinv_ML_alpha L d ML) as [Ha _].
  destruct (grp_decF_step d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ b G Hzn Hlt Hb) as [G' E].
  split; [| exact E]. unfold dinv_L8. Lsplit L.
  split; [exact ML|]. split; [exact G'| exact Hw].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dkeep (d d' : dst) : Prop :=
  d_nInUse d' = d_nInUse d /\ d_rand d' = d_rand d /\ d_sbcrc d' = d_sbcrc d /\ d_origPtr d' = d_origPtr d /\
  d_sel d' = d_sel d /\ d_bs100k d' = d_bs100k d /\ d_limit d' = d_limit d /\ d_base d' = d_base d /\
  d_perm d' = d_perm d /\ d_minLens d' = d_minLens d /\ d_mtfbase d' = d_mtfbase d /\ d_mtfa d' = d_mtfa d /\
  d_small d' = d_small d /\ d_tt d' = d_tt d /\ d_ll16 d' = d_ll16 d /\ d_unzftab d' = d_unzftab d /\ d_state d' <> 2.
(* [comment removed for export] *)
Definition Lkeep (L L' : dsv) : Prop :=
  sv_alphaSize L' = sv_alphaSize L /\ sv_nblock L' = sv_nblock L /\ sv_nGroups L' = sv_nGroups L /\
  sv_nSelectors L' = sv_nSelectors L /\ sv_EOB L' = sv_EOB L /\ sv_nblockMAX L' = sv_nblockMAX L /\
  sv_groupNo L' = sv_groupNo L /\ sv_groupPos L' = sv_groupPos L /\ sv_gSel L' = sv_gSel L /\ sv_gMinlen L' = sv_gMinlen L.

Lemma dkeep_gb : forall d lbl bb bl x, lbl <> 2 -> dkeep d (d_set_bsLive (gbst d lbl bb bl) x).
Proof. intros d lbl bb bl x H. destruct d. unfold dkeep; cbn. repeat split; first [reflexivity | exact H]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Lkeep_nextSym : forall L a, Lkeep L (sv_set_nextSym L a).
Proof. intros. destruct L. unfold Lkeep; cbn. repeat split; reflexivity. Qed.

Lemma dinv_ML_keep : forall L L' d d', dinv_ML L d -> Lkeep L L' -> dkeep d d' -> dinv_ML L' d'.
Proof.
  (intros L L' d d'; cps_intros (AL & GRP & TABS & MTF & BLK & CUR); cps_intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10); cps_intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & NS)).
  unfold dinv_ML. rewrite L3, L1. split; [| split; [| split; [| split; [| split]]]].
  - apply (alpha_ok_frame L L' d d' AL); assumption.
  - apply (grp_okF_frame L L' d d' GRP); assumption.
  - apply (tabs_okF_frame d d'); assumption.
  - apply (mtf_okF_frame d d' MTF); assumption.
  - apply (blkF_frame L L' d d' BLK); assumption.
  - apply (cur_okF_frame L L' d d' CUR); assumption.
Qed.
Lemma dinv_L8_keep : forall w L d d', dinv_L8 w L d -> dkeep d d' -> dinv_L8 w L d'.
Proof.
  (intros w L d d'; cps_intros (ML & G & W); intros K). cps_pose K as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  split; [| split; [| exact W]].
  - apply (dinv_ML_keep L L d d' ML); [| exact K]. destruct L; unfold Lkeep; cbn; repeat split; reflexivity.
  - apply (grp_decF_frame d d'); assumption.
Qed.
(* [comment removed for export] *)
Lemma dinv_SYM_intro : forall L d ns, dinv_ML L d -> 0 <= ns < sv_alphaSize L -> dinv_SYM (sv_set_nextSym L ns) d.
Proof.
  intros L d ns ML H. split.
  - apply (dinv_ML_keep L _ d d ML); [apply Lkeep_nextSym|]. destruct d; unfold dkeep; cbn; repeat split; try reflexivity.
    destruct ML as [AL _]. unfold alpha_ok in AL. cbn in AL. lia.
  - destruct L; cbn. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mvs_L_fields : forall L d,
  sv_alphaSize (mvs_L L d) = sv_alphaSize L /\ sv_nblock (mvs_L L d) = sv_nblock L /\
  sv_nGroups (mvs_L L d) = sv_nGroups L /\ sv_nSelectors (mvs_L L d) = sv_nSelectors L /\
  sv_EOB (mvs_L L d) = sv_EOB L /\ sv_nblockMAX (mvs_L L d) = sv_nblockMAX L /\
  sv_N (mvs_L L d) = sv_N L /\ sv_es (mvs_L L d) = sv_es L /\ sv_nextSym (mvs_L L d) = sv_nextSym L /\
  sv_zn (mvs_L L d) = sv_gMinlen (mvs_L L d).
Proof.
  intros L d. unfold mvs_L. destruct (sv_groupPos L =? 0); destruct L; cbn; repeat split; reflexivity.
Qed.

Lemma dinv_ML_mvs : forall L d, dinv_ML L d ->
  (sv_groupPos L <> 0 \/ sv_groupNo L + 1 < sv_nSelectors L) -> dinv_ML (mvs_L L d) d.
Proof.
  intros L d ML H. cps_pose ML as (AL & GRP & TABS & MTF & BLK & CUR).
  cps_pose (mvs_L_fields L d) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  unfold dinv_ML. rewrite E3, E1.
  split; [apply (alpha_ok_frame L _ d d AL); first [assumption | reflexivity | destruct AL as [(_ & _ & _ & _ & _ & NS) _]; exact NS] |].
  split; [apply (grp_okF_frame L _ d d GRP); first [assumption | reflexivity] |].
  split; [exact TABS|]. split; [exact MTF|].
  split; [apply (blkF_frame L _ d d BLK); first [assumption | reflexivity] |].
  (* [comment removed for export] *)
  cps_destruct CUR as (C1 & C2 & C3 & C4 & C5). cps_destruct GRP as (G1 & G2 & G3 & G4 & G5).
  unfold cur_okF, mvs_L, BZ_G_SIZE. destruct (Z.eqb_spec (sv_groupPos L) 0) as [E|E].
  - destruct H as [H|H]; [lia|]. Lsplit L.
    pose proof (G3 (L_groupNo + 1) ltac:(lia)) as SEL. repeat split; try lia; reflexivity.
  - Lsplit L. repeat split; try lia; assumption.
Qed.

Lemma dinv_L8G_intro : forall L d, dinv_HMTFB L d ->
  (sv_groupPos L <> 0 \/ sv_groupNo L + 1 < sv_nSelectors L) -> dinv_L8G (mvs_L L d) d.
Proof.
  (intros L d; cps_intros (ML & RUN & NB); intros H). cps_pose (mvs_L_fields L d) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  unfold dinv_L8G, dinv_HMTFB. rewrite E7, E8, E10. split; [| reflexivity]. split; [apply dinv_ML_mvs; assumption|].
  split; assumption.
Qed.
Lemma dinv_L8CG_intro : forall L d, dinv_HMTFC L d ->
  (sv_groupPos L <> 0 \/ sv_groupNo L + 1 < sv_nSelectors L) -> dinv_L8CG (mvs_L L d) d.
Proof.
  intros L d ML H. cps_pose (mvs_L_fields L d) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  unfold dinv_L8CG, dinv_HMTF1. rewrite E10. split; [apply dinv_ML_mvs; assumption| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma dinv_L8G_L8 : forall L d v, dinv_L8G L d -> 0 <= v < 2 ^ sv_gMinlen L -> dinv_L8 3 (sv_set_zvec L v) d.
Proof. intros L d v ((ML & RUN & NB) & ZN) Hv. apply dinv_L8_init; [exact ML | exact ZN | exact Hv | intros _; split; assumption]. Qed.
Lemma dinv_L8CG_L8 : forall L d v, dinv_L8CG L d -> 0 <= v < 2 ^ sv_gMinlen L -> dinv_L8 5 (sv_set_zvec L v) d.
Proof. intros L d v [ML ZN] Hv. apply dinv_L8_init; [exact ML | exact ZN | exact Hv | intros; exfalso; lia]. Qed.
Lemma K_L8G_drun : forall F L d s, K_L8G F L d s = drun F 38 L d s. Proof. reflexivity. Qed.
Lemma K_L8CG_drun : forall F L d s, K_L8CG F L d s = drun F 40 L d s. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dinv_HRUN_intro : forall L d ns, dinv_L8 3 L d -> 0 <= ns <= 1 -> 3 <= sv_alphaSize L ->
  dinv_HRUN (sv_set_nextSym L ns) d.
Proof.
  (intros L d ns; cps_intros (ML & G & W); intros Hns Ha). destruct (W eq_refl) as [RUN NB].
  unfold dinv_HRUN. split; [| Lsplit L; split; [lia | exact RUN]].
  apply (dinv_ML_keep L _ d d ML); [apply Lkeep_nextSym|]. destruct d; unfold dkeep; cbn; repeat split; try reflexivity.
  destruct ML as [AL _]. unfold alpha_ok in AL. cbn in AL. lia.
Qed.
Lemma dinv_HRUNEND_intro : forall L d ns, dinv_L8 3 L d -> 2 <= ns < sv_alphaSize L ->
  dinv_HRUNEND (sv_set_nextSym L ns) d.
Proof.
  (intros L d ns; cps_intros (ML & G & W); intros Hns). destruct (W eq_refl) as [RUN NB]. unfold run_okF in RUN.
  unfold dinv_HRUNEND. split; [| Lsplit L; lia].
  apply (dinv_ML_keep L _ d d ML); [apply Lkeep_nextSym|]. destruct d; unfold dkeep; cbn; repeat split; try reflexivity.
  destruct ML as [AL _]. unfold alpha_ok in AL. cbn in AL. lia.
Qed.
