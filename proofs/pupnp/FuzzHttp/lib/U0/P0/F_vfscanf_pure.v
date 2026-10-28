(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_vfscanf_lib.
Import ListNotations.
Open Scope Z_scope.

Section Txt.
  Variables (txt : list Z) (p : Z).
  Hypothesis Hp : 0 <= p < zlength txt.
  Hypothesis Hnul : znth txt p = 0.
  Hypothesis Hpre : forall i, 0 <= i < p -> znth txt i <> 0.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.

  Notation U := (U txt p).

  #[using="Hp Hnul Hpre BYT"] Lemma vfW_U : forall k c f, U k c f -> sh_stdio f = true ->
    exists c1 f1 k1, is_ws_loop (S (length txt)) (sh_lim0 f) = Some (c1, f1) /\ U (k1 - 1) c1 (sh_unget f1) /\ 1 <= k1 /\
      sh_stdio (sh_unget f1) = true /\ m_isspace c1 = false.
  Proof.
    intros k c f HU ST.
    destruct (U_lim0 txt p k c f HU) as (Ul & Sl & Cl & Rl & Nl & SNl).
    destruct (ws_loop_U txt p Hp Hnul Hpre BYT (S (length txt)) 0 c (sh_lim0 f) Ul ltac:(intros; exact SNl) ltac:(intros X; rewrite Sl, ST in X; discriminate X)
                (len_pot txt p Hp 0 c (sh_lim0 f) Ul))
      as (c1 & f1 & k1 & HL & U1 & K1 & SP1 & S1 & _).
    destruct (U_unget txt p k1 c1 f1 U1 ltac:(lia)) as (Uu & Su & _).
    exists c1, f1, k1. split; [exact HL|]. split; [exact Uu|]. split; [lia|]. split; [|exact SP1]. rewrite Su, S1, Sl. exact ST.
  Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma vfs_U : forall ds k c f mt, U k c f -> sh_stdio f = true ->
    exists r, vfs (S (length txt)) ds f mt = Some r /\ (r = -1 \/ mt <= r <= mt + nconv ds).
  Proof.
    induction ds as [|d ds IH]; intros k c f mt HU ST.
    { exists mt. split; [reflexivity | right; cbn; lia]. }
    pose proof (nconv_nonneg ds) as NC.
    cbn [vfs]. destruct d as [| |ch].
    -
      cbn [nconv]. unfold vf_D, vf_W.
      destruct (vfW_U k c f HU ST) as (c1 & f1 & k1 & HL & U1 & K1 & S1 & SP1). rewrite HL.
      destruct (U_lim0 txt p (k1 - 1) c1 (sh_unget f1) U1) as (Ul & Sl & Cl & Rl & Nl & SNl).
      pose proof (U_getc txt p Hp Hnul Hpre BYT 0 c1 (sh_lim0 (sh_unget f1)) Ul ltac:(intros; exact SNl) ltac:(intros X; rewrite Sl, S1 in X; discriminate X)) as G.
      destruct (sh_getc (sh_lim0 (sh_unget f1))) as [c4 f4]. destruct G as (U4 & S4 & C4 & N4 & P4 & R4 & Rp4 & NE4 & E4).
      destruct (Z.ltb_spec c4 0) as [LT|GE].
      { eexists. split; [reflexivity|]. destruct (mt =? 0); [left; reflexivity | right; lia]. }
      destruct (NE4 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
      destruct (U_unget txt p (0 + 1) c4 f4 U4 ltac:(lia)) as (Uu & Su & Cu & Nu & SNu & _).
      destruct (intscan_U txt p Hp Hnul Hpre BYT 10 0 (0 + 1 - 1) c4 (sh_unget f4) Uu ltac:(lia) ltac:(left; reflexivity)
                  ltac:(intros; rewrite SNu; exact Q3) ltac:(intros X; rewrite Su, S4, Sl, S1 in X; discriminate X)) as (fR & HI & RP).
      rewrite HI. destruct RP as (B1 & B2 & B3 & B4 & B5 & B6 & (k' & c' & U')).
      destruct (sh_cnt fR =? 0). { exists mt. split; [reflexivity | right; lia]. }
      destruct (IH k' c' fR (mt + 1) U' ltac:(rewrite B2, Su, S4, Sl; exact S1)) as (r & HV & HR).
      exists r. split; [exact HV | lia].
    -
      cbn [nconv]. unfold vf_W.
      destruct (vfW_U k c f HU ST) as (c1 & f1 & k1 & HL & U1 & K1 & S1 & SP1). rewrite HL.
      exact (IH _ _ _ mt U1 S1).
    -
      cbn [nconv]. unfold vf_L.
      destruct (U_lim0 txt p k c f HU) as (Ul & Sl & Cl & Rl & Nl & SNl).
      pose proof (U_getc txt p Hp Hnul Hpre BYT 0 c (sh_lim0 f) Ul ltac:(intros; exact SNl) ltac:(intros X; rewrite Sl, ST in X; discriminate X)) as G.
      destruct (sh_getc (sh_lim0 f)) as [c1 f1]. destruct G as (U1 & S1 & _).
      destruct (c1 =? ch). { exact (IH _ _ _ mt U1 ltac:(rewrite S1, Sl; exact ST)). }
      destruct (c1 <? 0).
      + eexists. split; [reflexivity|]. destruct (mt =? 0); [left; reflexivity | right; lia].
      + exists mt. split; [reflexivity | right; lia].
  Qed.

  #[using="Hp"] Lemma ssf0_U : U 0 1 (ssf0 txt p).
  Proof.
    unfold ScanIntProps.U, ssf0. cbn. repeat split; try lia; try reflexivity; intros; try discriminate; try lia.
  Qed.

  #[using="Hp Hnul Hpre BYT"] Lemma sscanf_model_total : forall ds, exists r, sscanf_model ds txt p = Some r /\ (r = -1 \/ 0 <= r <= nconv ds).
  Proof. intros ds. unfold sscanf_model. destruct (vfs_U ds 0 1 (ssf0 txt p) 0 ssf0_U eq_refl) as (r & H & R). exists r. split; [exact H | lia]. Qed.
End Txt.
