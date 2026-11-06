(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Record img_tabs : Type := MkTabs {
  t_rip : option (Z * (Z * Z * Z * Z * Z * Z * Z * Z * Z));
  t_amc : option (Z * (Z * Z * Z * Z * Z));
  t_chr : option (Z * (Z * Z));
  t_sw  : option (Z * Z);
  t_cks : list (Z * Z)
}.

(* [comment removed for export] *)
Definition no_tabs : img_tabs := MkTabs None None None None [].

(* [comment removed for export] *)
Definition row_at {A : Type} (o : option (Z * A)) (b : Z) : option A :=
  match o with
  | Some (b', row) => if b =? b' then Some row else None
  | None => None
  end.

Lemma row_at_some {A : Type} (o : option (Z * A)) (b : Z) (row : A) : row_at o b = Some row -> o = Some (b, row).
Proof.
  unfold row_at. destruct o as [[b' r]|]; [|discriminate]. destruct (b =? b') eqn:E; [|discriminate].
  apply Z.eqb_eq in E. subst b'. intros H. injection H as <-. reflexivity.
Qed.

Definition rip_params (T : img_tabs) (b : Z) : option (Z * Z * Z * Z * Z * Z * Z * Z * Z) := row_at (t_rip T) b.
Definition amc_params (T : img_tabs) (b : Z) : option (Z * Z * Z * Z * Z) := row_at (t_amc T) b.
Definition memchr_params (T : img_tabs) (b : Z) : option (Z * Z) := row_at (t_chr T) b.
Definition sw_params (T : img_tabs) (b : Z) : option Z := row_at (t_sw T) b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lt40 (x : Z) : bool := (0 <=? x) && (x <? 1099511627776).

Definition text_ok (b span : Z) : bool := (0x10000 <=? b) && (b + span <? 140737488355328) && (b mod 4 =? 0).

Definition rip_row_ok (r : Z * (Z * Z * Z * Z * Z * Z * Z * Z * Z)) : bool :=
  let '(b, (z, gK, gMB, gME, gHE, aK, aMB, aME, aHE)) := r in
  text_ok b 0x20000 && lt40 gK && lt40 gMB && lt40 gME && lt40 gHE && lt40 aK && lt40 aMB && lt40 aME && lt40 aHE.

Definition amc_row_ok (r : Z * (Z * Z * Z * Z * Z)) : bool :=
  let '(b, (r', gI, aI, gR, e)) := r in
  text_ok b 0x30000 && (0 <=? e) && (e + 0x1000 <? 140737488355328) && (e mod 4 =? 0) && lt40 gI && lt40 aI && lt40 gR.

Definition chr_row_ok (r : Z * (Z * Z)) : bool :=
  let '(b, (cM, cH)) := r in lt40 cM && lt40 cH.

Definition sw_row_ok (r : Z * Z) : bool :=
  let '(b, sr) := r in
  (0 <=? b) && (b + 0x200 <=? 140737488355328) && (0 <=? sr) && (sr + 0x40 <=? 140737488355328) && (b mod 4 =? 0).

Definition opt_ok {A : Type} (f : A -> bool) (o : option A) : bool :=
  match o with Some x => f x | None => true end.

Definition tabs_ok (T : img_tabs) : bool :=
  opt_ok rip_row_ok (t_rip T) && opt_ok amc_row_ok (t_amc T) && opt_ok chr_row_ok (t_chr T) && opt_ok sw_row_ok (t_sw T).

Lemma no_tabs_ok : tabs_ok no_tabs = true.
Proof. reflexivity. Qed.

Lemma lt40_spec (x : Z) : lt40 x = true -> 0 <= x < 2 ^ 40.
Proof. unfold lt40. intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. change (2 ^ 40) with 1099511627776. lia. Qed.

Lemma text_ok_spec (b span : Z) : text_ok b span = true -> 0x10000 <= b /\ b + span < 2 ^ 47 /\ b mod 4 = 0.
Proof.
  unfold text_ok. intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. change (2 ^ 47) with 140737488355328. lia.
Qed.

Section Facts.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.

Lemma tabs_ok_parts : opt_ok rip_row_ok (t_rip T) = true /\ opt_ok amc_row_ok (t_amc T) = true /\
  opt_ok chr_row_ok (t_chr T) = true /\ opt_ok sw_row_ok (t_sw T) = true.
Proof.
  pose proof HT as H. unfold tabs_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  repeat split; assumption.
Qed.

Lemma rip_row_facts (b z gK gMB gME gHE aK aMB aME aHE : Z) : rip_params T b = Some (z, gK, gMB, gME, gHE, aK, aMB, aME, aHE) ->
  (0x10000 <= b /\ b + 0x20000 < 2 ^ 47 /\ b mod 4 = 0) /\
  0 <= gK < 2 ^ 40 /\ 0 <= gMB < 2 ^ 40 /\ 0 <= gME < 2 ^ 40 /\ 0 <= gHE < 2 ^ 40 /\
  0 <= aK < 2 ^ 40 /\ 0 <= aMB < 2 ^ 40 /\ 0 <= aME < 2 ^ 40 /\ 0 <= aHE < 2 ^ 40.
Proof.
  intros Hp. apply row_at_some in Hp. destruct tabs_ok_parts as (H & _). rewrite Hp in H. cbn [opt_ok rip_row_ok] in H.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply text_ok_spec in H0. apply lt40_spec in H1, H2, H3, H4, H5, H6, H7, H8. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma rip_params_40 (b z gK gMB gME gHE aK aMB aME aHE : Z) : rip_params T b = Some (z, gK, gMB, gME, gHE, aK, aMB, aME, aHE) ->
  0 <= gK < 2 ^ 40 /\ 0 <= gMB < 2 ^ 40 /\ 0 <= gME < 2 ^ 40 /\ 0 <= gHE < 2 ^ 40 /\
  0 <= aK < 2 ^ 40 /\ 0 <= aMB < 2 ^ 40 /\ 0 <= aME < 2 ^ 40 /\ 0 <= aHE < 2 ^ 40.
Proof. intros Hp. exact (proj2 (rip_row_facts _ _ _ _ _ _ _ _ _ _ Hp)). Qed.

Lemma rip_params_ok (b z gK gMB gME gHE aK aMB aME aHE : Z) : rip_params T b = Some (z, gK, gMB, gME, gHE, aK, aMB, aME, aHE) ->
  (0 <= gK < 2 ^ 60 /\ 0 <= gMB < 2 ^ 60 /\ 0 <= gME < 2 ^ 60 /\ 0 <= gHE < 2 ^ 60 /\
   0 <= aK < 2 ^ 60 /\ 0 <= aMB < 2 ^ 60 /\ 0 <= aME < 2 ^ 60 /\ 0 <= aHE < 2 ^ 60) /\
  (0x10000 <= b /\ b + 0x20000 < 2 ^ 47 /\ b mod 4 = 0).
Proof.
  intros Hp. destruct (rip_row_facts _ _ _ _ _ _ _ _ _ _ Hp) as (Hb & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  assert (E : 2 ^ 40 < 2 ^ 60) by reflexivity. split; [repeat split; lia | exact Hb].
Qed.

Lemma amc_params_ok (b r gI aI gR e : Z) : amc_params T b = Some (r, gI, aI, gR, e) ->
  (0x10000 <= b /\ b + 0x30000 < 2 ^ 47 /\ b mod 4 = 0) /\ (0 <= e /\ e + 0x1000 < 2 ^ 47 /\ e mod 4 = 0) /\
  0 <= gI < 2 ^ 40 /\ 0 <= aI < 2 ^ 40 /\ 0 <= gR < 2 ^ 40.
Proof.
  intros Hp. apply row_at_some in Hp. destruct tabs_ok_parts as (_ & H & _). rewrite Hp in H. cbn [opt_ok amc_row_ok] in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply text_ok_spec in H0. apply lt40_spec in H4, H5, H6. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3.
  change (2 ^ 47) with 140737488355328 in *. repeat split; lia.
Qed.

Lemma memchr_params_rng (b cM cH : Z) : memchr_params T b = Some (cM, cH) -> 0 <= cM < 2 ^ 40 /\ 0 <= cH < 2 ^ 40.
Proof.
  intros Hp. apply row_at_some in Hp. destruct tabs_ok_parts as (_ & _ & H & _). rewrite Hp in H. cbn [opt_ok chr_row_ok] in H.
  apply andb_prop in H as [H1 H2]. apply lt40_spec in H1, H2. split; assumption.
Qed.

Lemma sw_params_bnd (b sr : Z) : sw_params T b = Some sr ->
  0 <= b /\ b + 0x200 <= 2 ^ 47 /\ 0 <= sr /\ sr + 0x40 <= 2 ^ 47 /\ b mod 4 = 0.
Proof.
  intros Hp. apply row_at_some in Hp. destruct tabs_ok_parts as (_ & _ & _ & H). rewrite Hp in H. cbn [opt_ok sw_row_ok] in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2, H3, H4. apply Z.eqb_eq in H5. change (2 ^ 47) with 140737488355328. lia.
Qed.

End Facts.
