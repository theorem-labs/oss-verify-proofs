(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel PrintfModelX.
From OSSVerify.Proofs.openssl.ct.lib.P Require Export Printf_zfacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma conv_typex_range : forall t ty, conv_typex t = Some ty -> 65 <= t <= 122.
Proof.
  intros t ty H. unfold conv_typex in H. destruct (Z.eqb_spec t 99) as [->|NE]; [lia|].
  exact (conv_type_range _ _ H).
Qed.
Lemma states0_convx : forall t ty, conv_typex t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
  intros t ty H. unfold conv_typex in H. destruct (Z.eqb_spec t 99) as [->|NE].
  - injection H as <-. reflexivity.
  - exact (states0_conv _ _ H).
Qed.
Lemma conv_typex_ty : forall t ty, conv_typex t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11.
Proof.
  intros t ty H. unfold conv_typex in H. destruct (Z.eqb_spec t 99) as [->|NE].
  - injection H as <-. right; left; reflexivity.
  - exact (conv_type_ty _ _ H).
Qed.
(* [comment removed for export] *)
Lemma conv_typex_cases : forall t ty, conv_typex t = Some ty ->
  (t = 115 /\ ty = T_PTR) \/ ((t = 100 \/ t = 105 \/ t = 99) /\ ty = T_INT) \/ ((t = 117 \/ t = 120 \/ t = 88) /\ ty = T_UINT).
Proof.
  intros t ty H. unfold conv_typex, conv_type in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; lia.
Qed.

(* [comment removed for export] *)
Definition STATES1 : list Z :=
  [25; 0; 0; 0; 25; 25; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 14; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 11; 13; 25; 25; 25; 0; 13; 0; 0; 2; 0; 9; 14; 0; 0; 0; 9; 0; 14; 0; 0; 14; 0; 0].
Lemma conv_type_l_inv : forall t ty, conv_type_l t = Some ty ->
  ((t = 100 \/ t = 105) /\ ty = T_LONG) \/ ((t = 117 \/ t = 120 \/ t = 88) /\ ty = T_ULONG).
Proof.
  intros t ty H. unfold conv_type_l in H.
  repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; lia.
Qed.
Lemma conv_type_l_range : forall t ty, conv_type_l t = Some ty -> 65 <= t <= 122.
Proof. intros t ty H. destruct (conv_type_l_inv _ _ H) as [[T _]|[T _]]; lia. Qed.
Lemma states1_conv : forall t ty, conv_type_l t = Some ty -> znth STATES1 (t - 65) = ty.
Proof.
  intros t ty H. destruct (conv_type_l_inv _ _ H) as [[[->| ->] ->]|[[->|[->| ->]] ->]]; reflexivity.
Qed.
Lemma states0_l : znth STATES0 (108 - 65) = LPRE.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma conv_statex_cases : forall s ty ps n, conv_statex s = Some (ty, ps, n) ->
  (exists t s', s = t :: s' /\ t <> 122 /\ t <> 108 /\ conv_typex t = Some ty /\ ps = 0 /\ n = 1%nat)
  \/ (exists t2 s', s = 122 :: t2 :: s' /\ conv_type_z t2 = Some ty /\ ps = ZTPRE /\ n = 2%nat)
  \/ (exists t2 s', s = 108 :: t2 :: s' /\ conv_type_l t2 = Some ty /\ ps = LPRE /\ n = 2%nat).
Proof.
  intros s ty ps n H. unfold conv_statex in H. destruct s as [|t s']; [discriminate|].
  destruct (Z.eqb_spec t 122) as [E|NE].
  - destruct s' as [|t2 s'']; [discriminate|]. destruct (conv_type_z t2) as [ty'|] eqn:CZ; [|discriminate].
    injection H as <- <- <-. right; left. exists t2, s''. subst t. repeat split; first [reflexivity | exact CZ].
  - destruct (Z.eqb_spec t 108) as [EL|NL].
    + destruct s' as [|t2 s'']; [discriminate|]. destruct (conv_type_l t2) as [ty'|] eqn:CL; [|discriminate].
      injection H as <- <- <-. right; right. exists t2, s''. subst t. repeat split; first [reflexivity | exact CL].
    + destruct (conv_typex t) as [ty'|] eqn:CT; [|discriminate]. injection H as <- <- <-.
      left. exists t, s'. repeat split; first [reflexivity | exact NE | exact NL | exact CT].
Qed.

(* [comment removed for export] *)
Lemma parse_dirx_shape : forall s d st rest, parse_dirx s = Some (d, st, rest) ->
  match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
  let (fl, s1) := parse_flags s 0 in
  d_fl d = fl /\
  exists c1 s1b, s1 = c1 :: s1b /\
  exists s2,
  ( (c1 <> 42 /\ fst st = false /\ getint s1 0 = Some (d_w d, s2))
    \/ (c1 = 42 /\ fst st = true /\ d_w d = 0 /\ s2 = s1b /\ match s1b with c1' :: _ => is_digit c1' = false | [] => False end) ) /\
  exists c2 s2b, s2 = c2 :: s2b /\
  exists ps n,
  ( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ snd st = false /\ conv_statex s2 = Some (d_ty d, ps, n) /\ d_t d = nth (n - 1)%nat s2 0 /\ rest = skipn n s2)
  \/ (c2 = 46 /\ d_xp d = true /\ snd st = false /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
      exists s3, getint s2b 0 = Some (d_p d, s3) /\ conv_statex s3 = Some (d_ty d, ps, n) /\ d_t d = nth (n - 1)%nat s3 0 /\ rest = skipn n s3)
  \/ (c2 = 46 /\ d_xp d = true /\ snd st = true /\ d_p d = 0 /\ exists s3b, s2b = 42 :: s3b /\ match s3b with c4 :: _ => is_digit c4 = false | [] => False end /\
      conv_statex s3b = Some (d_ty d, ps, n) /\ d_t d = nth (n - 1)%nat s3b 0 /\ rest = skipn n s3b) ).
Proof.
  intros s d st rest H. unfold parse_dirx in H.
  split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
  match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
  destruct (parse_flags s 0) as [fl s1].
  destruct s1 as [|c1 s1b]; [discriminate|].
  (* [comment removed for export] *)
  match type of H with (match ?wr with | Some _ => _ | None => None end) = _ =>
    destruct wr as [[[w ws'] s2]|] eqn:WR; [|discriminate] end.
  assert (WALT : ( (c1 <> 42 /\ ws' = false /\ getint (c1 :: s1b) 0 = Some (w, s2))
                 \/ (c1 = 42 /\ ws' = true /\ w = 0 /\ s2 = s1b /\ match s1b with c1' :: _ => is_digit c1' = false | [] => False end) )).
  { destruct (Z.eqb_spec c1 42) as [E42|N42].
    - destruct s1b as [|c1' s1'']; [discriminate|]. destruct (is_digit c1') eqn:DG; [discriminate|].
      injection WR as <- <- <-. right. repeat split; try assumption; reflexivity.
    - destruct (getint (c1 :: s1b) 0) as [[w0 s20]|] eqn:G; [|discriminate]. injection WR as <- <- <-.
      left. repeat split; try assumption; reflexivity. }
  clear WR.
  destruct s2 as [|c2 s2b]; [discriminate|].
  (* [comment removed for export] *)
  match type of H with (match ?px with | Some _ => _ | None => None end) = _ =>
    destruct px as [[[[p xp] ps'] s3]|] eqn:PXE; [|discriminate] end.
  destruct (conv_statex s3) as [[[ty pst] n]|] eqn:CS; [|discriminate].
  injection H as <- <- <-. cbn - [conv_statex getint is_digit Z.eqb].
  split; [reflexivity|]. exists c1, s1b. split; [reflexivity|].
  exists (c2 :: s2b). split; [exact WALT|]. exists c2, s2b. split; [reflexivity|].
  exists pst, n.
  destruct (Z.eqb_spec c2 46) as [E46|N46].
  - destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42'].
    + destruct s3b as [|c4 s4b]; [discriminate|]. destruct (is_digit c4) eqn:DG4; [discriminate|].
      injection PXE as <- <- <- <-. right; right. split; [exact E46|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists (c4 :: s4b). split; [rewrite E42'; reflexivity|]. split; [exact DG4|]. split; [exact CS|]. split; reflexivity.
    + destruct (getint (c3 :: s3b) 0) as [[p0 s30]|] eqn:G2; [|discriminate]. injection PXE as <- <- <- <-.
      right; left. split; [exact E46|]. split; [reflexivity|]. split; [reflexivity|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
      exists s30. split; [first [reflexivity | exact G2]|]. split; [exact CS|]. split; reflexivity.
  - injection PXE as <- <- <- <-.
    left. split; [exact N46|]. repeat split; first [reflexivity | exact CS].
Qed.

(* [comment removed for export] *)
Lemma dir_eff_w_false : forall d args, dir_eff_w d false args = Some (d, args).
Proof. reflexivity. Qed.
Lemma dir_eff_p_false : forall d args, dir_eff_p d false args = Some (d, args).
Proof. reflexivity. Qed.
Lemma dir_eff_false : forall d args, dir_eff d (false, false) args = Some (d, args).
Proof. reflexivity. Qed.
Lemma dir_eff_w_true_inv : forall d args d' args', dir_eff_w d true args = Some (d', args') ->
  exists wv, args = PA_i wv :: args' /\ -2147483647 <= wv <= 2147483647
    /\ d' = mkDir (if wv <? 0 then Z.lor (d_fl d) LEFT_ADJ else d_fl d) (Z.abs wv) (d_p d) (d_xp d) (d_t d) (d_ty d).
Proof.
  intros d args d' args' H. unfold dir_eff_w in H.
  destruct args as [|[| |wv| | |] args0]; try discriminate.
  destruct (Z.ltb_spec wv (-2147483647)); [discriminate|]. destruct (Z.ltb_spec 2147483647 wv); [discriminate|].
  cbn [orb] in H. injection H as <- <-. exists wv. repeat split; try lia.
Qed.
Lemma dir_eff_p_true_inv : forall d args d' args', dir_eff_p d true args = Some (d', args') ->
  exists pv, args = PA_i pv :: args' /\ 0 <= pv <= 2147483647
    /\ d' = mkDir (d_fl d) (d_w d) pv true (d_t d) (d_ty d).
Proof.
  intros d args d' args' H. unfold dir_eff_p in H.
  destruct args as [|[| |pv| | |] args0]; try discriminate.
  destruct (Z.ltb_spec pv 0); [discriminate|]. destruct (Z.ltb_spec 2147483647 pv); [discriminate|].
  cbn [orb] in H. injection H as <- <-. exists pv. repeat split; try lia.
Qed.
(* [comment removed for export] *)
Lemma dir_eff_stages : forall d st args d' args', dir_eff d st args = Some (d', args') ->
  exists d1 args1, dir_eff_w d (fst st) args = Some (d1, args1) /\ dir_eff_p d1 (snd st) args1 = Some (d', args').
Proof.
  intros d [ws ps] args d' args' H. unfold dir_eff in H. cbn [fst snd] in *.
  destruct (dir_eff_w d ws args) as [[d1 args1]|]; [|discriminate]. exists d1, args1. split; [reflexivity | exact H].
Qed.
(* [comment removed for export] *)
Lemma dir_eff_true_inv : forall d args d' args', dir_eff d (true, false) args = Some (d', args') ->
  exists wv, args = PA_i wv :: args' /\ -2147483647 <= wv <= 2147483647
    /\ d' = mkDir (if wv <? 0 then Z.lor (d_fl d) LEFT_ADJ else d_fl d) (Z.abs wv) (d_p d) (d_xp d) (d_t d) (d_ty d).
Proof.
  intros d args d' args' H. destruct (dir_eff_stages _ _ _ _ _ H) as (d1 & args1 & W & P). cbn [fst snd] in W, P.
  rewrite dir_eff_p_false in P. injection P as <- <-. exact (dir_eff_w_true_inv _ _ _ _ W).
Qed.
(* [comment removed for export] *)
Lemma nstars_range : forall st, 0 <= nstars st <= 2.
Proof. intros [[|] [|]]; unfold nstars; cbn [fst snd]; lia. Qed.
Lemma dir_eff_skip : forall d st args d' args', dir_eff d st args = Some (d', args') ->
  args' = skipn (Z.to_nat (nstars st)) args.
Proof.
  intros d [ws ps] args d' args' H. destruct (dir_eff_stages _ _ _ _ _ H) as (d1 & args1 & W & P). cbn [fst snd nstars] in *.
  destruct ws.
  - destruct (dir_eff_w_true_inv _ _ _ _ W) as (wv & -> & _ & ->). destruct ps.
    + destruct (dir_eff_p_true_inv _ _ _ _ P) as (pv & -> & _ & ->). reflexivity.
    + rewrite dir_eff_p_false in P. injection P as _ <-. reflexivity.
  - rewrite dir_eff_w_false in W. injection W as <- <-. destruct ps.
    + destruct (dir_eff_p_true_inv _ _ _ _ P) as (pv & -> & _ & ->). reflexivity.
    + rewrite dir_eff_p_false in P. injection P as _ <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_left_adj_range : forall fl, 0 <= fl < 131072 -> 0 <= Z.lor fl LEFT_ADJ < 131072.
Proof. intros fl H. unfold LEFT_ADJ. apply lor_bound17; lia. Qed.
