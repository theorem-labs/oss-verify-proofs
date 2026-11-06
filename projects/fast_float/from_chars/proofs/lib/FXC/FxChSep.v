(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib.

Module FxKeep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition keep_ok (model' : Model) (M M' : smodel) (m0 m0' : word -> option byte) : Prop :=
  incl (sm_maps M) (sm_maps M') /\ incl (sm_own M) (sm_own M') /\
  (forall x, 0 <= x < alloc_top (m_vmmaps model') -> m0' (Z_to_bv 64 x) = m0 (Z_to_bv 64 x)) /\
  (forall x, in_zr (sm_zr M) x = true -> in_zr (sm_zr M') x = true).   (* [comment removed for export] *)

Lemma keep_ok_refl : forall model M m0, keep_ok model M M m0 m0.
Proof. intros model M m0. split; [apply incl_refl | split; [apply incl_refl | split; [reflexivity | intros x Hx; exact Hx]]]. Qed.
End FxKeep.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u_lsub_mod : forall E a b, uE E (lsub a b) = (uE E a - uE E b) mod two64.
Proof.
  intros E a b. unfold uE. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma pdisj_nth2 : forall l i i' p q, pdisj l -> nth_error l i = Some p -> nth_error l i' = Some q -> i <> i' -> iv_disj p q.
Proof.
  induction l as [|x r IH]; intros i i' p q H Hp Hq Hne; [destruct i; discriminate|].
  destruct H as [Hx Hr]. destruct i as [|i], i' as [|i']; cbn [nth_error] in Hp, Hq; try lia.
  - injection Hp as <-. rewrite Forall_forall in Hx. exact (Hx q (nth_error_In _ _ Hq)).
  - injection Hq as <-. rewrite Forall_forall in Hx. pose proof (Hx p (nth_error_In _ _ Hp)) as Hd. unfold iv_disj in *. lia.
  - exact (IH i i' p q Hr Hp Hq ltac:(lia)).
Qed.

Lemma ladd_u2 : forall E a b, bv_unsigned (lden E a) + bv_unsigned (lden E b) < two64 ->
  bv_unsigned (lden E (ladd a b)) = bv_unsigned (lden E a) + bv_unsigned (lden E b).
Proof.
  intros E a b H. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E a)). pose proof (bv_unsigned_in_range _ (lden E b)).
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *. lia.
Qed.

Lemma uE_range : forall E l, 0 <= uE E l < two64.
Proof. intros E l. unfold uE. pose proof (bv_unsigned_in_range _ (lden E l)) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma small_diff : forall E x y lo hi, lo <= uE E (lsub x y) <= hi ->
  (uE E y <= uE E x /\ uE E x - uE E y = uE E (lsub x y)) \/ (uE E x < uE E y /\ uE E x - uE E y + two64 = uE E (lsub x y)).
Proof.
  intros E x y lo hi H. rewrite u_lsub_mod in *. pose proof (uE_range E x). pose proof (uE_range E y).
  destruct (Z_le_gt_dec (uE E y) (uE E x)) as [Hle|Hgt].
  - left. split; [exact Hle|]. rewrite Z.mod_small by lia. reflexivity.
  - right. split; [lia|]. replace (uE E x - uE E y) with ((uE E x - uE E y + two64) + (-1) * two64) at 2 by lia.
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition contained_b (fs : list fact) (a : lin) (n : Z) (gb : lin) (gs : Z) : bool :=
  match lin_off a gb with
  | Some d => (Z.leb 0 d && Z.leb (d + n) gs)%bool
  | None => let '(lo, hi) := irange fs (lsub a gb) in (Z.leb 0 lo && Z.leb (hi + n) gs)%bool
  end.

Lemma contained_sound : forall E fs a n gb gs, Forall (fact_ok E) fs -> contained_b fs a n gb gs = true -> 0 < n ->
  uE E gb + gs <= two64 -> uE E gb <= uE E a /\ uE E a + n <= uE E gb + gs.
Proof.
  intros E fs a n gb gs HF H Hn Hg. unfold contained_b in H. pose proof (uE_range E a) as Ra. pose proof (uE_range E gb) as Rb.
  destruct (lin_off a gb) as [d|] eqn:Hd.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. destruct (lin_off_sound E a gb d Hd) as [Hv Hr].
    assert (Hu : uE E (lsub a gb) = d) by (unfold uE; rewrite Hv; apply fg64'; exact Hr).
    destruct (small_diff E a gb d d ltac:(lia)) as [[Hl He]|[Hl He]]; lia.
  - destruct (irange fs (lsub a gb)) as [lo hi] eqn:Hir. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
    pose proof (irange_sound E fs (lsub a gb) HF) as Hs. rewrite Hir in Hs. cbn [fst snd] in Hs. fold (uE E (lsub a gb)) in Hs.
    destruct (small_diff E a gb lo hi Hs) as [[Hl He]|[Hl He]]; lia.
Qed.

(* [comment removed for export] *)
Definition lal4096 (l : lin) : bool := (Z.eqb (l_c l mod 4096) 0 && forallb (fun '(_, c) => Z.eqb (c mod 4096) 0) (l_t l))%bool.

Lemma tsum_al4096 : forall E t, forallb (fun '(_, c) => Z.eqb (c mod 4096) 0) t = true -> tsum E t mod 4096 = 0.
Proof.
  intros E t. induction t as [|[x c] t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [tsum]. rewrite Z.add_mod by lia. rewrite (IH H2), Z.add_0_r. rewrite Z.mul_mod by lia. rewrite H1. reflexivity.
Qed.

Lemma lal4096_sound : forall E l, lal4096 l = true -> uE E l mod 4096 = 0.
Proof.
  intros E l H. unfold lal4096 in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. unfold uE.
  rewrite u_lden_mod. rewrite Z.mod_mod_divide by (unfold two64; exists 4503599627370496; lia).
  unfold lz. rewrite Z.add_mod, H1, (tsum_al4096 E _ H2) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint sep_grant_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (R : region) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& Z.leb 1 (snd (irange fs (rg_size R))) &&&
                contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g)) (gsz_lo fs g)) |||
               sep_grant_acc fs r j (Datatypes.S i) R      (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition sep_shadow_b (fs : list fact) (R : region) : bool :=
  let rb := irange fs (rg_base R) in
  if (if Z.leb SH_LO (fst rb) then Z.ltb (snd rb + snd (irange fs (rg_size R))) two64 else false)
  then Z.leb (snd (irange fs (ladd (rg_base R) (rg_size R)))) SH_HI else false.
(* [comment removed for export] *)
Definition in_res_b (res : list (word * word)) (lo hi : Z) : bool :=
  existsb (fun p => (Z.leb (bv_unsigned (fst p)) lo && Z.leb hi (bv_unsigned (fst p) + bv_unsigned (snd p)))%bool) res.
Definition sep_res_b (res : list (word * word)) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some s => (Z.ltb 0 s && in_res_b res b (b + s))%bool
  | _, _ => false
  end.
Definition sep_pres_b (res : list (word * word)) (R : region) : bool :=
  match is_const (rg_base R), is_const (rg_size R) with
  | Some b, Some s => (Z.ltb 0 s && Z.leb SH_OFF b && in_res_b res (8 * (b - SH_OFF)) (8 * (b + s - SH_OFF)))%bool
  | _, _ => false
  end.

Lemma in_res_sound : forall res lo hi x, in_res_b res lo hi = true -> lo <= x < hi -> covered res x = true.
Proof.
  intros res lo hi x H Hx. unfold in_res_b in H. apply existsb_exists in H as (p & Hp & Hc). apply andb_prop in Hc as [C1 C2].
  apply Z.leb_le in C1, C2. unfold covered. apply existsb_exists. exists p. split; [exact Hp|]. unfold in_iv, in_rng, B, S.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition sep_band_b (fs : list fact) (sp : lin) (R : region) : bool :=
  if Z.leb (snd (irange fs (lsub sp (rg_base R)))) 8388608 then true else Z.ltb (snd (irange fs (lsub (rg_base R) sp))) 4611686018427387904.
(* [comment removed for export] *)
Definition lfew2 (l : lin) : bool := match l_t l with _ :: _ :: _ :: _ => false | _ => true end.
Definition cand_b (b gb : lin) : bool := match lin_off b gb with Some _ => true | None => lfew2 (lsub b gb) end.
Fixpoint cont1_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& cand_b b (fst (fst g)) &&& contained_b fs b z (fst (fst g)) (gsz_lo fs g)) |||
              cont1_acc fs r j (Datatypes.S i) b z
  end.
Definition cont1 (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  let z := snd (irange fs (rg_size R)) in if Z.leb 1 z then cont1_acc fs gs j O (rg_base R) z else false.
Lemma cont1_acc_sound : forall fs gs j i R, Z.leb 1 (snd (irange fs (rg_size R))) = true ->
  cont1_acc fs gs j i (rg_base R) (snd (irange fs (rg_size R))) = true -> sep_grant_acc fs gs j i R = true.
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R Hz H; cbn [cont1_acc] in H; [discriminate|]. cbn [sep_grant_acc]. rewrite Hz.
  destruct (negb (is_mark g)); [|exact (IH (Datatypes.S i) R Hz H)].
  destruct (negb (Nat.eqb i j)); [|exact (IH (Datatypes.S i) R Hz H)].
  destruct (cand_b (rg_base R) (fst (fst g))).
  - destruct (contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g)) (gsz_lo fs g)); [reflexivity | exact (IH (Datatypes.S i) R Hz H)].
  - rewrite (IH (Datatypes.S i) R Hz H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.
Lemma cont1_sound : forall fs gs j R, cont1 fs gs j R = true -> sep_grant_acc fs gs j O R = true.
Proof.
  intros fs gs j R H. unfold cont1 in H. cbv zeta in H. destruct (Z.leb 1 (snd (irange fs (rg_size R)))) eqn:Hz; [|discriminate].
  exact (cont1_acc_sound fs gs j O R Hz H).
Qed.
Definition band_few2 (fs : list fact) (sp : lin) (R : region) : bool := if lfew2 (lsub sp (rg_base R)) then sep_band_b fs sp R else false.
Definition sep_app_b (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp : lin) (R : region) : bool :=
  if cont1 fs gs j R then true
  else if band_few2 fs sp R then true
  else if sep_grant_acc fs gs j O R then true else sep_band_b fs sp R.
Lemma sep_app_b_eq : forall fs gs j sp R, sep_app_b fs gs j sp R = (sep_grant_acc fs gs j O R || sep_band_b fs sp R)%bool.
Proof.
  intros fs gs j sp R. unfold sep_app_b. destruct (cont1 fs gs j R) eqn:Hc; [rewrite (cont1_sound fs gs j R Hc); reflexivity|].
  unfold band_few2. destruct (lfew2 (lsub sp (rg_base R))); [|reflexivity].
  destruct (sep_band_b fs sp R); [|reflexivity]. destruct (sep_grant_acc fs gs j O R); reflexivity.
Qed.

Lemma sep_grant_acc_spec : forall fs gs j i R, sep_grant_acc fs gs j i R = true ->
  exists i' g, (i <= i')%nat /\ i' <> j /\ nth_error gs (i' - i) = Some g /\ 1 <= snd (irange fs (rg_size R)) /\
    contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (fst (fst g)) (gsz_lo fs g) = true /\ is_mark g = false.
Proof.
  intros fs gs. induction gs as [|g r IH]; intros j i R H; cbn [sep_grant_acc] in H; [discriminate|].
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply negb_true_iff, Nat.eqb_neq in H1.
    apply negb_true_iff in H0.
    apply Z.leb_le in H2. exists i, g. rewrite Nat.sub_diag. repeat split; first [assumption | reflexivity | lia].
  - destruct (IH j (Datatypes.S i) R H) as (i' & g' & Hi & Hj & Hn & Hb & Hs & Hmk). exists i', g'. split; [lia|]. split; [exact Hj|].
    replace (i' - i)%nat with (Datatypes.S (i' - Datatypes.S i)) by lia. cbn [nth_error]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint sep_pgrant_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (R : region) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&& Z.leb 1 (snd (irange fs (rg_size R))) &&&
                match srl_lin fs 3 (fst (fst g)) with
                | Some pb => contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (laddc pb SH_OFF) (gsz_lo fs g / 8)
                | None => false
                end) ||| sep_pgrant_acc fs r j (Datatypes.S i) R
  end.
Definition sep_pband_b (fs : list fact) (sp : lin) (R : region) : bool :=
  let id := irange fs (lsub (lscale 8 (rg_base R)) sp) in     (* [comment removed for export] *)
  if (if (if Z.leb (8 * SH_OFF - 8388608 - 4095) (fst id) then Z.ltb (snd id) 9223372036854775808 else false)
      then Z.ltb (snd (irange fs (rg_base R))) 1152921504606846976 else false)
  then Z.leb 9 (lalign fs (rg_base R)) else false.
(* [comment removed for export] *)
Lemma pg_band : forall x t : Z, x mod 4096 = 0 -> t - 4095 <= x -> 4096 * (t / 4096) <= x.
Proof.
  intros x t Hx Ht. pose proof (Z.div_mod x 4096 ltac:(lia)) as E1. rewrite Hx, Z.add_0_r in E1.
  assert (t / 4096 <= x / 4096) by (apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia). lia.
Qed.
(* [comment removed for export] *)
Definition fact_hi (fs : list fact) (l : lin) (dflt : Z) : Z :=
  fold_right (fun f acc => match f with
                           | FRange l' _ hi => if terms_eqb (l_t l') (l_t l)
                                               then let d := w64 (l_c l - l_c l') in if Z.ltb (hi + d) two64 then Z.min (hi + d) acc else acc
                                               else acc
                           | _ => acc end) dflt fs.
Lemma fact_shift_sound : forall E l l' hi, l_t l' = l_t l -> uE E l' <= hi -> hi + w64 (l_c l - l_c l') < two64 ->
  uE E l <= hi + w64 (l_c l - l_c l').
Proof.
  intros E l l' hi Ht Hu Hw. pose proof (uE_range E l') as R'. pose proof (w64_range (l_c l - l_c l')) as Rd.
  assert (Hl : uE E l = (uE E l' + w64 (l_c l - l_c l')) mod two64).
  { unfold uE. rewrite !u_lden_mod. rewrite w64_mod. unfold lz. rewrite Ht.
    rewrite Z.add_mod_idemp_l by (unfold two64; lia). rewrite Z.add_mod_idemp_r by (unfold two64; lia). f_equal. lia. }
  rewrite Hl, Z.mod_small by lia. lia.
Qed.
Lemma fact_hi_sound : forall E fs l d, Forall (fact_ok E) fs -> uE E l <= d -> uE E l <= fact_hi fs l d.
Proof.
  intros E fs l d HF Hd. unfold fact_hi. induction HF as [|f fs' Hf HF' IH]; cbn [fold_right]; [exact Hd|].
  destruct f as [c a b tk | l' lo hi | l' k r | l' m v | x v j | xb bsb]; try exact IH.
  destruct (terms_eqb (l_t l') (l_t l)) eqn:Hl; [|exact IH]. apply terms_eqb_eq in Hl.
  destruct (Z.ltb (hi + w64 (l_c l - l_c l')) two64) eqn:Hw; [|exact IH]. apply Z.ltb_lt in Hw.
  cbn [fact_ok] in Hf. pose proof (fact_shift_sound E l l' hi Hl ltac:(unfold uE; lia) Hw). lia.
Qed.
Definition sep_noshadow_b (fs : list fact) (R : region) : bool :=
  let l := laddc (rg_base R) (- SH_HI) in
  Z.leb (fact_hi fs l (snd (irange fs l))) (two64 + SH_LO - snd (irange fs (rg_size R)) - SH_HI).
(* [comment removed for export] *)
Fixpoint contp1_acc (fs : list fact) (gs : list (lin * lin * gkind)) (j i : nat) (b : lin) (z : Z) : bool :=
  match gs with
  | [] => false
  | g :: r => (negb (is_mark g) &&& negb (Nat.eqb i j) &&&
               match srl_lin fs 3 (fst (fst g)) with
               | Some pb => cand_b b (laddc pb SH_OFF) &&& contained_b fs b z (laddc pb SH_OFF) (gsz_lo fs g / 8)
               | None => false
               end) ||| contp1_acc fs r j (Datatypes.S i) b z
  end.
Definition contp1 (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (R : region) : bool :=
  let z := snd (irange fs (rg_size R)) in if Z.leb 1 z then contp1_acc fs gs j O (rg_base R) z else false.
Lemma contp1_acc_sound : forall fs gs j i R, Z.leb 1 (snd (irange fs (rg_size R))) = true ->
  contp1_acc fs gs j i (rg_base R) (snd (irange fs (rg_size R))) = true -> sep_pgrant_acc fs gs j i R = true.
Proof.
  intros fs gs j. induction gs as [|g r IH]; intros i R Hz H; cbn [contp1_acc] in H; [discriminate|]. cbn [sep_pgrant_acc]. rewrite Hz.
  destruct (negb (is_mark g)); [|exact (IH (Datatypes.S i) R Hz H)].
  destruct (negb (Nat.eqb i j)); [|exact (IH (Datatypes.S i) R Hz H)].
  destruct (srl_lin fs 3 (fst (fst g))) as [pb|]; [|exact (IH (Datatypes.S i) R Hz H)].
  destruct (cand_b (rg_base R) (laddc pb SH_OFF)).
  - destruct (contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (laddc pb SH_OFF) (gsz_lo fs g / 8)); [reflexivity | exact (IH (Datatypes.S i) R Hz H)].
  - rewrite (IH (Datatypes.S i) R Hz H). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.
Lemma contp1_sound : forall fs gs j R, contp1 fs gs j R = true -> sep_pgrant_acc fs gs j O R = true.
Proof.
  intros fs gs j R H. unfold contp1 in H. cbv zeta in H. destruct (Z.leb 1 (snd (irange fs (rg_size R)))) eqn:Hz; [|discriminate].
  exact (contp1_acc_sound fs gs j O R Hz H).
Qed.
Definition sep_pc_b (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp : lin) (R : region) : bool :=
  if contp1 fs gs j R then true
  else if sep_noshadow_b fs R then true
  else if sep_pgrant_acc fs gs j O R then true else sep_pband_b fs sp R.
Lemma sep_pc_b_eq : forall fs gs j sp R, sep_pc_b fs gs j sp R = (sep_pgrant_acc fs gs j O R || sep_pband_b fs sp R || sep_noshadow_b fs R)%bool.
Proof.
  intros fs gs j sp R. unfold sep_pc_b. destruct (contp1 fs gs j R) eqn:Hc; [rewrite (contp1_sound fs gs j R Hc); reflexivity|].
  destruct (sep_noshadow_b fs R); [destruct (sep_pgrant_acc fs gs j O R), (sep_pband_b fs sp R); reflexivity|].
  destruct (sep_pgrant_acc fs gs j O R); [reflexivity|]. destruct (sep_pband_b fs sp R); reflexivity.
Qed.

Lemma noshadow_sound : forall E fs R, Forall (fact_ok E) fs -> sep_noshadow_b fs R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> in_shadow w = false.
Proof.
  intros E fs R HF H w Hw. unfold sep_noshadow_b in H. apply Z.leb_le in H.
  pose proof (irange_sound E fs (laddc (rg_base R) (- SH_HI)) HF) as Rn0.
  pose proof (fact_hi_sound E fs (laddc (rg_base R) (- SH_HI)) _ HF (proj2 Rn0)) as Rn.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  pose proof (uE_range E (rg_base R)). unfold in_shadow. apply andb_false_iff.
  destruct (Z_le_gt_dec SH_HI (uE E (rg_base R))) as [Hge|Hlt]; [right; apply Z.ltb_ge; lia|left; apply Z.leb_gt].
  assert (Hu : uE E (laddc (rg_base R) (- SH_HI)) = uE E (rg_base R) - SH_HI + two64).
  { unfold uE at 1. rewrite lden_laddc, Z_to_bv_unsigned. fold (uE E (rg_base R)). unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64.
    replace (uE E (rg_base R) + - SH_HI) with ((uE E (rg_base R) - SH_HI + two64) + (-1) * two64) by lia.
    rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. unfold SH_HI, two64 in *; lia. }
  rewrite Hu in Rn. unfold SH_LO, SH_HI, two64 in *. lia.
Qed.

Lemma sep_pgrant_acc_spec : forall fs gs j i R, sep_pgrant_acc fs gs j i R = true ->
  exists i' g pb, (i <= i')%nat /\ i' <> j /\ nth_error gs (i' - i) = Some g /\ srl_lin fs 3 (fst (fst g)) = Some pb /\
    1 <= snd (irange fs (rg_size R)) /\
    contained_b fs (rg_base R) (snd (irange fs (rg_size R))) (laddc pb SH_OFF) (gsz_lo fs g / 8) = true /\ is_mark g = false.
Proof.
  intros fs gs. induction gs as [|g r IH]; intros j i R H; cbn [sep_pgrant_acc] in H; [discriminate|].
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H1 H]. apply andb_prop in H1 as [H1 H2]. apply andb_prop in H1 as [H0 H1]. apply negb_true_iff, Nat.eqb_neq in H1. apply Z.leb_le in H2.
    apply negb_true_iff in H0.
    destruct (srl_lin fs 3 (fst (fst g))) as [pb|] eqn:Hs; [|discriminate].
    exists i, g, pb. rewrite Nat.sub_diag. repeat split; first [assumption | reflexivity | lia].
  - destruct (IH j (Datatypes.S i) R H) as (i' & g' & pb & Hi & Hj & Hn & Hs & Hb & Hz & Hmk). exists i', g', pb. split; [lia|]. split; [exact Hj|].
    replace (i' - i)%nat with (Datatypes.S (i' - Datatypes.S i)) by lia. cbn [nth_error]. repeat split; assumption.
Qed.

Section Sep.
Variable E : valu.
Variable fs : list fact.
Variable gs : list (lin * lin * gkind).
Variable model : Model.
Variable sp : lin.
Variable BL : list (word * word).        (* [comment removed for export] *)
Hypothesis HF : Forall (fact_ok E) fs.
Hypothesis Hmaps : vm_maps (m_vmmaps model) = lden_maps E BL gs.
Hypothesis Hpd : pdisj (vm_maps (m_vmmaps model)).
Hypothesis Hgsh : Forall (gshape_ok E) gs.
Hypothesis Hgtop : Forall (fun g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model)) gs.
Hypothesis Hsp : vm_init_sp (m_vmmaps model) = lden E sp.
Hypothesis Hsphi : bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi.
Hypothesis Hspok : init_sp_ok (m_vmmaps model).

#[using="Type"] Lemma gden_uB : forall g, gshape_ok E g -> B (gden E g) = uE E (fst (fst g)).
Proof. LiaFast.lf_pins LiaFast.u0. intros g _. reflexivity. Qed.
#[using="Type"] Lemma gden_uS : forall g, gshape_ok E g -> S (gden E g) = gsz E g.
Proof. LiaFast.lf_pins LiaFast.u0. intros g _. reflexivity. Qed.

(* [comment removed for export] *)
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi"] Theorem sep_app_sound : forall j g a n R,
  nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  sep_app_b fs gs j sp R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi : LiaFast.U) => LiaFast.u0).
  intros j g a n R Hj Hjm Hlo Hhi Hrs Hrw H w Hw Hin. rewrite sep_app_b_eq in H.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  apply orb_prop in H as [H|H].
  - destruct (sep_grant_acc_spec fs gs j O R H) as (i' & g' & _ & Hne & Hn' & Hs1 & Hc & Hmk'). rewrite Nat.sub_0_r in Hn'.
    assert (Hd : iv_disj (gden E g) (gden E g')).
    { rewrite Hmaps in Hpd. apply (pdisj_lden_nth E BL gs j i' g g' Hpd Hj Hn'); [intros ->; exact (Hne eq_refl) | exact Hjm | exact Hmk']. }
    rewrite Forall_forall in Hgsh.
    pose proof (Hgsh g (nth_error_In _ _ Hj)) as Gg. pose proof (Hgsh g' (nth_error_In _ _ Hn')) as Gg'.
    unfold iv_disj in Hd. rewrite !gden_uB, !gden_uS in Hd by assumption. pose proof (gsz_bounds E fs g' HF) as Gb.
    destruct (contained_sound E fs (rg_base R) _ (fst (fst g')) (gsz_lo fs g') HF Hc ltac:(lia)
                ltac:(destruct Gg' as (_ & _ & _ & G4 & _); unfold two64; lia)) as [C1 C2]. lia.
  - unfold sep_band_b in H.
    rewrite Forall_forall in Hgtop. pose proof (Hgtop g (nth_error_In _ _ Hj)) as Gt.
    unfold alloc_top, stack_max_size in Gt. rewrite Hsp in Gt, Hsphi. fold (uE E sp) in Gt, Hsphi. unfold sp_window_hi in Hsphi.
    pose proof (uE_range E sp). pose proof (uE_range E (rg_base R)).
    apply orb_prop in H as [H|H].
    + apply Z.leb_le in H. pose proof (irange_sound E fs (lsub sp (rg_base R)) HF) as Rd.
      fold (uE E (lsub sp (rg_base R))) in Rd.
      destruct (small_diff E sp (rg_base R) _ _ Rd) as [[Hl He]|[Hl He]]; [lia|].
      unfold two64 in *. lia.
    + apply Z.ltb_lt in H. pose proof (irange_sound E fs (lsub (rg_base R) sp) HF) as Rd.
      fold (uE E (lsub (rg_base R) sp)) in Rd.
      destruct (small_diff E (rg_base R) sp _ _ Rd) as [[Hl He]|[Hl He]]; [lia|].
      unfold two64 in *. lia.
Qed.
#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi"] Theorem sep_pc_sound : forall j g a n R,
  nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  uE E a mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> SH_LO <= uE E a / 8 + SH_OFF -> uE E a / 8 + SH_OFF + n / 8 <= SH_HI ->
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  sep_pc_b fs gs j sp R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a / 8 + SH_OFF <= w < uE E a / 8 + SH_OFF + n / 8).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi : LiaFast.U) => LiaFast.u0).
  intros j g a n R Hj Hjm Hlo Hhi Ha8 Hn8 Hn Hps1 Hps2 Hrs Hrw H w Hw Hin. rewrite sep_pc_b_eq in H.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  rewrite Forall_forall in Hgsh. pose proof (Hgsh g (nth_error_In _ _ Hj)) as Gg.
  apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - destruct (sep_pgrant_acc_spec fs gs j O R H) as (i' & g' & pb & _ & Hne & Hn' & Hsl & Hs1 & Hc & Hmk'). rewrite Nat.sub_0_r in Hn'.
    assert (Hd : iv_disj (gden E g) (gden E g')).
    { rewrite Hmaps in Hpd. apply (pdisj_lden_nth E BL gs j i' g g' Hpd Hj Hn'); [intros ->; exact (Hne eq_refl) | exact Hjm | exact Hmk']. }
    pose proof (Hgsh g' (nth_error_In _ _ Hn')) as Gg'.
    unfold iv_disj in Hd. rewrite !gden_uB, !gden_uS in Hd by assumption.
    pose proof (srl_lin_sound E fs 3 (fst (fst g')) pb HF ltac:(lia) Hsl) as Hpbv. rewrite Z.shiftr_div_pow2 in Hpbv by lia.
    change (2 ^ 3) with 8 in Hpbv. fold (uE E pb) in Hpbv. fold (uE E (fst (fst g'))) in Hpbv.
    assert (HbP : uE E (laddc pb SH_OFF) = uE E (fst (fst g')) / 8 + SH_OFF).
    { unfold uE at 1. rewrite lden_laddc, Z_to_bv_unsigned. fold (uE E pb). rewrite Hpbv.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small.
      pose proof (uE_range E (fst (fst g'))). assert (uE E (fst (fst g')) / 8 <= uE E (fst (fst g'))) by (apply Z.div_le_upper_bound; lia).
      assert (0 <= uE E (fst (fst g')) / 8) by (apply Z.div_pos; lia). unfold SH_OFF, two64 in *. lia. }
    destruct (contained_sound E fs (rg_base R) _ (laddc pb SH_OFF) (gsz_lo fs g' / 8) HF Hc ltac:(lia)) as [C1 C2].
    { rewrite HbP. pose proof (gsz_bounds E fs g' HF) as Gb. pose proof (gsz_lo_nonneg fs g'). destruct Gg' as (G1' & _ & _ & G4 & _). assert (gsz_lo fs g' / 8 <= gsz_lo fs g') by (apply Z.div_le_upper_bound; lia).
      assert (uE E (fst (fst g')) / 8 <= uE E (fst (fst g'))) by (apply Z.div_le_upper_bound; pose proof (uE_range E (fst (fst g'))); lia).
      unfold SH_OFF, two64. lia. }
    rewrite HbP in C1, C2.
    pose proof (gsz_bounds E fs g' HF) as Gb. assert (Gdv : gsz_lo fs g' / 8 <= gsz E g' / 8) by (apply Z.div_le_mono; lia).
    destruct Gg' as (G1 & G2 & G3 & G4 & G5). destruct Gg as (F1 & F2 & F3 & F4 & F5).
    set (x := uE E (fst (fst g'))) in *. set (s' := gsz E g') in *. set (y := uE E (fst (fst g))) in *.
    assert (Hx8 : x = 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); apply Z.mod_divide in G3; [|lia]; destruct G3 as [q Hq];
                                          assert (x mod 8 = 0) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_mod_mult); lia).
    assert (Hs8 : s' = 8 * (s' / 8)) by (pose proof (Z.div_mod s' 8 ltac:(lia)); apply Z.mod_divide in G2; [|lia]; destruct G2 as [q Hq];
                                          assert (s' mod 8 = 0) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_mod_mult); lia).
    assert (Ha8' : uE E a = 8 * (uE E a / 8)) by (pose proof (Z.div_mod (uE E a) 8 ltac:(lia)); lia).
    assert (Hn8' : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
    lia.
  - unfold sep_pband_b in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1, H4. apply Z.ltb_lt in H2, H3.
    pose proof (irange_sound E fs (lsub (lscale 8 (rg_base R)) sp) HF) as Rd. pose proof (irange_sound E fs (rg_base R) HF) as Rb.
    fold (uE E (lsub (lscale 8 (rg_base R)) sp)) in Rd. fold (uE E (rg_base R)) in Rb.
    assert (H8 : uE E (lscale 8 (rg_base R)) = 8 * uE E (rg_base R)).
    { unfold uE. rewrite lscale_mul by (unfold two64; lia). rewrite bv_mul_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small 8) by (unfold two64; lia). rewrite Z.mul_comm. apply Z.mod_small.
      fold (uE E (rg_base R)). pose proof (uE_range E (rg_base R)). unfold two64 in *. lia. }
    rewrite Forall_forall in Hgtop. pose proof (Hgtop g (nth_error_In _ _ Hj)) as Gt.
    assert (Gtp : uE E (fst (fst g)) + gsz E g <= atop_pg (m_vmmaps model))
      by (destruct Gg as (F1 & F2 & F3 & F4 & F5); exact (grant_le_atop_pg _ _ _ F3 F2 Gt)).
    unfold atop_pg in Gtp.
    unfold alloc_top, stack_max_size in Gt, Gtp. rewrite Hsp in Gt, Gtp, Hsphi. fold (uE E sp) in Gt, Gtp, Hsphi. unfold sp_window_hi in Hsphi.
    pose proof (lalign_sound E fs (rg_base R) HF) as [Hal0 Hal]. fold (uE E (rg_base R)) in Hal.
    assert (H512 : (512 | uE E (rg_base R))).
    { apply (Z.divide_trans _ (2 ^ lalign fs (rg_base R))); [|exact Hal].
      replace (2 ^ lalign fs (rg_base R)) with (2 ^ 9 * 2 ^ (lalign fs (rg_base R) - 9)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      exists (2 ^ (lalign fs (rg_base R) - 9)). ring. }
    destruct H512 as [q Hq].
    destruct (small_diff E (lscale 8 (rg_base R)) sp _ _ Rd) as [[Hl He]|[Hl He]].
    + rewrite H8 in He. assert (Hn8' : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
      assert (Ha8' : uE E a = 8 * (uE E a / 8)) by (pose proof (Z.div_mod (uE E a) 8 ltac:(lia)); lia).
      assert (Hpg : 4096 * ((uE E sp - 8 * 1024 * 1024) / 4096) <= 4096 * (q - 0x3fffc0)).
      { apply pg_band; [rewrite Z.mul_comm; apply Z_mod_mult|]. unfold SH_OFF in *. lia. }
      unfold SH_OFF in *. lia.
    + rewrite H8 in Hl, He. pose proof (uE_range E sp). pose proof (uE_range E (rg_base R)). unfold two64 in *. lia.
  - unfold sep_noshadow_b in H. apply Z.leb_le in H. pose proof (irange_sound E fs (laddc (rg_base R) (- SH_HI)) HF) as Rn0.
    pose proof (fact_hi_sound E fs (laddc (rg_base R) (- SH_HI)) _ HF (proj2 Rn0)) as Rn1.
    assert (Rn : 0 <= uE E (laddc (rg_base R) (- SH_HI)) <= fact_hi fs (laddc (rg_base R) (- SH_HI)) (snd (irange fs (laddc (rg_base R) (- SH_HI)))))
      by (split; [apply uE_range | exact Rn1]).
    clear Rn0 Rn1. pose proof (uE_range E (rg_base R)).
    destruct (Z_le_gt_dec SH_HI (uE E (rg_base R))) as [Hge|Hlt]; [unfold SH_LO, SH_HI, SH_OFF in *; lia|].
    assert (Hu : uE E (laddc (rg_base R) (- SH_HI)) = uE E (rg_base R) - SH_HI + two64).
    { unfold uE at 1. rewrite lden_laddc, Z_to_bv_unsigned. fold (uE E (rg_base R)). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64.
      replace (uE E (rg_base R) + - SH_HI) with ((uE E (rg_base R) - SH_HI + two64) + (-1) * two64) by lia.
      rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. unfold SH_HI, two64 in *; lia. }
    rewrite Hu in Rn. unfold SH_LO, SH_HI, SH_OFF, two64 in *. lia.
Qed.
Definition sep_app2_b (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp : lin) (a : lin) (n : Z) (R : region) : bool :=
  (* [comment removed for export] *)
  if cont1 fs gs j R then true
  else if band_few2 fs sp R then true
  else if (if sep_noshadow_b fs (RGz a n RZ TEmpty) then sep_shadow_b fs R else false) then true
  else if sep_grant_acc fs gs j O R then true else sep_band_b fs sp R.
#[using="Type"] Lemma sep_app2_b_eq : forall fs0 gs0 j sp0 a n R, sep_app2_b fs0 gs0 j sp0 a n R =
  ((sep_grant_acc fs0 gs0 j O R || sep_band_b fs0 sp0 R) || (sep_noshadow_b fs0 (RGz a n RZ TEmpty) && sep_shadow_b fs0 R))%bool.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fs0 gs0 j sp0 a n R. unfold sep_app2_b. destruct (cont1 fs0 gs0 j R) eqn:Hc; [rewrite (cont1_sound fs0 gs0 j R Hc); reflexivity|].
  unfold band_few2. destruct (lfew2 (lsub sp0 (rg_base R))).
  - destruct (sep_band_b fs0 sp0 R); [destruct (sep_grant_acc fs0 gs0 j O R); reflexivity|].
    destruct (sep_noshadow_b fs0 (RGz a n RZ TEmpty)), (sep_shadow_b fs0 R), (sep_grant_acc fs0 gs0 j O R); reflexivity.
  - destruct (sep_noshadow_b fs0 (RGz a n RZ TEmpty)), (sep_shadow_b fs0 R), (sep_grant_acc fs0 gs0 j O R), (sep_band_b fs0 sp0 R); reflexivity.
Qed.
#[using="Type"] Lemma sep_app2_b_app : forall fs0 gs0 j sp0 a n R, sep_app2_b fs0 gs0 j sp0 a n R =
  (sep_app_b fs0 gs0 j sp0 R || (sep_noshadow_b fs0 (RGz a n RZ TEmpty) && sep_shadow_b fs0 R))%bool.
Proof. LiaFast.lf_pins LiaFast.u0. intros. rewrite sep_app2_b_eq, sep_app_b_eq. reflexivity. Qed.

#[using="model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi"] Theorem sep_app2_sound : forall j g a n R,
  nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g -> 0 <= n < two64 ->
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  sep_app2_b fs gs j sp a n R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof. LiaFast.lf_pins (fun (model BL HF Hmaps Hpd Hgsh Hgtop Hsp Hsphi : LiaFast.U) => LiaFast.u0).
  intros j g a n R Hj Hjm Hlo Hhi Hn Hrs Hrw H w Hw Hin. rewrite sep_app2_b_app in H. apply orb_prop in H as [H|H].
  - exact (sep_app_sound j g a n R Hj Hjm Hlo Hhi Hrs Hrw H w Hw Hin).
  - apply andb_prop in H as [H1 H2]. unfold sep_shadow_b in H2. apply andb_prop in H2 as [S1 S3]. apply andb_prop in S1 as [S1 S2].
    apply Z.leb_le in S1, S3. apply Z.ltb_lt in S2.
    pose proof (irange_sound E fs (rg_base R) HF) as Rb. pose proof (irange_sound E fs (rg_size R) HF) as Rs.
    pose proof (irange_sound E fs (ladd (rg_base R) (rg_size R)) HF) as Rt. rewrite ladd_u2 in Rt by (unfold uE in *; lia).
    unfold rsz in Rs. fold (rsz E R) in Rs. fold (uE E (rg_base R)) in Rb. fold (rsz E R) in Rt. fold (uE E (rg_base R)) in Rt.
    pose proof (noshadow_sound E fs (RGz a n RZ TEmpty) HF H1 w) as Hns. cbn [rg_base] in Hns. rewrite rsz_RGz in Hns by exact Hn.
    specialize (Hns Hin). unfold in_shadow in Hns. apply andb_false_iff in Hns as [Hx|Hx]; [apply Z.leb_gt in Hx | apply Z.ltb_ge in Hx]; lia.
Qed.
(* [comment removed for export] *)
Hypothesis Hmres : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_reserved (m_vmmaps model)) x = false.

#[using="BL Hmaps Hgsh"] Lemma grant_pts_covered : forall j g a n, nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a ->
  uE E a + n <= uE E (fst (fst g)) + gsz E g -> forall x, uE E a <= x < uE E a + n -> covered (vm_maps (m_vmmaps model)) x = true.
Proof. LiaFast.lf_pins (fun (BL Hmaps Hgsh : LiaFast.U) => LiaFast.u0).
  intros j g a n Hj Hjm Hlo Hhi x Hx. rewrite Hmaps. rewrite Forall_forall in Hgsh. pose proof (Hgsh g (nth_error_In _ _ Hj)) as Gg.
  unfold covered. apply existsb_exists. exists (gden E g). split; [exact (lden_maps_in E BL gs g (nth_error_In _ _ Hj) Hjm)|].
  unfold in_iv, in_rng. rewrite gden_uB, gden_uS by exact Gg. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

#[using="BL Hmaps Hgsh Hmres"] Theorem sep_res_sound : forall j g a n R,
  nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  sep_res_b (vm_reserved (m_vmmaps model)) R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof. LiaFast.lf_pins (fun (BL Hmaps Hgsh Hmres : LiaFast.U) => LiaFast.u0).
  intros j g a n R Hj Hjm Hlo Hhi H w Hw Hin. unfold sep_res_b in H.
  destruct (is_const (rg_base R)) as [b|] eqn:Hb; [|discriminate]. destruct (is_const (rg_size R)) as [s0|] eqn:Hs; [|discriminate].
  apply andb_prop in H as [_ H]. destruct (is_const_sound E _ b Hb) as [Hbv Hbr]. destruct (is_const_sound E _ s0 Hs) as [Hsv Hsr].
  assert (HbE : uE E (rg_base R) = b) by (unfold uE; rewrite Hbv; apply fg64'; exact Hbr).
  assert (HsE : rsz E R = s0) by (unfold rsz; rewrite Hsv; apply fg64'; exact Hsr).
  rewrite HbE, HsE in Hw. pose proof (in_res_sound _ _ _ w H Hw) as Hc.
  rewrite (Hmres w (grant_pts_covered j g a n Hj Hjm Hlo Hhi w Hin)) in Hc. discriminate.
Qed.

#[using="BL Hmaps Hgsh Hmres"] Theorem sep_pres_sound : forall j g a n R,
  nth_error gs j = Some g -> is_mark g = false -> uE E (fst (fst g)) <= uE E a -> uE E a + n <= uE E (fst (fst g)) + gsz E g ->
  uE E a mod 8 = 0 -> n mod 8 = 0 ->
  sep_pres_b (vm_reserved (m_vmmaps model)) R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a / 8 + SH_OFF <= w < uE E a / 8 + SH_OFF + n / 8).
Proof. LiaFast.lf_pins (fun (BL Hmaps Hgsh Hmres : LiaFast.U) => LiaFast.u0).
  intros j g a n R Hj Hjm Hlo Hhi Ha8 Hn8 H w Hw Hin. unfold sep_pres_b in H.
  destruct (is_const (rg_base R)) as [b|] eqn:Hb; [|discriminate]. destruct (is_const (rg_size R)) as [s0|] eqn:Hs; [|discriminate].
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [_ Hb0]. apply Z.leb_le in Hb0.
  destruct (is_const_sound E _ b Hb) as [Hbv Hbr]. destruct (is_const_sound E _ s0 Hs) as [Hsv Hsr].
  assert (HbE : uE E (rg_base R) = b) by (unfold uE; rewrite Hbv; apply fg64'; exact Hbr).
  assert (HsE : rsz E R = s0) by (unfold rsz; rewrite Hsv; apply fg64'; exact Hsr).
  rewrite HbE, HsE in Hw. set (x := 8 * (w - SH_OFF)).
  assert (Ha8' : uE E a = 8 * (uE E a / 8)) by (pose proof (Z.div_mod (uE E a) 8 ltac:(lia)); lia).
  assert (Hn8' : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
  pose proof (in_res_sound _ _ _ x Hr ltac:(unfold x; lia)) as Hc.
  rewrite (Hmres x (grant_pts_covered j g a n Hj Hjm Hlo Hhi x ltac:(unfold x; lia))) in Hc. discriminate.
Qed.
(* [comment removed for export] *)
Definition range_band_b (fs : list fact) (sp a : lin) : bool :=
  let id := irange fs (lsub (lscale 8 a) sp) in
  (Z.leb (8 * SH_OFF - 8388608 - 4095) (fst id) && Z.ltb (snd id) 9223372036854775808 && Z.ltb (snd (irange fs a)) 1152921504606846976 &&
   Z.leb 9 (lalign fs a))%bool.
Definition sep_rb_b (fs : list fact) (gs : list (lin * lin * gkind)) (j : nat) (sp a : lin) (R : region) : bool :=
  (range_band_b fs sp a && sep_pgrant_acc fs gs j O R)%bool.

#[using="model HF Hgsh Hgtop Hsp Hsphi"] Theorem sep_rb_sound : forall j a n R,
  0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 -> sep_rb_b fs gs j sp a R = true ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (uE E a <= w < uE E a + n).
Proof. LiaFast.lf_pins (fun (model HF Hgsh Hgtop Hsp Hsphi : LiaFast.U) => LiaFast.u0).
  intros j a n R Hrs Hrw H w Hw Hin. unfold sep_rb_b in H. apply andb_prop in H as [Hb Hg].
  unfold range_band_b in Hb. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H4. apply Z.ltb_lt in H2, H3.
  pose proof (irange_sound E fs (lsub (lscale 8 a) sp) HF) as Rd. pose proof (irange_sound E fs a HF) as Ra.
  fold (uE E (lsub (lscale 8 a) sp)) in Rd. fold (uE E a) in Ra.
  assert (H8 : uE E (lscale 8 a) = 8 * uE E a).
  { unfold uE. rewrite lscale_mul by (unfold two64; lia). rewrite bv_mul_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. rewrite (Z.mod_small 8) by (unfold two64; lia). rewrite Z.mul_comm. apply Z.mod_small.
    fold (uE E a). pose proof (uE_range E a). unfold two64 in *. lia. }
  pose proof Hsphi as Hsphi'. rewrite Hsp in Hsphi'. fold (uE E sp) in Hsphi'. unfold sp_window_hi in Hsphi'.
  destruct (small_diff E (lscale 8 a) sp _ _ Rd) as [[Hl He]|[Hl He]]; [|rewrite H8 in Hl, He; pose proof (uE_range E sp); pose proof (uE_range E a); unfold two64 in *; lia].
  rewrite H8 in He.
  (* [comment removed for export] *)
  destruct (sep_pgrant_acc_spec fs gs j O R Hg) as (i' & g' & pb & _ & _ & Hn' & Hsl & Hs1 & Hc & _). rewrite Nat.sub_0_r in Hn'.
  rewrite Forall_forall in Hgsh, Hgtop. pose proof (Hgsh g' (nth_error_In _ _ Hn')) as Gg'. pose proof (Hgtop g' (nth_error_In _ _ Hn')) as Gt.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. unfold rsz in Rs. fold (rsz E R) in Rs.
  pose proof (srl_lin_sound E fs 3 (fst (fst g')) pb HF ltac:(lia) Hsl) as Hpbv. rewrite Z.shiftr_div_pow2 in Hpbv by lia.
  change (2 ^ 3) with 8 in Hpbv. fold (uE E pb) in Hpbv. fold (uE E (fst (fst g'))) in Hpbv.
  assert (HbP : uE E (laddc pb SH_OFF) = uE E (fst (fst g')) / 8 + SH_OFF).
  { unfold uE at 1. rewrite lden_laddc, Z_to_bv_unsigned. fold (uE E pb). rewrite Hpbv.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small.
    pose proof (uE_range E (fst (fst g'))). assert (uE E (fst (fst g')) / 8 <= uE E (fst (fst g'))) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= uE E (fst (fst g')) / 8) by (apply Z.div_pos; lia). unfold SH_OFF, two64 in *. lia. }
  destruct Gg' as (G1 & G2 & G3 & G4 & G5).
  destruct (contained_sound E fs (rg_base R) _ (laddc pb SH_OFF) (gsz_lo fs g' / 8) HF Hc ltac:(lia)) as [C1 C2].
  { rewrite HbP. pose proof (gsz_bounds E fs g' HF) as Gb. pose proof (gsz_lo_nonneg fs g'). assert (gsz_lo fs g' / 8 <= gsz_lo fs g') by (apply Z.div_le_upper_bound; lia).
    assert (uE E (fst (fst g')) / 8 <= uE E (fst (fst g'))) by (apply Z.div_le_upper_bound; pose proof (uE_range E (fst (fst g'))); lia).
    unfold SH_OFF, two64. lia. }
  rewrite HbP in C1, C2.
  pose proof (gsz_bounds E fs g' HF) as Gb. assert (Gdv : gsz_lo fs g' / 8 <= gsz E g' / 8) by (apply Z.div_le_mono; lia).
  assert (Gtp : uE E (fst (fst g')) + gsz E g' <= atop_pg (m_vmmaps model)) by exact (grant_le_atop_pg _ _ _ G3 G2 Gt).
  unfold atop_pg, alloc_top, stack_max_size in Gtp. rewrite Hsp in Gtp. fold (uE E sp) in Gtp.
  pose proof (lalign_sound E fs a HF) as [Hal0 Hal]. fold (uE E a) in Hal.
  assert (H512 : (512 | uE E a)).
  { apply (Z.divide_trans _ (2 ^ lalign fs a)); [|exact Hal].
    replace (2 ^ lalign fs a) with (2 ^ 9 * 2 ^ (lalign fs a - 9)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    exists (2 ^ (lalign fs a - 9)). ring. }
  destruct H512 as [q Hq].
  assert (Hpg : 4096 * ((uE E sp - 8 * 1024 * 1024) / 4096) <= 4096 * (q - 0x3fffc0)).
  { apply pg_band; [rewrite Z.mul_comm; apply Z_mod_mult|]. unfold SH_OFF in *. lia. }
  assert (Hdv : (uE E (fst (fst g')) + gsz E g') / 8 <= 512 * (q - 0x3fffc0)) by (apply Z.div_le_upper_bound; lia).
  assert (Hsum : uE E (fst (fst g')) / 8 + gsz E g' / 8 <= (uE E (fst (fst g')) + gsz E g') / 8).
  { pose proof (Z.div_mod (uE E (fst (fst g'))) 8 ltac:(lia)). pose proof (Z.div_mod (gsz E g') 8 ltac:(lia)).
    pose proof (Z.div_mod (uE E (fst (fst g')) + gsz E g') 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (uE E (fst (fst g'))) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (gsz E g') 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (uE E (fst (fst g')) + gsz E g') 8 ltac:(lia)). lia. }
  unfold SH_OFF in *. lia.
Qed.
End Sep.

(* [comment removed for export] *)
Definition zero_ov2 (fs : list fact) (a : lin) (n : Z) (R : region) : bool :=
  match rg_kind R with
  | RZ => let '(lo, hi) := irange fs (lsub a (rg_base R)) in
          (Z.leb 0 lo && Z.ltb hi 4611686018427387904 && range_zero (rg_cont R) lo (hi + n))%bool
  | _ => false
  end.

Lemma zero_ov2_sound : forall E fs a n R, Forall (fact_ok E) fs -> zero_ov2 fs a n R = true -> 0 <= n < 4611686018427387904 ->
  uE E (rg_base R) + rsz E R <= two64 ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> uE E a <= w < uE E a + n ->
  rg_kind R = RZ /\ (tget (okey (w - uE E (rg_base R))) (rg_cont R) = None \/ tget (okey (w - uE E (rg_base R))) (rg_cont R) = Some (BK 0)).
Proof.
  intros E fs a n R HF H Hn HRw w Hw Hin. unfold zero_ov2 in H. destruct (rg_kind R) eqn:Hk; try discriminate. split; [reflexivity|].
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hr. destruct (irange fs (lsub a (rg_base R))) as [lo hi] eqn:Hir.
  cbn [fst snd] in Hr. apply andb_prop in H as [H Hz]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  fold (uE E (lsub a (rg_base R))) in Hr. pose proof (uE_range E a). pose proof (uE_range E (rg_base R)).
  destruct (small_diff E a (rg_base R) lo hi Hr) as [[Hl He]|[Hl He]]; [|unfold two64 in *; lia].
  destruct (tget (okey (w - uE E (rg_base R))) (rg_cont R)) as [v|] eqn:Ht; [right|left; reflexivity].
  rewrite (range_zero_spec _ lo (hi + n) _ v Hz Ht ltac:(rewrite okey_pos by lia; lia)). reflexivity.
Qed.
