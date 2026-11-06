(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChEnt FxChEntM FxChSubst FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxDirConv.

Module FxVConst.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChEnt FxChEntM FxChSubst FxChMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition vc_sig (v : positive) (c : Z) : tree lin := tset v (lconst c) TEmpty.
Definition vconst_post (S : sst) (M : smodel) (v : positive) : option sst :=
  let '(lo, hi) := irange (s_facts S) (lvar v) in
  let σ := vc_sig v lo in
  if (Z.eqb lo hi && Z.leb 0 lo && Z.ltb lo two64 && Pos.ltb v (s_next S) && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool
  then Some (ssubst σ (s_next S) S) else None.

Lemma svar_vc_same : forall v c, svar (vc_sig v c) v = lconst c.
Proof. intros. unfold svar, vc_sig. rewrite tget_tset_same. reflexivity. Qed.
Lemma svar_vc_other : forall v c x, x <> v -> svar (vc_sig v c) x = lvar x.
Proof. intros v c x Hx. unfold svar, vc_sig. rewrite tget_tset_other by congruence. rewrite tget_empty. reflexivity. Qed.

Section VC.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_vconst : forall S M v S' E ms model, vconst_post S M v = Some S' ->
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M v S' E ms model Hp Hd. unfold vconst_post in Hp.
  destruct (irange (s_facts S) (lvar v)) as [lo hi] eqn:Hir.
  set (σ := vc_sig v lo) in *.
  destruct (Z.eqb lo hi && Z.leb 0 lo && Z.ltb lo two64 && Pos.ltb v (s_next S) && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool eqn:Hb; [|discriminate].
  injection Hp as <-.
  apply andb_prop in Hb as [Hb Hmk]. apply andb_prop in Hb as [Hb Hsm]. apply andb_prop in Hb as [Hb Hv]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [Heq Hle].
  apply Z.eqb_eq in Heq. apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt. apply Pos.ltb_lt in Hv. apply sm_eqb_eq in Hsm.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) (lvar v) HF) as Rv. rewrite Hir, lden_lvar in Rv. cbn [fst snd] in Rv.
  assert (Hu : bv_unsigned (E v) = lo) by lia.
  assert (Hag : agree (s_next S) E (ecomp E σ)).
  { intros x Hx. unfold ecomp. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vc_same, lden_lconst. apply bv_eq. rewrite Hu, u_Z_to_bv. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. symmetry. apply Z.mod_small. lia.
    - unfold σ. rewrite svar_vc_other by exact Hne. rewrite lden_lvar. reflexivity. }
  assert (Hsig : sig_wf σ (s_next S) (s_next S)).
  { intros x Hx. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vc_same. reflexivity.
    - unfold σ. rewrite svar_vc_other by exact Hne. apply lwf_lvar. exact Hx. }
  pose proof (den_agree segs LIMIT model0 mem0 E (ecomp E σ) S M ms model Hd Hag) as Hd2.
  pose proof (den_subst segs LIMIT model0 mem0 E σ S M (s_next S) ms model Hsig Hmk Hd2) as Hd3. rewrite Hsm in Hd3. exact Hd3.
Qed.
End VC.
(* [comment removed for export] *)
End FxVConst.

Module FxVLin.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChEnt FxChEntM FxChSubst FxChMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition vl_sig (v : positive) (l : lin) : tree lin := tset v l TEmpty.
Definition eq_fact (g : lin) (f : fact) : bool := match f with FRange g' lo hi => (lin_eqb g' g && Z.eqb lo 0 && Z.eqb hi 0)%bool | _ => false end.
Definition no_var (v : positive) (l : lin) : bool := forallb (fun p => negb (Pos.eqb (fst p) v)) (l_t l).
Definition vlin_post (S : sst) (M : smodel) (v : positive) (l : lin) (k : Z) : option sst :=
  let fs := s_facts S in let σ := vl_sig v l in
  if (Z.leb 1 k && Z.leb k 4096 && existsb (eq_fact (lscale k (lsub l (lvar v)))) fs && no_var v l && lwf (s_next S) l && Pos.ltb v (s_next S) &&
      Z.ltb (snd (irange fs l)) (2 ^ 50) && Z.ltb (snd (irange fs (lvar v))) (2 ^ 50) && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool
  then Some (ssubst σ (s_next S) S) else None.

Lemma svar_vl_same : forall v l, svar (vl_sig v l) v = l.
Proof. intros. unfold svar, vl_sig. rewrite tget_tset_same. reflexivity. Qed.
Lemma svar_vl_other : forall v l x, x <> v -> svar (vl_sig v l) x = lvar x.
Proof. intros v l x Hx. unfold svar, vl_sig. rewrite tget_tset_other by congruence. rewrite tget_empty. reflexivity. Qed.

Section VL.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_vlin : forall S M v l k S' E ms model, vlin_post S M v l k = Some S' ->
  DEN segs LIMIT model0 mem0 E S M ms model -> DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M v l k S' E ms model Hp Hd. unfold vlin_post in Hp. cbv zeta in Hp.
  set (σ := vl_sig v l) in *. set (fs := s_facts S) in *.
  match type of Hp with ((if ?c then _ else _) = _) => destruct c eqn:Hb; [|discriminate] end. injection Hp as <-.
  repeat match type of Hb with ((_ && _)%bool = true) => apply andb_prop in Hb as [Hb ?Hc] end.
  apply Z.leb_le in Hb, Hc7. apply existsb_exists in Hc6 as (f & Hfin & Hef). apply Pos.ltb_lt in Hc3. apply Z.ltb_lt in Hc2, Hc1. apply sm_eqb_eq in Hc0.
  rename Hc into Hmk. rename Hc0 into Hsm. rename Hc5 into Hnv. rename Hc4 into Hwl.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _). fold fs in HF.
  (* [comment removed for export] *)
  destruct f as [? ? ? ?|g lo hi|? ? ?|? ? ?|? ? ?|? ?]; try discriminate. unfold eq_fact in Hef.
  apply andb_prop in Hef as [Hef Hhi0]. apply andb_prop in Hef as [Hg Hlo0]. apply lin_eqb_eq in Hg. apply Z.eqb_eq in Hlo0, Hhi0. subst g lo hi.
  rewrite Forall_forall in HF. pose proof (HF _ Hfin) as Hfk. cbn [fact_ok] in Hfk.
  pose proof (irange_sound E fs l (proj2 (Forall_forall _ _) HF)) as Rl. fold (uE E l) in Rl.
  pose proof (irange_sound E fs (lvar v) (proj2 (Forall_forall _ _) HF)) as Rv. fold (uE E (lvar v)) in Rv.
  pose proof (uE_range E l) as RL. pose proof (uE_range E (lvar v)) as RV.
  set (A := uE E l) in *. set (B := uE E (lvar v)) in *.
  assert (Hz : bv_unsigned (lden E (lscale k (lsub l (lvar v)))) = 0) by lia.
  rewrite lden_lscale in Hz. fold (uE E (lsub l (lvar v))) in Hz. rewrite u_lsub_mod in Hz. fold A B in Hz.
  rewrite u_Z_to_bv in Hz. unfold bv_wrap, bv_modulus in Hz. change (2 ^ Z.of_N 64) with two64 in Hz.
  assert (HAB : A = B).
  { destruct (Z_le_gt_dec B A) as [Hle|Hgt].
    - rewrite (Z.mod_small (A - B)) in Hz by (unfold two64 in *; lia). rewrite Z.mod_small in Hz by (unfold two64 in *; nia). nia.
    - exfalso. assert (E1 : (A - B) mod two64 = A - B + two64) by (symmetry; apply (Z.mod_unique _ _ (-1)); unfold two64 in *; lia).
      rewrite E1 in Hz. assert (E2 : (k * (A - B + two64)) mod two64 = (k * (A - B)) mod two64).
      { replace (k * (A - B + two64)) with (k * (A - B) + k * two64) by lia. apply Z.mod_add. unfold two64. lia. }
      rewrite E2 in Hz. assert (E3 : (k * (A - B)) mod two64 = k * (A - B) + two64) by (symmetry; apply (Z.mod_unique _ _ (-1)); unfold two64 in *; nia).
      rewrite E3 in Hz. unfold two64 in *. nia. }
  assert (Hag : agree (s_next S) E (ecomp E σ)).
  { intros x Hx. unfold ecomp. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vl_same. apply bv_eq. fold (uE E l). fold A. rewrite HAB. unfold B, uE. rewrite lden_lvar. reflexivity.
    - unfold σ. rewrite svar_vl_other by exact Hne. rewrite lden_lvar. reflexivity. }
  assert (Hsig : sig_wf σ (s_next S) (s_next S)).
  { intros x Hx. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_vl_same. exact Hwl.
    - unfold σ. rewrite svar_vl_other by exact Hne. apply lwf_lvar. exact Hx. }
  pose proof (den_agree segs LIMIT model0 mem0 E (ecomp E σ) S M ms model Hd Hag) as Hd2.
  pose proof (den_subst segs LIMIT model0 mem0 E σ S M (s_next S) ms model Hsig Hmk Hd2) as Hd3. rewrite Hsm in Hd3. exact Hd3.
Qed.
End VL.
(* [comment removed for export] *)
End FxVLin.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition dec_sig (v q r : positive) (k : Z) : tree lin := tset v (ladd (lscale (2 ^ k) (lvar q)) (lvar r)) TEmpty.
Definition dec_post (S : sst) (M : smodel) (v : positive) (k : Z) : option sst :=
  let q := s_next S in let r := Pos.succ q in let n := Pos.succ r in
  let σ := dec_sig v q r k in
  if (Pos.ltb v q && Z.ltb 0 k && Z.ltb k 64 && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool then
    Some (add_facts (ssubst σ n S) [FRange (lvar r) 0 (2 ^ k - 1); FRange (lvar q) (fst (irange (s_facts S) (lvar v)) / 2 ^ k) (snd (irange (s_facts S) (lvar v)) / 2 ^ k)])
  else None.

Lemma svar_dec_same : forall v q r k, svar (dec_sig v q r k) v = ladd (lscale (2 ^ k) (lvar q)) (lvar r).
Proof. intros. unfold svar, dec_sig. rewrite tget_tset_same. reflexivity. Qed.
Lemma svar_dec_other : forall v q r k x, x <> v -> svar (dec_sig v q r k) x = lvar x.
Proof. intros v q r k x Hx. unfold svar, dec_sig. rewrite tget_tset_other by congruence. rewrite tget_empty. reflexivity. Qed.

Section Dec.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_dec : forall S M v k S', dec_post S M v k = Some S' ->
  forall E ms model T, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' S' M ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M v k S' Hp E ms model T Hd Hk. unfold dec_post in Hp.
  set (q := s_next S) in *. set (r := Pos.succ q) in *. set (n := Pos.succ r) in *. set (σ := dec_sig v q r k) in *.
  destruct (Pos.ltb v q && Z.ltb 0 k && Z.ltb k 64 && sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool eqn:Hb; [|discriminate]. injection Hp as <-.
  apply andb_prop in Hb as [Hb Hmk]. apply andb_prop in Hb as [Hb Hsm]. apply andb_prop in Hb as [Hb Hk2]. apply andb_prop in Hb as [Hv Hk1].
  apply Pos.ltb_lt in Hv. apply Z.ltb_lt in Hk1. apply Z.ltb_lt in Hk2. apply sm_eqb_eq in Hsm.
  set (u := bv_unsigned (E v)).
  pose proof (bv_unsigned_in_range _ (E v)) as Ru. fold u in Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 64) with two64 in Ru.
  assert (Hpow : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hmod : 0 <= u mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
  assert (Hdiv : 0 <= u / 2 ^ k <= u) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  assert (Hdm : u = 2 ^ k * (u / 2 ^ k) + u mod 2 ^ k) by (apply Z.div_mod; lia).
  assert (Hpk : 2 ^ k <= two64) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
  set (E2 := upd (upd E q (Z_to_bv 64 (u / 2 ^ k))) r (Z_to_bv 64 (u mod 2 ^ k))).
  assert (Hq : E2 q = Z_to_bv 64 (u / 2 ^ k)).
  { unfold E2, upd. replace (Pos.eqb q r) with false by (symmetry; apply Pos.eqb_neq; unfold r; lia). rewrite Pos.eqb_refl. reflexivity. }
  assert (Hr : E2 r = Z_to_bv 64 (u mod 2 ^ k)) by (unfold E2, upd; rewrite Pos.eqb_refl; reflexivity).
  assert (Hag : agree q E E2).
  { intros x Hx. unfold E2, upd.
    replace (Pos.eqb x r) with false by (symmetry; apply Pos.eqb_neq; unfold r; lia).
    replace (Pos.eqb x q) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (Uq : bv_unsigned (E2 q) = u / 2 ^ k) by (rewrite Hq, u_Z_to_bv; apply Z.mod_small; lia).
  assert (Ur : bv_unsigned (E2 r) = u mod 2 ^ k) by (rewrite Hr, u_Z_to_bv; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  assert (Hv2 : lden E2 (svar σ v) = E v).
  { unfold σ. rewrite svar_dec_same, lden_ladd, lden_lscale, !lden_lvar, Uq.
    apply bv_eq. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite u_Z_to_bv, Ur. fold u.
    rewrite Zplus_mod_idemp_l. rewrite <- Hdm. apply Z.mod_small. lia. }
  assert (Hag2 : agree q E (ecomp E2 σ)).
  { intros x Hx. unfold ecomp. destruct (Pos.eq_dec x v) as [->|Hne]; [symmetry; exact Hv2|].
    unfold σ. rewrite svar_dec_other by exact Hne. rewrite lden_lvar. exact (Hag x Hx). }
  assert (Hsig : sig_wf σ q n).
  { intros x Hx. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_dec_same. apply lwf_ladd; [apply lwf_lscale|]; apply lwf_lvar; unfold n, r; lia.
    - unfold σ. rewrite svar_dec_other by exact Hne. apply lwf_lvar. unfold n, r. lia. }
  pose proof (den_agree segs LIMIT model0 mem0 E (ecomp E2 σ) S M ms model Hd Hag2) as Hd2.
  pose proof (den_subst segs LIMIT model0 mem0 E2 σ S M n ms model Hsig Hmk Hd2) as Hd3. rewrite Hsm in Hd3.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) (lvar v) HF) as Rv. rewrite lden_lvar in Rv. fold u in Rv.
  apply (Hk E2 ms model Hag).
  refine (den_add_facts segs LIMIT model0 mem0 [FRange (lvar r) 0 (2 ^ k - 1); FRange (lvar q) (fst (irange (s_facts S) (lvar v)) / 2 ^ k) (snd (irange (s_facts S) (lvar v)) / 2 ^ k)]
            E2 (ssubst σ n S) M ms model Hd3 _).
  assert (Hnx : s_next (ssubst σ n S) = n) by reflexivity.
  constructor; [split; [cbn [fwf]; apply lwf_lvar; rewrite Hnx; unfold n; lia | cbn [fact_ok]; rewrite lden_lvar, Ur; lia]|].
  constructor; [split; [cbn [fwf]; apply lwf_lvar; rewrite Hnx; unfold n, r; lia
                       | cbn [fact_ok]; rewrite lden_lvar, Uq; split; apply Z.div_le_mono; lia]|].
  constructor.
Qed.
End Dec.
(* [comment removed for export] *)
