(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChEnt FxChEntM FxChSubst FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxDirConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition decn_form (c : Z) (q r : positive) (k : Z) : lin := lsub (lconst c) (ladd (lscale (2 ^ k) (lvar q)) (lvar r)).
Definition decn_sig (v q r : positive) (c k : Z) : tree lin := tset v (decn_form c q r k) TEmpty.
Definition decn_post (S : sst) (M : smodel) (v : positive) (c k : Z) : option sst :=
  let q := s_next S in let r := Pos.succ q in let n := Pos.succ r in
  let σ := decn_sig v q r c k in
  let rv := irange (s_facts S) (lvar v) in
  if (Pos.ltb v q && Z.ltb 0 k && Z.ltb k 64 && Z.leb 0 (fst rv) && Z.leb (snd rv) c && Z.ltb c two64 &&
      sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool then
    Some (add_facts (ssubst σ n S) [FRange (lvar r) 0 (2 ^ k - 1); FRange (lvar q) ((c - snd rv) / 2 ^ k) ((c - fst rv) / 2 ^ k)])
  else None.

Lemma svar_decn_same : forall v q r c k, svar (decn_sig v q r c k) v = decn_form c q r k.
Proof. intros. unfold svar, decn_sig. rewrite tget_tset_same. reflexivity. Qed.
Lemma svar_decn_other : forall v q r c k x, x <> v -> svar (decn_sig v q r c k) x = lvar x.
Proof. intros v q r c k x Hx. unfold svar, decn_sig. rewrite tget_tset_other by congruence. rewrite tget_empty. reflexivity. Qed.

Section DecN.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_decn : forall S M v c k S', decn_post S M v c k = Some S' ->
  forall E ms model T, DEN segs LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' S' M ms' model' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M v c k S' Hp E ms model T Hd Hk. unfold decn_post in Hp.
  set (q := s_next S) in *. set (r := Pos.succ q) in *. set (n := Pos.succ r) in *. set (σ := decn_sig v q r c k) in *.
  set (rv := irange (s_facts S) (lvar v)) in *.
  destruct (Pos.ltb v q && Z.ltb 0 k && Z.ltb k 64 && Z.leb 0 (fst rv) && Z.leb (snd rv) c && Z.ltb c two64 &&
            sm_eqb (msubst σ M) M && marks_ok σ (sm_maps M))%bool eqn:Hb; [|discriminate]. injection Hp as <-.
  apply andb_prop in Hb as [Hb Hmk]. apply andb_prop in Hb as [Hb Hsm]. apply andb_prop in Hb as [Hb Hc2]. apply andb_prop in Hb as [Hb Hhi].
  apply andb_prop in Hb as [Hb Hlo]. apply andb_prop in Hb as [Hb Hk2]. apply andb_prop in Hb as [Hv Hk1].
  apply Pos.ltb_lt in Hv. apply Z.ltb_lt in Hk1. apply Z.ltb_lt in Hk2. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.ltb_lt in Hc2.
  apply sm_eqb_eq in Hsm.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) (lvar v) HF) as Rv. rewrite lden_lvar in Rv. fold rv in Rv.
  set (u := bv_unsigned (E v)) in *.
  set (w := c - u).
  assert (Rw : 0 <= w <= c) by (unfold w; lia).
  assert (Hpow : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hmod : 0 <= w mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
  assert (Hdiv : 0 <= w / 2 ^ k <= w) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  assert (Hdm : w = 2 ^ k * (w / 2 ^ k) + w mod 2 ^ k) by (apply Z.div_mod; lia).
  assert (Hpk : 2 ^ k <= two64) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
  set (E2 := upd (upd E q (Z_to_bv 64 (w / 2 ^ k))) r (Z_to_bv 64 (w mod 2 ^ k))).
  assert (Hq : E2 q = Z_to_bv 64 (w / 2 ^ k)).
  { unfold E2, upd. replace (Pos.eqb q r) with false by (symmetry; apply Pos.eqb_neq; unfold r; lia). rewrite Pos.eqb_refl. reflexivity. }
  assert (Hr : E2 r = Z_to_bv 64 (w mod 2 ^ k)) by (unfold E2, upd; rewrite Pos.eqb_refl; reflexivity).
  assert (Hag : agree q E E2).
  { intros x Hx. unfold E2, upd.
    replace (Pos.eqb x r) with false by (symmetry; apply Pos.eqb_neq; unfold r; lia).
    replace (Pos.eqb x q) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (Uq : bv_unsigned (E2 q) = w / 2 ^ k) by (rewrite Hq, u_Z_to_bv; apply Z.mod_small; lia).
  assert (Ur : bv_unsigned (E2 r) = w mod 2 ^ k) by (rewrite Hr, u_Z_to_bv; apply Z.mod_small; lia).
  assert (Hv2 : lden E2 (svar σ v) = E v).
  { unfold σ. rewrite svar_decn_same. unfold decn_form. apply bv_eq.
    rewrite lden_lsub, bv_sub_unsigned, lden_lconst, u_Z_to_bv, lden_ladd, bv_add_unsigned, lden_lscale, !lden_lvar, Uq, Ur, u_Z_to_bv.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite Zplus_mod_idemp_l, <- Hdm. rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l.
    replace (c - w) with u by (unfold w; lia). apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ (E v)) as Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 64) with two64 in Ru. exact Ru. }
  assert (Hag2 : agree q E (ecomp E2 σ)).
  { intros x Hx. unfold ecomp. destruct (Pos.eq_dec x v) as [->|Hne]; [symmetry; exact Hv2|].
    unfold σ. rewrite svar_decn_other by exact Hne. rewrite lden_lvar. exact (Hag x Hx). }
  assert (Hsig : sig_wf σ q n).
  { intros x Hx. destruct (Pos.eq_dec x v) as [->|Hne].
    - unfold σ. rewrite svar_decn_same. unfold decn_form. apply lwf_lsub; [apply lwf_lconst|].
      apply lwf_ladd; [apply lwf_lscale|]; apply lwf_lvar; unfold n, r; lia.
    - unfold σ. rewrite svar_decn_other by exact Hne. apply lwf_lvar. unfold n, r. lia. }
  pose proof (den_agree segs LIMIT model0 mem0 E (ecomp E2 σ) S M ms model Hd Hag2) as Hd2.
  pose proof (den_subst segs LIMIT model0 mem0 E2 σ S M n ms model Hsig Hmk Hd2) as Hd3. rewrite Hsm in Hd3.
  apply (Hk E2 ms model Hag).
  refine (den_add_facts segs LIMIT model0 mem0 [FRange (lvar r) 0 (2 ^ k - 1); FRange (lvar q) ((c - snd rv) / 2 ^ k) ((c - fst rv) / 2 ^ k)]
            E2 (ssubst σ n S) M ms model Hd3 _).
  assert (Hnx : s_next (ssubst σ n S) = n) by reflexivity.
  constructor; [split; [cbn [fwf]; apply lwf_lvar; rewrite Hnx; unfold n; lia | cbn [fact_ok]; rewrite lden_lvar, Ur; lia]|].
  constructor; [split; [cbn [fwf]; apply lwf_lvar; rewrite Hnx; unfold n, r; lia
                       | cbn [fact_ok]; rewrite lden_lvar, Uq; split; apply Z.div_le_mono; unfold w; lia]|].
  constructor.
Qed.
End DecN.
(* [comment removed for export] *)
