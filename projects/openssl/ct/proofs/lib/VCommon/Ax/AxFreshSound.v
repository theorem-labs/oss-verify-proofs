(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxState AxStep AxEntryRel AxSys AxOcc AxFresh AxJoin AxJoinSound AxRun.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Section Fresh.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable MR : valuation -> amodel -> Model -> Prop.
Hypothesis MR_agree : forall v ρ ρ' am m, (forall x, x <> v -> ρ' x = ρ x) -> model_occ v am = false -> MR ρ am m -> MR ρ' am m.
Hypothesis MR_nx : forall ρ am m nx, MR ρ am m -> MR ρ (set_next am nx) m.
Variable KT : valuation -> list byte -> TSet.
Hypothesis KT_agree : forall ρ ρ' o, (forall x, entry_var x = true -> ρ' x = ρ x) -> KT ρ' o = KT ρ o.

Notation RR ρ := (R segs amodel (MR ρ) LIM ρ).
Notation Snd := (Sound segs cfg LIM MR KT).

Lemma sat_fresh_store (ρ : valuation) (s : store) (v : int) (h : lin) (k : Z) :
  sat ρ s -> 0 <= k -> ρ v = leval ρ h / 2 ^ k -> ts_occ v (snd h) = false -> sat ρ (fresh_store s v h k).
Proof.
  intros Hs Hk Hv Ho. unfold fresh_store. set (k2 := 2 ^ k). assert (Hk2 : 0 < k2) by (apply Z.pow_pos_nonneg; lia).
  assert (H1 : sat ρ (ST (st_box s) (Fact (fst h, tadd (snd h) [(v, - k2)]) 0 (k2 - 1) false :: st_facts s))).
  { destruct Hs as [Hb Hf]. split; [exact Hb|]. constructor; [|exact Hf].
    unfold fact_sat, leval. cbn [fc_hole fc_f fc_lo fc_hi fst snd]. rewrite teval_tadd. cbn [teval]. rewrite Hv. fold k2.
    unfold leval. pose proof (Z.div_mod (fst h + teval ρ (snd h)) k2 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (fst h + teval ρ (snd h)) k2 Hk2) as Hm. lia. }
  destruct (lrange s h) as [[lo hi]|] eqn:El; [|exact H1].
  pose proof (lrange_sound ρ s h Hs _ El) as Hr. cbn [fst snd] in Hr.
  apply sat_sadd; [exact H1|]. rewrite leval_lvar, Z.mul_1_l, Hv. fold k2. split; apply Z.div_le_mono; lia.
Qed.

Theorem fresh_sound (A : astate amodel) (v : int) (h : lin) (k : Z) :
  fresh_ok A v h k = true -> Snd (fresh_child A v h k) -> Snd A.
Proof.
  intros Hok HS ρ c HR o Ho. unfold fresh_ok in Hok.
  apply land_true in Hok as [Hok Hk64]. apply land_true in Hok as [Hok Hk]. apply land_true in Hok as [Ho1 Ho2].
  apply negb_true_iff in Ho1. apply negb_true_iff in Ho2. apply Z.leb_le in Hk.
  set (ρ' := upd_val ρ v (leval ρ h / 2 ^ k)).
  pose proof (upd_val_agree ρ v (leval ρ h / 2 ^ k)) as Hag. fold ρ' in Hag.
  pose proof (R_agree segs LIM MR MR_agree v ρ ρ' A c Hag Ho1 HR) as HR'.
  assert (Eh : leval ρ' h = leval ρ h) by (apply (leval_agree v); assumption).
  assert (HR2 : RR ρ' (fresh_child A v h k) c).
  { destruct HR' as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna].
    constructor; cbn [fresh_child a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
    apply sat_fresh_store; [exact Hsat | exact Hk | | exact Ho2]. rewrite Eh. unfold ρ'. apply upd_val_same. }
  pose proof (HS ρ' c HR2 o (out_agree v ρ ρ' A o Hag Ho1 Ho)) as X.
  rewrite (KT_agree ρ ρ' o (agree_entry v ρ ρ' Hag (occ_entry v A Ho1))) in X. exact X.
Qed.

Theorem bump_sound (A : astate amodel) : Snd (bump_next A) -> Snd A.
Proof.
  intros HS ρ c HR o Ho. apply (HS ρ c); [|exact Ho].
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna].
  constructor; cbn [bump_next a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption. apply MR_nx. exact Hmod.
Qed.

Theorem floor_sound (A B : astate amodel) (r : int) (k : Z) : floor_child A r k = Some B -> Snd B -> Snd A.
Proof.
  unfold floor_child. destruct (floor_form A r k) as [h|]; [|discriminate].
  destruct (fresh_ok A (am_next (a_model A)) h k &&& (am_next (a_model A) <? 65536)%uint63) eqn:E; [|discriminate].
  apply land_true in E as [E _]. intros H HS. injection H as <-.
  apply (fresh_sound A _ h k E). apply bump_sound. exact HS.
Qed.

End Fresh.
