(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxMemC AxState AxStep AxSys AxJoin AxJoinSound AxRun.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Lemma cuts_cover_sound : forall (cuts : list (Z * Z)) (lo hi v : Z), cuts_cover lo hi cuts = true -> lo <= v <= hi ->
  exists c, In c cuts /\ fst c <= v <= snd c.
Proof.
  induction cuts as [|[l h] r IH]; intros lo hi v H Hv; cbn [cuts_cover] in H.
  - apply Z.ltb_lt in H. lia.
  - apply land_true in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (Z_le_gt_dec v h) as [Hle|Hgt]; [exists (l, h); split; [left; reflexivity | cbn; lia]|].
    apply lor_true in H2 as [H2|H2]; [apply Z.leb_le in H2; lia|].
    destruct (IH (h + 1) hi v H2 ltac:(lia)) as [c [Hc Hcv]]. exists c. split; [right; exact Hc | exact Hcv].
Qed.

Section Split.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable MR : valuation -> amodel -> Model -> Prop.
Variable KT : valuation -> list byte -> TSet.

Notation RR ρ := (R segs amodel (MR ρ) LIM ρ).
Notation Snd := (Sound segs cfg LIM MR KT).

Lemma R_with_store (ρ : valuation) (A : astate amodel) (c : config) (s : store) : RR ρ A c -> sat ρ s -> RR ρ (with_store A s) c.
Proof.
  intros [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna] Hs.
  constructor; cbn [with_store a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  apply RRegs_renorm; assumption.
Qed.

(* [comment removed for export] *)
Lemma split_case (ρ : valuation) (A : astate amodel) (f : lin) (cuts : list (Z * Z)) :
  sat ρ (a_facts A) -> split_ok A f cuts = true ->
  exists c, In c (List.filter (fun c => feasible (sadd (a_facts A) f (fst c) (snd c)) f) cuts) /\ fst c <= leval ρ f <= snd c
            /\ sat ρ (sadd (a_facts A) f (fst c) (snd c)).
Proof.
  intros Hs H. unfold split_ok in H. destruct (lrange (a_facts A) f) as [[lo hi]|] eqn:El; [|discriminate].
  pose proof (lrange_sound ρ _ f Hs _ El) as Hr. cbn [fst snd] in Hr.
  destruct (cuts_cover_sound cuts lo hi (leval ρ f) H Hr) as [c [Hc Hcv]].
  assert (Hs' : sat ρ (sadd (a_facts A) f (fst c) (snd c))) by (apply sat_sadd; assumption).
  exists c. split; [apply filter_In; split; [exact Hc | exact (feasible_sat ρ _ f Hs')]|]. split; assumption.
Qed.

Theorem split_sound (A : astate amodel) (f : lin) (cuts : list (Z * Z)) :
  split_ok A f cuts = true -> (forall B, In B (split_children A f cuts) -> Snd B) -> Snd A.
Proof.
  intros Hok HS ρ c HR o Ho. destruct (split_case ρ A f cuts (r_sat _ _ _ _ _ _ _ HR) Hok) as [cu [Hin [_ Hs']]].
  apply (HS (with_store A (sadd (a_facts A) f (fst cu) (snd cu)))).
  - unfold split_children. apply in_map_iff. exists cu. split; [reflexivity | exact Hin].
  - apply R_with_store; assumption.
  - exact Ho.
Qed.

Lemma R_pin_reg (ρ : valuation) (A : astate amodel) (c : config) (r : reg) (cu : Z * Z) (f : lin) :
  RR ρ A c -> (forall w, xv_val ρ (aget (a_regs A) (ri r)) w -> bv_unsigned w = leval ρ f) -> fst cu <= leval ρ f <= snd cu ->
  RR ρ (pin_reg (ri r) cu A) c.
Proof.
  intros HR Hf Hcu. unfold pin_reg. destruct (Z.eqb_spec (fst cu) (snd cu)) as [E|E]; [|exact HR].
  destruct HR as [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna].
  constructor; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  intros r'. rewrite aget_aset. destruct (Z.eqb_spec (bv_unsigned r') 0) as [E0|E0].
  - specialize (Hregs r'). unfold aget in Hregs. replace (ri r' =? 0)%uint63 with true in Hregs; [exact Hregs|].
    symmetry. apply Uint63.eqb_spec. apply to_Z_inj. rewrite phi_ri, E0. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned r) (bv_unsigned r')) as [E1|E1]; [|exact (Hregs r')].
    assert (r' = r) by (apply bv_eq; symmetry; exact E1). subst r'.
    pose proof (Hf _ (Hregs r)) as Hw. cbn [xv_val]. rewrite wZ_wofZ, Hw.
    pose proof (bvu_range (rg (cfg_ms c) r)) as Hrange. rewrite Hw in Hrange. rewrite Z.mod_small by lia. lia.
Qed.

Theorem split_reg_sound (A : astate amodel) (r : int) (f : lin) (cuts : list (Z * Z)) :
  (r <? 32)%uint63 = true -> xform (a_facts A) (canon_v (a_facts A) (aget (a_regs A) r)) = Some f -> split_ok A f cuts = true ->
  (forall B, In B (split_children_reg A r f cuts) -> Snd B) -> Snd A.
Proof.
  intros Hr Hxf Hok HS ρ c HR o Ho. pose proof (r_sat _ _ _ _ _ _ _ HR) as Hsat.
  destruct (split_case ρ A f cuts Hsat Hok) as [cu [Hin [Hcu Hs']]].
  apply Uint63.ltb_spec in Hr. change (to_Z 32%uint63) with 32 in Hr. pose proof (to_Z_bounded r) as Hrb.
  set (rr := Z_to_bv 5 (to_Z r) : reg).
  assert (Err : ri rr = r).
  { apply to_Z_inj. rewrite phi_ri. unfold rr. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  apply (HS (pin_reg r cu (with_store A (sadd (a_facts A) f (fst cu) (snd cu))))).
  - unfold split_children_reg. apply in_map_iff. exists cu. split; [reflexivity | exact Hin].
  - rewrite <- Err. apply (R_pin_reg ρ _ c rr cu f); [apply R_with_store; assumption | | exact Hcu].
    intros w Hw. cbn [with_store a_regs] in Hw. rewrite aget_renorm, Err in Hw.
    (* [comment removed for export] *)
    pose proof (r_regs _ _ _ _ _ _ _ HR rr) as Hw0. rewrite Err in Hw0.
    pose proof (xform_sound ρ _ _ _ f Hsat (canon_v_sound ρ _ _ _ Hsat Hw0) Hxf) as E0.
    pose proof (canon_v_sound ρ _ _ _ Hs' Hw0) as Hw1.
    (* [comment removed for export] *)
    destruct (aget (a_regs A) r) as [x|ts o'| | | |] eqn:Ea; cbn [canon_v xform] in Hxf; try discriminate.
    + cbn [canon_v xv_val] in Hw, Hw1. rewrite Hw, <- Hw1. exact E0.
    + cbn [canon_v] in Hw, Hw1. unfold mk_xs in Hw, Hw1.
      destruct (fst (canon_form (sadd (a_facts A) f (fst cu) (snd cu)) ts o')); cbn [xv_val] in Hw, Hw1; rewrite Hw, <- Hw1; exact E0.
  - cbn [pin_reg]. unfold pin_reg. destruct (fst cu =? snd cu); exact Ho.
Qed.

End Split.
