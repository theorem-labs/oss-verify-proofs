(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxImg AxMem AxZZ AxState AxEntryRel AxEntryAg AxSys AxOcc.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition upd_val (ρ : valuation) (v : int) (z : Z) : valuation := fun x => if (x =? v)%uint63 then z else ρ x.

Lemma upd_val_same (ρ : valuation) (v : int) (z : Z) : upd_val ρ v z v = z.
Proof. unfold upd_val. rewrite Uint63.eqb_refl. reflexivity. Qed.

Lemma upd_val_agree (ρ : valuation) (v : int) (z : Z) : forall x, x <> v -> upd_val ρ v z x = ρ x.
Proof. intros x Hx. unfold upd_val. destruct (x =? v)%uint63 eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity]. Qed.

Lemma agree_entry (v : int) (ρ ρ' : valuation) :
  (forall x, x <> v -> ρ' x = ρ x) -> entry_var v = false -> forall x, entry_var x = true -> ρ' x = ρ x.
Proof. intros Hag He x Hx. apply Hag. intros ->. rewrite He in Hx. discriminate Hx. Qed.

Lemma dec_str_agree (ρ ρ' : valuation) (k : Z) : (forall x, entry_var x = true -> ρ' x = ρ x) -> dec_str k ρ' = dec_str k ρ.
Proof. exact (dec_str_agree_entry ρ ρ' k). Qed.

Lemma pieces_agree (v : int) (ρ ρ' : valuation) :
  (forall x, x <> v -> ρ' x = ρ x) -> entry_var v = false ->
  forall (l : list piece) (o : list byte), existsb (piece_occ v) l = false -> pieces_val ρ l o -> pieces_val ρ' l o.
Proof.
  intros Hag He. induction l as [|p r IH]; intros o Ho H; [exact H|]. cbn [existsb] in Ho. apply orb_false_iff in Ho as [Hp Hr].
  destruct p as [b|k]; cbn [pieces_val] in *.
  - destruct H as [y [o' [-> [Hy H']]]]. exists y, o'. split; [reflexivity|]. split; [|exact (IH o' Hr H')].
    exact (xb_z_agree v ρ ρ' b _ Hag Hp Hy).
  - destruct H as [o' [-> H']]. exists o'. split; [|exact (IH o' Hr H')].
    rewrite (dec_str_agree ρ ρ' k (agree_entry v ρ ρ' Hag He)). reflexivity.
Qed.

Lemma out_agree (v : int) (ρ ρ' : valuation) (A : AST) (o : list byte) :
  (forall x, x <> v -> ρ' x = ρ x) -> state_occ v A = false -> out_val ρ A o -> out_val ρ' A o.
Proof.
  intros Hag Ho H. destruct (state_occ_parts v A Ho) as (He & _ & _ & _ & _ & Hm).
  destruct (model_occ_parts v _ Hm) as (_ & _ & _ & _ & _ & _ & _ & Hout).
  exact (pieces_agree v ρ ρ' Hag He _ o Hout H).
Qed.

Section Agree.
Variable segs : list Segment.
Variable v : int.
Variables ρ ρ' : valuation.
Hypothesis Hag : forall x, x <> v -> ρ' x = ρ x.

Lemma rbase_agree (R : region) : ts_occ v (rg_ts R) = false -> rbase ρ' R = rbase ρ R.
Proof. intros H. unfold rbase. exact (smod_agree v ρ ρ' _ _ Hag H). Qed.

Lemma region_occ_parts (R : region) : region_occ v R = false -> ts_occ v (rg_ts R) = false /\ inone (cell_occ v) (rg_cells R) = true.
Proof. unfold region_occ. intros H. apply orb_false_iff in H as [H1 H2]. apply negb_false_iff in H2. split; assumption. Qed.

Lemma mem_occ_in (A : list region) (R : region) : existsb (region_occ v) A = false -> In R A -> region_occ v R = false.
Proof.
  intros H HIn. destruct (region_occ v R) eqn:E; [|reflexivity].
  assert (X : existsb (region_occ v) A = true) by (apply existsb_exists; exists R; split; assumption). rewrite X in H. discriminate H.
Qed.

Lemma rbyte_occ (R : region) (y : int) : inone (cell_occ v) (rg_cells R) = true -> xb_occ v (rbyte segs R y) = false.
Proof.
  intros H. unfold rbyte. destruct (get_cell_opt R (y >> 3)%uint63) as [c|] eqn:E.
  - unfold get_cell_opt in E. pose proof (inone_iget _ _ _ _ _ H E) as Hc. destruct c as [w|l]; [reflexivity|]. cbn [cbyte cell_occ] in *.
    destruct (xb_occ v (nth (i2n (y land 7)%uint63) l BT)) eqn:E2; [|reflexivity].
    destruct (Nat.lt_ge_cases (i2n (y land 7)%uint63) (length l)) as [L|L].
    + assert (X : existsb (xb_occ v) l = true) by (apply existsb_exists; exists (nth (i2n (y land 7)%uint63) l BT); split; [apply nth_In; exact L | exact E2]).
      rewrite X in Hc. discriminate Hc.
    + rewrite nth_overflow in E2 by exact L. discriminate E2.
  - unfold default_byte. destruct (rg_kind R) as [| | |w i|ph]; try reflexivity. destruct (fimg_i segs i y); reflexivity.
Qed.

Lemma RRegion_agree (m : word -> option byte) (R : region) :
  entry_var v = false -> region_occ v R = false -> RRegion segs ρ m R -> RRegion segs ρ' m R.
Proof.
  intros He Ho HR. destruct (region_occ_parts R Ho) as [Ht Hc]. unfold RRegion in *. rewrite (rbase_agree R Ht).
  destruct (rg_kind R) as [| | |w i|ph] eqn:Ek; try exact (eb_rel_agree ph ρ ρ' m _ _ (agree_entry v ρ ρ' Hag He) HR).
  all: intros y Hy; rewrite (rbase_agree R Ht); destruct (HR y Hy) as [[b [Hb Hx]] Hw]; (split; [|exact Hw]); exists b; (split; [exact Hb|]);
    exact (xb_z_agree v ρ ρ' _ _ Hag (rbyte_occ R y Hc) Hx).
Qed.

Lemma regions_ok_agree (A : list region) : (forall R, In R A -> ts_occ v (rg_ts R) = false) -> regions_ok ρ A -> regions_ok ρ' A.
Proof.
  induction A as [|R A' IH]; intros Ho H; [exact I|]. cbn [regions_ok] in *. destruct H as (Hwf & Hd & Hok).
  assert (ER : rbase ρ' R = rbase ρ R) by (apply rbase_agree; apply Ho; left; reflexivity).
  split; [|split].
  - unfold region_wf in *. rewrite ER. exact Hwf.
  - rewrite Forall_forall in *. intros R2 HIn. specialize (Hd R2 HIn). unfold rdisj in *.
    rewrite ER, (rbase_agree R2 (Ho R2 (or_intror HIn))). exact Hd.
  - apply IH; [intros R2 HIn; apply Ho; right; exact HIn | exact Hok].
Qed.

End Agree.

Lemma R_agree (segs : list Segment) (LIM : Z) (MR : valuation -> amodel -> Model -> Prop)
    (MR_agree : forall v ρ ρ' am m, (forall x, x <> v -> ρ' x = ρ x) -> model_occ v am = false -> MR ρ am m -> MR ρ' am m)
    (v : int) (ρ ρ' : valuation) (A : astate amodel) (c : config) :
  (forall x, x <> v -> ρ' x = ρ x) -> state_occ v A = false -> R segs amodel (MR ρ) LIM ρ A c -> R segs amodel (MR ρ') LIM ρ' A c.
Proof.
  intros Hag Ho [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15].
  destruct (state_occ_parts v A Ho) as (He & Hregs & Hrsv & Hmem & Hst & Hm).
  assert (Hts : forall R0, In R0 (a_mem A) -> ts_occ v (rg_ts R0) = false).
  { intros R0 HIn. exact (proj1 (region_occ_parts v R0 (mem_occ_in v _ R0 Hmem HIn))). }
  assert (Hrg : forall R0 z, In R0 (a_mem A) -> (in_rg ρ' R0 z <-> in_rg ρ R0 z)).
  { intros R0 z HIn. unfold in_rg. rewrite (rbase_agree v ρ ρ' Hag R0 (Hts R0 HIn)). tauto. }
  constructor; try assumption.
  -   intros r. specialize (H4 r). unfold aget in *. destruct (ri r =? 0)%uint63; [exact H4|].
    destruct (iget 5 (a_regs A) (ri r)) as [x|] eqn:E; [|exact H4].
    exact (xv_val_agree v ρ ρ' x _ Hag (inone_iget _ _ _ _ _ Hregs E) H4).
  -   destruct (a_resv A) as [|x|]; cbn [RResv rsv_occ] in *; try exact H5.
    destruct H5 as [a [Ea Hx]]. exists a. split; [exact Ea | exact (xv_val_agree v ρ ρ' x a Hag Hrsv Hx)].
  -   destruct H7 as [Hok HF]. split; [exact (regions_ok_agree v ρ ρ' Hag _ Hts Hok)|].
    rewrite Forall_forall in *. intros R0 HIn. exact (RRegion_agree segs v ρ ρ' Hag _ R0 He (mem_occ_in v _ R0 Hmem HIn) (HF R0 HIn)).
  -   exact (MR_agree v ρ ρ' _ _ Hag Hm H8).
  -   destruct H11 as [Hb Hf]. unfold store_occ in Hst. apply orb_false_iff in Hst as [S1 S2]. split.
    + intros x i Hx Hi. destruct (x =? v)%uint63 eqn:E.
      * apply Uint63.eqb_spec in E. subst x. assert (L : (v <? 65536)%uint63 = true) by (apply Uint63.ltb_spec; exact Hx).
        rewrite L, Hi in S1. discriminate S1.
      * rewrite Hag; [exact (Hb x i Hx Hi)|]. intros ->. rewrite Uint63.eqb_refl in E. discriminate E.
    + rewrite Forall_forall in *. intros fc Hfc. specialize (Hf fc Hfc).
      assert (Efc : leval ρ' (fc_f fc) = leval ρ (fc_f fc)).
      { apply (leval_agree v ρ ρ' Hag). destruct (ts_occ v (snd (fc_f fc))) eqn:E; [|reflexivity].
        assert (X : existsb (fact_occ v) (st_facts (a_facts A)) = true) by (apply existsb_exists; exists fc; split; [exact Hfc | exact E]).
        rewrite X in S2. discriminate S2. }
      unfold fact_sat in *. rewrite Efc. exact Hf.
  -   destruct H12 as [Hpl|(P1 & P2 & P3 & P4)]; [left; exact Hpl | right]. split; [|split; [|split]]; try assumption.
    + intros R0 HIn Hs z Hz. apply (P1 R0 HIn Hs z). apply Hrg; assumption.
    + intros z Hz Hmiss. apply (P2 z Hz). intros R0 HIn Hs Hr. apply (Hmiss R0 HIn Hs). apply Hrg; assumption.
  -   intros R0 HIn Hs z Hz. apply (H14 R0 HIn Hs z). apply Hrg; assumption.
  -   destruct H15 as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|].
    intros R0 HIn Hs z Hz. apply (N3 R0 HIn Hs z). apply Hrg; assumption.
Qed.
