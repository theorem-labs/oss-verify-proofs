(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxGeom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Geom.
Variable IM : fimage.
Variable code : itrie finstr.
Variable RO : itrie unit.

(* [comment removed for export] *)
Definition kinds_ok (M : itrie region) : Prop :=
  forall t rg, iget t M = Some rg -> t <> 0%uint63 ->
    (rg_dflt rg = Some PKUnk \/ rg_dflt rg = None) /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_kind p = PKUnk.

Lemma kinds_ok_of_unk M : kinds_unk M -> kinds_ok M.
Proof. intros Hk t rg Ht Ht0. destruct (Hk t rg Ht Ht0) as [Hd Hp]. split; [left; exact Hd | exact Hp]. Qed.

Lemma fm_store_kinds_ok M a sz v M' :
  fm_store IM M a sz v = Some M' -> kinds_ok M -> kinds_ok M'.
Proof.
  intros Hst Hk t rg' Ht Ht0. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & Hwr & _ & _ & _ & ->).
  rewrite iget_iset in Ht. destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t0. injection Ht as <-. destruct (Hk t rg Hrg Ht0) as [Hd Hpk].
    split; [exact Hd|].
    intros pn p' Hp'. unfold store_region in Hp'. cbn [rg_pages] in Hp'. rewrite iget_iset in Hp'.
    destruct (pn =? (off >> 12))%uint63 eqn:Epn.
    + injection Hp' as <-. unfold store_page. cbn [pg_kind].
      unfold page_at in Hp. destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p0|] eqn:E.
      * injection Hp as <-. exact (Hpk _ _ E).
      * destruct (t =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
        destruct Hd as [Hd|Hd]; rewrite Hd in Hp; [|discriminate].
        destruct (page_in_region rg (off >> 12)%uint63); [|discriminate]. injection Hp as <-. reflexivity.
    + exact (Hpk _ _ Hp').
  - exact (Hk t rg' Ht Ht0).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ro_region (rg : region) : Prop :=
  rg_dflt rg = None /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_wr p = false.

Lemma fm_store_ro_kept M a sz v M' t rg :
  fm_store IM M a sz v = Some M' -> t <> 0%uint63 -> iget t M = Some rg -> ro_region rg -> iget t M' = Some rg.
Proof.
  intros Hst Ht0 Hrg [Hd Hp]. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg0 & p & Hrg0 & Hpa & Hwr & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:Et; [|exact Hrg].
  apply Uint63.eqb_spec in Et. subst t0. rewrite Hrg in Hrg0. injection Hrg0 as <-.
  exfalso. unfold page_at in Hpa. destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p0|] eqn:E.
  - injection Hpa as <-. rewrite (Hp _ _ E) in Hwr. discriminate.
  - destruct (t =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|]. rewrite Hd in Hpa. discriminate.
Qed.

Lemma fx_step_ro_kept F F' t rg :
  fx_step IM code RO F = FNext F' -> t <> 0%uint63 -> iget t (f_mem F) = Some rg -> ro_region rg -> iget t (f_mem F') = Some rg.
Proof.
  intros H Ht0 Hrg Hro. destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact Hrg.
  - exact (fm_store_ro_kept _ _ _ _ _ _ _ Hst Ht0 Hrg Hro).
Qed.

Theorem fx_run_ro_kept : forall bp k F F' r cnt t rg,
  fx_run IM code RO bp k F = (F', r, cnt) ->
  t <> 0%uint63 -> iget t (f_mem F) = Some rg -> ro_region rg -> iget t (f_mem F') = Some rg.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt t rg H Ht0 Hrg Hro.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. exact Hrg. }
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-; try exact Hrg.
    exact (fx_step_ro_kept F s' t rg Es Ht0 Hrg Hro).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    pose proof (IH _ _ _ _ t rg E1 Ht0 Hrg Hro) as H1.
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (IH _ _ _ _ t rg E2 Ht0 H1 Hro).
    + injection H as <- <- <-. exact H1.
Qed.

Definition shape_invA (M : itrie region) : Prop :=
  cells_inb M /\ (forall rg0, iget 0%uint63 M = Some rg0 -> rg_dflt rg0 = None) /\ kinds_ok M.

Section Run.
Variable segs : list Segment.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis Hcode : code_ok segs code.
Hypothesis Hnw : im_nowr IM.
Local Abbreviation Rr := (R segs IM rho).

Lemma fx_step_shapeA F ms F' :
  Rr F ms -> fx_step IM code RO F = FNext F' -> shape_invA (f_mem F) ->
  shape_invA (f_mem F') /\ pages0_sub (f_mem F) (f_mem F').
Proof.
  intros HR H (Hinb & Hdf & Hku). destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. split; [split; [assumption | split; assumption] | apply pages0_sub_refl].
  - split.
    + split; [exact (fm_store_cells_inb IM segs rho _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) Hinb Hst)|]. split.
      * intros rg0' H0'. pose proof (fm_store_geom IM _ _ _ _ _ Hst 0%uint63) as Hg. rewrite H0' in Hg.
        destruct (iget 0%uint63 (f_mem F)) as [rg0|] eqn:E0; [|destruct Hg].
        destruct Hg as (_ & _ & _ & Hd & _). rewrite Hd. exact (Hdf rg0 eq_refl).
      * exact (fm_store_kinds_ok _ _ _ _ _ Hst Hku).
    + exact (fm_store_pages0 IM _ _ _ _ _ Hnw Hdf Hst).
Qed.

Theorem fx_run_shapeA : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  forall ms, Rr F ms -> shape_invA (f_mem F) ->
  shape_invA (f_mem F') /\ pages0_sub (f_mem F) (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H ms HR Hsh.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. split; [exact Hsh | apply pages0_sub_refl]. }
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-;
      try (split; [exact Hsh | apply pages0_sub_refl]).
    exact (fx_step_shapeA F ms s' HR Es Hsh).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (fx_run_sound segs IM rho Hrho0 code RO Hcode bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & IH1).
    destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _).
    destruct (IH _ _ _ _ ltac:(lia) E1 ms HR Hsh) as [Hsh1 Hp1].
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (IH _ _ _ _ ltac:(lia) E2 ms1 HR1 Hsh1) as [Hsh2 Hp2].
      split; [exact Hsh2 | exact (pages0_sub_trans _ _ _ Hp1 Hp2)].
    + injection H as <- <- <-. split; [exact Hsh1 | exact Hp1].
Qed.
End Run.
End Geom.
