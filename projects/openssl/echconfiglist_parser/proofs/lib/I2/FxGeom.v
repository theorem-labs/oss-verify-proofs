(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Geom.
Variable IM : fimage.
Variable code : itrie finstr.
Variable RO : itrie unit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_geom (rg rg' : region) : Prop :=
  rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg /\ rg_dflt rg' = rg_dflt rg
  /\ rg_clo rg' = rg_clo rg /\ rg_chi rg' = rg_chi rg /\ rg_kind rg' = rg_kind rg.

Definition geom_rel (M M' : itrie region) : Prop :=
  forall t, match iget t M, iget t M' with
            | Some rg, Some rg' => same_geom rg rg'
            | None, None => True
            | _, _ => False
            end.

Lemma same_geom_refl rg : same_geom rg rg.
Proof. repeat split; reflexivity. Qed.
Lemma same_geom_trans a b c : same_geom a b -> same_geom b c -> same_geom a c.
Proof. intros (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.

Lemma geom_rel_refl M : geom_rel M M.
Proof. intros t. destruct (iget t M); [apply same_geom_refl | exact I]. Qed.
Lemma geom_rel_trans M1 M2 M3 : geom_rel M1 M2 -> geom_rel M2 M3 -> geom_rel M1 M3.
Proof.
  intros H1 H2 t. specialize (H1 t). specialize (H2 t).
  destruct (iget t M1), (iget t M2), (iget t M3); try contradiction; [|exact I].
  eapply same_geom_trans; eassumption.
Qed.

Lemma fm_store_geom M a sz v M' : fm_store IM M a sz v = Some M' -> geom_rel M M'.
Proof.
  intros Hst t. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _ & _ & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t0. rewrite Hrg. unfold store_region. repeat split; reflexivity.
  - destruct (iget t M); [apply same_geom_refl | exact I].
Qed.

Lemma fx_step_geom F F' : fx_step IM code RO F = FNext F' -> geom_rel (f_mem F) (f_mem F').
Proof.
  intros H. destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. apply geom_rel_refl.
  - exact (fm_store_geom _ _ _ _ _ Hst).
Qed.

Theorem fx_run_geom : forall bp k F F' r cnt,
  fx_run IM code RO bp k F = (F', r, cnt) -> geom_rel (f_mem F) (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt H.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63; [injection H as <- <- <-; apply geom_rel_refl|].
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-; try apply geom_rel_refl.
    exact (fx_step_geom F s' Es).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (geom_rel_trans _ _ _ (IH _ _ _ _ E1) (IH _ _ _ _ E2)).
    + injection H as <- <- <-. exact (IH _ _ _ _ E1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cells_inb (M : itrie region) : Prop :=
  forall t rg pn p ci c, iget t M = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) = Some c ->
    to_Z pn * 4096 + to_Z ci * 8 < to_Z (rg_len rg) /\ to_Z ci < 512
    /\ (forall v, c = CV v -> to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg)).

Section WithRel.
Variable segs : list Segment.
Variable rho : int -> word.

(* [comment removed for export] *)
Lemma page_at_cells rg t pn p ci c :
  page_at IM rg t pn = Some p -> iget ci (pg_cells p) = Some c -> iget pn (rg_pages rg) = Some p.
Proof.
  intros Hp Hc. unfold page_at in Hp.
  destruct (iget pn (rg_pages rg)) as [p0|] eqn:E; [congruence|].
  exfalso.
  destruct (if (t =? 0)%uint63 then find_seg IM (pn << 12)%uint63 else None) as [sg|].
  - injection Hp as <-. cbn [pg_cells] in Hc. rewrite iget_iempty in Hc. discriminate.
  - destruct (rg_dflt rg) as [kd|]; [|discriminate].
    destruct (page_in_region rg pn); [|discriminate]. injection Hp as <-. cbn [pg_cells] in Hc. rewrite iget_iempty in Hc. discriminate.
Qed.

Lemma fm_store_cells_inb M m a sz v M' :
  mem_ok segs IM rho M m -> cells_inb M -> fm_store IM M a sz v = Some M' -> cells_inb M'.
Proof.
  intros Hmok Hinb Hst. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & _ & C1 & C2 & C3 & ->).
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (i63_range off) as Hoff0. pose proof (msz_nat_pos sz) as Hn.
  intros t rg' pn' p' ci' c' Ht Hp' Hc'.
  rewrite iget_iset in Ht. destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t0. injection Ht as <-.
    unfold store_region in Hp' |- *. cbn [rg_pages rg_len] in Hp' |- *. rewrite iget_iset in Hp'.
    destruct (pn' =? (off >> 12))%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. subst pn'. injection Hp' as <-.
      rewrite iget_store_page in Hc'.
      destruct (ci' =? ((off land 4095) >> 3))%uint63 eqn:Eci.
      * apply Uint63.eqb_spec in Eci. subst ci'.
        rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095.
        pose proof (cell_index_range (to_Z off) ltac:(lia)) as Hci.
        pose proof (off_decomp (to_Z off) ltac:(lia)) as Hdec.
        pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)).
        split; [lia|]. split; [lia|].
        (* [comment removed for export] *)
        intros v0 Ev0. injection Hc' as Hc'. rewrite Ev0 in Hc'.
        destruct Hmok as [Hregs _]. destruct (Hregs t rg Hrg) as [_ Hpages].
        assert (Hpn : to_Z (off >> 12)%uint63 < 2 ^ 50) by (rewrite to_Z_lsr12; lia).
        destruct (Hpages _ _ Hpn Hp) as (Hpage & _ & _).
        destruct (ci_cases rg (off >> 12)%uint63 (to_Z off) (Z.of_nat (msz_nat sz)) ltac:(lia) ltac:(lia) Hcell Hin (to_Z_lsr12 off))
          as [Hwhole | Hcut].
        { unfold clim, blim in Hwhole. rewrite to_Z_lsr12 in Hwhole. Z.div_mod_to_equations. nia. }
        exfalso.
        destruct (store_newc_cut segs IM rho m t (off >> 12)%uint63 (blim rg (off >> 12)%uint63) p ((off land 4095) >> 3)%uint63 (off land 7)%uint63 sz v
                    Hpage ltac:(rewrite to_Z_lsr3, to_Z_land4095; lia) ltac:(rewrite to_Z_lsr3, to_Z_land4095; exact Hcut))
          as (sl' & Esl' & _).
        { rewrite to_Z_lsr3, to_Z_land4095, to_Z_land7. unfold blim. rewrite to_Z_lsr12.
          unfold blim in Hcut. rewrite to_Z_lsr12 in Hcut. Z.div_mod_to_equations. nia. }
        rewrite Esl' in Hc'. discriminate Hc'.
      * destruct (Hinb t rg (off >> 12)%uint63 p ci' c' Hrg (page_at_cells _ _ _ _ _ _ Hp Hc') Hc') as (H1 & H2 & H3).
        split; [exact H1 | split; [exact H2 | exact H3]].
    + exact (Hinb t rg pn' p' ci' c' Hrg Hp' Hc').
  - exact (Hinb t rg' pn' p' ci' c' Ht Hp' Hc').
Qed.
End WithRel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cellx (M : itrie region) (t pn ci : int) : Prop :=
  exists rg p c, iget t M = Some rg /\ iget pn (rg_pages rg) = Some p /\ iget ci (pg_cells p) = Some c.

Lemma fm_store_cellx M a sz v M' t pn ci :
  fm_store IM M a sz v = Some M' -> cellx M t pn ci -> cellx M' t pn ci.
Proof.
  intros Hst (rg & p & c & Ht & Hp & Hc). destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg0 & p0 & Hrg0 & Hp0 & _ & _ & _ & _ & ->).
  unfold cellx. rewrite iget_iset. destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t0. rewrite Hrg0 in Ht. injection Ht as ->.
    exists (store_region rg (off >> 12)%uint63 (store_page IM p0 (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (off land 7)%uint63 sz v)).
    unfold store_region. cbn [rg_pages]. rewrite iget_iset. destruct (pn =? (off >> 12))%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. subst pn.
      assert (p0 = p) by (unfold page_at in Hp0; rewrite Hp in Hp0; congruence). subst p0.
      unfold store_page. cbn [pg_cells].
      destruct (ci =? ((off land 4095) >> 3))%uint63 eqn:Eci.
      * eexists. eexists. split; [reflexivity|]. split; [reflexivity|]. cbn [pg_cells]. rewrite iget_iset, Eci. reflexivity.
      * eexists. exists c. split; [reflexivity|]. split; [reflexivity|]. cbn [pg_cells]. rewrite iget_iset, Eci. exact Hc.
    + exists p, c. split; [reflexivity|]. split; [exact Hp | exact Hc].
  - exists rg, p, c. split; [exact Ht|]. split; [exact Hp | exact Hc].
Qed.

Lemma fx_step_cellx F F' t pn ci : fx_step IM code RO F = FNext F' -> cellx (f_mem F) t pn ci -> cellx (f_mem F') t pn ci.
Proof.
  intros H Hc. destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. exact Hc.
  - exact (fm_store_cellx _ _ _ _ _ _ _ _ Hst Hc).
Qed.

Theorem fx_run_cellx : forall bp k F F' r cnt t pn ci,
  fx_run IM code RO bp k F = (F', r, cnt) -> cellx (f_mem F) t pn ci -> cellx (f_mem F') t pn ci.
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt t pn ci H Hc.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63; [injection H as <- <- <-; exact Hc|].
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-; try exact Hc.
    exact (fx_step_cellx F s' t pn ci Es Hc).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      exact (IH _ _ _ _ _ _ _ E2 (IH _ _ _ _ _ _ _ E1 Hc)).
    + injection H as <- <- <-. exact (IH _ _ _ _ _ _ _ E1 Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition im_nowr : Prop := forall a sg, find_seg IM a = Some sg -> sg_wr sg = false.

Definition pages0_sub (M M' : itrie region) : Prop :=
  forall rg0', iget 0%uint63 M' = Some rg0' ->
  exists rg0, iget 0%uint63 M = Some rg0
    /\ forall pn p', iget pn (rg_pages rg0') = Some p' ->
         exists p, iget pn (rg_pages rg0) = Some p /\ pg_kind p' = pg_kind p.

Lemma pages0_sub_refl M : pages0_sub M M.
Proof. intros rg0' H. exists rg0'. split; [exact H|]. intros pn p' Hp. exists p'. split; [exact Hp | reflexivity]. Qed.
Lemma pages0_sub_trans M1 M2 M3 : pages0_sub M1 M2 -> pages0_sub M2 M3 -> pages0_sub M1 M3.
Proof.
  intros H1 H2 rg3 Hg3. destruct (H2 rg3 Hg3) as (rg2 & Hg2 & P2). destruct (H1 rg2 Hg2) as (rg1 & Hg1 & P1).
  exists rg1. split; [exact Hg1|]. intros pn p3 Hp3.
  destruct (P2 pn p3 Hp3) as (p2 & Hp2 & K2). destruct (P1 pn p2 Hp2) as (p1 & Hp1 & K1).
  exists p1. split; [exact Hp1 | congruence].
Qed.

Lemma fm_store_pages0 M a sz v M' :
  im_nowr -> (forall rg0, iget 0%uint63 M = Some rg0 -> rg_dflt rg0 = None) ->
  fm_store IM M a sz v = Some M' -> pages0_sub M M'.
Proof.
  intros Hnw Hdf Hst rg0' H0'. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & Hwr & _ & _ & _ & ->).
  rewrite iget_iset in H0'. destruct (0 =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t0. injection H0' as <-. exists rg. split; [exact Hrg|].
    intros pn p' Hp'. unfold store_region in Hp'. cbn [rg_pages] in Hp'. rewrite iget_iset in Hp'.
    destruct (pn =? (off >> 12))%uint63 eqn:Epn.
    + apply Uint63.eqb_spec in Epn. subst pn. injection Hp' as <-.
      unfold store_page. cbn [pg_kind].
      (* [comment removed for export] *)
      unfold page_at in Hp. destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p0|] eqn:E.
      * injection Hp as <-. exists p0. split; [reflexivity | reflexivity].
      * exfalso. change ((0 =? 0)%uint63) with true in Hp. cbv iota in Hp.
        destruct (find_seg IM ((off >> 12) << 12)%uint63) as [sg|] eqn:Hsg.
        { injection Hp as <-. cbn in Hwr. rewrite (Hnw _ _ Hsg) in Hwr. discriminate. }
        rewrite (Hdf rg Hrg) in Hp. discriminate.
    + exists p'. split; [exact Hp' | reflexivity].
  - exists rg0'. split; [exact H0'|]. intros pn p' Hp'. exists p'. split; [exact Hp' | reflexivity].
Qed.

(* [comment removed for export] *)
Section Run.
Variable segs : list Segment.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis Hcode : code_ok segs code.
Hypothesis Hnw : im_nowr.
Local Abbreviation Rr := (R segs IM rho).

(* [comment removed for export] *)
Definition kinds_unk (M : itrie region) : Prop :=
  forall t rg, iget t M = Some rg -> t <> 0%uint63 ->
    rg_dflt rg = Some PKUnk /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_kind p = PKUnk.

Lemma fm_store_kinds_unk M a sz v M' :
  fm_store IM M a sz v = Some M' -> kinds_unk M -> kinds_unk M'.
Proof.
  intros Hst Hk t rg' Ht Ht0. destruct a as [t0 [top off]].
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & Hwr & _ & _ & _ & ->).
  rewrite iget_iset in Ht. destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t0. injection Ht as <-. destruct (Hk t rg Hrg Ht0) as [Hd Hpk].
    unfold store_region. cbn [rg_dflt rg_pages]. split; [exact Hd|].
    intros pn p' Hp'. rewrite iget_iset in Hp'. destruct (pn =? (off >> 12))%uint63 eqn:Epn.
    + injection Hp' as <-. unfold store_page. cbn [pg_kind].
      unfold page_at in Hp. destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p0|] eqn:E.
      * injection Hp as <-. exact (Hpk _ _ E).
      * destruct (t =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|].
        rewrite Hd in Hp. destruct (page_in_region rg (off >> 12)%uint63); [|discriminate]. injection Hp as <-. reflexivity.
    + exact (Hpk _ _ Hp').
  - exact (Hk t rg' Ht Ht0).
Qed.

Definition shape_inv (M : itrie region) : Prop :=
  cells_inb M /\ (forall rg0, iget 0%uint63 M = Some rg0 -> rg_dflt rg0 = None) /\ kinds_unk M.

Lemma fx_step_shape F ms F' :
  Rr F ms -> fx_step IM code RO F = FNext F' -> shape_inv (f_mem F) ->
  shape_inv (f_mem F') /\ pages0_sub (f_mem F) (f_mem F').
Proof.
  intros HR H (Hinb & Hdf & Hku). destruct (fx_step_mem IM code RO F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. split; [split; [assumption | split; assumption] | apply pages0_sub_refl].
  - split.
    + split; [exact (fm_store_cells_inb segs rho _ _ _ _ _ _ (R_mem _ _ _ _ _ HR) Hinb Hst)|]. split.
      * intros rg0' H0'. pose proof (fm_store_geom _ _ _ _ _ Hst 0%uint63) as Hg. rewrite H0' in Hg.
        destruct (iget 0%uint63 (f_mem F)) as [rg0|] eqn:E0; [|destruct Hg].
        destruct Hg as (_ & _ & _ & Hd & _). rewrite Hd. exact (Hdf rg0 eq_refl).
      * exact (fm_store_kinds_unk _ _ _ _ _ Hst Hku).
    + exact (fm_store_pages0 _ _ _ _ _ Hnw Hdf Hst).
Qed.

Theorem fx_run_shape : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  forall ms, Rr F ms -> shape_inv (f_mem F) ->
  shape_inv (f_mem F') /\ pages0_sub (f_mem F) (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H ms HR Hsh.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. split; [exact Hsh | apply pages0_sub_refl]. }
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-;
      try (split; [exact Hsh | apply pages0_sub_refl]).
    exact (fx_step_shape F ms s' HR Es Hsh).
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
