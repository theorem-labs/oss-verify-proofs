(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutLib.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CCA.
Definition mem := (word -> option byte).
Definition vis (A : list (Z * Z)) (model : Model) (M : mem) : mem := mrestrict (ahid A model) M.

Lemma vis_sbm : forall A model model1 M, same_but_materialized model model1 -> vis A model1 M = vis A model M.
Proof. intros A model model1 M H. unfold vis. rewrite (L5LZ.sbm_ahid A model model1 H). reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Definition AtV (c : CC.cutpoint) (E : env) (R : bvmap 5 word) (A : list (Z * Z)) (M : mem) (model : Model) : Prop :=
  CC.At segs c E R (vis A model M).

(* [comment removed for export] *)
Record leaf_factsA (c : CC.cutpoint) (ps : SR.post_spec) (E' : env) (R' : bvmap 5 word) (A : list (Z * Z))
       (M : mem) (model : Model) (M1 : mem) (model1 : Model) : Prop := LFA {
  lfa_vis : CC.leaf_facts segs c ps E' R' (vis A model M) (vis A model1 M1);
  lfa_frame : forall a : word, SGP.outside E' (CC.cp_F c) a -> M1 a = M a;
  lfa_grows : mem_grows M M1;
  lfa_hid : forall a : word, ahid A model a = true -> M1 a = M a;
  lfa_sbm : same_but_materialized model model1;
  lfa_minv : MInv A model1 }.

(* [comment removed for export] *)
Lemma ret_cps : forall (fx : FPState) R pc (M : mem) model A K,
  CL.is_ret_at segs pc ->
  m_halted model = None -> MInv A model -> A_wf A -> H_off_segments segs (ahid A model) -> wx_segs_nowrap segs ->
  Hoare.ret_ok (getr R 1%bv) ->
  (forall model1, MInv A model1 -> same_but_materialized model model1 ->
     srealizes segs SCFG (mkCfg (@mkst fx R (getr R 1%bv) M (seg_rom segs)) model1) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model) K.
Proof.
  intros fx R pc M model A K (w & rd & rs1 & imm & Hf & He & Hd & Urd & Urs & Uimm) Hh HMI HAwf Hoff Hnw Hret HK.
  assert (rd = 0%bv) as -> by (apply bv_eq; exact Urd).
  assert (rs1 = 1%bv) as -> by (apply bv_eq; exact Urs).
  assert (imm = 0%bv) as -> by (apply bv_eq; exact Uimm).
  set (H := ahid A model).
  assert (MS : msteps segs (@mkst fx R (Z_to_bv 64 pc) (mrestrict H M) (seg_rom segs)) (@mkst fx R (getr R 1%bv) (mrestrict H M) (seg_rom segs))).
  { eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_jalr_x0 segs R (Z_to_bv 64 pc) (mrestrict H M) (seg_rom segs) w 1%bv 0%bv (getr R 1%bv) Hf He Hd eq_refl).
    change (bv_signed (0%bv : bv 12)) with 0. unfold Hoare.ret_ok in Hret. rewrite Hret. reflexivity. }
  eapply (L5LZ.cps_of_msteps_lazy segs H A fx fx R _ M R _ (mrestrict H M) model K Hoff Hnw (L5LZ.lazy_cover_ahid A model) HAwf HMI Hh MS).
  intros model1 HMI1 HS _.
  replace (munrestrict H M (mrestrict H M)) with M; [exact (HK model1 HMI1 HS)|].
  apply FunctionalExtensionality.functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Section Cert.
Variable CPS : list CC.cutpoint.
Variable Amb : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis FPI_msteps : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.

Definition IH (mu : Z) : Prop :=
  forall j cj (fx2 : FPState) E2 R2 A2 M2 model2,
    nth_error CPS j = Some cj -> AtV cj E2 R2 A2 M2 model2 -> Amb j E2 A2 M2 model2 -> FPI fx2 -> CC.meas cj E2 < mu ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (CC.cp_pc cj) M2) model2) K.

Definition leaf_ok (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : Prop :=
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    AtV c E R A M model -> Amb i E A M model -> FPI fx' ->
    env_agree (CC.cp_nx c) E E' -> leaf_factsA c ps E' R' A M model M1 model1 ->
    IH (CC.meas c E) ->
    srealizes segs SCFG (mkCfg (mk fx' R' (SR.ps_pc ps) M1) model1) K.

Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis LEAVES : forall i c k ps, nth_error CPS i = Some c -> nth_error (CC.cp_PSS c) k = Some ps -> leaf_ok i c ps.
Hypothesis AMB_MODEL : forall i E A M model, Amb i E A M model ->
  m_halted model = None /\ MInv A model /\ A_wf A /\ H_off_segments segs (ahid A model).
Hypothesis NOWRAP : wx_segs_nowrap segs.

Theorem cutcert_sound :
  forall i c (fx : FPState) E R A M model,
    nth_error CPS i = Some c -> AtV c E R A M model -> Amb i E A M model -> FPI fx ->
    srealizes segs SCFG (mkCfg (mk fx R (CC.cp_pc c) M) model) K.
Proof.
  assert (G : forall n : nat, forall i c (fx : FPState) E R A M model,
             nth_error CPS i = Some c -> AtV c E R A M model -> Amb i E A M model -> FPI fx -> (Z.to_nat (CC.meas c E) < n)%nat ->
             srealizes segs SCFG (mkCfg (mk fx R (CC.cp_pc c) M) model) K).
  { induction n as [|n IHn]; intros i c fx E R A M model Hc HAt HAmb HFP Hn; [lia|].
    pose proof HAt as [HR HK].
    destruct (PLANS i c Hc fx E R (vis A model M) HR HK) as (fx' & E' & R' & M1v & k & ps & Hps & Hag & Hms & HLF).
    destruct (AMB_MODEL i E A M model HAmb) as (Hh & HMI & HAwf & Hoff).
    set (H := ahid A model) in *.
    eapply (L5LZ.cps_of_msteps_lazy segs H A fx fx' R _ M R' _ M1v model K Hoff NOWRAP (L5LZ.lazy_cover_ahid A model) HAwf HMI Hh Hms).
    intros model1 HMI1 HSBM HC1.
    set (M1 := munrestrict H M M1v).
    assert (V1 : vis A model1 M1 = M1v).
    { rewrite (vis_sbm A model model1 M1 HSBM). unfold vis. fold H. apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
    eapply (LEAVES i c k ps Hc Hps fx' E R A M model E' R' M1 model1); [exact HAt | exact HAmb | exact (FPI_msteps _ _ _ _ _ _ _ _ Hms HFP) | exact Hag | |].
    - constructor.
      + rewrite V1. exact HLF.
      + intros a Ho. unfold M1, munrestrict. destruct (H a) eqn:Ea; [reflexivity|].
        rewrite (CC.lf_frame _ _ _ _ _ _ _ HLF a Ho). unfold vis, mrestrict. fold H. rewrite Ea. reflexivity.
      + intros a Ha. unfold M1, munrestrict. destruct (H a) eqn:Ea; [exact Ha|].
        apply (CC.lf_grows _ _ _ _ _ _ _ HLF). unfold vis, mrestrict. fold H. rewrite Ea. exact Ha.
      + intros a Ha. unfold M1, munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      + exact HSBM.
      + exact HMI1.
    - intros j cj fx2 E2 R2 A2 M2 model2 Hcj HAt2 HAmb2 HFP2 Hlt.
      eapply IHn; [exact Hcj | exact HAt2 | exact HAmb2 | exact HFP2 |].
      unfold CC.meas in *. pose proof (bv_unsigned_in_range _ (edenot E2 (CC.cp_meas cj))) as B2.
      pose proof (bv_unsigned_in_range _ (edenot E (CC.cp_meas c))) as B1. lia. }
  intros i c fx E R A M model Hc HAt HAmb HFP. eapply (G (Datatypes.S (Z.to_nat (CC.meas c E)))); eauto.
Qed.

(* [comment removed for export] *)
Variable NF : nat.
Definition amb_goto (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : Prop :=
  forall E R A M model E' R' M1 model1,
    AtV c E R A M model -> Amb i E A M model -> env_agree (CC.cp_nx c) E E' -> leaf_factsA c ps E' R' A M model M1 model1 ->
    Amb j (CC.env_over NF s E') A M1 model1.

Lemma leaf_goto : forall i c ps j cj s,
  nth_error CPS j = Some cj -> CC.goto_chk NF c ps cj s = true -> amb_goto i c ps j s -> leaf_ok i c ps.
Proof.
  intros i c ps j cj s Hcj Hchk Hamb fx' E R A M model E' R' M1 model1 HAt HAmb HFP Hag HLF HIH.
  destruct (CC.goto_chk_sound segs NF c ps cj s E E' R' _ _ Hchk Hag (lfa_vis _ _ _ _ _ _ _ _ _ HLF)) as (Hpc & HAt' & Hm & _).
  rewrite Hpc. eapply (HIH j cj); [exact Hcj | exact HAt' | | exact HFP | exact Hm].
  eapply Hamb; eassumption.
Qed.
End Cert.

(* [comment removed for export] *)
Theorem cutcert_sound_tagged :
  forall (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (NF : nat)
         (Amb : nat -> env -> list (Z * Z) -> mem -> Model -> Prop) (K : ShapeAlg.TSet) (FPI : FPState -> Prop),
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c) ->
  CC.tags_chk CPS TAGS NF = true ->
  (forall i E A M model, Amb i E A M model -> m_halted model = None /\ MInv A model /\ A_wf A /\ H_off_segments segs (ahid A model)) ->
  wx_segs_nowrap segs ->
  (forall i c tags k ps j s, nth_error CPS i = Some c -> nth_error TAGS i = Some tags ->
       nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TGoto j s) -> amb_goto Amb NF i c ps j s) ->
  (forall i c tags k ps id, nth_error CPS i = Some c -> nth_error TAGS i = Some tags ->
       nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TOther id) -> leaf_ok CPS Amb K FPI i c ps) ->
  forall i c (fx : FPState) E R A M model,
    nth_error CPS i = Some c -> AtV c E R A M model -> Amb i E A M model -> FPI fx ->
    srealizes segs SCFG (mkCfg (mk fx R (CC.cp_pc c) M) model) K.
Proof.
  intros CPS TAGS NF Amb K FPI FPM PLANS TCHK AMBM NOWRAP GOTOS OTHERS.
  apply (cutcert_sound CPS Amb K FPI FPM PLANS); [|exact AMBM | exact NOWRAP].
  intros i c k ps Hc Hps.
  destruct (CC.tags_chk_go_nth CPS NF CPS TAGS i c TCHK Hc) as (tags & Htags & Hl).
  destruct (CC.leaves_chk_nth CPS NF c (CC.cp_PSS c) tags k ps Hl Hps) as (t & Ht & Hm).
  destruct t as [j s|id].
  - destruct Hm as (cj & Hcj & Hg). eapply leaf_goto; [exact Hcj | exact Hg |]. eapply GOTOS; eassumption.
  - eapply OTHERS; eassumption.
Qed.

End WithSegs.
End CCA.
