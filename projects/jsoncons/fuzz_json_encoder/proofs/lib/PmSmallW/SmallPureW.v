(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPUW.
Abbreviation mem := (word -> option byte).

Section PureLeafW.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable FPI : FPState -> Prop.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom segs)) -> FPI fx -> FPI fx'.
Variables (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (NF : nat) (F0 : list SGP.region) (ENDS : list Z).
Hypothesis F0vars : forallb (SGP.region_vars_lt NF) F0 = true.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis tags_ok : CC.tags_chk CPS TAGS NF = true.
Hypothesis cut_facts : CC.cps_all CPS (fun _ c => SP.cut_chk NF F0 c) = true.
Hypothesis exit_facts : CC.others_all CPS TAGS (fun _ ps _ => SP.exit_chk ENDS ps) = true.
Hypothesis rets : forall pc, In pc ENDS -> CL.is_ret_at segs pc.
(* [comment removed for export] *)
Variable WI : nat -> env -> mem -> Prop.

Theorem pure_leaf_sound_w : forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet) (E0 : env) (cp0 : CC.cutpoint) (r : Z),
  m_halted model = None -> m_vm_lazy model = [] -> FPI fx ->
  (forall x : reg, ev E0 (ridx x) = getr R x) ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  nth_error CPS 0 = Some cp0 -> CC.At segs cp0 E0 R M -> WI 0%nat E0 M ->
  (forall i c tags k ps j s E R1 (M1 : mem) E' R' (M' : mem),
      nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TGoto j s) ->
      CC.At segs c E R1 M1 -> env_agree NF E0 E -> (forall a : word, SGP.outside E0 F0 a -> M1 a = M a) -> WI i E M1 ->
      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M1 M' -> env_agree NF E0 E' -> (forall a : word, SGP.outside E0 F0 a -> M' a = M a) ->
      WI j (CC.env_over NF s E') M') ->
  (forall (fx' : FPState) i c tags k ps id E R1 (M1 : mem) E' R' (M' : mem),
      nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TOther id) ->
      CC.At segs c E R1 M1 -> WI i E M1 -> env_agree (CC.cp_nx c) E E' ->
      FPI fx' -> env_agree NF E0 E' -> CC.leaf_facts segs c ps E' R' M1 M' ->
      (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> mem_grows M M' -> regs_preserved R R' ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc cp0)) M (seg_rom segs)) model) K.
Proof.
  intros fx R M model K E0 cp0 r Hh Hl Hfp EV Hra Hraok Hcp0 HAt HWI0 Hgotos Hcont.
  set (Amb := fun i E M1 m => CL.pure_amb NF E0 M model F0 i E M1 m /\ WI i E M1).
  eapply (CC.cutcert_sound_tagged segs CPS TAGS NF Amb K FPI FPM plans tags_ok) with (i := 0%nat) (c := cp0) (E := E0).
  - intros i E M1 m1 [H _]. eapply (CL.pure_amb_model NF E0 M model F0 i); eauto.
  - intros i c tags k ps j s Hc Htags Hps Htag E R1 M1 m1 E' R' M' HAt1 [HAmb HW] Hag HLF.
    pose proof (CL.pure_amb_goto segs NF E0 M model F0 i c ps j s (SP.SUBF CPS NF F0 F0vars cut_facts E0 i c Hc) (SP.NFle CPS NF F0 cut_facts i c Hc) E R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF) as HP.
    assert (HA' : CL.pure_amb NF E0 M model F0 0%nat E' M' m1).
    { eapply (CL.pure_amb_step segs NF E0 M model F0) with (c := c); [exact (SP.SUBF CPS NF F0 F0vars cut_facts E0 i c Hc) | exact (SP.NFle CPS NF F0 cut_facts i c Hc) | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
    split; [exact HP|]. destruct HAmb as (_ & HagE & Hfr1 & _). destruct HA' as (_ & HagE' & Hfr' & _).
    exact (Hgotos i c tags k ps j s E R1 M1 E' R' M' Hc Htags Hps Htag HAt1 HagE Hfr1 HW Hag HLF HagE' Hfr').
  - intros i c tags k ps id Hc Htags Hps Htag.
    intros fx' E R1 M1 m1 E' R' M' HAt1 [HAmb HW] HFP Hag HLF _.
    pose proof (CC.others_all_sound _ _ _ exit_facts i c tags k ps id Hc Htags Hps Htag) as X. cbv beta in X. apply andb_prop in X as [Xpc Xk].
    assert (HA' : CL.pure_amb NF E0 M model F0 0%nat E' M' m1).
    { eapply (CL.pure_amb_step segs NF E0 M model F0) with (c := c); [exact (SP.SUBF CPS NF F0 F0vars cut_facts E0 i c Hc) | exact (SP.NFle CPS NF F0 cut_facts i c Hc) | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
    destruct HA' as (-> & HagE & Hfr & Hgr).
    assert (Hcs : forall x : reg, In (ridx x) SP.CSV1 -> getr R' x = getr R x).
    { intros x Hx. assert (Hx32 : (ridx x < 32)%nat) by (unfold SP.CSV1 in Hx; cbn in Hx; intuition lia).
      rewrite (CL.ps_keeps_sound segs c ps E0 E' R' M1 M' SP.CSV1 NF x HLF Xk HagE Hx ltac:(lia)).
      apply EV. }
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (Hcs 1%bv ltac:(left; reflexivity)); exact Hra).
    eapply CL.ret_cps; [exact (rets _ (CL.ps_at_sound _ _ Xpc)) | exact Hh | exact Hl | |].
    + rewrite Hra'. destruct Hraok as (Hr1 & Hr2). apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hr2.
    + rewrite Hra'. eapply (Hcont fx' i c tags k ps id E R1 M1 E' R' M' Hc Htags Hps Htag HAt1 HW Hag HFP HagE HLF Hfr Hgr).
      intros x Hx. exact (Hcs x (SP.csv_in x Hx)).
  - exact Hcp0.
  - exact HAt.
  - split; [|exact HWI0]. split; [reflexivity|]. split; [apply CC.env_agree_refl|]. split; [reflexivity | apply mem_grows_refl].
  - exact Hfp.
  Unshelve. all: exact 0%nat.
Qed.
End PureLeafW.
End SPUW.
