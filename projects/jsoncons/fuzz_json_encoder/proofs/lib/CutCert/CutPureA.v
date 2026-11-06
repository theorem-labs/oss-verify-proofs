(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module CPA.
Definition mem := (word -> option byte).


(* [comment removed for export] *)
Lemma writable_vis : forall segs (H : word -> bool) (M : mem) a n, 0 <= a -> a + n <= 2 ^ 64 -> CL5A.visr H a n -> L5.writable segs M a n -> L5.writable segs (mrestrict H M) a n.
Proof.
  intros segs H M a n Ha Hn HV HW dd k Hd Hk. rewrite (store_ok_mrestrict_eq segs H k M); [exact (HW dd k Hd Hk)|].
  intros q Hq. unfold woff. rewrite L5.unsigned_lit by lia. replace (a + dd + Z.of_nat q) with (a + (dd + Z.of_nat q)) by lia. apply HV. lia.
Qed.
Lemma kwr_of_writable : forall segs E (M : mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A < 2 ^ 64 -> A + N <= 2 ^ 64 -> L5.writable segs M A N -> kentry_ok segs E M (KWr a n).
Proof.
  intros segs E M a n A N Ha Hn H0 H1 Hw. cbn [kentry_ok]. rewrite Ha, Hn.
  split; [unfold flat; rewrite Ha; pose proof (u64_range (edenot E n)) as Hr; unfold elenZ in Hn; rewrite Hn in Hr; lia|]. intros dd m Hd Hm. apply Hw; assumption.
Qed.

Section Shape.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable FPI : FPState -> Prop.
(* [comment removed for export] *)
Definition cps_pureA (pc r sp scr dd : Z) (W : list L5.range) (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> Prop) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)),
    CBA.cps_asanG L ar HI FPI pc r sp scr LB FF LK cr A dd Pre
      (fun R M R' M' LB' cr' LBk W' => Post R M R' M' /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W' = W).
End Shape.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LB : list (Z * Z).
Variable FF : list fframe.
Variable LK0 : list fframe.
Variable cr0 : credit.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FF sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LB FF sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Hypothesis KNIL : K [].
Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Definition NOB : list CA.blocks := map (fun _ => []) CPS.
Definition NOF : list (list (expr * Z * Z)) := map (fun _ => []) CPS.
Definition Cred0 : nat -> env -> credit -> Prop := fun _ _ c => c = cr0.
Lemma nth_map_nil : forall {X Y} (l : list X) i, nth i (map (fun _ : X => @nil Y) l) [] = [].
Proof. intros X Y l. induction l as [|x l IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH. Qed.
Lemma NOBnil : forall i, nth i NOB [] = []. Proof. intros i. apply nth_map_nil. Qed.
Lemma NOFnil : forall i, nth i NOF [] = []. Proof. intros i. apply nth_map_nil. Qed.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 XI).

(* [comment removed for export] *)
Definition pure_leaf_chk (rets : list Z) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc => if existsb (Z.eqb pc) rets then (CBA.exit_base_chk NF pc c ps && CHA.foot_chk NF d c [] [])%bool else true
  end.

Theorem pure_cert_soundA : forall (rets : list Z),
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound (hl_segs L) c) ->
  CC.tags_chk CPS TAGS NF = true ->
  CHA.heap_chkA NF d NOB NOF CPS TAGS = true ->
  CH2.leaves_all CPS TAGS (pure_leaf_chk rets) = true ->
  (forall pc, In pc rets -> CL.is_ret_at (hl_segs L) pc) ->
  (* [comment removed for export] *)
  (forall i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E R E' R' A M model M1 model1, CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model ->
       env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> XI i E A M model -> XI j (CC.env_over NF s E') A M1 model1) ->
  (* [comment removed for export] *)
  (forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> existsb (Z.eqb pc) rets = false -> CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps) ->
  (* [comment removed for export] *)
  (forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> In pc rets ->
     forall (fx' : FPState) E R A M model E' R' M1 model1,
       CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
       forall model2 LK,
         regs_preserved R0 R' -> CHA.ahpres L ar LB FF sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
         ri_inv HI LB FF LK cr0 A M1 (vml_of model2) -> env_agree NF E0 E' -> AAMB i E A M1 model1 ->
         srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0) M1 (seg_rom (hl_segs L))) model2) K) ->
  forall i c (fx : FPState) R,
    nth_error CPS i = Some c -> CCA.AtV (hl_segs L) c E0 R A0 M0 model0 -> XI i E0 A0 M0 model0 ->
    ri_inv HI LB FF LK0 cr0 A0 M0 (vml_of model0) -> CHA.amodel_ok A0 model0 -> CHA.ffroom FF LK0 D0 -> FPI fx ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M0 (seg_rom (hl_segs L))) model0) K.
Proof.
  intros rets FPM PLANS TAGSOK HEAPOK LEAFOK RETAT XIGOTO CALLS EXITS i c fx R Hc HAt HXI HH Hmo Hroom HFP.
  eapply (CHA.cert_soundA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
            CPS K FPI XI TAGS FPM PLANS TAGSOK HEAPOK) with (i := i) (E := E0).
  - intros i1 c1 k ps j s IL E E' R' M M' cr _ _ _ HC. exact HC.
  - exact XIGOTO.
  - intros i1 c1 k ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ LEAFOK _ _ _ _ _ IL) as X. unfold pure_leaf_chk in X.
    destruct (existsb (Z.eqb pc) rets) eqn:Hex; [|exact (CALLS i1 c1 k ps pc IL Hex)].
    apply existsb_exists in Hex as (pc' & Hin & Heq). apply Z.eqb_eq in Heq. subst pc'.
    apply andb_prop in X as [Xbase Xfoot].
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF _. pose proof HAX as [HA _].
    assert (Hpc : SR.ps_pc ps = pc) by (unfold CBA.exit_base_chk in Xbase; apply andb_prop in Xbase as [Xb _]; apply andb_prop in Xb as [Xb _]; apply Z.eqb_eq in Xb; exact Xb).
    refine (CBA.exit_ret L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              K DEF0 R0 ra0 EV0 RA0 RA0ok pc i1 c1 ps (RETAT pc Hin) Xbase _ (NOFnil i1) fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HA Hag HLF _); [rewrite NOBnil, NOFnil; exact Xfoot|].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'. unfold Cred0 in HC1. subst cr1.
    unfold CHA.curB in HH1. rewrite NOBnil in HH1. cbn [CH2.den map app] in HH1.
    exact (EXITS i1 c1 k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M' m' HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA').
  - exact Hc.
  - exact HAt.
  - split; [|exact HXI].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model0))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr0, LK0. unfold CHA.curB, CHA.curF. rewrite NOBnil, NOFnil. cbn [CH2.den CHA.denF map app length]. rewrite Z.sub_0_r.
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact HFP.
Qed.

(* [comment removed for export] *)
Lemma pure_callee_leaf : forall pc scr dc Wc wregs news a0x i c ps j cj ci
    (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> Prop),
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr 0 [] [] wregs news a0x c ps cj [] [] [] [] = Some ci ->
  SR.ps_pc ps = pc -> dc <= D0 ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    cps_pureA L ar HI FPI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr dc Wc Pre Post ->
    (forall LK, CHA.common_facts L ar HI NF E0 M0 model0 A0 LB FF LK0 sp0 d W NOB NOF Cred0 D0 scr 0 c ps cj ci i E E' R' A M1 model1 ->
       ri_inv HI LB FF LK cr0 A M1 (vml_of model1) -> incl LK LK0 ->
       Pre R' M1 /\
       forall R2 M2 model2 LK2 A2,
         Post R' M1 R2 M2 -> regs_preserved R' R2 -> CHA.ahpres L ar LB FF (sp0 + CH2.ci_csp ci) scr Wc M1 M2 -> ri_inv HI LB FF LK2 cr0 A2 M2 (vml_of model2) ->
         let E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2 in
         match a0x with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
         (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CHA.in_reg E' r a) /\
         (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LB FF sp0 SCR W a) /\
         XI j E2 A2 M2 model2 /\
         (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros pc scr dc Wc wregs news a0x i c ps j cj ci Pre Post Hcj Hchk Hpc Hdc fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH SPEC USER.
  refine (CBA.callee_leaf L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LB FF LK0 sp0 d W Wo NOB NOF Cred0 D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
            CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI KNIL pc scr 0%nat [] wregs news a0x dc i c ps j cj ci Hcj _ Hpc _ _ fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH _);
    [rewrite !NOBnil, !NOFnil; exact Hchk | rewrite !NOFnil; reflexivity | rewrite NOFnil; cbn [length]; lia |].
  unfold CHA.curB, CHA.curF. rewrite !NOBnil, !NOFnil. cbn [CH2.den CHA.denF map app].
  intros cr LK CF HH1 HLK1 HC1. unfold Cred0 in HC1. subst cr. destruct (USER LK CF HH1 HLK1) as [HPre HPost].
  eexists. eexists. split; [exact (SPEC LB FF LK cr0 A)|]. split; [exact HPre|].
  intros R2 M2 model2 LB' cr' LBk Wc' LK2 A2 (HPo & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LK2 A2 HPo HRP HP HH2) as (Ha0 & HWr & HWk & HXj & Hnews).
  exists []. split; [reflexivity|]. cbv zeta. split; [exact Ha0|]. split; [cbn [CH2.den map app]; apply incl_refl|]. split; [exact HWr|]. split; [exact HWk|].
  split; [try rewrite NOBnil; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|]. split; [exact HXj | exact Hnews].
Qed.
End Inst.
End CPA.
