(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncBridgesA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module EHTA.
Import PMES.
Abbreviation mem := (word -> option byte).

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
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variable CL : Z.                    (* [comment removed for export] *)
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBo : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable D0 : Z.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Abbreviation gB := (EBA.gB GR).
Variable kx bx : Z.
Abbreviation CredV := (EBA.CredV L CL kx bx).
Variable XIv : eghost -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis SCR8 : SCR mod 8 = 0.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FFrest sp0 SCR a
                                                       /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBo FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M00 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
(* [comment removed for export] *)
Variable STAT : list kentry.
Hypothesis STAT_ok : forallb (CHA.static_chk SCELLS GLO GHI) STAT = true.
(* [comment removed for export] *)
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS0 : PMESA.objs_encA M00 FFrest V S2.
Hypothesis STKSH0 : PMSA.stksh ar M00 sp0 SCR.
Hypothesis IMG0 : PMLA.img_ro IC M00.
Hypothesis IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Hypothesis W_app : forall w a, In w W -> L5.in_rng w a -> ~ (BIGSHADOW_LO <= a < BIGSHADOW_HI) /\ ~ (PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
(* [comment removed for export] *)
Variable OB : expr.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : bv_unsigned (edenot E0 OB) = S2.

Abbreviation FPI := PMSA.fp_ok.
Abbreviation OKV := (CHV.okV L ar M00 LBo FFrest sp0 d W).
Abbreviation AAMBV := (CHV.aambV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV).
Abbreviation AMBXV := (CHV.ambXV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation AMBV := (CHV.ambV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation LEAFOKV := (CHV.leaf_okV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv CPS K FPI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Abbreviation curB := (CHA.curB BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

(* [comment removed for export] *)
Hypothesis W_COL : forall a, V + O_COLUMN <= a < V + O_COLUMN + 8 -> exists w, In w W /\ L5.in_rng w a.
(* [comment removed for export] *)
Hypothesis V10 : bv_unsigned (ev E0 10) = V.

(* [comment removed for export] *)
Lemma cps_perm : forall pc r sp scr LB1 LB2 FF LK cr A dc Pre Post, Permutation LB1 LB2 ->
  PMSA.cps_asan L ar HI pc r sp scr LB2 FF LK cr A dc Pre Post -> PMSA.cps_asan L ar HI pc r sp scr LB1 FF LK cr A dc Pre Post.
Proof.
  intros pc r sp scr LB1 LB2 FF LK cr A dc Pre Post HP SPEC fx R M model KK HH. apply SPEC. exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH HP).
Qed.

(* [comment removed for export] *)
Definition hcall_chk (scr : Z) (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z))
  (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi && expr_eqb (nth 10 regs (ELit 0)) (EVar 10))%bool
  then CHA.custom_chk NF d SCELLS GLO GHI scr 0 [] FFi [(EVar 10, 296, ELit 8); (OB, 0, ELit 24)] (STAT ++ unews) None c ps cj BLi FFi BLj FFj
  else None.

(* [comment removed for export] *)
Lemma hcall_leaf_okV : forall (pc scr dc : Z) unews i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  hcall_chk scr unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  CH2.blocks_vars_lt NF (nth i BLS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (* [comment removed for export] *)
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     Permutation (CH2.den E' (nth i BLS []) ++ GR) (stack_blocks (g_sb g) (g_scap g))) ->
  (* [comment removed for export] *)
  (forall E R A (M : mem) model E' R' (M' : mem) model' cr LK, CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (LBo ++ g_lbv g) (curF i E) LK cr A M' (vml_of model') -> incl LK LK0 -> PMESA.ecreditA L CL cr g kx bx ->
     getr R' 10%bv = Z_to_bv 64 V -> shadow_zero M' V 51 -> shadow_zero M' S2 3 -> PMSA.stksh ar M' sp0 SCR -> PMLA.img_ro IC M' ->
     exists (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       PMSA.cps_asan L ar HI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr (LBo ++ g_lbv g) (curF i E) LK cr A dc Pre Post /\ Pre R' M' /\
       forall R2 (M2 : mem) model2 LB' cr' LBk Wc LK2 A2, Post R' M' R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
         CHA.ahpres L ar LBk (curF i E) (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_rt model' model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
         ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) ->
         let E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2 in
         exists g' : eghost, g_sb g' = g_sb g /\ g_scap g' = g_scap g /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ Wc = PMESA.W_h V S2 /\ PMESA.ecreditA L CL cr' g' kx bx /\
           XIv g' j E2 A2 M2 model2 /\ (forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr dc unews i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk BVN Hdc XIPERM CALL.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold hcall_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb R10]. apply andb_prop in Hb as [B3 B4]. apply CH2.blocks_eqb_eq in B3. apply expr_eqb_eq in R10.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc scr 0%nat [] [(EVar 10, 296, ELit 8); (OB, 0, ELit 24)] (STAT ++ unews) None dc i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof (XIPERM E R A M model E' R' M1 model1 HAt HA HXI Hag HLF) as PERM.
  destruct (EBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx STK SCR_pos SCR8 NF32 V S2 OBJS0 STKSH0 IMG0 IMG_RO_ok W_app g M0c i E A M1 model1 HOKV HA')
    as (ZV & ZS & ZSTK & ZIMG).
  destruct (EBA.objs_facts M00 FFrest V S2 OBJS0) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  set (own := CH2.den E' BLi) in *. fold BLi in HdenB. fold FFi in HdenF.
  assert (HcB : CHA.curB (CHV.LBr LBo eghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB, own. fold BLi. rewrite <- HdenB. reflexivity. }
  rewrite HcB in HH1.
  (* [comment removed for export] *)
  assert (PERMG : forall g1, g_sb g1 = g_sb g -> g_scap g1 = g_scap g -> Permutation (own ++ LBo ++ PML.srep_blocks (g_rep g1) ++ GR) (LBo ++ g_lbv g1)).
  { intros g1 E1 E2. unfold g_lbv. rewrite E1, E2.
    transitivity (LBo ++ PML.srep_blocks (g_rep g1) ++ own ++ GR).
    - rewrite (app_assoc LBo (PML.srep_blocks (g_rep g1)) (own ++ GR)). rewrite (app_assoc own LBo _). rewrite (app_assoc (own ++ LBo) _ GR).
      rewrite <- (app_assoc own LBo (PML.srep_blocks (g_rep g1))). rewrite <- (app_assoc own (LBo ++ _) GR).
      apply (Permutation_app_swap_app own (LBo ++ PML.srep_blocks (g_rep g1)) GR).
    - apply Permutation_app_head. apply Permutation_app_head. exact PERM. }
  pose proof (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH1 (PERMG g eq_refl eq_refl)) as HH1'.
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 V).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq, R10. cbn [edenot].
    destruct HagE' as [AG _]. rewrite <- (AG 10%nat) by lia. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E0 10)). f_equal. exact V10. }
  destruct (CALL E R A M model E' R' M1 model1 cr LK HAt HA HXI Hag HLF CF HH1' HLK1 HC1 Ga0 ZV ZS ZSTK ZIMG) as (Pre & Post & SPEC & HPre & HPost).
  exists Pre, Post. split; [rewrite HcB; exact (cps_perm _ _ _ _ _ _ _ _ _ _ _ _ _ (PERMG g eq_refl eq_refl) SPEC)|]. split; [exact HPre|].
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (g' & Gsb & Gscap & -> & -> & -> & HC' & HXI2 & Hunews).
  exists [], g'. split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  assert (HV10 : bv_unsigned (ev E' 10) = V) by (destruct HagE' as [AG _]; rewrite <- (AG 10%nat) by lia; exact V10).
  split; [exact I|].
  split; [intros bb Hb; exact Hb|].
  split.
  { intros w a Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin.
    - exists (EVar 10, 296, ELit 8). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite HV10. rewrite u64_of_Z by lia. lia.
    - exists (OB, 0, ELit 24). split; [right; left; reflexivity|]. unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia. }
  split.
  { intros w a Hw Hin (_ & _ & Hout). destruct Hw as [<-|[<-|[]]].
    - destruct (W_COL a ltac:(unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia)) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    - exact (Hout (S2, 24) W_S2 Hin). }
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB g') BLS j E2 = own ++ LBo ++ PML.srep_blocks (g_rep g') ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB. rewrite B3. unfold own. rewrite (CH2.den_agree NF E' E2 BLi ltac:(eapply CC.env_agree_le; [exact Hag2 | lia]) BVN). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 (Permutation_sym (PERMG g' Gsb Gscap)))|].
  split; [exact HC'|].
  split; [exact HXI2|].
  intros X HX HXc. apply in_app_or in HX as [HX|HX]; [|exact (Hunews X HX HXc)].
  rewrite forallb_forall in STAT_ok. exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
Qed.
End Inst.
End EHTA.
