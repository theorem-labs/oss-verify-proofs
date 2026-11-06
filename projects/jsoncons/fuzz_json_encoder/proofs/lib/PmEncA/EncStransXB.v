(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB EncBridgesXB EncHtransXB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module ESTA.
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
Definition PAYMAX : Z := 1125899906842624.
Definition strans_chk (scr : Z) (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z))
  (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  let g0 := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi)%bool
  then CHA.custom_chk NF d SCELLS GLO GHI scr 1 BLi FFi [(OB, 0, ELit 24)] (KRange (EVar g0) 0 PAYMAX :: STAT ++ unews) (Some (EVar g0)) c ps cj BLi FFi BLj FFj
  else None.

(* [comment removed for export] *)
Lemma enc_inv_grown_scr : forall (M' M2 : mem) g rep' n LBk FFk spc scr,
  PMESA.enc_invA L IC EC M' V S2 g -> CHA.ahpres L ar LBk FFk spc scr [(S2, 24)] M' M2 ->
  (exists f, In f FFk /\ ff_addr f + 32 <= V /\ V + 408 <= ff_addr f + ff_bytes (ff_class f) - 8) ->
  (S2 + 24 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= S2) ->
  (forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b LBk /\ PMLA.apart (fst b) (snd b) S2 24) ->
  PMESA.sink_atA L M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
  (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47) ->
  PMESA.enc_invA L IC EC M2 V S2 (EBA.g_upd g rep' n).
Proof.
  intros M' M2 g rep' n LBk FFk spc scr INV (HP1 & HP2 & HP3) (f & Hf & Vf1 & Vf2) S2app HSB Hsink Hlen Hnew.
  pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & (R1 & R2 & R3 & R4 & RB)). unfold ENC_SIZE in R2.
  pose proof (EBA.objs_facts M00 FFrest V S2 OBJS0) as (_ & _ & _ & _ & _ & _ & AP). unfold PMLA.apart in AP.
  assert (KV : forall a, V <= a < V + 408 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. apply HP1. split; [lia|]. split; [do 3 right; left; exists f; split; [exact Hf | lia]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M' M2 a n0) by (intros a n0 H1 H2 i Hi; apply KV; lia).
  assert (STB : forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b (g_lbv g)) by (intros b Hb; unfold g_lbv; apply in_or_app; right; exact Hb).
  unfold EBA.g_upd. split; [|split; [|split; [|split; [exact Hsink | split; [exact Hlen | split; [exact I6|]]]]]]; cbn [g_es g_len g_rep g_sb g_scap].
  - apply (EKA.enc_obj_agree L IC EC M' M2 V S2 _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_COLUMN; lia | apply AV; unfold O_COLON, ENC_SIZE; lia | | exact I1].
    apply (L5C.defined_agree M' M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia|].
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - apply (EKA.stack_at_agree L M' M2 V _ _ _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_STACK; lia | | exact I2].
    intros Hne. assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply HP1. split; [lia|]. split; [left; exists (g_sb g, g_scap g); split; [exact HinK | cbn [fst snd]; lia]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PMLA.apart in HapS. lia.
  - apply (EKA.stack_sh_agree M' M2 _ _ _); [|exact I3]. intros Hne.
    assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    destruct I2 as (_ & _ & _ & S4 & S5 & _).
    assert (C8 : g_scap g mod 8 = 0) by (destruct S5 as [[E _]|(k & Hk & ->)]; [contradiction | apply EKA.mul32_mod8; lia]).
    assert (B8 : g_sb g mod 8 = 0) by (apply Z.mod_divide in B1; [|lia]; destruct B1 as [q ->]; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult).
    split; [exact B8|]. split; [exact C8|]. split; [pose proof (EKA.depth_nonneg (g_es g)); lia|].
    intros j Hj. apply HP1.
    assert (C32 : 32 <= g_scap g) by (destruct S5 as [[E _]|(k & Hk & E)]; [contradiction | pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); nia]).
    assert (G4 : 4 <= g_scap g / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (CL5A.shreg_in_shadow (g_sb g) (g_scap g / 8) (S (g_sb g) + j) B8 ltac:(lia) ltac:(unfold S; lia)) as SH.
    replace (8 * (g_scap g / 8)) with (g_scap g) in SH by (apply Z.mod_divide in C8; [|lia]; destruct C8 as [q Hq]; rewrite Hq at 1; rewrite Hq; rewrite Z.div_mul; lia).
    pose proof (CHA.shadow_range (g_sb g) (g_scap g) (S (g_sb g) + j) B0 ltac:(lia) B3 SH) as SR.
    split; [lia|]. split; [do 6 right; exists (g_sb g, g_scap g); split; [exact HinK | exact SH]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI in S2app. lia.
  - split; [exact R1|]. split; [unfold ENC_SIZE; lia|]. split; [exact R3|]. split; [exact R4|].
    intros b Hb. unfold g_lbv in Hb. cbn [g_rep g_sb g_scap] in Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (Hnew b Hb) | exact (RB b (STB b Hb))].
Qed.

(* [comment removed for export] *)
Lemma strans_leaf_okV : forall (pc scr dc : Z) unews i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  strans_chk scr unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  CH2.blocks_vars_lt NF (nth i BLS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (* [comment removed for export] *)
  (forall E R A (M : mem) model E' R' (M' : mem) model' cr LK, CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 1 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) (curF i E) LK cr A M' (vml_of model') -> incl LK LK0 -> PMESA.ecreditA L CL cr g kx bx ->
     shadow_zero M' V 51 -> shadow_zero M' S2 3 -> PMSA.stksh ar M' sp0 SCR -> PMLA.img_ro IC M' ->
     exists (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       PMSA.cps_asan L ar HI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) (curF i E) LK cr A dc Pre Post /\ Pre R' M' /\
       forall R2 (M2 : mem) model2 LB' cr' LBk Wc LK2 A2, Post R' M' R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
         CHA.ahpres L ar LBk (curF i E) (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_rt model' model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
         ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) ->
         exists (g' : eghost) (pay : Z), let E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 pay] R2 in
           g_sb g' = g_sb g /\ g_scap g' = g_scap g /\ LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g') /\ LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR /\
           Wc = [(S2, 24)] /\ getr R2 10%bv = Z_to_bv 64 pay /\ 0 <= pay <= PAYMAX /\ PMESA.ecreditA L CL cr' g' kx bx /\
           XIv g' j E2 A2 M2 model2 /\ (forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr dc unews i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk BVN Hdc CALL.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold strans_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [B3 B4]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc scr 1%nat BLi [(OB, 0, ELit 24)] _ (Some (EVar (CC.cp_nx cj - APC.NCS - 1)%nat)) dc i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (EBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx STK SCR_pos SCR8 NF32 V S2 OBJS0 STKSH0 IMG0 IMG_RO_ok W_app g M0c i E A M1 model1 HOKV HA')
    as (ZV & ZS & ZSTK & ZIMG).
  set (own := CH2.den E' BLi) in *. fold BLi in HdenB. fold FFi in HdenF.
  assert (HcB : CHA.curB (CHV.LBr LBo eghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB, own. fold BLi. rewrite <- HdenB. reflexivity. }
  rewrite HcB in HH1.
  (* [comment removed for export] *)
  assert (PERMG : forall g1, Permutation (own ++ LBo ++ PML.srep_blocks (g_rep g1) ++ GR) ((own ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g1))).
  { intros g1. rewrite <- (app_assoc own (LBo ++ GR) _). apply Permutation_app_head. rewrite <- (app_assoc LBo GR _). apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH1 (PERMG g)) as HH1'.
  destruct (CALL E R A M model E' R' M1 model1 cr LK HAt HA HXI Hag HLF CF HH1' HLK1 HC1 ZV ZS ZSTK ZIMG) as (Pre & Post & SPEC & HPre & HPost).
  exists Pre, Post. split; [rewrite HcB; exact (EHTA.cps_perm L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ _ _ (PERMG g) SPEC)|]. split; [exact HPre|].
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (g' & pay & Gsb & Gscap & -> & -> & -> & Ha0 & Hpay & HC' & HXI2 & Hunews).
  exists [Z_to_bv 64 pay], g'. split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 pay] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  assert (HG0 : ev E2 (CC.cp_nx cj - APC.NCS - 1)%nat = Z_to_bv 64 pay).
  { replace (CC.cp_nx cj - APC.NCS - 1)%nat with (CH2.ci_nx ci + 0)%nat by (rewrite V5; lia). unfold E2. rewrite CH2.retEx_ghost by (cbn; lia). reflexivity. }
  split; [cbn [edenot]; rewrite HG0; exact Ha0|].
  split; [intros bb Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb]|].
  split.
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (OB, 0, ELit 24). split; [left; reflexivity|]. unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia. }
  split.
  { intros w a [<-|[]] Hin (_ & _ & Hout). exact (Hout (S2, 24) W_S2 Hin). }
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB g') BLS j E2 = own ++ LBo ++ PML.srep_blocks (g_rep g') ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB. rewrite B3. unfold own. rewrite (CH2.den_agree NF E' E2 BLi ltac:(eapply CC.env_agree_le; [exact Hag2 | lia]) BVN). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 (Permutation_sym (PERMG g')))|].
  split; [exact HC'|].
  split; [exact HXI2|].
  intros X HX HXc. destruct HX as [<-|HX].
  { cbn [kentry_ok]. cbn [edenot]. rewrite HG0. unfold PAYMAX in *. rewrite u64_of_Z by lia. lia. }
  apply in_app_or in HX as [HX|HX]; [|exact (Hunews X HX HXc)].
  rewrite forallb_forall in STAT_ok. exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
Qed.
End Inst.
End ESTA.
