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


Module EK5A.
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
Lemma grow_leaf_okS : forall (pc n : Z) Xtra (unews : list kentry) i c k ps j cj ci g M0c,
  EBA.grow_call L ar HI CL pc n Xtra ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  EBA.sink_chk NF d SCELLS GLO GHI STAT OB unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) EBA.STR_SCRA [(S2, 24)] M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     PMESA.sink_atA L M' S2 (g_rep g) /\ len (PML.srep_chars (g_rep g)) = g_len g /\ PMESA.lbv_rng V S2 g /\
     incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR) /\ 0 <= n /\ g_len g + n <= CL /\
     Xtra (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) (curF i E) (sp0 + CH2.ci_csp ci) S2 (g_rep g) R' M') ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 rep', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) EBA.STR_SCRA [(S2, 24)] M' M2 ->
     PMESA.sink_atA L M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
     (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47) ->
     XIv (EBA.g_upd g rep' n) j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc n Xtra unews i c k ps j cj ci g M0c GC HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS XILEAF XIRET.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold EBA.sink_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. subst ob ok.
  apply CH2.blocks_eqb_eq in B3. pose proof (CHA.frames_eqb_eq _ _ B4) as B4e.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc EBA.STR_SCRA 0%nat BLi [(OB, 0, ELit 24)] (STAT ++ unews) None 0 i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (XILEAF E R A M model E' R' M1 model1 HAt HA HXI Hag HLF CF) as (Hsink & Hlen & HRNG & HST & Hn0 & HROOM & HXTRA).
  destruct (EBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx STK SCR_pos SCR8 NF32 V S2 OBJS0 STKSH0 IMG0 IMG_RO_ok W_app g M0c i E A M1 model1 HOKV HA')
    as (ZV & ZS & ZSTK & ZIMG).
  destruct (EBA.amb_rng L ar C HI HIok CL NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx g M0c i E A M1 model1 HA') as [RF TOP].
  destruct (EBA.objs_facts M00 FFrest V S2 OBJS0) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof STK as (S1 & S2' & S3).
  destruct (CHA.rf_ceil _ _ _ _ RF) as (CL0 & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & _).
  set (own := CH2.den E' BLi) in *.
  assert (HcB : CHA.curB (CHV.LBr LBo eghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB, own. fold BLi. fold BLi in HdenB. rewrite <- HdenB. reflexivity. }
  fold BLi in HdenB. fold FFi in HdenF.
  rewrite HcB in HH1 |- *.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 S2).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). rewrite <- Ho. unfold estart. cbn [a_base a_off]. rewrite Z.add_0_r. reflexivity. }
  set (kx' := kx + kv_st (g_scap g) * hl_k_per_malloc L). set (bx' := bx + PMESA.bpot_st L (g_scap g)).
  eexists _, _. split; [exact (GC (own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A S2 (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) kx' bx' (g_rep g))|].
  split.
  { (* [comment removed for export] *)
    split; [exact Ga0|]. split; [exact HXTRA|]. split; [exact Hsink|].
    split; [destruct (g_rep g) as [s|cap p s]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; apply in_or_app; right; left; reflexivity]|].
    split; [split; [destruct O4 as (f & Hf & F1 & F2); exists f; split; [unfold CHA.curF; apply in_or_app; right; exact Hf | exact (conj F1 F2)] | split; [exact O5 | exact ZS]]|].
    split.
    { destruct Hstk as (A1 & _). apply (PTA.stksh_mono ar M1 sp0 SCR (sp0 + CH2.ci_csp ci) EBA.STR_SCRA ZSTK (EBA.al16_8 _ _ S1 SCR8) (EBA.al16_8 _ 4368 A1 eq_refl)). unfold EBA.STR_SCRA in *. lia. }
    split; [exact (EKA.scredit_of_ecredit L CL KPM BLIN BOV cr g kx bx HC1)|].
    rewrite Hlen. exact HROOM. }
  (* [comment removed for export] *)
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 (rep' & s' & Hls' & Hgrown & HCR' & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  pose proof (fun LBKE INCL => UNEWS E R A M model E' R' M1 model1 cr LK R2 M2 model2 LB' cr' LK2 A2 HAt HA HXI HagE' Hag HLF CF HH1 HRP LBKE HH2 INCL) as UN.
  pose proof (EBA.den_app_nodup L ar C HI HIok LBo GR own (g_rep g) _ _ _ _ _ _ HH1) as Hdrop.
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { clear - Hchk. unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d EBA.STR_SCRA 0 c ps cj BLi FFi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    do 6 (apply andb_prop in Hb as [Hb _]). apply andb_prop in Hb as [_ Hb]. exact Hb. }
  pose proof HRNG as (R1 & R2' & R3 & R4 & RB).
  assert (FACTS : PMESA.sink_atA L M2 S2 rep' /\ len (PML.srep_chars rep') = g_len g + n /\ LBk = own ++ LBo ++ GR /\
                  Permutation LB' (own ++ LBo ++ PML.srep_blocks rep' ++ GR) /\
                  (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47)).
  { destruct Hgrown as [(F & -> & Hs & -> & ->)|(NFt & p' & Gx)].
    - split; [exact Hs|]. split; [destruct (g_rep g); cbn [same_rep PML.srep_chars] in Hls', Hlen |- *; lia|]. split; [exact Hdrop|].
      split; [destruct (g_rep g); cbn [same_rep PML.srep_blocks]; apply Permutation_refl|].
      intros b Hb. apply RB. unfold g_lbv. apply in_or_app. left. destruct (g_rep g); cbn [same_rep PML.srep_blocks] in Hb |- *; exact Hb.
    - cbv zeta in Gx. destruct Gx as (-> & Hs & FB & -> & ->). split; [exact Hs|]. split; [destruct (g_rep g); cbn [PML.srep_chars] in Hls', Hlen |- *; lia|]. split; [exact Hdrop|].
      rewrite Hdrop. split; [exact (CHV.perm_ghost_in own LBo [] GR _)|].
      intros b [<-|[]]. cbn [fst snd]. destruct FB as ((Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & _). lia. }
  clear Hgrown. destruct FACTS as (Hsink2 & Hlen2 & -> & Hperm & Hnew).
  exists [], (EBA.g_upd g rep' n). split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  split; [exact I|].
  split; [rewrite app_assoc; apply incl_appl; apply incl_refl|].
  split.
  { intros w a [<-|[]] Hin. exists (OB, 0, ELit 24). split; [left; reflexivity|].
    unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia. }
  split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko (S2, 24) W_S2 Hin)|].
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB (EBA.g_upd g rep' n)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB, EBA.g_upd. cbn [g_rep]. rewrite B3. unfold own. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 Hperm)|].
  split.
  { unfold EBA.CredV. apply (EKA.ecredit_of_scredit L CL cr' g kx bx rep' (EBA.g_upd g rep' n) eq_refl eq_refl HCR'); [exact (proj1 HC1) | exact (proj1 (proj2 (proj2 HC1)))]. }
  split.
  { exact (XIRET E R A M model E' R' M1 model1 E2 A2 M2 model2 rep' HAt HA HXI HagE' Hag HLF Hag2 V3 CF HP Hsink2 Hlen2 Hnew). }
  (* [comment removed for export] *)
  intros X HX HXj. apply in_app_or in HX. destruct HX as [HX|HX].
  - pose proof STAT_ok as STOK. rewrite forallb_forall in STOK.
    exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STOK X HX)).
  - unfold E2. apply (UN HP); [|exact HX | exact HXj].
    intros bb Hbb. apply (Permutation_in bb (Permutation_sym Hperm)). apply in_app_or in Hbb as [Hbb|Hbb]; apply in_or_app; [left; exact Hbb|]. right.
    apply in_app_or in Hbb as [Hbb|Hbb]; apply in_or_app; [left; exact Hbb | right; apply in_or_app; right; exact Hbb].
Qed.

(* [comment removed for export] *)
Lemma append_leaf_okS : forall pc (unews : list kentry) (n : Z) i c k ps j cj ci g M0c,
  PMESA.str_append_x_specA L ar HI IC CL pc ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  EBA.sink_chk NF d SCELLS GLO GHI STAT OB unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) EBA.STR_SCRA [(S2, 24)] M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     PMESA.sink_atA L M' S2 (g_rep g) /\ len (PML.srep_chars (g_rep g)) = g_len g /\ PMESA.lbv_rng V S2 g /\
     incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR) /\ 0 <= n /\ g_len g + n <= CL /\
     exists q src, PMSA.a1 R' q /\ PMSA.a2 R' (len src) /\ len src = n /\ L5.bytes_at (hl_segs L) M' q src /\
                   PMESA.src_okA ar HI IC M' (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) (curF i E) (sp0 + CH2.ci_csp ci) S2 (g_rep g) q (len src)) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 rep', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 EBA.STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) EBA.STR_SCRA [(S2, 24)] M' M2 ->
     PMESA.sink_atA L M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
     (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47) ->
     XIv (EBA.g_upd g rep' n) j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc unews n i c k ps j cj ci g M0c APPEND HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS XILEAF XIRET.
  apply (grow_leaf_okS pc n _ unews i c k ps j cj ci g M0c (EBA.append_grow L ar HI IC CL pc n APPEND) HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS); [|exact XIRET].
  intros E R A M model E' R' M' model' HAt HA HXI Hag HLF CF.
  destruct (XILEAF E R A M model E' R' M' model' HAt HA HXI Hag HLF CF) as (HS & HL & HR & HST & Hn & HROOM & SRC).
  split; [exact HS|]. split; [exact HL|]. split; [exact HR|]. split; [exact HST|]. split; [exact Hn|]. split; [exact HROOM | exact SRC].
Qed.

End Inst.
End EK5A.
