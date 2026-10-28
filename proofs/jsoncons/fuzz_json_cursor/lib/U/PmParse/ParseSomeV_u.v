(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeChk5_u ParseSomeChk6_u ParseSomeChk7_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u ParseSomeF_u ParseSomeH_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSV.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Section V.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation seg := (PSI.seg I).   Local Abbreviation wend := (PSI.wend I). Local Abbreviation wlen := (PSI.wlen I). Local Abbreviation st0 := (PSI.st0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis VNULL_OK : PMS.visit_null_spec L VNULL.
Hypothesis VBOOL_OK : PMS.visit_bool_spec L VBOOL.

Lemma vis_call : forall pc, pc = VNULL \/ pc = VBOOL -> forall (x : Z) (fx' : FPState) R' (M' : mem) model1 spc retpc,
  (pc = VBOOL -> PML.a1 R' x /\ 0 <= x <= 1) ->
  PML.entry L R' M' spc retpc PMS.VIS_SCR -> PML.a0 R' V -> PML.vis_at M' V -> PML.obj_on_stack L spc V 48 ->
  PML.fp_ok fx' -> m_halted model1 = None -> m_vm_lazy model1 = [] ->
  (forall fx2 R2 (M2 : mem), PML.fp_ok fx2 -> PML.a0 R2 1 -> PMCUR.ev_at RSEGS M2 V (if Z.eqb pc VNULL then PMCUR.EvNull else PMCUR.EvBool (Z.eqb x 1)) ->
     regs_preserved R' R2 -> L5.frame_but [(spc - PMS.VIS_SCR, PMS.VIS_SCR); (V + 8, 40)] M' M2 -> mem_grows M' M2 ->
     srealizes RSEGS SCFG (@PML.cfg fx2 R2 retpc M2 model1) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model1) K.
Proof.
  intros pc Hpc x fx' R' M' model1 spc retpc Hx Hent Ha0 Hvis Hobj HFP Hmh Hml RET.
  destruct Hpc as [->| ->].
  - apply (VNULL_OK V spc retpc fx' R' M' model1 K Hmh Hml (PSI.iHKnil I) HFP).
    { split; [exact Hent|]. split; [exact Ha0|]. split; [exact Hvis|]. split; [exact Hobj | exact Logic.I]. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & He & Hev) HRP HFB HGR. subst e. apply (RET fx2 R2 M2 HFP2 Ha0'); [exact Hev | exact HRP | exact HFB | exact HGR].
  - destruct (Hx eq_refl) as (Ha1 & Hx01).
    apply (VBOOL_OK V spc retpc fx' R' M' model1 K Hmh Hml (PSI.iHKnil I) HFP).
    { split; [exact Hent|]. split; [exact Ha0|]. split; [exact Hvis|]. split; [exact Hobj | exists x; split; [exact Ha1 | exact Hx01]]. }
    intros fx2 R2 M2 HFP2 (Ha0' & e & (x' & Hx1 & Hx2 & ->) & Hev) HRP HFB HGR.
    assert (Hxx : x' = x).
    { unfold PML.a1 in Hx1, Ha1. rewrite Ha1 in Hx1. apply (f_equal bv_unsigned) in Hx1. rewrite !u64_of_Z in Hx1 by lia. lia. }
    subst x'. apply (RET fx2 R2 M2 HFP2 Ha0'); [exact Hev | exact HRP | exact HFB | exact HGR].
Qed.

Lemma leaf_vis : forall i c k ps1 pc j, is_leaf i c k ps1 (CC.TOther pc) -> (pc = VNULL \/ pc = VBOOL) -> CH2.ret_of G.RETS i k = Some j ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc j IL Hpcs Hret.
  assert (Hvb : (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool = true) by (destruct Hpcs as [-> | ->]; reflexivity).
  assert (Hnx : is_exit_pc pc = false /\ (pc =? VECPUSH) = false /\ (pc =? PUSHB) = false /\ (pc =? POP) = false /\ (pc =? PARENT) = false /\ (pc =? SETEC) = false)
    by (destruct Hpcs as [-> | ->]; repeat split; reflexivity).
  destruct Hnx as (Nx & N1 & N2 & N3 & N4 & N5).
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. rewrite Nx in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  rewrite N1, N2, N3, N4, N5, Hvb in XS.
  destruct (vis_chk pc c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate]. apply Nat.leb_le in XS.
  pose proof (CH2.leaves_all_sound _ _ _ vis_leaf_ok _ _ _ _ _ IL) as X2. unfold PSMV.vis_leaf_chk in X2. rewrite Hvb, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  destruct (kind_of i) eqn:K1; try discriminate. destruct (kind_of j) eqn:K2; try discriminate.
  destruct (PSM5.rview i c ps1 j (CC.cp_nx cj - APC.NCS)%nat) as [[[[[pv lv] pe] ce] d]|] eqn:HRV; [|discriminate].
  apply andb_prop in X2 as [X2 Ya1]. apply andb_prop in X2 as [X2 HBL]. apply andb_prop in X2 as [X2 Yst]. apply andb_prop in X2 as [Yss Ymore].
  unfold vis_chk in Hchk. lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb Hvt]. apply andb_prop in Hb as [Ha0e HBL']. apply expr_eqb_eq in Ha0e.
  set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *.
  destruct (PSF.rview_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & pvj & Hvwj & Hflds & Hvars).
  assert (Hpvj : pvj = lv) by exact (PSF.flds_inj _ _ Hflds). subst pvj.
  destruct (PSF.same_state_facts d Yss) as (Dst & Dsst & Dnst & Dmore & Ddone & Dc).

  assert (HA1 : exists x, (pc = VBOOL -> nth 11 (CA.ps_reglist ps1) (ELit 0) = ELit x) /\ 0 <= x <= 1).
  { destruct (Z.eqb_spec pc VBOOL) as [Hpb|Hpb]; [|exists 0; split; [intros X; exfalso; exact (Hpb X) | clear; lia]].
    destruct (nth 11 (CA.ps_reglist ps1) (ELit 0)) as [x| | | | | | |]; try discriminate Ya1. exists x. split; [reflexivity|]. apply orb_prop in Ya1 as [Q|Q]; apply Z.eqb_eq in Q; clear - Q; lia. }
  destruct HA1 as (x & Hx1 & Hx01).
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (tags & Hc & _); exact Hc).
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K XI
           (PSI.DEF0 I) (PSI.CRED_BLK I) pc PMS.VIS_SCR 0%nat [(Vb, 8, ELit 40)] (vis_news pc (CA.ps_reglist ps1)) (Some (ELit 1)) [(V + 8, 40)] i c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL').
  - intros w a [<-|[]] Hin. exists (V + 8, 40). split; [unfold PSI.W, PMS.W_parc, PML.W_par; cbn [app]; right; right; right; right; left; reflexivity | exact Hin].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Vb, 8, ELit 40). split; [left; reflexivity|].
    destruct (PSB.FRZ I E' HagE') as (_ & GV & _). unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. fold (uv E' Vb). rewrite GV. rewrite u64_of_Z by lia. lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    destruct (PSF.call_common I i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    unfold PSI.XI in HX. destruct HX as (X1 & X2' & X3 & HX). rewrite K1, (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
    assert (HGR0 : mem_grows M' M') by (intros x0 Hx0; exact Hx0).
    destruct (PSB.leaf_state_g I i c k ps1 _ pv lv pe ce d E1 E' R' M1 M' M' model1 bm bd stack buf IL HLD HA' HGR0 Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    rewrite Dst in L8. rewrite Dsst in L9. rewrite Dnst in L10. rewrite Dmore in L11. rewrite Ddone in L12. rewrite Dc in L13. cbn [PSB.newv] in *.
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
    assert (Hbmt : bm = true) by (apply PSB.b2z_inj1; rewrite <- HC8, <- AG2; exact (PSB.rng_is_sound E' M' _ _ 1 HKc Ymore)). subst bm.
    set (psc := PSI.ps_of pv pe ce E1 true bd stack buf) in *.
    assert (Hst : 18 <= PML.ps_st psc <= 27) by (unfold psc, PSI.ps_of; cbn [PML.ps_st]; rewrite <- AG1; exact (PSB.rng_in_sound E' M' _ _ 18 27 HKc Yst)).
    destruct (HPAX true bd ltac:(rewrite L11; exact HC8) ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite L13 in Hlen.
    destruct (PSB.FRZ I E' HagE') as (F1 & F2 & F3 & _).
    destruct (PSF.other_facts _ _ _ _ _ IL) as (Fnf & F2b).
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _).
    pose proof (PSI.iOV I) as (OV1 & OV2 & OV3).

    assert (Ra0 : PML.a0 R' V).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Vb)). fold (uv E' Vb). rewrite F2. reflexivity. }
    assert (Ra1 : pc = VBOOL -> PML.a1 R' x /\ 0 <= x <= 1).
    { intros Hpb. split; [|exact Hx01]. unfold PML.a1. rewrite (HRL 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat.
      rewrite (Hx1 Hpb). reflexivity. }
    assert (HVT : PML.u64 M' V PML.VT_VISITOR).
    { pose proof (PB2.kword64_elim E' M' _ _ V (PB.has_ok E' M' _ _ HKc Hvt)) as T. rewrite PB2.uv_lit in T by (unfold PML.VT_VISITOR; clear; lia). apply T.
      unfold estart. cbn [a_base a_off]. fold (uv E' Vb). rewrite F2. clear; lia. }
    assert (HdV' : L5.defined M' V 48) by exact (PSB.amb_def I i E1 M' model1 V 48 HA' (proj2 (PSI.iHVIS I)) ltac:(clear - O4 O5; lia)).
    apply (vis_call pc Hpcs x fx' R' M' model1 (sp + CH2.ci_csp ci) (CC.cp_pc cj) Ra1 Hent Ra0 (conj HVT HdV')
             ltac:(unfold PML.obj_on_stack; split; [clear - Hcsp OV1; lia|]; split; [exact OV2 | exact OV3]) HFP Hmh Hml).
    intros fx2 R2 M2 HFP2 Ha0' Hev HRP HFB HGR.
    set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
    assert (Hnxv : CH2.ci_nx ci = nx) by (rewrite (PSF.custom_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk); apply Nat.sub_0_r).
    assert (Hag2 : env_agree nx E' E2) by (unfold E2; rewrite Hnxv; apply CH2.retEx_agree).
    assert (Hnf2 : (GT.NF <= nx)%nat).
    { pose proof (PSF.call_nf _ _ _ _ _ _ IL Hret) as Q. rewrite Hcutj in Q. unfold nx. clear - Q. lia. }
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | exact Hnf2]]).
    assert (AGX : forall y, In y (pe :: ce :: PSM2.flds lv) -> uv E2 y = uv E' y) by (intros y Hy; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 y Hag2 (Hvars y Hy))).
    destruct (PSF.flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    assert (ESV2 : forall q, estart E2 (SA Vb q) = V + q).
    { intros q. destruct (PSB.FRZ I E2 HagE2) as (_ & GV2 & _). unfold estart. cbn [a_base a_off]. fold (uv E2 Vb). rewrite GV2. reflexivity. }
    apply (RET fx2 R2 M2 [] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. unfold PML.a0 in Ha0'. exact Ha0'.
    +
      intros X HXin. rewrite LS. unfold vis_news in HXin. destruct Hev as (_ & Hev).
      destruct Hpcs as [-> | ->]; cbn [Z.eqb] in Hev |- *.
      * change (VNULL =? VNULL) with true in HXin, Hev. cbv iota in HXin, Hev. unfold VSU.const_news, VSU.fl in HXin. destruct HXin as [<-|[]].
        eapply CL5.kword64_intro with (A := V + 8) (z := 4); [fold E2; rewrite (ESV2 (0 + 8)); clear; lia | clear - O1 O4 O5; lia | clear - O1 O4 O5; lia | reflexivity | exact Hev].
      * change (VBOOL =? VNULL) with false in HXin, Hev. cbv iota in HXin, Hev. destruct Hev as (Hfl & Hby).
        unfold VSU.bool_news, VSU.fl in HXin. rewrite (Hx1 eq_refl) in HXin. destruct HXin as [<-|[<-|[]]].
        -- eapply CL5.kword64_intro with (A := V + 8) (z := 8); [fold E2; rewrite (ESV2 (0 + 8)); clear; lia | clear - O1 O4 O5; lia | clear - O1 O4 O5; lia | reflexivity | exact Hfl].
        -- eapply PB2.kword8_intro with (A := V + 32) (z := x); [fold E2; rewrite (ESV2 (0 + 32)); clear; lia | clear - O1 O4 O5; lia | clear - O1 O4 O5; lia | reflexivity | clear - Hx01; lia |].
           assert (Hxe : (if x =? 1 then 1 else 0) = x) by (clear - Hx01; destruct (Z.eqb_spec x 1); lia). rewrite Hxe in Hby. exact Hby.
    +
      intros HPRES. fold E2. unfold PSI.XI. rewrite K2, Hvwj.
      destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL2). destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL2) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
      assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2b); exact Hden).
      rewrite HBL2, !PB.den_cons in Hden. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden. injection Hden as Eb1 Eb2 Eb3 Eb4. rewrite Eb1 in C0, C1, C4. rewrite Eb2 in C1, C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
      rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1. clear C2 D2.
      assert (KEEP : forall a n (bs : list Z), (a = uv E1 pe /\ n = uv E1 ce) \/ (a = uv E1 (PB4.pv_sb pv) /\ n = uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) -> Z.of_nat (length bs) <= n ->
                     L5.bytes_at RSEGS M' a bs -> L5.bytes_at RSEGS M2 a bs).
      { intros a n0 bs Hab Hn HBs. apply (PSF.hpres_blk I _ _ _ _ M' M2 a n0 bs HPRES); [| exact Hn | destruct Hab as [[-> ->]|[-> ->]]; clear - C0 D0; lia | destruct Hab as [[-> ->]|[-> ->]]; unfold hl_ceil in *; clear - C4 D4 S4; lia | | | exact HBs].
        - rewrite HdenE'. cbn [In app]. destruct Hab as [[-> ->]|[-> ->]]; [exists (uv E1 pe, uv E1 ce); split; [left; reflexivity|] | exists (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)); split; [right; left; reflexivity|]]; cbn [fst snd]; clear; lia.
        - intros w Hw q Hq. unfold L5.in_rng. destruct Hw as [<-|[]]; cbn [fst snd]; unfold hl_ceil in *; destruct Hab as [[-> ->]|[-> ->]]; clear - Hq C4 D4 CL O4 S2; lia.
        - intros q Hq. unfold in_errno. rewrite (PmLayout.ly_errno L LAY). unfold hl_ceil in *. destruct Hab as [[-> ->]|[-> ->]]; clear - Hq C0 C1 D0 D1; lia. }
      split; [rewrite PSI.SCRV in *; apply (PSF.hpres_def I _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1] | unfold hl_ceil; clear - CL; lia | clear - O2 O3; lia]|].
      split; [exact CM1|]. split; [exact CM2|].
      exists true, bd, stack, bufm.
      assert (HIMG2 : forall a, 0x10000 <= a < 0xf8000 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha. apply HFB. rewrite L5.unsigned_lit by (clear - Ha; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd];
          [destruct Hent as (_ & _ & _ & _ & Hstk'); pose proof (L5C.stk_floor _ _ _ _ Hstk') as SF; clear - Ha SF; lia | clear - Ha O1 O4; lia]. }
      split.
      { unfold PSI.contents. rewrite Ape, Ace, Awend, Awptr, Ast, Amore, Adone, Asize, Asb, Asend, Ascend. rewrite L2, L3, L4, L5, L7, L6, L13, L11, L12.
        split; [apply (KEEP _ (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))); [right; split; reflexivity | clear - HC3; lia | exact HSB]|].
        split; [exact HC2|]. split; [exact HC3|]. split; [reflexivity|]. split; [clear - HC5 L14 L15 L16; lia|]. split; [exact Hlen|].
        split; [clear - Hlen HC6 HC6b; lia|].
        split; [intros Hn; exfalso; rewrite L8 in Hn; change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hn; unfold PML.ST_NUMBER in Hn; clear - Hn Hst; lia|]. split; [exact HC8 | exact HC9]. }
      split; [apply (PSH.ls_hpres I _ _ _ _ M' M2 g HPRES); [intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; clear - Hin O1 O4; lia | exact (PSI.iHG I) | exact (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS)]|].
      assert (HPS : PSI.ps_of lv pe ce E2 true bd stack bufm
                    = PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd (uv E1 ce) (uv E1 pe) bufm (PB4.win_of (uv E' (PB4.pv_wptr lv)) wend)).
      { rewrite (PSF.ps_of_agree lv pe ce E2 E' _ _ _ _ AGX), (HEQ true bd bufm), L8, L9, L10. reflexivity. }
      rewrite HPS. clear HPS.
      assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> bufm = PML.ps_buf psc) by (intros Hn _; exfalso; unfold PML.ST_NUMBER in Hn; clear - Hn Hst; lia).
      pose proof (PSI.WIN I) as (W0 & W1 & _).
      assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
      split; [exact (PSX.wf_upd_same psc bd _ _ bufm _ HW Hbufeq)|].
      split.
      { destruct HB as [HB1 HB2]. split; [|exact HB2]. unfold PSS.upd at 1 2. cbn [PML.ps_buf]. rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia).
        replace (PML.buf_need (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PML.buf_need psc) by reflexivity. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1. clear - HB1 Hwl1 Hlen HC6 L14 L15. lia. }
      split; [split; [exact (PSSC.lvl_same psc _ (proj1 (proj1 HWS)) eq_refl eq_refl eq_refl eq_refl) | exact (proj2 (proj1 HWS))]|].
      split; [reflexivity|]. split; [exact Hst|].
      exists (if Z.eqb pc VNULL then PMCUR.EvNull else PMCUR.EvBool (Z.eqb x 1)). split; [exact Hev | destruct (Z.eqb pc VNULL); exact Logic.I].
Qed.
End V.
End PSV.
