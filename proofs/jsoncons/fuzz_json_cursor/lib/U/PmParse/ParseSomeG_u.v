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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeChk5_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u ParseSomeF_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSG.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Section G.
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

Hypothesis POP_OK : PMS.pop_state_spec L.
Hypothesis PARENT_OK : PMS.parent_spec L.
Lemma leaf_pop : forall i c k ps1 j, is_leaf i c k ps1 (CC.TOther POP) -> CH2.ret_of G.RETS i k = Some j -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j IL Hret.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. change (is_exit_pc POP) with false in XS. cbv iota in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  change (POP =? VECPUSH) with false in XS. change (POP =? PUSHB) with false in XS. rewrite Z.eqb_refl in XS. cbv iota in XS.
  destruct (pop_chk c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  pose proof (CH2.leaves_all_sound _ _ _ pure2_ok _ _ _ _ _ IL) as X2. unfold PSM5.pure_chk2 in X2. rewrite Z.eqb_refl, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  destruct (kind_of i) eqn:K1; try discriminate. destruct (kind_of j) eqn:K2; try discriminate.
  destruct (PSM5.rviewp i c ps1 j (CC.cp_nx cj - APC.NCS - 1)%nat) as [[[[[pv lv] pe] ce] d]|] eqn:HRV; [|discriminate].
  unfold pop_chk in Hchk. destruct (CAX.cell_at (SR.ps_cells ps1) Pb 256 8) as [c8|] eqn:Hc8; [|discriminate].
  apply andb_prop in X2 as [X2 Y5]. apply andb_prop in X2 as [X2 Y4]. apply andb_prop in X2 as [X2 Y3]. apply andb_prop in X2 as [Y1 Y2]. apply expr_eqb_eq in Y5. subst c8.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *.
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K XI
           (PSI.DEF0 I) (PSI.CRED_BLK I) POP 48 1%nat [(Pb, 256, ELit 8)] [KWord (SA Pb 256) 8 (APC.eaddz (PB4.pv_send lv) (-1)); KRange (EVar nx) 0 255] (Some (EVar nx)) [(P + 256, 8)] i c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (P, 272). split; [unfold PSI.W, PML.W_par; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - intros E' HagE' w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (Pb, 256, ELit 8). split; [left; reflexivity|].
    destruct (PSB.FRZ I E' HagE') as (F1 & _). unfold CH2.in_reg, estart. cbn [a_base a_off]. fold (uv E' Pb). rewrite F1. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    destruct (PSF.call_common I i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    destruct (PSF.rviewp_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & Hvwj & Hvars).
    destruct (PSF.same_state_facts d Y1) as (Dst & Dsst & Dnst & Dmore & Ddone & Dc).
    unfold PSI.XI in HX. destruct HX as (X1 & X2' & X3 & HX). rewrite K1, (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
    assert (HGR0 : mem_grows M' M') by (intros x0 Hx0; exact Hx0).
    destruct (PSB.leaf_state_g I i c k ps1 _ pv lv pe ce d E1 E' R' M1 M' M' model1 bm bd stack buf IL HLD HA' HGR0 Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    rewrite Dst in L8. rewrite Dsst in L9. rewrite Dnst in L10. rewrite Dmore in L11. rewrite Ddone in L12. rewrite Dc in L13. cbn [PSB.newv] in *.
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
    assert (Hbmt : bm = true) by (apply PSB.b2z_inj1; rewrite <- HC8, <- AG2; exact (PSB.rng_is_sound E' M' _ _ 1 HKc Y2)). subst bm.
    set (psc := PSI.ps_of pv pe ce E1 true bd stack buf) in *.
    destruct (PSF.wf_last psc HW eq_refl) as (rest & x & Hstk & Hx). unfold psc, PSI.ps_of in Hstk. cbn [PML.ps_stack] in Hstk.
    destruct (HPAX true bd ltac:(rewrite L11; exact HC8) ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite L13 in Hlen.
    pose proof (PSB.pa_buf _ _ _ HPA) as HBUF. cbn [PSI.ps_of PML.ps_bptr PML.ps_buf] in HBUF. rewrite L6 in HBUF.
    destruct (PSB.FRZ I E' HagE') as (F1 & _).
    destruct (PSF.other_facts _ _ _ _ _ IL) as (Fnf & F2).
    assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2); exact Hden).
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL2). destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL2) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    rewrite HBL2, !PB.den_cons in Hden. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden. injection Hden as Eb1 Eb2 Eb3 Eb4. rewrite Eb1 in C0, C1, C4. rewrite Eb2 in C1, C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _). pose proof (PSI.iOP I) as (OP1 & OP2 & _).
    rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1. clear C2 D2.
    assert (Ra0 : PML.a0 R' P).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Pb)). fold (uv E' Pb). rewrite F1. reflexivity. }
    rewrite Hstk in HPA.
    pose proof (POP_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) (PSI.ps_of lv pe ce E' true bd (rest ++ [x]) bufm) rest fx' R' M' model1 K Hmh Hml (PSI.iHKnil I) HFP) as CALLEE. unfold PML.cfg in *. apply CALLEE; clear CALLEE.
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact HPA|]. unfold PSI.ps_of. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [reflexivity|]. split; [unfold PML.obj_on_stack; split; [clear - Hcsp OP1; lia|]; split; [exact OP2 | exact (proj2 (proj2 (PSI.iOP I)))]|]. split; [lia|]. rewrite L2, L4. unfold hl_ceil in *. split; lia. }
    intros fx2 R2 M2 HFP2 (Hpost & Hu) HRP HFB HGR. cbn [PSI.ps_of PML.ps_sb] in Hu.
    assert (Hnxv : CH2.ci_nx ci = nx) by (rewrite (PSF.custom_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk); reflexivity).
    rewrite Hnxv in RET.
    set (E2 := CH2.retEx E' nx [Z_to_bv 64 x] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Hnf2 : (GT.NF <= nx)%nat).
    { pose proof (PSF.call_nf _ _ _ _ _ _ IL Hret) as Q. rewrite Hcutj in Q. exact Q. }
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | exact Hnf2]]).
    assert (GG : ev E2 nx = Z_to_bv 64 x).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 x] R2 0%nat) as GG0. cbn [length] in GG0. specialize (GG0 (Nat.lt_0_succ _)). rewrite Nat.add_0_r in GG0. exact GG0. }
    assert (AGX : forall y, In y (pe :: ce :: PSM2.flds lv) -> uv E2 y = uv E' y) by (intros y Hy; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 y Hag2 (Hvars y Hy))).
    destruct (PSF.flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    assert (Hrl : Z.of_nat (length stack) = Z.of_nat (length rest) + 1) by (rewrite Hstk, length_app; cbn [length]; lia).
    destruct (PSB.FRZ I E2 HagE2) as (F1' & _).
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG. exact Hpost.
    + fold E2. intros X [<-|[<-|[]]].
      * rewrite LS. eapply CL5.kword64_intro with (A := P + 256) (z := uv E1 (PB4.pv_sb pv) + Z.of_nat (length rest)).
        -- unfold estart. cbn [a_base a_off]. fold (uv E2 Pb). rewrite F1'. reflexivity.
        -- clear - O1 O2 O3; lia.
        -- clear - O1 O2 O3; lia.
        -- apply PB.edenot_of_uv. rewrite PB.uv_eaddz, Asend, L3, HC2, Hrl. rewrite Z.mod_small by (clear - D0 D4 S4 HC3 Hrl; lia). clear; lia.
        -- rewrite L2 in Hu. exact Hu.
      * cbn [kentry_ok edenot]. rewrite GG. rewrite u64_of_Z by lia. lia.
    + intros HPRES.
      fold E2. unfold PSI.XI. rewrite K2, Hvwj.
      assert (KEEP : forall a n (bs : list Z), (a = uv E1 pe /\ n = uv E1 ce) \/ (a = uv E1 (PB4.pv_sb pv) /\ n = uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) -> Z.of_nat (length bs) <= n ->
                     L5.bytes_at RSEGS M' a bs -> L5.bytes_at RSEGS M2 a bs).
      { intros a n0 bs Hab Hn HBs. apply (PSF.hpres_blk I _ _ _ _ M' M2 a n0 bs HPRES); [| exact Hn | destruct Hab as [[-> ->]|[-> ->]]; clear - C0 D0; lia | destruct Hab as [[-> ->]|[-> ->]]; unfold hl_ceil in *; clear - C4 D4 S4; lia | | | exact HBs].
        - rewrite HdenE'. cbn [In app]. destruct Hab as [[-> ->]|[-> ->]]; [exists (uv E1 pe, uv E1 ce); split; [left; reflexivity|] | exists (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)); split; [right; left; reflexivity|]]; cbn [fst snd]; clear; lia.
        - intros w Hw q Hq. unfold L5.in_rng. destruct Hw as [<-|[]]; cbn [fst snd]; unfold hl_ceil in *; destruct Hab as [[-> ->]|[-> ->]]; clear - Hq C4 D4 CL O2; lia.
        - intros q Hq. unfold in_errno. rewrite (PmLayout.ly_errno L LAY). unfold hl_ceil in *. destruct Hab as [[-> ->]|[-> ->]]; clear - Hq C0 C1 D0 D1; lia. }
      split; [rewrite PSI.SCRV in *; apply (PSF.hpres_def I _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1] | unfold hl_ceil; clear - CL; lia | clear - O2 O3; lia]|].
      split; [exact CM1|]. split; [exact CM2|].
      exists true, bd, rest, bufm.
      assert (HIMG2 : forall a, 0x10000 <= a < 0xf8000 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha. apply HFB. rewrite L5.unsigned_lit by (clear - Ha; lia). intros rg [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [destruct Hent as (_ & _ & _ & _ & Hstk'); pose proof (L5C.stk_floor _ _ _ _ Hstk') as SF; clear - Ha SF; lia | clear - Ha O1 O2; lia]. }
      split.
      { unfold PSI.contents, PSM5.set_send. cbn [PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wend PB4.pv_wptr PB4.pv_size PB4.pv_st PB4.pv_more PB4.pv_done].
        rewrite PB.uv_eaddz, Ape, Ace, Awend, Awptr, Ast, Amore, Adone, Asize, Asb, Asend, Ascend. rewrite L2, L3, L4, L5, L7, L6, L13, L11, L12.
        split; [apply (KEEP _ (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))); [right; split; reflexivity | clear - HC3 Hrl; lia | rewrite Hstk in HSB; exact (PSF.bytes_prefix _ _ _ _ HSB)]|].
        split; [rewrite HC2, Hrl; rewrite Z.mod_small by (clear - D0 D4 S4 HC3 Hrl; lia); clear; lia|]. split; [clear - HC3 Hrl; lia|]. split; [reflexivity|]. split; [clear - HC5 L14 L15 L16; lia|]. split; [exact Hlen|].
        split; [clear - Hlen HC6 HC6b; lia|].
        split; [intros _; apply (KEEP _ (uv E1 ce)); [left; split; reflexivity | clear - Hlen HC6 HC6b; lia | exact HBUF]|]. split; [exact HC8 | exact HC9]. }
      split; [exact (PSB.ls_frame M' M2 g HIMG2 (PSI.iHG I) (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS))|].
      exists x. split; [rewrite Hcutj; fold nx; rewrite GG; apply u64_of_Z; clear - Hx; lia|].
      assert (HPS : PSI.ps_of (PSM5.set_send lv (APC.eaddz (PB4.pv_send lv) (-1))) pe ce E2 true bd (rest ++ [x]) bufm
                    = PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd (uv E1 ce) (uv E1 pe) bufm (PB4.win_of (uv E' (PB4.pv_wptr lv)) wend)).
      { transitivity (PSI.ps_of lv pe ce E2 true bd (rest ++ [x]) bufm); [reflexivity|]. rewrite (PSF.ps_of_agree lv pe ce E2 E' _ _ _ _ AGX), <- Hstk, (HEQ true bd bufm), L8, L9, L10. reflexivity. }
      rewrite HPS. clear HPS.
      destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg.
      pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Hst. rewrite AG1 in Hst. change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hst.
      assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> bufm = PML.ps_buf psc).
      { intros Hn _. exfalso. unfold PML.ST_NUMBER in Hn. apply orb_prop in Y4 as [Q|Q]; apply Z.ltb_lt in Q; clear - Q Hst Hn; lia. }
      pose proof (PSI.WIN I) as (W0 & W1 & _).
      assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
      split; [exact (PSX.wf_upd_same psc bd _ _ bufm _ HW Hbufeq)|].
      split.
      { destruct HB as [HB1 HB2]. split; [|exact HB2]. unfold PSS.upd at 1 2. cbn [PML.ps_buf]. rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia).
        replace (PML.buf_need (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PML.buf_need psc) by reflexivity. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1. clear - HB1 Hwl1 Hlen HC6 L14 L15. lia. }
      split; [split; [exact (PSSC.lvl_same psc _ (proj1 (proj1 HWS)) eq_refl eq_refl eq_refl eq_refl) | exact (proj2 (proj1 HWS))]|].
      intros Hj. rewrite Hj in Y3. cbn [implb] in Y3. apply andb_prop in Y3 as [Y3 Y3c]. apply andb_prop in Y3 as [Y3a Y3b]. apply Nat.ltb_lt in Y3b, Y3c.
      replace (PSI.RANK (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PSI.RANK psc) by reflexivity.
      assert (H50 : ev E2 50 = ev E1 50) by (destruct Hag as [Hev1 _]; destruct Hag2 as [Hev2 _]; rewrite <- (Hev2 _ Y3c), <- (Hev1 _ Y3b); reflexivity).
      rewrite H50. apply HR. apply orb_prop in Y3a as [Y3a|Y3a]; [apply orb_prop in Y3a as [Y3a|Y3a]; [apply orb_prop in Y3a as [Y3a|Y3a]|]|]; apply Nat.eqb_eq in Y3a; [left | right; left | right; right; left | right; right; right]; exact Y3a.
Qed.

Lemma leaf_parent : forall i c k ps1 j, is_leaf i c k ps1 (CC.TOther PARENT) -> CH2.ret_of G.RETS i k = Some j -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j IL Hret.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. change (is_exit_pc PARENT) with false in XS. cbv iota in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  change (PARENT =? VECPUSH) with false in XS. change (PARENT =? PUSHB) with false in XS. change (PARENT =? POP) with false in XS. rewrite Z.eqb_refl in XS. cbv iota in XS.
  destruct (parent_chk c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  pose proof (CH2.leaves_all_sound _ _ _ pure2_ok _ _ _ _ _ IL) as X2. unfold PSM5.pure_chk2 in X2. change (PARENT =? POP) with false in X2. rewrite Z.eqb_refl, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  assert (KK : (kind_of i = KInv \/ kind_of i = KParent) /\ kind_of j = KParent /\ exists pv lv pe ce d, PSM5.rview i c ps1 j (CC.cp_nx cj - APC.NCS - 1)%nat = Some (pv, lv, pe, ce, d) /\
    PSM5.same_state d = true /\ PSM2.rng_is (SR.ps_cells ps1) (PB4.pv_more pv) 1 = true /\ (let '(lo, hi) := PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv) in (hi <? 17) || (17 <? lo)) = true).
  { destruct (kind_of i); try discriminate; (destruct (kind_of j); try discriminate); (destruct (PSM5.rview i c ps1 j (CC.cp_nx cj - APC.NCS - 1)%nat) as [[[[[pv lv] pe] ce] d]|]; [|discriminate]);
      apply andb_prop in X2 as [X2 D3]; apply andb_prop in X2 as [D1 D2]; (split; [tauto|]); (split; [reflexivity|]); exists pv, lv, pe, ce, d; repeat split; assumption. }
  destruct KK as (K1 & K2 & pv & lv & pe & ce & d & HRV & Y1 & Y2 & Y4).
  unfold parent_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. apply andb_prop in Hb as [Ha0e HBL]. apply expr_eqb_eq in Ha0e.
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *.
  apply (PB4.pure_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K XI
           (PSI.DEF0 I) (PSI.CRED_BLK I) PARENT 48 1%nat [] [KRange (EVar nx) 0 255] (Some (EVar nx)) [] i c k ps1 j cj ci IL Hret Hcj Hpc Hchk HBL).
  - intros w a [].
  - intros E' HagE' w a [].
  - intros fx' E1 E' R' M1 M' model1 HagE' Hag HLF HRL HA' HX Hent Hcsp HFP Hmh Hml RET.
    destruct (PSF.call_common I i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    destruct (PSF.rview_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & pvj & Hvwj & Hflds & Hvars). apply PSF.flds_inj in Hflds. subst pvj.
    destruct (PSF.same_state_facts d Y1) as (Dst & Dsst & Dnst & Dmore & Ddone & Dc).
    unfold PSI.XI in HX. destruct HX as (X1 & X2' & X3 & HX). rewrite (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    assert (HXc : exists bm bd stack buf, PSI.contents I pv pe ce E1 M1 bm bd stack buf /\ PML.ls_ok g M1 /\ PML.wf_ps (PSI.ps_of pv pe ce E1 bm bd stack buf) /\ PML.buf_bound (PSI.ps_of pv pe ce E1 bm bd stack buf) B).
    { destruct K1 as [K1|K1]; rewrite K1 in HX; destruct HX as (bm & bd & stack & buf & Q1 & Q2 & Q3 & Q4); exists bm, bd, stack, buf.
      - split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact (proj1 Q4)].
      - split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact Q4]. }
    destruct HXc as (bm & bd & stack & buf & HC & HS & HW & HB).
    assert (HGR0 : mem_grows M' M') by (intros x0 Hx0; exact Hx0).
    destruct (PSB.leaf_state_g I i c k ps1 _ pv lv pe ce d E1 E' R' M1 M' M' model1 bm bd stack buf IL HLD HA' HGR0 Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    rewrite Dst in L8. rewrite Dsst in L9. rewrite Dnst in L10. rewrite Dmore in L11. rewrite Ddone in L12. rewrite Dc in L13. cbn [PSB.newv] in *.
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
    assert (Hbmt : bm = true) by (apply PSB.b2z_inj1; rewrite <- HC8, <- AG2; exact (PSB.rng_is_sound E' M' _ _ 1 HKc Y2)). subst bm.
    set (psc := PSI.ps_of pv pe ce E1 true bd stack buf) in *.
    destruct (PSF.wf_last psc HW eq_refl) as (rest & x & Hstk & Hx). unfold psc, PSI.ps_of in Hstk. cbn [PML.ps_stack] in Hstk.
    destruct (HPAX true bd ltac:(rewrite L11; exact HC8) ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite L13 in Hlen.
    pose proof (PSB.pa_buf _ _ _ HPA) as HBUF. cbn [PSI.ps_of PML.ps_bptr PML.ps_buf] in HBUF. rewrite L6 in HBUF.
    destruct (PSB.FRZ I E' HagE') as (F1 & _).
    destruct (PSF.other_facts _ _ _ _ _ IL) as (Fnf & F2).
    assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2); exact Hden).
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL2). destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL2) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    rewrite HBL2, !PB.den_cons in Hden. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden. injection Hden as Eb1 Eb2 Eb3 Eb4. rewrite Eb1 in C0, C1, C4. rewrite Eb2 in C1, C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _). pose proof (PSI.iOP I) as (OP1 & OP2 & _).
    rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1. clear C2 D2.
    assert (Ra0 : PML.a0 R' P).
    { unfold PML.a0. rewrite (HRL 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Ha0e.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' Pb)). fold (uv E' Pb). rewrite F1. reflexivity. }
    rewrite Hstk in HPA.
    pose proof (PARENT_OK P x (sp + CH2.ci_csp ci) (CC.cp_pc cj) (PSI.ps_of lv pe ce E' true bd (rest ++ [x]) bufm) rest fx' R' M' model1 K Hmh Hml (PSI.iHKnil I) HFP) as CALLEE. unfold PML.cfg in *. apply CALLEE; clear CALLEE.
    { split; [exact Hent|]. split; [exact Ra0|]. split; [exact HPA|]. unfold PSI.ps_of. cbn [PML.ps_stack PML.ps_sb PML.ps_scap].
      split; [reflexivity|]. split; [unfold PML.obj_on_stack; split; [clear - Hcsp OP1; lia|]; split; [exact OP2 | exact (proj2 (proj2 (PSI.iOP I)))]|]. split; [lia|]. rewrite L2, L4. unfold hl_ceil in *. split; lia. }
    intros fx2 R2 M2 HFP2 Hpost HRP HFB HGR.
    assert (Hnxv : CH2.ci_nx ci = nx) by (rewrite (PSF.custom_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk); reflexivity).
    rewrite Hnxv in RET.
    set (E2 := CH2.retEx E' nx [Z_to_bv 64 x] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Hnf2 : (GT.NF <= nx)%nat).
    { pose proof (PSF.call_nf _ _ _ _ _ _ IL Hret) as Q. rewrite Hcutj in Q. exact Q. }
    assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | exact Hnf2]]).
    assert (GG : ev E2 nx = Z_to_bv 64 x).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 x] R2 0%nat) as GG0. cbn [length] in GG0. specialize (GG0 (Nat.lt_0_succ _)). rewrite Nat.add_0_r in GG0. exact GG0. }
    assert (AGX : forall y, In y (pe :: ce :: PSM2.flds lv) -> uv E2 y = uv E' y) by (intros y Hy; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 y Hag2 (Hvars y Hy))).
    destruct (PSF.flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    assert (Hrl : Z.of_nat (length stack) = Z.of_nat (length rest) + 1) by (rewrite Hstk, length_app; cbn [length]; lia).
    destruct (PSB.FRZ I E2 HagE2) as (F1' & _).
    apply (RET fx2 R2 M2 [Z_to_bv 64 x] eq_refl HFP2 HRP HFB HGR).
    + cbn [edenot]. fold E2. rewrite GG. exact Hpost.
    + fold E2. intros X [<-|[]]. cbn [kentry_ok edenot]. rewrite GG. rewrite u64_of_Z by (clear - Hx; lia). clear - Hx; lia.
    + intros HPRES.
      fold E2. unfold PSI.XI. rewrite K2, Hvwj.
      assert (KEEP : forall a n (bs : list Z), (a = uv E1 pe /\ n = uv E1 ce) \/ (a = uv E1 (PB4.pv_sb pv) /\ n = uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) -> Z.of_nat (length bs) <= n ->
                     L5.bytes_at RSEGS M' a bs -> L5.bytes_at RSEGS M2 a bs).
      { intros a n0 bs Hab Hn HBs. apply (PSF.hpres_blk I _ _ _ _ M' M2 a n0 bs HPRES); [| exact Hn | destruct Hab as [[-> ->]|[-> ->]]; clear - C0 D0; lia | destruct Hab as [[-> ->]|[-> ->]]; unfold hl_ceil in *; clear - C4 D4 S4; lia | | | exact HBs].
        - rewrite HdenE'. cbn [In app]. destruct Hab as [[-> ->]|[-> ->]]; [exists (uv E1 pe, uv E1 ce); split; [left; reflexivity|] | exists (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)); split; [right; left; reflexivity|]]; cbn [fst snd]; clear; lia.
        - intros w [].
        - intros q Hq. unfold in_errno. rewrite (PmLayout.ly_errno L LAY). unfold hl_ceil in *. destruct Hab as [[-> ->]|[-> ->]]; clear - Hq C0 C1 D0 D1; lia. }
      split; [rewrite PSI.SCRV in *; apply (PSF.hpres_def I _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1] | unfold hl_ceil; clear - CL; lia | clear - O2 O3; lia]|].
      split; [exact CM1|]. split; [exact CM2|].
      exists true, bd, stack, bufm.
      assert (HIMG2 : forall a, 0x10000 <= a < 0xf8000 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha. apply HFB. rewrite L5.unsigned_lit by (clear - Ha; lia). intros rg [<-|[]]; unfold L5.in_rng; cbn [fst snd]; destruct Hent as (_ & _ & _ & _ & Hstk'); pose proof (L5C.stk_floor _ _ _ _ Hstk') as SF; clear - Ha SF; lia. }
      split.
      { unfold PSI.contents. rewrite Ape, Ace, Awend, Awptr, Ast, Amore, Adone, Asize, Asb, Asend, Ascend. rewrite L2, L3, L4, L5, L7, L6, L13, L11, L12.
        split; [apply (KEEP _ (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))); [right; split; reflexivity | exact HC3 | exact HSB]|].
        split; [exact HC2|]. split; [exact HC3|]. split; [reflexivity|]. split; [clear - HC5 L14 L15 L16; lia|]. split; [exact Hlen|].
        split; [clear - Hlen HC6 HC6b; lia|].
        split; [intros _; apply (KEEP _ (uv E1 ce)); [left; split; reflexivity | clear - Hlen HC6 HC6b; lia | exact HBUF]|]. split; [exact HC8 | exact HC9]. }
      split; [exact (PSB.ls_frame M' M2 g HIMG2 (PSI.iHG I) (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS))|].
      assert (HPS : PSI.ps_of lv pe ce E2 true bd stack bufm
                    = PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd (uv E1 ce) (uv E1 pe) bufm (PB4.win_of (uv E' (PB4.pv_wptr lv)) wend)).
      { rewrite (PSF.ps_of_agree lv pe ce E2 E' _ _ _ _ AGX), (HEQ true bd bufm), L8, L9, L10. reflexivity. }
      rewrite HPS. clear HPS.
      destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg.
      pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Hst. rewrite AG1 in Hst. change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hst.
      assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> bufm = PML.ps_buf psc).
      { intros Hn _. exfalso. unfold PML.ST_NUMBER in Hn. apply orb_prop in Y4 as [Q|Q]; apply Z.ltb_lt in Q; clear - Q Hst Hn; lia. }
      pose proof (PSI.WIN I) as (W0 & W1 & _).
      assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
      split; [exact (PSX.wf_upd_same psc bd _ _ bufm _ HW Hbufeq)|].
      destruct HB as [HB1 HB2]. split; [|exact HB2]. unfold PSS.upd at 1 2. cbn [PML.ps_buf]. rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia).
      replace (PML.buf_need (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PML.buf_need psc) by reflexivity. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1. clear - HB1 Hwl1 Hlen HC6 L14 L15. lia.
Qed.
End G.
End PSG.
