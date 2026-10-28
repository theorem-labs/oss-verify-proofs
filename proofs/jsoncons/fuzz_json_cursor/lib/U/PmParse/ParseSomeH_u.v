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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseBridges6_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeChk5_u ParseSomeChk6_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u ParseSomeF_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSH.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Lemma rviewv_facts : forall i c ps j nxj pv lv pe ce d, PSM5.rviewv i c ps j nxj = Some (pv, lv, pe, ce, d) ->
  PSM2.ldelta i c ps = Some (pv, lv, pe, ce, d) /\
  PSM2.vw j = Some (PSM5.set_vec lv (EVar nxj) (PSU2.eadd (EVar nxj) (APC.eaddz (PSU2.esub (PB4.pv_send lv) (PB4.pv_sb lv)) 1)) (PSU2.eadd (EVar nxj) (EVar (nxj + 1))), pe, ce) /\
  forallb (APC.expr_vars_lt nxj) (pe :: ce :: PSM2.flds lv) = true.
Proof.
  intros i c ps j nxj pv lv pe ce d H. unfold PSM5.rviewv in H. destruct (PSM2.ldelta i c ps) as [[[[[pv0 lv0] pe0] ce0] d0]|]; [|discriminate]. destruct (PSM2.vw j) as [[[pvj pej] cej]|]; [|discriminate].
  cbv zeta in H. lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as -> -> -> -> ->.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B2, B3. subst pej cej.
  split; [reflexivity|]. split; [|exact B4]. f_equal. f_equal. f_equal. apply PSF.flds_inj.
  unfold PSM2.flds in *. cbn [combine forallb fst snd] in B1. repeat (let Q := fresh "Q" in apply andb_prop in B1 as [Q B1]; apply expr_eqb_eq in Q; rewrite Q). reflexivity.
Qed.
Lemma vecpush_blj : forall NF d VB VK c ps cj BLi BLj ci, PB4.vecpush_chk NF d VB VK c ps cj BLi BLj = Some ci ->
  exists b1 sbe sce, BLi = [b1; (sbe, sce)] /\ BLj = [b1; (EVar (CC.cp_nx cj - APC.NCS - 2), EVar (CC.cp_nx cj - APC.NCS - 2 + 1))].
Proof.
  intros NF d VB VK c ps cj BLi BLj ci H. unfold PB4.vecpush_chk in H.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok]. destruct (split_lit (nth 11 (CA.ps_reglist ps) (ELit 0))) as [xb xk]. destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp0].
  destruct BLi as [|b1 [|[sbe sce] [|? ?]]]; try discriminate.
  destruct (CAX.cell_at (SR.ps_cells ps) ob ok 8) as [c0|]; [|discriminate]. destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [c8|]; [|discriminate]. destruct (CAX.cell_at (SR.ps_cells ps) xb xk 1) as [xv|]; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  repeat (apply andb_prop in Hb as [Hb ?B]). apply CH2.blocks_eqb_eq in B1. exists b1, sbe, sce. split; [reflexivity | exact B1].
Qed.

Lemma wf_len1026 : forall ps, PML.wf_ps ps -> PML.ps_more ps = true -> PML.ps_st ps <> PML.ST_CR -> (length (PML.ps_stack ps) <= 1026)%nat.
Proof.
  intros ps (_ & _ & _ & _ & C & T & Hs & HC & HM) Hm Hst. destruct (HM Hm) as (HL & HL2 & _ & HT & _). rewrite Hs. cbn [length]. rewrite length_app.
  destruct HT as [[-> _]|[[-> _]|[(S & HS & -> & _)|(S & HS & -> & Q)]]]; [cbn [length]; lia | cbn [length]; lia | cbn [length]; lia | contradiction].
Qed.

Lemma wf_vec : forall ps done' sb' scap' bcap' bptr' buf' w', PML.wf_ps ps -> In scap' [66; 132; 264; 528; 1056] -> (PML.ps_st ps = PML.ST_NUMBER -> PML.ps_more ps = true -> buf' = PML.ps_buf ps) ->
  PML.wf_ps (PML.PS (PML.ps_st ps) (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) done' (PML.ps_level ps) (PML.ps_stack ps) sb' scap' bcap' bptr' buf' w').
Proof.
  intros ps done' sb' scap' bcap' bptr' buf' w' (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) Hs Hb. unfold PML.wf_ps. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact Hs|]. exists C, T. split; [exact W5|]. split; [exact W6|]. intros Hm. destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6). repeat (split; [assumption|]).
  intros Hn. rewrite (Hb Hn Hm). exact (X6 Hn).
Qed.

Lemma rviewb_facts : forall i c ps j nxj pv lv pe ce d, PSM6.rviewb i c ps j nxj = Some (pv, lv, pe, ce, d) ->
  PSM2.ldelta i c ps = Some (pv, lv, pe, ce, d) /\ PSM2.vw j = Some (PSM6.set_size lv (APC.eaddz (PB4.pv_size lv) 1), EVar nxj, PSU.emul2 (EVar (nxj + 1))) /\
  forallb (APC.expr_vars_lt nxj) (pe :: ce :: PSM2.flds lv) = true.
Proof.
  intros i c ps j nxj pv lv pe ce d H. unfold PSM6.rviewb in H. destruct (PSM2.ldelta i c ps) as [[[[[pv0 lv0] pe0] ce0] d0]|]; [|discriminate]. destruct (PSM2.vw j) as [[[pvj pej] cej]|]; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as -> -> -> -> ->.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B2, B3. subst pej cej.
  split; [reflexivity|]. split; [|exact B4]. f_equal. f_equal. f_equal. apply PSF.flds_inj.
  unfold PSM2.flds in *. cbn [combine forallb fst snd] in B1. repeat (let Q := fresh "Q" in apply andb_prop in B1 as [Q B1]; apply expr_eqb_eq in Q; rewrite Q). reflexivity.
Qed.
Lemma pushbc_blj : forall NF d OB OK KMIN c ps cj BLi BLj ci, PB4.pushbc_chk NF d OB OK KMIN c ps cj BLi BLj = Some ci ->
  exists pe ce BLk, BLi = (pe, ce) :: BLk /\ BLj = (EVar (CC.cp_nx cj - APC.NCS - 2), PSU.emul2 (EVar (CC.cp_nx cj - APC.NCS - 2 + 1))) :: BLk.
Proof.
  intros NF d OB OK KMIN c ps cj BLi BLj ci H. unfold PB4.pushbc_chk in H.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok]. destruct BLi as [|[pe ce] BLk]; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|]; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  repeat (apply andb_prop in Hb as [Hb ?B]). apply CH2.blocks_eqb_eq in B1. exists pe, ce, BLk. split; [reflexivity | exact B1].
Qed.

Section H.
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

Hypothesis VECPUSH_OK : PMS.vec_push_spec L HI.
Lemma VADDR : estart E0 (SA Pb 248) = P + 248.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). pose proof (PSI.UU I) as (_ & U10 & _). unfold uv, Pb. cbn [edenot]. rewrite U10. reflexivity. Qed.
Lemma VOBJ : sp <= P + 248 /\ P + 248 + 24 <= hl_sptop L /\ (P + 248) mod 8 = 0 /\ (forall a, P + 248 <= a < P + 248 + 24 -> exists w, In w W /\ L5.in_rng w a).
Proof.
  destruct (PSI.iOP I) as (O1 & O2 & O3). split; [lia|]. split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite O3; reflexivity|].
  intros a Ha. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.

Lemma ls_hpres : forall LBk spc scr (Wc : list L5.range) (M1 M2 : mem) g1, L5C.hpres L LBk spc scr Wc M1 M2 -> (forall w a, In w Wc -> L5.in_rng w a -> 2 ^ 40 <= a) -> g1 <> PML.LS0 -> PML.ls_ok g1 M1 -> PML.ls_ok g1 M2.
Proof.
  intros LBk spc scr Wc M1 M2 g1 HP HW Hg H. apply (PB2.ls_ok_keep M1 M2); [|exact Hg | exact H].
  intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). unfold PB2.ls_foot, PML.IMG_RO_HI in Ha. split; [lia|].
  split; [right; right; rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); split; [lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia]|].
  split; [unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia|]. intros w Hw Hin. pose proof (HW w a Hw Hin). lia.
Qed.

Lemma leaf_vec : forall i c k ps1 j, is_leaf i c k ps1 (CC.TOther VECPUSH) -> CH2.ret_of G.RETS i k = Some j -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j IL Hret.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. change (is_exit_pc VECPUSH) with false in XS. cbv iota in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  rewrite Z.eqb_refl in XS. cbv iota in XS.
  destruct (PB4.vecpush_chk GT.NF G.HDECL Pb 248 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  pose proof (CH2.leaves_all_sound _ _ _ vec2_ok _ _ _ _ _ IL) as X2. unfold PSM5.vec_chk2 in X2. rewrite Z.eqb_refl, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  destruct (kind_of i) eqn:K1; try discriminate. destruct (kind_of j) eqn:K2; try discriminate.
  destruct (PSM5.rviewv i c ps1 j (CC.cp_nx cj - APC.NCS - 2)%nat) as [[[[[pv lv] pe] ce] d]|] eqn:HRV; [|discriminate].
  apply andb_prop in X2 as [X2 Y6]. apply andb_prop in X2 as [X2 Y5]. apply andb_prop in X2 as [X2 Y4]. apply andb_prop in X2 as [X2 Y3]. apply andb_prop in X2 as [Y1 Y2]. apply Z.eqb_eq in Y4.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *.
  apply (PB6.vecpush_leaf_ok2 L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K (PSI.iHKnil I) XI
           (PSI.DEF0 I) Pb 248 eq_refl (P + 248) VADDR VOBJ VECPUSH_OK i c k ps1 j cj ci IL Hret Hcj Hpc Hchk).
  intros E1 E' R' M1 M' model1 cr1 b1 sbe sce c8 xv xk HagE' Hag HLF HA' HX HBL Hcell8 Hcellx Hxk HH1 HCR1.
    destruct (PSF.call_common I i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    destruct (rviewv_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & Hvwj & Hvars). fold nx in Hvwj, Hvars.
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
    destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg. apply Z.ltb_lt in Y3.
    pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Hst. rewrite AG1 in Hst. change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hst.
    assert (Hl1026 : (length stack <= 1026)%nat) by (apply (wf_len1026 psc HW eq_refl); unfold PML.ST_CR; clear - Hst Y3; lia).

    change (248 + 8) with 256 in Hcell8. rewrite Hcell8 in Y6. apply expr_eqb_eq in Y6. subst c8.
    destruct (PSM5.pushed_lit ps1 j) as [x|] eqn:Hpl; [|discriminate]. unfold PSM5.pushed_lit in Hpl. rewrite Y4 in Hxk. subst xk. rewrite Hcellx, Hcutj in Hpl.
    destruct xv as [xl| | | | | | |]; try discriminate. destruct (CAX.cell_at (CC.cp_know cj) (EVar 2) (-120) 1) as [[xl'| | | | | | |]|] eqn:Hcellj; try discriminate.
    lazymatch type of Hpl with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hpl as ->.
    apply andb_prop in Hb as [Hb Hx2]. apply andb_prop in Hb as [Hx0 Hx1]. apply Z.eqb_eq in Hx0. apply Z.leb_le in Hx1. apply Z.ltb_lt in Hx2. subst xl'.

    destruct (PSF.other_facts _ _ _ _ _ IL) as (Fnf & F2). destruct b1 as [pe2 ce2]. cbn [fst snd].
    assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2); exact Hden).
    destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    pose proof HdenE' as HdE. rewrite HBL, !PB.den_cons in HdE. change (CH2.den E' []) with (@nil (Z * Z)) in HdE. injection HdE as Eb1 Eb2 Eb3 Eb4.
    pose proof Hden as HdE1. rewrite HBL, !PB.den_cons in HdE1. change (CH2.den E1 []) with (@nil (Z * Z)) in HdE1. injection HdE1 as Fb1 Fb2 Fb3 Fb4.
    rewrite Fb1 in C0, C1, C4. rewrite Fb2 in C1, C4. rewrite Fb3 in D0, D1, D4. rewrite Fb4 in D1, D4. clear C2 D2.
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _).
    rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1.
    assert (Hscap : In (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) [66; 132; 264; 528; 1056]) by exact (proj1 (proj2 (proj2 (proj2 HW)))).
    destruct (PSI.KXBX I) as (K0 & B0').
    assert (HCR1' : PPS.bufcred L cr1 (uv E1 ce) (PPS.stk_kx L (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) + kx) (PPS.stk_bx L (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) + bx)).
    { unfold PSI.Cred, PB.cap_of, PB.tl_of, PSI.KXf, PSI.BXf in HCR1. rewrite Hden in HCR1. cbn [hd tl snd] in HCR1. exact HCR1. }
    assert (GROW : Z.of_nat (length stack) = uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv) -> In (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) [66; 132; 264; 528]).
    { intros Q. cbn [In] in Hscap |- *. clear - Q Hscap Hl1026. lia. }
    exists stack. rewrite Eb3, Eb4, L3.
    split; [exact HSB|]. split; [exact HC2|]. split; [exact Hl1026|]. split; [exact HC3|]. split; [exact Hscap|].
    split; [intros Q; exact (proj1 (PSS.stk_grow L cr1 _ _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HCR1'))|].
    intros E2 M2 LBk spc b2 cap2 cr2 Hag2 HPRES Hincl (BR0 & BR1 & BR2) Hby Hden2 Hcase. fold nx in Hag2. rewrite Eb1, Eb2 in Hden2. rewrite PB2.uv_lit in Hby by (clear - Hx1 Hx2; lia).
    destruct (vecpush_blj _ _ _ _ _ _ _ _ _ _ Hchk) as (b1' & sbe' & sce' & HBLi' & HBLj). fold nx in HBLj. rewrite HBL in HBLi'. injection HBLi' as <- <- <-.
    assert (HagE2 : env_agree GT.NF E0 E2).
    { eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2|]]. pose proof (PSF.call_nf _ _ _ _ _ _ IL Hret) as Q. rewrite Hcutj in Q. exact Q. }
    pose proof Hden2 as HdJ. rewrite HBLj, !PB.den_cons in HdJ. change (CH2.den E2 []) with (@nil (Z * Z)) in HdJ. injection HdJ as _ _ G0 G1. fold (uv E2 (EVar nx)) in G0. fold (uv E2 (EVar (nx + 1))) in G1.
    assert (AGX : forall y, In y (pe :: ce :: PSM2.flds lv) -> uv E2 y = uv E' y) by (intros y Hy; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 y Hag2 (Hvars y Hy))).
    destruct (PSF.flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    destruct (HPAX true bd ltac:(rewrite L11; exact HC8) ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite L13 in Hlen.
    pose proof (PSB.pa_buf _ _ _ HPA) as HBUF. cbn [PSI.ps_of PML.ps_bptr PML.ps_buf] in HBUF. rewrite L6 in HBUF.
    assert (Hcap2 : Z.of_nat (length stack) + 1 <= cap2 /\ In cap2 [66; 132; 264; 528; 1056]).
    { destruct Hcase as [(_ & -> & _ & Q)|(-> & _ & Q)]; [split; [clear - Q; lia | exact Hscap]|]. specialize (GROW Q). cbn [In] in GROW |- *. clear - Q GROW. lia. }
    destruct Hcap2 as (Hcap2 & Hcapin).
    split.
    - unfold PSI.XI. rewrite K2, Hvwj.
      split; [rewrite PSI.SCRV in *; apply (PSF.hpres_def I _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1] | unfold hl_ceil; clear - CL; lia | clear - O2 O3; lia]|].
      split; [exact CM1|]. split; [exact CM2|].
      exists true, bd, (stack ++ [x]), bufm.
      assert (Usl : uv E2 (APC.eaddz (PSU2.esub (PB4.pv_send lv) (PB4.pv_sb lv)) 1) = Z.of_nat (length stack) + 1).
      { rewrite PB.uv_eaddz. unfold PSU2.esub, PSU.esub. rewrite PB.uv_esub, Asend, Asb, L3, L2, HC2.
        replace (uv E1 (PB4.pv_sb pv) + Z.of_nat (length stack) - uv E1 (PB4.pv_sb pv)) with (Z.of_nat (length stack)) by (clear; lia).
        rewrite (Z.mod_small (Z.of_nat (length stack))) by (clear - Hl1026; lia). apply Z.mod_small. clear - Hl1026; lia. }
      assert (Usend : uv E2 (PSU2.eadd (EVar nx) (APC.eaddz (PSU2.esub (PB4.pv_send lv) (PB4.pv_sb lv)) 1)) = b2 + Z.of_nat (length stack) + 1).
      { unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd, Usl, G0. unfold hl_ceil in *. rewrite Z.mod_small by (clear - BR0 BR1 S4 Hcap2; lia). clear; lia. }
      assert (Uscend : uv E2 (PSU2.eadd (EVar nx) (EVar (nx + 1))) = b2 + cap2).
      { unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd, G0, G1. unfold hl_ceil in *. apply Z.mod_small. clear - BR0 BR1 BR2 S4; lia. }
      split.
      { unfold PSI.contents, PSM5.set_vec. cbn [PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wend PB4.pv_wptr PB4.pv_size PB4.pv_st PB4.pv_more PB4.pv_done].
        rewrite Usend, Uscend, G0, Ape, Ace, Awend, Awptr, Ast, Amore, Adone, Asize. rewrite L5, L7, L6, L13, L11, L12. rewrite length_app. cbn [length].
        split; [exact Hby|]. split; [clear; lia|]. split; [clear - Hcap2; lia|]. split; [reflexivity|]. split; [clear - HC5 L14 L15 L16; lia|]. split; [exact Hlen|].
        split; [clear - Hlen HC6 HC6b; lia|].
        split; [intros Hn; exfalso; rewrite L8 in Hn; change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hn; unfold PML.ST_NUMBER in Hn; clear - Hn Hst Y3; lia|]. split; [exact HC8 | exact HC9]. }
      split; [apply (ls_hpres _ _ _ _ M' M2 g HPRES); [intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; clear - Hin O1 O2; lia | exact (PSI.iHG I) | exact (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS)]|].
      rewrite Hcutj, Hcellj. exists stack. split; [reflexivity|].
      assert (HPS : PSI.ps_of (PSM5.set_vec lv (EVar nx) (PSU2.eadd (EVar nx) (APC.eaddz (PSU2.esub (PB4.pv_send lv) (PB4.pv_sb lv)) 1)) (PSU2.eadd (EVar nx) (EVar (nx + 1)))) pe ce E2 true bd stack bufm
                    = PML.PS (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd (PML.ps_level psc) (PML.ps_stack psc) b2 cap2 (uv E1 ce) (uv E1 pe) bufm (PB4.win_of (uv E' (PB4.pv_wptr lv)) wend)).
      { unfold PSI.ps_of at 1, PSM5.set_vec. cbn [PB4.pv_level PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wend PB4.pv_wptr PB4.pv_size PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_more PB4.pv_done].
        rewrite Uscend, G0, Ape, Ace, Alevel, Awend, Awptr, Ast, Asst, Anst. rewrite L1, L5, L6, L7, L8, L9, L10. replace (b2 + cap2 - b2) with cap2 by (clear; lia). reflexivity. }
      rewrite HPS. clear HPS.
      assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> bufm = PML.ps_buf psc) by (intros Hn _; exfalso; unfold PML.ST_NUMBER in Hn; clear - Hn Hst Y3; lia).
      split; [exact (wf_vec psc bd b2 cap2 _ _ bufm _ HW Hcapin Hbufeq)|].
      pose proof (PSI.WIN I) as (W0 & W1 & _).
      assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
      split.
      { destruct HB as [HB1 HB2]. split; [|exact HB2]. cbn [PML.ps_buf]. rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia).
        match goal with |- _ + _ + PML.buf_need ?p <= _ => replace (PML.buf_need p) with (PML.buf_need psc) by reflexivity end.
        unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1. clear - HB1 Hwl1 Hlen HC6 L14 L15. lia. }
      split; [exact (PSSC.lvl_same psc _ (proj1 (proj1 HWS)) eq_refl eq_refl eq_refl eq_refl) | exact (proj2 (proj1 HWS))].
    - unfold PSI.Cred, PB.cap_of, PB.tl_of, PSI.KXf, PSI.BXf. rewrite Hden2. cbn [hd tl snd].
      destruct Hcase as [(_ & -> & -> & _)|(-> & -> & Q)]; [exact HCR1'|].
      exact (proj2 (PSS.stk_grow L cr1 _ _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) K0 B0' (GROW Q) HCR1')).
Qed.

Hypothesis PUSHB_OK : PMS.str_push_back_spec L HI.
Lemma OADDR : estart E0 (SA Pb 224) = P + 224.
Proof. unfold estart. cbn [a_base a_off]. fold (uv E0 Pb). pose proof (PSI.UU I) as (_ & U10 & _). unfold uv, Pb. cbn [edenot]. rewrite U10. reflexivity. Qed.
Lemma OBJ : sp <= P + 224 /\ P + 224 + 24 <= hl_sptop L /\ (P + 224) mod 8 = 0 /\ (forall a, P + 224 <= a < P + 224 + 24 -> exists w, In w W /\ L5.in_rng w a).
Proof.
  destruct (PSI.iOP I) as (O1 & O2 & O3). split; [lia|]. split; [lia|]. split; [rewrite Z.add_mod by lia; rewrite O3; reflexivity|].
  intros a Ha. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.

Lemma leaf_pushb : forall i c k ps1 j, is_leaf i c k ps1 (CC.TOther PUSHB) -> CH2.ret_of G.RETS i k = Some j -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j IL Hret.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. change (is_exit_pc PUSHB) with false in XS. cbv iota in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  change (PUSHB =? VECPUSH) with false in XS. rewrite Z.eqb_refl in XS. cbv iota in XS.
  destruct (PB4.pushbc_chk GT.NF G.HDECL Pb 224 132 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  pose proof (CH2.leaves_all_sound _ _ _ pushb2_ok _ _ _ _ _ IL) as X2. unfold PSM6.pushb_chk2 in X2. rewrite Z.eqb_refl, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  destruct (kind_of i) eqn:K1; try discriminate. destruct (kind_of j) eqn:K2; try discriminate.
  destruct (PSM6.rviewb i c ps1 j (CC.cp_nx cj - APC.NCS - 2)%nat) as [[[[[pv lv] pe] ce] d]|] eqn:HRV; [|discriminate].
  apply andb_prop in X2 as [X2 Y11]. apply andb_prop in X2 as [X2 Y10]. apply andb_prop in X2 as [X2 Y9]. apply andb_prop in X2 as [X2 Y8]. apply andb_prop in X2 as [X2 Y7]. apply andb_prop in X2 as [X2 Dc].
  apply andb_prop in X2 as [X2 Ddone]. apply andb_prop in X2 as [X2 Dmore]. apply andb_prop in X2 as [X2 Dnst]. apply andb_prop in X2 as [Dst Dsst]. apply expr_eqb_eq in Y9.
  destruct (PSM2.d_st d) eqn:Est; [discriminate|]. destruct (PSM2.d_sst d) eqn:Esst; [discriminate|]. destruct (PSM2.d_nst d) eqn:Enst; [discriminate|]. destruct (PSM2.d_more d) eqn:Emore; [discriminate|].
  destruct (PSM2.d_done d) eqn:Edone; [discriminate|]. clear Dst Dsst Dnst Dmore Ddone.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *.
  apply (PB6.pushbc_leaf_ok2 L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K (PSI.iHKnil I) XI
           (PSI.DEF0 I) (P + 248) VOBJ Pb 224 eq_refl (P + 224) OADDR OBJ (PSI.KXf I) (PSI.BXf I) (PSI.CRED_EQ I) PUSHB_OK 132 i c k ps1 j cj ci IL Hret Hcj Hpc Hchk).
  intros E1 E' R' M1 M' model1 pe2 ce2 BLk se HagE' Hag HLF HA' HX HBL Hcell.
    destruct (PSF.call_common I i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    destruct (rviewb_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & Hvwj & Hvars). fold nx in Hvwj, Hvars.
    unfold PSI.XI in HX. destruct HX as (X1 & X2' & X3 & HX). rewrite K1, (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
    assert (HGR0 : mem_grows M' M') by (intros x0 Hx0; exact Hx0).
    destruct (PSB.leaf_state_g I i c k ps1 _ pv lv pe ce d E1 E' R' M1 M' M' model1 bm bd stack buf IL HLD HA' HGR0 Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    rewrite Est in L8. rewrite Esst in L9. rewrite Enst in L10. rewrite Emore in L11. rewrite Edone in L12. rewrite Dc in L13. cbn [PSB.newv] in *.
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
    assert (Hbmt : bm = true) by (apply PSB.b2z_inj1; rewrite <- HC8, <- AG2; exact (PSB.rng_is_sound E' M' _ _ 1 HKc Y7)). subst bm.
    set (psc := PSI.ps_of pv pe ce E1 true bd stack buf) in *.
    destruct (PSM2.rng_of (SR.ps_cells ps1) (PB4.pv_st pv)) as [lo hi] eqn:Hrg. apply Z.ltb_lt in Y8.
    pose proof (PSB.rng_of_sound E' M' _ _ lo hi HKc Hrg) as Hst. rewrite AG1 in Hst. change (uv E1 (PB4.pv_st pv)) with (PML.ps_st psc) in Hst.
    rewrite Hcell in Y11. apply expr_eqb_eq in Y11. subst se.
    exists []. split; [intros q Hq; cbn [length] in Hq; lia|]. split; [rewrite L13; reflexivity|].
    intros E2 M2 LBk spc cap2 p2 Hag2 HPRES Hincl HLBk (BR0 & BR1 & BR2) Hstr Hden2. fold nx in Hag2. cbn [app] in Hstr.
    set (cv := uv E' (nth 11 (CA.ps_reglist ps1) (ELit 0))) in *.
    destruct (pushbc_blj _ _ _ _ _ _ _ _ _ _ _ Hchk) as (pe' & ce' & BLk' & HBLi' & HBLj). fold nx in HBLj. rewrite HBL in HBLi'. injection HBLi' as <- <- <-.
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe3 & ce3 & sbe & sce & HBL3). rewrite HBL in HBL3. injection HBL3 as -> -> ->.
    assert (HagE2 : env_agree GT.NF E0 E2).
    { eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2|]]. pose proof (PSF.call_nf _ _ _ _ _ _ IL Hret) as Q. rewrite Hcutj in Q. exact Q. }
    destruct (PSF.other_facts _ _ _ _ _ IL) as (Fnf & F2).
    assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2); exact Hden).
    destruct (PSB.own_blocks I i E1 M' model1 pe3 ce3 sbe sce HA' HBL) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    pose proof HdenE' as HdE. rewrite HBL, !PB.den_cons in HdE. change (CH2.den E' []) with (@nil (Z * Z)) in HdE. injection HdE as Eb1 Eb2 Eb3 Eb4.
    pose proof Hden as HdE1. rewrite HBL, !PB.den_cons in HdE1. change (CH2.den E1 []) with (@nil (Z * Z)) in HdE1. injection HdE1 as Fb1 Fb2 Fb3 Fb4.
    rewrite Fb1 in C0, C1, C4. rewrite Fb2 in C1, C4. rewrite Fb3 in D0, D1, D4. rewrite Fb4 in D1, D4. clear C2 D2.
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _).
    rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1.
    rewrite HBLj, !PB.den_cons in Hden2. change (CH2.den E2 []) with (@nil (Z * Z)) in Hden2. change (CH2.den E' []) with (@nil (Z * Z)) in Hden2. injection Hden2 as G0 G1 _ _.
    fold (uv E2 (EVar nx)) in G0. fold (uv E2 (PSU.emul2 (EVar (nx + 1)))) in G1.
    assert (AGX : forall y, In y (pe :: ce :: PSM2.flds lv) -> uv E2 y = uv E' y) by (intros y Hy; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 y Hag2 (Hvars y Hy))).
    destruct (PSF.flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    destruct Hstr as ((_ & _ & _ & _ & Hby & _) & _ & Hlt). cbn [length] in Hlt.
    assert (KEEP : forall (bs : list Z), Z.of_nat (length bs) <= uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv) -> L5.bytes_at RSEGS M' (uv E1 (PB4.pv_sb pv)) bs -> L5.bytes_at RSEGS M2 (uv E1 (PB4.pv_sb pv)) bs).
    { intros bs Hn HBs. apply (PSF.hpres_blk I _ _ _ _ M' M2 _ (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) bs HPRES); [| exact Hn | clear - D0; lia | unfold hl_ceil in *; clear - D4 S4; lia | | | exact HBs].
      - exists (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)). cbn [fst snd]. split; [|clear; lia]. rewrite HLBk, PB.den_cons. change (CH2.den E' []) with (@nil (Z * Z)). cbn [app].
        left. fold (uv E' sbe) (uv E' sce). rewrite Eb3, Eb4. reflexivity.
      - intros w [<-|[]] q Hq. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in *. clear - Hq D4 CL O2. lia.
      - intros q Hq. unfold in_errno. rewrite (PmLayout.ly_errno L LAY). unfold hl_ceil in *. clear - Hq D0 D1. lia. }
    unfold PSI.XI. rewrite K2, Hvwj.
    split; [rewrite PSI.SCRV in *; apply (PSF.hpres_def I _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1] | unfold hl_ceil; clear - CL; lia | clear - O2 O3; lia]|].
    split; [exact CM1|]. split; [exact CM2|].
    exists true, bd, stack, [cv].
    split.
    { unfold PSI.contents, PSM6.set_size. cbn [PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wend PB4.pv_wptr PB4.pv_size PB4.pv_st PB4.pv_more PB4.pv_done].
      rewrite PB.uv_eaddz, G0, G1, Awend, Awptr, Ast, Amore, Adone, Asize, Asb, Asend, Ascend. rewrite L2, L3, L4, L5, L13, L11, L12. cbn [length].
      split; [exact (KEEP _ HC3 HSB)|]. split; [exact HC2|]. split; [exact HC3|]. split; [reflexivity|]. split; [clear - HC5 L14 L15 L16; lia|]. split; [reflexivity|].
      split; [clear - BR2; lia|]. split; [intros _; exact Hby|]. split; [exact HC8 | exact HC9]. }
    split; [apply (ls_hpres _ _ _ _ M' M2 g HPRES); [intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; clear - Hin O1 O2; lia | exact (PSI.iHG I) | exact (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS)]|].
    split; [rewrite Y9; unfold cv; f_equal; symmetry; apply (PB.uv_agree _ E' E2 _ Hag2); rewrite <- Y9; exact Y10|].
    split; [rewrite G0; exact Hby|].
    assert (HPS : PSI.ps_of (PSM6.set_size lv (APC.eaddz (PB4.pv_size lv) 1)) (EVar nx) (PSU.emul2 (EVar (nx + 1))) E2 true bd stack []
                  = PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) (PML.ps_more psc) bd cap2 p2 [] (PB4.win_of (uv E' (PB4.pv_wptr lv)) wend)).
    { unfold PSI.ps_of at 1, PSM6.set_size. cbn [PB4.pv_level PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wend PB4.pv_wptr PB4.pv_size PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_more PB4.pv_done].
      rewrite G0, G1, Alevel, Awend, Awptr, Ast, Asst, Anst, Asb, Ascend. rewrite L1, L2, L4, L5, L8, L9, L10. reflexivity. }
    rewrite HPS. clear HPS.
    assert (Hbufeq : PML.ps_st psc = PML.ST_NUMBER -> PML.ps_more psc = true -> [] = PML.ps_buf psc) by (intros Hn _; exfalso; unfold PML.ST_NUMBER in Hn; clear - Hn Hst Y8; lia).
    split; [exact (PSX.wf_upd_same psc bd _ _ [] _ HW Hbufeq)|].
    pose proof (PSI.WIN I) as (W0 & W1 & _).
    assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
    split.
    { destruct HB as [HB1 HB2]. split; [|exact HB2]. unfold PSS.upd at 1 2. cbn [PML.ps_buf length]. rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia).
      replace (PML.buf_need (PSS.upd psc _ _ _ _ _ _ _ _ _)) with (PML.buf_need psc) by reflexivity. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1. clear - HB1 Hwl1 L14 L15. lia. }
    split; [exact (PSSC.lvl_same psc _ (proj1 (proj1 HWS)) eq_refl eq_refl eq_refl eq_refl) | exact (proj2 (proj1 HWS))].
Qed.
End H.
End PSH.
