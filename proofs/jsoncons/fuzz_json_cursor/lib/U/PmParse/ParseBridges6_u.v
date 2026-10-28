(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PB6.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Lemma nodup_swap : forall (a b : Z) l, base.NoDup (a :: b :: l) -> base.NoDup (b :: a :: l).
Proof.
  intros a b l H. inversion H as [|x l0 N1 N2]; subst. inversion N2 as [|y l1 N3 N4]; subst.
  constructor; [|constructor; [|exact N4]].
  - intros X. apply list_elem_of_In in X. destruct X as [->|X]; [apply N1; apply list_elem_of_In; left; reflexivity | apply N3; apply list_elem_of_In; exact X].
  - intros X. apply N1. apply list_elem_of_In. right. apply list_elem_of_In in X. exact X.
Qed.

Section Inst6.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.

Hypothesis CRED_BLK : forall i j E E2 cr, CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS []) -> Cred i E cr -> Cred j E2 cr.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Variable VB : expr.
Variable VK : Z.
Hypothesis VB_frozen : APC.expr_vars_lt NF VB = true.
Variable vaddr : Z.
Hypothesis VADDR : estart E0 (SA VB VK) = vaddr.
Hypothesis VOBJ : sp0 <= vaddr /\ vaddr + 24 <= hl_sptop L /\ vaddr mod 8 = 0 /\ forall a, vaddr <= a < vaddr + 24 -> exists w, In w W /\ L5.in_rng w a.
Hypothesis VECPUSH : PMS.vec_push_spec L HI.

Lemma vecpush_leaf_ok2 : forall i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_VEC_PUSH) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_VEC_PUSH ->
  PB4.vecpush_chk NF d VB VK c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr b1 sbe sce c8 xv xk,
      env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M ->
      nth i BLS [] = [b1; (sbe, sce)] -> CAX.cell_at (SR.ps_cells ps) VB (VK + 8) 8 = Some c8 -> CAX.cell_at (SR.ps_cells ps) (EVar 2) xk 1 = Some xv -> snd (split_lit (nth 11 (CA.ps_reglist ps) (ELit 0))) = xk ->
      hi_heap HI (CH2.cur LBrest BLS i E) cr M' (m_vmmaps model) -> Cred i E cr ->
      exists st : list Z,
        L5.bytes_at RSEGS M' (uv E' sbe) st /\ uv E' c8 = uv E' sbe + Z.of_nat (length st) /\ (length st <= 1026)%nat /\ Z.of_nat (length st) <= uv E' sce /\
        In (uv E' sce) [66; 132; 264; 528; 1056] /\
        (Z.of_nat (length st) = uv E' sce -> credit_ok L cr (2 * uv E' sce)) /\
        forall E2 (M2 : mem) LBk spc b' cap' cr2,
          env_agree (CC.cp_nx cj - APC.NCS - 2) E' E2 -> L5C.hpres L LBk spc PB4.VEC_SCR [(vaddr, 24)] M' M2 -> incl LBrest LBk ->
          4096 <= b' /\ b' + cap' <= hl_ceil L /\ 66 <= cap' <= 1056 ->
          L5.bytes_at RSEGS M2 b' (st ++ [uv E' xv]) ->
          CH2.den E2 (nth j BLS []) = [(uv E' (fst b1), uv E' (snd b1)); (b', cap')] ->
          ((b' = uv E' sbe /\ cap' = uv E' sce /\ cr2 = cr /\ Z.of_nat (length st) < uv E' sce) \/
           (cap' = 2 * uv E' sce /\ cr2 = debit L cr (2 * uv E' sce) /\ Z.of_nat (length st) = uv E' sce)) ->
          XI j E2 M2 /\ Cred j E2 cr2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold PB4.vecpush_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (split_lit (nth 11 (CA.ps_reglist ps) (ELit 0))) as [xb xk] eqn:Hsplitx.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp0] eqn:Hsplits.
  destruct (nth i BLS []) as [|b1 [|[sbe sce] [|? ?]]] eqn:HBLi; try discriminate.
  destruct (CAX.cell_at (SR.ps_cells ps) ob ok 8) as [c0|] eqn:Hcell0; [|discriminate].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [c8|] eqn:Hcell8; [|discriminate].
  destruct (CAX.cell_at (SR.ps_cells ps) xb xk 1) as [xv|] eqn:Hcellx; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  repeat (apply andb_prop in Hb as [Hb ?B]).
  apply expr_eqb_eq in Hb, B9, B6. apply Z.eqb_eq in B10. apply Z.leb_le in B8. apply Z.ltb_lt in B7. apply CH2.blocks_eqb_eq in B1. subst ob ok xb c0.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              PB4.VEC_SCR 2%nat [b1] _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.
  assert (Ho : estart E' (SA VB VK) = vaddr) by (rewrite (PB.estart_agree NF E0 E' VB VK HagE' VB_frozen); exact VADDR).
  destruct VOBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  destruct (USER E E' R' M M' model cr b1 sbe sce c8 xv xk HagE' Hag HLF HA' HXI0 eq_refl Hcell8 Hcellx ltac:(try rewrite Hsplitx; reflexivity) HH HC)
    as (st & Hst & Hc8v & Hl1026 & Hlcap & Hcapin & Hcred & UPOST).
  set (b := uv E' sbe) in *. set (cap := uv E' sce) in *. set (x := uv E' xv) in *.
  pose proof (PB.prove_ok E' M' cells _ HK B4) as Hx255. cbn [kentry_ok] in Hx255. fold (uv E' xv) in Hx255. fold x in Hx255.
  pose proof (PB.prove_ok E' M' cells _ HK B3) as Hcapr. cbn [kentry_ok] in Hcapr. fold (uv E' sce) in Hcapr. fold cap in Hcapr.
  pose proof (PB.prove_ok E' M' cells _ HK B2) as Hbr. cbn [kentry_ok] in Hbr. fold (uv E' sbe) in Hbr. fold b in Hbr.

  assert (Ho8 : estart E' (SA VB (VK + 8)) = vaddr + 8) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  assert (Ho16 : estart E' (SA VB (VK + 16)) = vaddr + 16) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  pose proof (PB2.kword64_elim E' M' _ _ vaddr (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcell0) Ho) as C0. fold b in C0.
  pose proof (PB2.kword64_elim E' M' _ _ (vaddr + 8) (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcell8) Ho8) as C8. rewrite Hc8v in C8.
  pose proof (PB2.kword64_elim E' M' _ _ (vaddr + 16) (PB.has_ok E' M' cells _ HK B5) Ho16) as C16.
  assert (U16 : uv E' (PSU.eadd sbe sce) = b + cap) by (unfold PSU.eadd; rewrite PB.uv_eadd; fold b cap; apply Z.mod_small; lia). rewrite U16 in C16.
  assert (Hxa : estart E' (SA (EVar 2) xk) = sp0 + xk).
  { unfold estart. cbn [a_base a_off edenot]. destruct HagE' as [Hev _]. rewrite <- (Hev 2%nat) by lia. rewrite SP0. reflexivity. }
  pose proof (PB2.kword8_elim E' M' _ _ (sp0 + xk) (PB2.cell_at_ok E' M' cells _ _ _ _ HK Hcellx) Hxa) as CX. fold x in CX.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 vaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 (sp0 + xk)).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplitx). f_equal. exact Hxa. }
  assert (Hcsp : CH2.ci_csp ci = csp0).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
    lazymatch type of Hchk with (if ?bb then _ else _) = _ => destruct bb; [|discriminate] end. injection Hchk as ->.
    unfold CH2.common_chk_x in Hc0. destruct (nth 1 (CA.ps_reglist ps) (ELit 0)); try discriminate. rewrite Hsplits in Hc0.
    destruct spb as [|[|[|[|]]]| | | | | |]; try discriminate. lazymatch type of Hc0 with (if ?bb then _ else _) = _ => destruct bb; [|discriminate] end. injection Hc0 as <-. reflexivity. }

  unfold CH2.cur in HH. rewrite <- Hden, HBLi in HH. unfold CH2.den in HH. cbn [map fst snd] in HH. fold (uv E' (fst b1)) (uv E' (snd b1)) (uv E' sbe) (uv E' sce) in HH. fold b cap in HH.
  set (b1v := (uv E' (fst b1), uv E' (snd b1))) in *. cbn [app] in HH.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & Hcr1).
  assert (Nb1 : fst b1v <> b).
  { cbn [map fst] in Hnd. inversion Hnd as [|y l N1 N2]; subst. intros X. apply N1. apply list_elem_of_In. left. symmetry. exact X. }
  assert (Hrm : lb_remove b (b1v :: (b, cap) :: LBrest) = b1v :: LBrest).
  { cbn [lb_remove fst]. destruct (Z.eqb_spec (fst b1v) b) as [X|_]; [contradiction|]. rewrite Z.eqb_refl. reflexivity. }

  rewrite Hpc. rewrite LS.
  apply (VECPUSH (b1v :: (b, cap) :: LBrest) cr vaddr b cap (sp0 + xk) x (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) st fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [exact CX|]. split; [rewrite Hcsp; lia|]. split; [exact C0|]. split; [exact C8|]. split; [exact C16|]. split; [exact Hst|].
    split; [right; left; reflexivity|]. split; [exact Hlcap|]. split; [exact Hl1026|]. split; [unfold PML.obj_on_stack; lia | exact Hcred]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [HWc Hpost] HRP HPRES Hbv2 HH2.
  rewrite Hrm in Hpost.
  assert (EXP : exists b' cap', PML.u64 M2 vaddr b' /\ PML.u64 M2 (vaddr + 8) (b' + Z.of_nat (length st) + 1) /\ PML.u64 M2 (vaddr + 16) (b' + cap') /\ L5.bytes_at RSEGS M2 b' (st ++ [x]) /\
            hi_heap HI (b1v :: (b', cap') :: LBrest) cr' M2 (m_vmmaps model2) /\ LBk = b1v :: LBrest /\ 66 <= cap' <= 1056 /\ Z.of_nat (length st) + 1 <= cap' /\
            ((b' = b /\ cap' = cap /\ cr' = cr /\ Z.of_nat (length st) < cap) \/ (cap' = 2 * cap /\ cr' = debit L cr (2 * cap) /\ Z.of_nat (length st) = cap))).
  { destruct Hpost as [(G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7) | (G0 & b' & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8)].
    - exists b, cap. rewrite G5 in HH2. subst LBk. repeat split; try assumption; try lia. left. repeat split; try assumption.
    - exists b', (2 * cap). subst LBk. rewrite G6 in HH2.
      assert (Hc528 : cap <= 528) by (cbn [In] in Hcapin; lia).
      repeat split; try assumption; try lia.
      + replace (b' + Z.of_nat (length st) + 1) with (b' + cap + 1) by lia. exact G2.
      + destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (_ & Hnd2 & _).
        apply (hio_perm L SCFG HI HIok _ (b1v :: (b', 2 * cap) :: LBrest) _ _ _ HH2).
        * intros y. cbn [In]. tauto.
        * cbn [map fst] in Hnd2 |- *. apply nodup_swap. exact Hnd2.
      + right. repeat split; try assumption. }
  destruct EXP as (b' & cap' & D0 & D8 & D16 & Dst & HH3 & -> & Hcap' & Hlc' & Hcase).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH3) as (Hwf3 & Hnd3 & _).
  destruct (Hwf3 (b', cap') ltac:(right; left; reflexivity)) as (BR & BD & BA). cbn [fst snd] in BR, BD, BA. pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  assert (Nb3 : fst b1v <> b').
  { cbn [map fst] in Hnd3. inversion Hnd3 as [|y l N1 N2]; subst. intros X. apply N1. apply list_elem_of_In. left. symmetry. exact X. }
  assert (BA' : blocks_apart b' cap' (CH2.den E' [b1] ++ LBrest)).
  { cbn [lb_remove fst] in BA. destruct (Z.eqb_spec (fst b1v) b') as [X|_]; [contradiction|]. rewrite Z.eqb_refl in BA. exact BA. }

  set (ghosts := [Z_to_bv 64 b'; Z_to_bv 64 cap']).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  unfold hl_ceil in *.
  assert (G0 : bv_unsigned (ev E2 nx) = b') by (pose proof (PB2.ghost_val E' nx ghosts R2 0 b' eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap') by (apply (PB2.ghost_val E' nx ghosts R2 1 cap' eq_refl); [cbn; lia | lia]).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = [b1v; (b', cap')]).
  { rewrite B1. unfold CH2.den. cbn [map fst snd edenot]. rewrite G0, G1.
    pose proof (CH2.den_agree nx E' E2 [b1] Hag2 B0) as Dg. unfold CH2.den in Dg. cbn [map] in Dg. injection Dg as Dg1 Dg2. rewrite Dg1, Dg2. reflexivity. }
  destruct (UPOST E2 M2 (b1v :: LBrest) (sp0 + CH2.ci_csp ci) b' cap' cr' Hag2 ltac:(subst Wc; exact HPRES) ltac:(intros y Hy; right; exact Hy) ltac:(unfold hl_ceil; lia) Dst Hden2 Hcase) as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts (b1v :: LBrest) Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros y Hy. exact Hy.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (VB, VK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. fold E2.
    assert (Hest : estart E2 (SA VB VK) = vaddr) by (rewrite (PB.estart_agree NF E0 E2 VB VK HagE2 VB_frozen); exact VADDR).
    assert (Vc8 : APC.expr_vars_lt nx c8 = true).
    { destruct (PB.cell_at_has _ _ _ _ _ Hcell8) as (bb & Hin & ->). pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vk]. rewrite Hnx in Vk. exact Vk. }
    assert (Vsb : APC.expr_vars_lt nx sbe = true).
    { destruct (PB.cell_at_has _ _ _ _ _ Hcell0) as (bb & Hin & ->). pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vk]. rewrite Hnx in Vk. exact Vk. }
    assert (Usl : uv E2 (APC.eaddz (PSU2.esub c8 sbe) 1) = Z.of_nat (length st) + 1).
    { rewrite PB.uv_eaddz. unfold PSU2.esub, PSU.esub. rewrite PB.uv_esub, (PB.uv_agree nx E' E2 c8 Hag2 Vc8), (PB.uv_agree nx E' E2 sbe Hag2 Vsb), Hc8v. fold b.
      replace (b + Z.of_nat (length st) - b) with (Z.of_nat (length st)) by lia. rewrite (Z.mod_small (Z.of_nat (length st))) by lia. apply Z.mod_small. lia. }
    apply in_app_or in HX as [HX|HX].
    + rewrite LS. unfold PSU2.vec_cells in HX. cbn [In] in HX. destruct HX as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      * eapply CL5.kword64_intro with (A := vaddr) (z := b'); [exact Hest | lia | lia | cbn [edenot]; rewrite <- G0; symmetry; apply Z_to_bv_bv_unsigned | exact D0].
      * eapply CL5.kword64_intro with (A := vaddr + 8) (z := b' + Z.of_nat (length st) + 1); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | | exact D8].
        apply PB.edenot_of_uv. unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd, Usl. unfold uv at 1. cbn [edenot]. rewrite G0. rewrite Z.mod_small by lia. lia.
      * eapply CL5.kword64_intro with (A := vaddr + 16) (z := b' + cap'); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | | exact D16].
        apply PB.edenot_of_uv. unfold PSU2.eadd, PSU.eadd. rewrite PB.uv_eadd. unfold uv. cbn [edenot]. rewrite G0, G1. rewrite Z.mod_small by lia. lia.
      * cbn [kentry_ok edenot]. rewrite G1. lia.
      * assert (Ud : uv E2 (PSU2.esub (EVar (nx + 1)) (APC.eaddz (PSU2.esub c8 sbe) 1)) = cap' - (Z.of_nat (length st) + 1)).
        { unfold PSU2.esub at 1. unfold PSU.esub. rewrite PB.uv_esub, Usl. unfold uv. cbn [edenot]. rewrite G1. apply Z.mod_small. lia. }
        cbn [kentry_ok]. fold (uv E2 (PSU2.esub (EVar (nx + 1)) (APC.eaddz (PSU2.esub c8 sbe) 1))). rewrite Ud. lia.
    + rewrite forallb_forall in B. specialize (B X HX).
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 [b1] cells nx (EVar (nx + 1)) b' cap' X HagE' HK0 Hag2 G0 ltac:(unfold elenZ; cbn [edenot]; exact G1) BR BA' BD B).
  -
    rewrite Hnx. fold E2. split; [|exact HXI2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) PB4.VEC_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 (b1v :: LBrest) Wc cr' CF HPRES).
    + intros y Hy. right. exact Hy.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + unfold CH2.cur. rewrite Hden2. exact HH3.
    + rewrite Hnx. exact Hag2.
    + exact HC2.
Qed.

Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Variable oaddr : Z.
Hypothesis OADDR : estart E0 (SA OB OK) = oaddr.
Hypothesis OBJ : sp0 <= oaddr /\ oaddr + 24 <= hl_sptop L /\ oaddr mod 8 = 0 /\ forall a, oaddr <= a < oaddr + 24 -> exists w, In w W /\ L5.in_rng w a.
Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).
Hypothesis PUSHB : PMS.str_push_back_spec L HI.

Lemma pushbc_leaf_ok2 : forall KMIN i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_STR_PUSH_BACK) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_STR_PUSH_BACK ->
  PB4.pushbc_chk NF d OB OK KMIN c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model pe ce BLk se, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M ->
     nth i BLS [] = (pe, ce) :: BLk -> CAX.cell_at (SR.ps_cells ps) OB (OK + 8) 8 = Some se ->
     exists s : list Z,
       L5.bytes_at RSEGS M' (uv E' pe) s /\ Z.of_nat (length s) = uv E' se /\
       (forall E2 (M2 : mem) LBk spc cap' p', env_agree (CC.cp_nx cj - APC.NCS - 2) E' E2 -> L5C.hpres L LBk spc PB.STR_SCR [(oaddr, 24)] M' M2 -> incl LBrest LBk ->
          LBk = CH2.den E' BLk ++ LBrest -> 4096 <= p' /\ p' + cap' <= hl_ceil L /\ 2 * KMIN <= cap' <= 2 ^ 27 ->
          PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ [uv E' (nth 11 (CA.ps_reglist ps) (ELit 0))])) ->
          CH2.den E2 (nth j BLS []) = (p', cap') :: CH2.den E' BLk ->
          XI j E2 M2)) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros KMIN i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold PB4.pushbc_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (nth i BLS []) as [|[pe ce] BLk] eqn:HBLi; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|] eqn:Hcell; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B7]. apply andb_prop in Hb as [Hb B6b]. apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4].
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3. subst ob ok.
  apply CH2.blocks_eqb_eq in B6.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              PB.STR_SCR 2%nat BLk _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.

  assert (Ho : estart E' (SA OB OK) = oaddr) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct OBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  assert (Hpd0 : L5.defined M' (uv E' pe) (uv E' ce)).
  { unfold CH2.cur in HH. rewrite <- Hden, HBLi, PB.den_cons in HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf0 & _). exact (proj1 (proj2 (Hwf0 _ (or_introl eq_refl)))). }
  destruct (PB4.str_viewx E' M' cells OB OK pe ce se (2 * KMIN) (2 ^ 26 - 2) HK B4 ltac:(lia) ltac:(rewrite Ho; lia) ltac:(rewrite Ho; lia) Hpd0) as (sv & Hstrv & Hlenv & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite Ho in Hstrv.
  destruct (USER E E' R' M M' model pe ce BLk se HagE' Hag HLF HA' HXI0 eq_refl Hcell) as (s & Hbs & Hlen & UCONT).
  assert (Hstr : PML.str_at M' oaddr (PML.SLong (uv E' ce) (uv E' pe) s)) by (apply (PB3.str_retext M' oaddr _ _ sv s Hstrv Hbs); apply Nat2Z.inj; rewrite Hlen, Hlenv; reflexivity). set (p := uv E' pe) in *. set (cap := uv E' ce) in *. set (size := uv E' se) in *.

  unfold CH2.cur in HH. rewrite <- Hden, HBLi, PB.den_cons in HH. fold p cap in HH. set (rest := CH2.den E' BLk ++ LBrest) in *.
  change ((p, cap) :: CH2.den E' BLk ++ LBrest) with ((p, cap) :: rest) in HH.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 oaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  pose proof (PB.fact_ok' E' M' cells _ HK B5) as Hc255. cbn [kentry_ok] in Hc255. set (cv := bv_unsigned (edenot E' (nth 11 (CA.ps_reglist ps) (ELit 0)))) in *.
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 cv).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold cv. symmetry. apply Z_to_bv_bv_unsigned. }

  set (kx := KXf (CH2.den E' BLk)). set (bx := BXf (CH2.den E' BLk)).
  assert (HBC : PPS.bufcred L cr cap kx bx).
  { apply CRED_EQ in HC. unfold PB.cap_of, PB.tl_of in HC. rewrite <- Hden, HBLi, PB.den_cons in HC. exact HC. }
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & _ & Hcr0 & Hcr1).

  rewrite Hpc. rewrite LS.
  apply (PUSHB ((p, cap) :: rest) cr oaddr cap p cv (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) s fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hstr|]. split; [lia|]. split; [left; reflexivity|].
    split; [unfold PML.obj_on_stack; lia|]. split; [lia|].
    intros Hg. apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [Hgrown HWc] HRP HPRES Hbv2 HH2.
  assert (Hs1 : Z.of_nat (length (s ++ [cv])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; cbn [length]; lia).
  assert (EXP : exists p' cap', PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ [cv])) /\ LB' = (p', cap') :: rest /\ LBk = rest /\ 2 * KMIN <= cap' <= 2 ^ 27 /\ PPS.bufcred L cr' cap' kx bx).
  { assert (Hrm : lb_remove p ((p, cap) :: rest) = rest) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    destruct Hgrown as [(G1 & G2 & G3 & G4) | (p' & Hex)].
    - exists p, cap. rewrite G2, G3, G4, Hrm. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact HBC].
    - cbv zeta in Hex. destruct Hex as (G0 & G1 & G2 & G3 & G4 & G5). rewrite Hs1 in *.
      destruct (PPS.grow_cap_facts cap (size + 1) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4).
      exists p', (PML.grow_cap cap (size + 1)). rewrite G3, G5, Hrm, G4. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  destruct EXP as (p' & cap' & Hstr2 & -> & -> & Hcap' & HBC').
  destruct (CH2.first_block_facts L HI HIok p' cap' rest cr' M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.

  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] rest Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite PB.uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    unfold PSU.str_news in HX. apply in_app_or in HX as [HX|HX]; [|apply in_app_or in HX as [HX|HX]].
    + rewrite LS.
      assert (Hest : estart E2 (SA OB OK) = oaddr) by (rewrite (PB.estart_agree NF E0 E2 OB OK HagE2 OB_frozen); exact OADDR).
      assert (Hsz : uv E2 (APC.eaddz se 1) = Z.of_nat (length (s ++ [cv]))).
      { destruct (PB.cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite PB.uv_eaddz, (PB.uv_agree nx E' E2 se Hag2 Vse). fold size. rewrite Hs1. apply Z.mod_small. lia. }
      assert (Hpr' : 4096 <= p' <= 2 ^ 47) by (unfold hl_ceil in *; lia).
      exact (PB.str_cells_ok E2 M2 OB OK (APC.eaddz se 1) nx KMIN oaddr cap' p' (s ++ [cv]) Hest ltac:(lia) ltac:(lia) G0 G1 Hsz (conj Hl2 (conj Hc8' Hlt2)) Hcap' Hpr' X HX).
    + rewrite forallb_forall in B7. specialize (B7 X HX).
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' X HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
    + rewrite LS.
      assert (Hsz : uv E2 (APC.eaddz se 1) = size + 1).
      { destruct (PB.cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (PB.kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        rewrite PB.uv_eaddz, (PB.uv_agree nx E' E2 se Hag2 Vse). fold size. apply Z.mod_small. lia. }
      apply (PB.nul_facts_ok E2 M2 d (APC.eaddz se 1) nx BLk p' cap' (size + 1) G0 Ucap Hsz ltac:(rewrite <- Hs1; lia) ltac:(unfold hl_ceil in *; lia)); [|exact HX].
      intros Y HY. rewrite forallb_forall in B7. specialize (B7 Y HY). rewrite <- LS.
      exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
               E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' Y HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
  -
    rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    pose proof Hstr2 as Hstr2'. destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite PB.uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (Hdenj : CH2.den E2 (nth j BLS []) = (p', cap') :: CH2.den E' BLk).
    { rewrite B6, PB.den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    assert (Hcur : CH2.cur LBrest BLS j E2 = (p', cap') :: rest).
    { unfold CH2.cur. rewrite B6, PB.den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. unfold rest. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    split; [|apply (UCONT E2 M2 rest (sp0 + CH2.ci_csp ci) cap' p' Hag2); [subst Wc; exact HPRES | intros b0 Hb0; unfold rest; apply in_or_app; right; exact Hb0 | reflexivity | unfold hl_ceil in *; lia | exact Hstr2' | exact Hdenj]].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) PB.STR_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 rest Wc cr' CF HPRES).
    + intros b Hb. unfold rest. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + rewrite Hnx. exact Hag2.
    + apply CRED_EQ. unfold PB.cap_of, PB.tl_of. rewrite B6, PB.den_cons. cbn [hd snd tl]. rewrite Ucap. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). exact HBC'.
Qed.
End Inst6.

Section Inst6b.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).

Variable EB : expr.
Variable EK : Z.
Hypothesis EB_frozen : APC.expr_vars_lt NF EB = true.
Variable eaddr : Z.
Hypothesis EADDR : estart E0 (SA EB EK) = eaddr.
Hypothesis EOBJ : sp0 <= eaddr /\ eaddr + 16 <= hl_sptop L /\ eaddr mod 8 = 0.
Hypothesis EDEF0 : L5.defined M0 eaddr 16.
Variable g0 : PML.ls_state.
Hypothesis G0 : g0 <> PML.LS0.
Variable PBx : expr.
Variable PKx : Z.
Hypothesis PB_frozen : APC.expr_vars_lt NF PBx = true.
Variable paddr : Z.
Hypothesis PADDR : estart E0 (SA PBx PKx) = paddr.
Variable vaddr : Z.
Hypothesis OBJS : PML.obj_on_stack L sp0 paddr 272 /\ PML.obj_on_stack L sp0 vaddr 48 /\ PML.obj_on_stack L sp0 eaddr 16 /\
                  PML.apart paddr 272 vaddr 48 /\ PML.apart paddr 272 eaddr 16 /\ PML.apart vaddr 48 eaddr 16.

Variable VBx : expr.
Variable VKx : Z.
Hypothesis VB_frozen : APC.expr_vars_lt NF VBx = true.
Hypothesis VADDR : estart E0 (SA VBx VKx) = vaddr.
Hypothesis WPARC_in : forall w a, In w (PMS.W_parc paddr vaddr eaddr) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Variables CPC CSCR : Z.
Variable WFin : PML.pstate -> Prop.
Variable BBin : PML.pstate -> Z -> Prop.
Variable PAin : mem -> Z -> PML.pstate -> Prop.
Variable PAout : PML.pstate -> mem -> Z -> PML.pstate -> Prop.
Variable Args : bvmap 5 word -> mem -> Z -> Z -> Z -> PML.pstate -> Prop.
Variable Rel : PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop.
Hypothesis CALLEE : PMS.ptrans_gb L HI WFin BBin PAin PAout CPC CSCR Args Rel.
Hypothesis PAOUT_CAP : forall pst (M : mem) P ps2, PAout pst M P ps2 -> PML.ps_bcap ps2 mod 2 = 0.
Variable Bv : Z.
Variables KXv BXv : Z.

Lemma ghost_val : forall E' nx ghosts R2 q z, nth q ghosts (Z_to_bv 64 0) = Z_to_bv 64 z -> (q < length ghosts)%nat -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ev (CH2.retEx E' nx ghosts R2) (nx + q)) = z.
Proof. intros E' nx ghosts R2 q z H Hq Hz. rewrite (CH2.retEx_ghost E' nx ghosts R2 q Hq), H. apply u64_of_Z. exact Hz. Qed.

Definition ptrans_pre (R : bvmap 5 word) (M : mem) (cr : credit) (pst : PML.pstate) : Prop :=
  Args R M paddr vaddr eaddr pst /\ PAin M paddr pst /\ WFin pst /\ PML.win_ok M LBrest pst /\ BBin pst Bv /\ PML.vis_at M vaddr /\ PML.ec_at M eaddr 0 /\
  PML.ls_ok g0 M /\ PML.pcredit_x L cr pst KXv BXv.
Definition ptrans_post (pst : PML.pstate) (R2 : bvmap 5 word) (M2 : mem) (cr2 : credit) (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop :=
  PAout pst M2 paddr ps2 /\ PMCUR.wf_c ps2 /\ PML.win_ok M2 LBrest ps2 /\ PML.buf_bound ps2 Bv /\ PML.ec_at M2 eaddr code /\ (code <> 0 -> PML.ps_more ps2 = false) /\
  PML.ls_ok g' M2 /\ (g' = g0 \/ (g' = PML.regJ g0 /\ code <> 0)) /\ PML.pcredit_x L cr2 ps2 KXv BXv /\ Rel pst ps2 code R2.
Definition ptrans_postc (pst : PML.pstate) (R2 : bvmap 5 word) (M2 : mem) (cr2 : credit) (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop :=
  ptrans_post pst R2 M2 cr2 ps2 code g' /\ PMCUR.cur_post RSEGS pst ps2 code M2 vaddr.

Lemma ptrans_leaf_ok2 : forall ereg i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther CPC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = CPC ->
  PB2.ptrans_chkc NF d EB EK PBx PKx CSCR VBx VKx ereg c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr,
      env_agree NF E0 E' -> APC.sr_vars_lt (CH2.ci_nx ci) (CA.ps_reglist ps) = true -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat ->
      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMB i E M' model -> XI i E M ->
      hi_heap HI (CH2.cur LBrest BLS i E) cr M' (m_vmmaps model) -> Cred i E cr ->
      exists pst, CH2.den E' (nth i BLS []) = PML.ps_blocks pst /\ ptrans_pre R' M' cr pst /\
        forall R2 (M2 : mem) cr2 ps2 code g' E2,
          ptrans_postc pst R2 M2 cr2 ps2 code g' -> env_agree (CH2.ci_nx ci) E' E2 -> bv_unsigned (ev E2 (CH2.ci_nx ci)) = code -> ev E2 (CH2.ci_nx ci + 9) = getr R2 10%bv ->
          CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2 ->
          L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PMS.W_parc paddr vaddr eaddr) M' M2 ->
          XI j E2 M2 /\ Cred j E2 cr2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros ereg i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold PB2.ptrans_chkc in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [pb pk] eqn:Hsplit.
  destruct (split_lit (nth ereg (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit2.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1, B3. apply Z.eqb_eq in B2, B4. apply Z.leb_le in B5. apply CH2.blocks_eqb_eq in B6. subst pb pk eb ek.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              CSCR 5%nat [] _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat) by lia.
  rewrite <- Hnx in B6. set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Hoe : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  assert (Hop : estart E' (SA PBx PKx) = paddr) by (rewrite (PB.estart_agree NF E0 E' PBx PKx HagE' PB_frozen); exact PADDR).
  assert (Hov : estart E' (SA VBx VKx) = vaddr) by (rewrite (PB.estart_agree NF E0 E' VBx VKx HagE' VB_frozen); exact VADDR).
  assert (Hov8 : estart E' (SA VBx (VKx + 8)) = vaddr + 8) by (unfold estart in *; cbn [a_base a_off] in *; lia).
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HRL : regs_ok E' (CA.ps_reglist ps) R') by (rewrite <- Hreq; exact HR).
  destruct (USER E E' R' M M' model cr HagE' ltac:(rewrite <- Hreq; exact V1) Hnx Hag HLF HRL HA' HXI0 HH HC) as (pst & Hblk & (PA & PIN & PWF & PWIN & PBB & PVIS & PEC & PLS & PCR) & UPOST).
  destruct OBJS as (OP & OV & OE & AP1 & AP2 & AP3).
  assert (OBM : forall o n, PML.obj_on_stack L sp0 o n -> PML.obj_on_stack L (sp0 + CH2.ci_csp ci) o n) by (intros o n (X & Y & Z); repeat split; try assumption; lia).
  unfold CH2.cur in HH. rewrite <- Hden, Hblk in HH.
  rewrite Hpc, LS.
  apply (CALLEE LBrest cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) paddr vaddr eaddr Bv KXv BXv g0 pst fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    repeat (split; [assumption|]).
    split; [apply OBM; exact OP|]. split; [apply OBM; exact OV|]. split; [apply OBM; exact OE|]. repeat split; assumption. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (ps2 & code & g' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & -> & -> & -> & Q9 & Q10 & Q11) HRP HPRES Hbv2 HH2.
  pose proof (PAOUT_CAP _ _ _ _ Q1) as Hcap2.
  set (bp := PML.ps_bptr ps2) in *. set (bc := PML.ps_bcap ps2) in *. set (sb := PML.ps_sb ps2) in *. set (sc := PML.ps_scap ps2) in *.
  assert (Hblk2 : PML.ps_blocks ps2 = [(bp, bc); (sb, sc)]) by reflexivity. rewrite Hblk2 in HH2. cbn [app] in HH2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _).
  destruct (Hwf2 (bp, bc) ltac:(left; reflexivity)) as ((X0 & X1 & X2 & X3 & X4) & _). destruct (Hwf2 (sb, sc) ltac:(right; left; reflexivity)) as ((Y0 & Y1 & Y2 & Y3 & Y4) & _).
  cbn [fst snd] in *.
  assert (Hcode : 0 <= code <= 31) by (destruct Q5 as (_ & _ & [Z0|[Z1 _]]); lia).
  set (ghosts := [Z_to_bv 64 code; Z_to_bv 64 bp; Z_to_bv 64 (bc / 2); Z_to_bv 64 sb; Z_to_bv 64 sc]).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (Hh : 0 <= bc / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold hl_ceil in *.
  assert (G0' : bv_unsigned (ev E2 nx) = code) by (pose proof (ghost_val E' nx ghosts R2 0 code eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = bp) by (apply (ghost_val E' nx ghosts R2 1 bp eq_refl); [cbn; lia | lia]).
  assert (G2 : bv_unsigned (ev E2 (nx + 2)) = bc / 2) by (apply (ghost_val E' nx ghosts R2 2 (bc / 2) eq_refl); [cbn; lia | exact Hh]).
  assert (G3 : bv_unsigned (ev E2 (nx + 3)) = sb) by (apply (ghost_val E' nx ghosts R2 3 sb eq_refl); [cbn; lia | lia]).
  assert (G4 : bv_unsigned (ev E2 (nx + 4)) = sc) by (apply (ghost_val E' nx ghosts R2 4 sc eq_refl); [cbn; lia | lia]).
  assert (Hbcd : bc = 2 * (bc / 2)) by (pose proof (Z.div_mod bc 2 ltac:(lia)) as D; rewrite Hcap2 in D; lia).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2).
  { rewrite B6, Hblk2. unfold CH2.den. cbn [map fst snd]. unfold PSU.emul2. fold (PB.uv E2 (APC.escale 2 (EVar (nx + 2)))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot].
    rewrite G1, G2, G3, G4, <- Hbcd, Z.mod_small by lia. reflexivity. }
  assert (HPR : L5C.hpres L LBrest (sp0 + CH2.ci_csp ci) CSCR (PMS.W_parc paddr vaddr eaddr) M' M2) by exact HPRES.
  assert (GA0 : ev E2 (nx + 9) = getr R2 10%bv).
  { unfold E2, CH2.retEx, CH2.retE. change (length ghosts) with 5%nat. replace (nx + 9)%nat with (nx + 5 + 4)%nat by lia. rewrite APS.ext_list_at by (cbn; lia). reflexivity. }
  destruct (UPOST R2 M2 cr' ps2 code g' E2 (conj (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 Q10))))))))) Q11) Hag2 G0' GA0 Hden2 HPR) as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts LBrest (PMS.W_parc paddr vaddr eaddr) eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. unfold PMS.W_parc, PML.W_par in Hw. cbn [app] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (PBx, PKx, ELit 272). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Hop. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (EB, EK, ELit 16). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hoe. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
    + exists (VBx, VKx + 8, ELit 40). split; [right; right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hov8. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. fold E2. rewrite <- Hnx in HX. fold nx in HX.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct EOBJ as (O1 & O2 & O3). destruct Q5 as (Hu32 & _ & _). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | | exact Hu32].
      cbn [edenot]. rewrite <- G0'. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [kentry_ok edenot]. rewrite G0'. lia.
  -
    fold E2. split; [|exact HXI2].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) CSCR 5%nat c ps cj ci i j E E' R' M' model E2 M2 model2 LBrest (PMS.W_parc paddr vaddr eaddr) cr' CF HPRES).
    + intros b Hb. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (WPARC_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + unfold CH2.cur. rewrite Hden2, Hblk2. exact HH2.
    + exact Hag2.
    + exact HC2.
Qed.
End Inst6b.
End PB6.
