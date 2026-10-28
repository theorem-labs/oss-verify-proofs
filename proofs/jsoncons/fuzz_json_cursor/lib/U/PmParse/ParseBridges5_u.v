(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PB5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section Inst5.
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
Local Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Local Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Local Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).

Variable EB : expr.
Variable EK : Z.
Hypothesis EB_frozen : APC.expr_vars_lt NF EB = true.
Variable eaddr : Z.
Hypothesis EADDR : estart E0 (SA EB EK) = eaddr.
Hypothesis EOBJ : sp0 <= eaddr /\ eaddr + 16 <= hl_sptop L /\ eaddr mod 8 = 0.
Hypothesis EDEF0 : L5.defined M0 eaddr 16.
Local Abbreviation SETEC_W := (PB2.SETEC_W eaddr).
Hypothesis SETEC_W_in : forall w a, In w SETEC_W -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Hypothesis SETEC : PMS.set_ec_spec L.
Variable g0 : PML.ls_state.
Hypothesis G0 : g0 <> PML.LS0.

Lemma setec_leaf_ok2 : forall i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_SET_EC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_SET_EC ->
  PB2.setec_chk NF d EB EK c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model, env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M -> PML.ls_ok g0 M') ->
  (forall E E' R' (M M' : mem) model E2 (M2 : mem) code, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> HAMB i E M' model -> XI i E M ->
     env_agree (CH2.ci_nx ci) E' E2 -> nth 11 (CA.ps_reglist ps) (ELit 0) = ELit code -> PML.ec_at M2 eaddr code -> PML.ls_ok (PML.regJ g0) M2 ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBrest) (sp0 + CH2.ci_csp ci) PB2.SETEC_SCR SETEC_W M' M2 -> XI j E2 M2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps j cj ci IL Hret Hcj Hpc Hchk XPRE XPOST fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold PB2.setec_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit.
  destruct (nth 11 (CA.ps_reglist ps) (ELit 0)) as [code| | | | | | |] eqn:Hcode; try discriminate.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3, B4. apply CH2.blocks_eqb_eq in B5. subst eb ek.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              PB2.SETEC_SCR 0%nat (nth i BLS []) _ _ _ i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Ho : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  destruct EOBJ as (O1 & O2 & O3). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof LYI as [LI1 LI2]. pose proof LYE as [LE1 LE2].
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 eaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 code).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq, Hcode. reflexivity. }
  assert (HLS : PML.ls_ok g0 M') by exact (XPRE E E' R' M M' model Hag HLF HA' HXI0).
  assert (HDE : L5.defined M' eaddr 16).
  { intros q Hq. apply (Hdf (eaddr + q)); [lia | | apply EDEF0; exact Hq]. split; [right; left; split; lia | unfold in_errno; lia]. }
  rewrite Hpc, LS. destruct Hmo as (Hm1 & Hm2 & Hm3).
  apply (SETEC eaddr code (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) g0 fx' R' M' model K Hm1 Hm2 K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact HDE|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HLS | exact G0]. }
  intros fx2 R2 M2 HFP2 (Hec & Hls2 & Ha0') HRP HFB HGR.
  set (LBk := CH2.den E' (nth i BLS []) ++ LBrest).
  assert (HHk : hi_heap HI LBk cr M' (m_vmmaps model)) by (unfold LBk; rewrite Hden; exact HH).
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HHk)) as Hwf.
  assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> L5.outside SETEC_W a -> ~ (sp0 + CH2.ci_csp ci - PB2.SETEC_SCR <= a < sp0 + CH2.ci_csp ci) -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hout Hns. apply HFB. rewrite L5.unsigned_lit by exact Ha. intros r [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; unfold PMS.SETEC_SCR, PB2.SETEC_SCR in *; lia | exact (Hout r Hr)]. }
  assert (HPRES : L5C.hpres L LBk (sp0 + CH2.ci_csp ci) PB2.SETEC_SCR SETEC_W M' M2).
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (OUTF a K1 K4). destruct K2 as [(b & Hb & Hin)|[[C1 C2]|[C1 C2]]]; [|exact C2 | lia].
      destruct (Hwf b Hb) as ((R0 & R1 & R2' & R3 & R4) & _). unfold PB2.SETEC_SCR in *. lia.
    - intros q Hq. apply HGR. destruct Hstk as (_ & _ & _ & _ & T5). apply T5. exact Hq.
    - intros a _ _ _ Hd. apply HGR. exact Hd. }
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model [] LBk SETEC_W eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. unfold SETEC_W in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (EB, EK, ELit 16). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xd4df8, ELit 2). split; [right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xf6848, ELit 544). split; [right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
  -
    intros X HX _. fold nx. set (E2 := CH2.retEx E' nx [] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct Hec as (Hu32 & _ & Hcat). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | reflexivity | exact Hu32].
    + destruct Hcat as [Hz|[_ Hcat]]; [lia|].
      eapply CL5.kword64_intro with (A := eaddr + 8) (z := PML.OBJ_JSON_CATEGORY); [unfold estart in *; cbn [a_base a_off] in *; lia | lia | lia | reflexivity | exact Hcat].
  -
    fold nx. set (E2 := CH2.retEx E' nx [] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Z3 : CH2.blocks_vars_lt nx (nth i BLS []) = true).
    { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb2; [|discriminate] end. injection Hchk as ->.
      apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [_ Hb2]. exact Hb2. }
    assert (Hden2 : CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS [])).
    { rewrite B5, (CH2.den_agree nx E' E2 _ Hag2 Z3). exact Hden. }
    split; [|exact (XPOST E E' R' M M' model E2 M2 code HagE' Hag HLF HA' HXI0 Hag2 eq_refl Hec Hls2 HPRES)].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) PB2.SETEC_SCR 0%nat c ps cj ci i j E E' R' M' model E2 M2 model LBk SETEC_W cr CF HPRES).
    + intros b Hb. unfold LBk. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct (SETEC_W_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + apply L5C.model_but_vm_refl.
    + unfold CH2.cur. rewrite Hden2, <- Hden. fold LBk.
      apply (hio_frame L SCFG HI HIok LBk cr M' M2 _ HHk); [|intros x Hx; apply HGR; exact Hx].
      intros a Ha Hpriv. apply (OUTF a Ha).
      * intros w Hw Hin. unfold SETEC_W in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        -- destruct Hpriv as [(P1 & _)|P]; [lia|]. destruct (LYR a P) as [Q|Q]; lia.
        -- destruct Hpriv as [(_ & _ & P3)|P]; [apply P3; split; [rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia|]; intros AS; pose proof (PmLayout.ly_static L LAY a AS); lia|].
           destruct (PmLayout.ly_ro_img L LAY a P ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia.
        -- destruct Hpriv as [(_ & _ & P3)|P]; [apply P3; split; [rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia|]; intros AS; pose proof (PmLayout.ly_static L LAY a AS); lia|].
           destruct (PmLayout.ly_ro_img L LAY a P ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia.
      * intros Hin. destruct Hpriv as [(P1 & _)|P]; [unfold PB2.SETEC_SCR in *; lia|]. destruct (LYR a P) as [Q|Q]; unfold PB2.SETEC_SCR in *; lia.
    + exact Hag2.
    + apply CRED_EQ. apply CRED_EQ in HC. unfold PB.cap_of, PB.tl_of in *. rewrite Hden2. exact HC.
  Unshelve.

  cbv beta iota. fold nx. set (E2 := CH2.retEx E' nx [] R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  rewrite Ha0'. rewrite <- (SR.edenot_agree_AP nx E' E2 _ Hag2 (CH.nth_vars_lt nx (CA.ps_reglist ps) 10 ltac:(rewrite <- Hreq; exact V1))).
  rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. symmetry. exact Ho.
Qed.

Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.
Lemma reenter_leaf_ok2 : forall i c k ps pc,
  is_leaf i c k ps (CC.TOther pc) ->
  (forall E E' R R' (M M' : mem) model, CC.At (hl_segs L) c E R M -> HAMB i E M model -> HAMB i E M' model -> XI i E M -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     exists j cj E2, nth_error CPS j = Some cj /\ CC.cp_pc cj = SR.ps_pc ps /\
                CC.At (hl_segs L) cj E2 R' M' /\ env_agree NF E0 E2 /\ CH2.cur LBrest BLS j E2 = CH2.cur LBrest BLS i E /\ (forall cr, Cred i E cr -> Cred j E2 cr) /\
                XI j E2 M' /\ CC.meas cj E2 < CC.meas c E) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps pc IL USER fx' E R M model E' R' M' HAt [HA HX] HFP Hag HLF HIH.
  pose proof (CH2.leaf_amb3 L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 W_ok WRS_ok CPS TAGS HEAPCHK i c k ps pc IL E E' R R' M M' model HAt HA Hag HLF) as HA'.
  destruct (USER E E' R R' M M' model HAt HA HA' HX Hag HLF) as (j & cj & E2 & Hcj & Hpc & HAt2 & HagE2 & Hcur & HC2 & HX2 & Hm).
  rewrite <- Hpc. apply (HIH j cj fx' E2 R' M' model Hcj HAt2); [| exact HFP | exact Hm].
  split; [|exact HX2].
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  split; [exact Hmo|]. split; [exact Hbv|]. split; [exact HagE2|]. split; [exists cr; split; [rewrite Hcur; exact HH | exact (HC2 cr HC)]|]. split; assumption.
Qed.
End Inst5.
End PB5.
