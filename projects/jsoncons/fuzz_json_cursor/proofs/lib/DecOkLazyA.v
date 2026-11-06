(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  FrmInv FpBridge PmHeapIfaceA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA FloatLazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD DecAssume CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutPureA CutVFA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DOLA.
Section Run.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable FPI : FPState -> Prop.
Hypothesis FPI_to : forall fx : FPState, FPI fx -> FrmInv.fp_ok fx.
Abbreviation segs := (hl_segs L).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M', msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.
Variable AD : PDC.addrs.
Abbreviation ERRNO := (PDC.a_TP AD - 164).
Abbreviation GA := (PDC.a_G AD).
Abbreviation SCANEXP := (PDC.a_scanexp AD).
Abbreviation IMG_LO := (PDC.a_img_lo AD).
Abbreviation IMG_HI := (PDC.a_img_hi AD).

Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable DKINDS : list DOK.kind.
Variable HD : CH.hdecl.
Variables RET_PC SCALBNL : Z.
Variable INL : list (Z * (Z * list nat * option Z)).
Variable CALLEES : list (Z * (Z * option (Z * Z))).
Variable SCELLS : list (Z * Z * Z).
Variables GLO GHI : Z.
Abbreviation NF := DOK.NF.
Definition kind_of := DOSA.kind_of CPS RETS DKINDS SCANEXP.
Definition cutc := DOSA.cut_chk CPS RETS DKINDS SCANEXP.
Definition gchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => match nth_error CPS j with Some cj => DOSA.goto_chk2 CPS RETS DKINDS SCANEXP i c ps j cj s | None => false end
  | CC.TOther _ => true
  end.
Definition ochk := DOSA.other_chk CPS RETS DKINDS SCANEXP RET_PC SCALBNL INL CALLEES IMG_LO IMG_HI HD SCELLS GLO GHI.
Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis TAGS_OK : CC.tags_chk CPS TAGS NF = true.
Hypothesis HEAP_OK : CHA.heap_chkA NF HD (CPA.NOB CPS) (CPA.NOF CPS) CPS TAGS = true.
Hypothesis FOOT_OK : CC.cps_all CPS (fun _ c => CHA.foot_chk NF HD c [] []) = true.
Hypothesis CUTS_OK : CC.cps_all CPS cutc = true.
Hypothesis GOTOS_OK : CH2.leaves_all CPS TAGS gchk = true.
Hypothesis OTHERS_OK : CC.others_all CPS TAGS ochk = true.
Hypothesis HSCR : CH.hd_scr HD = 256.
Hypothesis HWRS : CH.hd_wrs HD = [(EVar 2, 0, ELit 8416); (EVar 21, 8, ELit 8); (EVar 4, -164, ELit 4)].
Hypothesis HCRS : CH.hd_crs HD = [(EVar 32, 0, APC.eaddz (EVar 47) 1); (EVar 21, 16, ELit 184); (ELit 0, GA, ELit 8)].
Hypothesis HIMGD : CH.hd_img HD = [(IMG_LO, IMG_HI)].
Hypothesis RET_OK : CL.is_ret_at segs RET_PC.
Hypothesis INL_OK : forall e, In e INL -> CVF.inl_sem segs e.
Hypothesis CALLEES_OK : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVFA.vf_contractA L ar HI FPI pc SCRc IMGc.
Hypothesis SCX : PDCA.scanexp_contractA L ar HI FPI AD.
Hypothesis SCALBNL_OK : CVFA.vf_contractA L ar HI FPI SCALBNL 112 (Some (IMG_LO, IMG_HI)).
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Hypothesis IMGR : hl_img_lo L <= IMG_LO /\ IMG_HI <= hl_img_hi L /\ forall a, IMG_LO <= a < IMG_HI -> ~ hl_rt_static L a.
Hypothesis TPV : hl_tp L = PDC.a_TP AD.
Hypothesis CELLS : forall a, (ERRNO <= a < ERRNO + 4 \/ GA <= a < GA + 8) -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a /\ (a < IMG_LO \/ IMG_HI <= a).

Definition E0_ok (E0 : env) (R : bvmap 5 word) (Q CAN : Z) (sv : nat -> Z) (N : Z) : Prop :=
  (forall x : reg, ev E0 (ridx x) = getr R x) /\ ev E0 32 = Z_to_bv 64 Q /\ ev E0 33 = Z_to_bv 64 CAN /\ ev E0 47 = Z_to_bv 64 N /\
  (forall r v, In (r, v) DOS.SAVE_VARS -> ev E0 v = Z_to_bv 64 (sv r)).

Theorem decfloat_runA : forall (e2 : bool) (i0 : nat) (c0 : CC.cutpoint)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (fx : FPState) (R : bvmap 5 word) (M : PDCA.mem) (model : Model) (K : TSet)
    (SP F P Q CAN : Z) (sv : nat -> Z) (txt : list Z) (E0 : env),
  nth_error CPS i0 = Some c0 -> kind_of i0 = KEnt -> CC.cp_pc c0 = (if e2 then PDC.a_E2 AD else PDC.a_E1 AD) ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> FPI fx ->
  CHA.astk ar M (SP + PDC.FRAME) (PDC.SCR_D + PDC.FRAME) -> CHA.ffroom FF LK 0 -> CHA.ffrs FF (SP + PDC.FRAME) ->
  PDCA.dec_preA L ar AD e2 LB FF R M SP F P Q CAN sv txt ->
  E0_ok E0 R Q CAN sv (Z.of_nat (length txt)) -> CCA.AtV segs c0 E0 R A M model ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : PDCA.mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)),
      FPI fx' -> PDCA.dec_postA L SP F Q sv txt R R' M' ->
      CHA.ahpres L ar LB FF (SP + PDC.FRAME) (PDC.SCR_D + PDC.FRAME) (PDCA.DW AD F) M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
      srealizes segs SCFG (mkCfg (mk fx' R' (sv 1%nat) M') model') K) ->
  srealizes segs SCFG (mkCfg (mk fx R (CC.cp_pc c0) M) model) K.
Proof.
  intros e2 i0 c0 LB FF LK cr A fx R M model K SP F P Q CAN sv txt E0 Hc0 Hk0 Hpc0 HH Hmo HKnil Hfp Hstk Hroom Hffrs Hpre HE0 HAt Hcont.
  destruct Hpre as (Hdp & HspF & Hfd8 & Hblk & RCAN & RAOK).
  destruct Hdp as (Rsp & Hal & Hfloor & Htop & RF & R23 & R18 & R22 & R24 & R9 & R20 & R4 & Hdef & Hwr & Hsaves & Hret & Hcan & Hguard & Hgap & Hfile & Hfs & Htext & Htap & Herrw & Himg & Hent).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  destruct HE0 as (EV & E32 & E33 & E47 & Esv).
  set (N := Z.of_nat (length txt)) in *. unfold PDC.FRAME, PDC.SCR_D, PDC.STK_FLOOR in *.
  assert (HN0 : 0 <= N) by (unfold N; lia).
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. pose proof (CHA.wf_top L ar _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as TOP.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (FLA.txt_facts_h L ar C HI HIok LY_img _ _ _ _ _ _ _ (SP + 8416) Q (N + 1) HH ltac:(lia) Hblk ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5).
  pose proof (FLA.txt_home_mono ar LB FF (SP + 8416) Q (N + 1) SP Q (N + 1) Hblk ltac:(lia) ltac:(lia) ltac:(lia)) as HblkS.
  destruct IMGR as (IM1 & IM2 & IM3).
  assert (ER : hl_img_lo L <= ERRNO /\ ERRNO + 4 <= hl_img_hi L) by (destruct (CELLS ERRNO ltac:(lia)) as [X _]; destruct (CELLS (ERRNO + 3) ltac:(lia)) as [Y _]; lia).
  assert (GR : hl_img_lo L <= GA /\ GA + 8 <= hl_img_hi L) by (destruct (CELLS GA ltac:(lia)) as [X _]; destruct (CELLS (GA + 7) ltac:(lia)) as [Y _]; lia).
  assert (ERI : forall a, ERRNO <= a < ERRNO + 4 -> a < IMG_LO \/ IMG_HI <= a) by (intros a Ha; exact (proj2 (proj2 (proj2 (CELLS a ltac:(lia)))))).
  pose proof LY_img as [LI0 LI1]. unfold BIGSHADOW_LO in LI1.

  assert (V2 : ev E0 2 = getr R 2%bv) by exact (EV 2%bv). assert (V4 : ev E0 4 = getr R 4%bv) by exact (EV 4%bv). assert (V21 : ev E0 21 = getr R 21%bv) by exact (EV 21%bv).
  assert (U2 : bv_unsigned (ev E0 2) = SP) by (rewrite V2; exact Rsp).
  assert (U21 : bv_unsigned (ev E0 21) = F) by (rewrite V21; exact RF).
  assert (U32 : bv_unsigned (ev E0 32) = Q) by (rewrite E32; apply u64_of_Z; lia).
  assert (U47 : bv_unsigned (ev E0 47) = N) by (rewrite E47; apply u64_of_Z; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, TPV; exact (DOK.rz_word R 4 _ R4)).
  assert (U4 : bv_unsigned (ev E0 4) = ERRNO + 164) by (rewrite V4; unfold PDC.rz, PDC.reg_of in R4; replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; reflexivity); lia).
  assert (R_SP : 140735332483072 + 256 <= SP /\ SP + 8416 <= 2 ^ 47) by lia.
  assert (R_F : 140735332483072 <= F /\ F + 256 <= 2 ^ 47) by lia.
  assert (R_Q : 4096 <= Q /\ Q + N < 2 ^ 47 /\ N < 2 ^ 26) by lia.
  assert (R_ERR : 0 <= ERRNO /\ ERRNO + 4 <= 140735332483072) by lia.
  assert (T_dig : exists ch r, txt = ch :: r /\ PD.is_dig ch = true).
  { destruct e2.
    - destruct Hent as (_ & r0 & Et). exists 48, r0. split; [exact Et | reflexivity].
    - destruct Hent as (_ & ch & r0 & Et & Hc0' & _). exists ch, r0. split; [exact Et|]. unfold PD.is_dig. apply andb_true_intro. split; apply Z.leb_le; lia. }
  assert (D_len : DOSA.D txt = PD.dec_len txt).
  { destruct T_dig as (ch & r0 & Et & Hd0). unfold DOSA.D, DOSA.txt'. rewrite Et. symmetry. apply PDS.dec_len_contD0. exact Hd0. }

  assert (SCRV : CH.hd_scr HD = 256) by exact HSCR.
  assert (STKF : SP mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr HD <= SP /\ SP <= ar_sptop ar) by (rewrite SCRV; split; [exact Hal | lia]).
  assert (SCRP : 0 <= CH.hd_scr HD) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= NF)%nat) by (unfold DOK.NF; lia).
  set (W := [(SP, 8416); (F + 8, 8); (ERRNO, 4)] : list L5.range).
  assert (WCL : forall a, (SP <= a < SP + 8416 \/ F + 8 <= a < F + 16 \/ ERRNO <= a < ERRNO + 4) ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF SP (CH.hd_scr HD) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. rewrite SCRV. destruct Ha as [Ha|[Ha|Ha]].
    - split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
    - split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
    - destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|]. split; [right; right; left; split; [exact C1 | intros [X|X]; [exact (C2 X) | exact (C3 X)]]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF SP (CH.hd_scr HD) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a Hw Hin. unfold L5.in_rng in Hin. unfold W in Hw. cbn [In] in Hw.
    destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin; apply WCL; lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HD) -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { rewrite HWRS. intros rg Hrg. cbn [In] in Hrg. destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (SP, 8416). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia].
    - rewrite U21 in Ha. rewrite u64_of_Z in Ha by lia. exists (F + 8, 8). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia].
    - rewrite U4 in Ha. rewrite u64_of_Z in Ha by lia. exists (ERRNO, 4). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs HD) -> SGP.region_vars_lt NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF SP HD a)).
  { rewrite HCRS. intros rg Hrg. cbn [In] in Hrg. destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off] in Ha; unfold CHA.sclientA; rewrite SCRV.
    - unfold APC.eaddz in Ha. rewrite mkAlu_denot in Ha. cbn [edenot] in Ha. rewrite u_add64, U32, U47 in Ha. rewrite u64_of_Z in Ha by lia. rewrite Z.mod_small in Ha by lia.
      split; [lia|]. split; [exact (FLA.txt_aclient_h L ar C HI HIok _ _ _ _ _ _ _ SP 256 Q (N + 1) a HH ltac:(lia) HblkS ltac:(lia))|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    - cbn [edenot] in Ha. rewrite U21 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
    - cbn [edenot] in Ha. rewrite !u64_of_Z in Ha by lia. destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|]. split; [right; right; left; split; [exact C1 | exact C2]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img HD) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { rewrite HIMGD. intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. split; [lia | exact (IM3 a Ha)]. }
  assert (Hffrs0 : CHA.ffrs FF SP) by (apply (CHA.ffrs_le FF (SP + 8416) SP Hffrs); lia).
  assert (DEF0 : L5.defined M (SP - CH.hd_scr HD) (CH.hd_scr HD)) by (rewrite SCRV; apply (L5.defined_sub M (SP + 8416 - 8672) 8672 (SP - 256) 256 S5); lia).
  assert (DEFUP : L5.defined M SP (ar_stack_top ar - SP)).
  { intros k Hk. destruct (Z_lt_le_dec k 8416) as [Hl|Hl].
    - replace (SP + k) with (SP + 8416 - 8672 + (8672 - 8416 + k)) by lia. apply S5. lia.
    - replace (SP + k) with (SP + 8416 + (k - 8416)) by lia. apply S6. lia. }

  assert (VS : CL5A.visr (ahid A model) (SP - 256) 8672) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VF : CL5A.visr (ahid A model) (F + 8) 192) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr (ahid A model) Q (N + 1)) by (exact (FLA.txt_visr_h L ar C HI HIok LY_img _ _ _ _ _ _ _ (SP + 8416) _ _ HH ltac:(lia) Hblk)).
  assert (TXTK : forall a, Q <= a < Q + (N + 1) -> CHA.akept L ar LB FF SP (CH.hd_scr HD) W a).
  { intros a Ha. rewrite SCRV. apply (FLA.txt_kept_h L ar C HI HIok LY_img _ _ _ _ _ _ _ SP Q (N + 1) _ _ _ HH); [lia | lia | exact HblkS | | exact Ha].
    intros w Hw. unfold W in Hw. cbn [In] in Hw. unfold PDC.apart in Ta1, Ta2, Ta3. cbv zeta in Ta1, Ta2, Ta3. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia. }
  assert (TVof : forall A' m' (M' : PDCA.mem) LKx crx, ri_inv HI LB FF LKx crx A' M' (vml_of m') ->
            (forall a, CHA.akept L ar LB FF SP (CH.hd_scr HD) W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> DOSA.TV txt Q M (CCA.vis A' m' M')).
  { intros A' m' M' LKx crx HHx Hfr x Hx. unfold DOSA.N in Hx.
    unfold CCA.vis. rewrite <- (Z_to_bv_bv_unsigned _ x). rewrite (CL5A.vis_eq (ahid A' m') M'); [apply Hfr; apply TXTK; lia|].
    pose proof (FLA.txt_visr_h L ar C HI HIok LY_img _ _ _ _ _ _ _ (SP + 8416) Q (N + 1) HHx ltac:(lia) Hblk (bv_unsigned x - Q) ltac:(lia)) as Vx.
    replace (Q + (bv_unsigned x - Q)) with (bv_unsigned x) in Vx by lia. exact Vx. }
  assert (CUT : forall i c, nth_error CPS i = Some c -> cutc i c = true) by (intros i c Hc; exact (CC.cps_all_sound _ _ CUTS_OK i c Hc)).
  assert (NFle : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat).
  { intros i c Hc. pose proof (CUT i c Hc) as X. unfold cutc, DOSA.cut_chk in X. do 2 (apply andb_prop in X as [X _]). apply Nat.leb_le. exact X. }
  set (XIA := fun (i : nat) (E : env) (_ : list (Z * Z)) (Mx : PDCA.mem) (_ : Model) => DOSA.XI segs CPS RETS DKINDS SCANEXP txt Q F i E Mx).

  assert (U64V : forall A' m' (M' : PDCA.mem) LKx crx v, ri_inv HI LB FF LKx crx A' M' (vml_of m') ->
            (L5.u64_at segs M' (F + 8) v -> L5.u64_at segs (CCA.vis A' m' M') (F + 8) v) /\ (L5.u64_at segs (CCA.vis A' m' M') (F + 8) v -> L5.u64_at segs M' (F + 8) v)).
  { intros A' m' M' LKx crx v HHx. split; intros Hu.
    - apply (CL5A.u64_vis segs (ahid A' m') M'); [lia | lia | apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HHx); lia | exact Hu].
    - exact (CL5A.u64_full segs _ (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ _ HHx) _ _ _ Hu). }
  assert (XIV : forall i E A' m' (M' : PDCA.mem) LKx crx, ri_inv HI LB FF LKx crx A' M' (vml_of m') ->
            (DOSA.XI segs CPS RETS DKINDS SCANEXP txt Q F i E M' -> DOSA.XI segs CPS RETS DKINDS SCANEXP txt Q F i E (CCA.vis A' m' M'))
            /\ (DOSA.XI segs CPS RETS DKINDS SCANEXP txt Q F i E (CCA.vis A' m' M') -> DOSA.XI segs CPS RETS DKINDS SCANEXP txt Q F i E M')).
  { intros i E A' m' M' LKx crx HHx. unfold DOSA.XI, DOSA.XI_sc.
    destruct (DOSA.kind_of CPS RETS DKINDS SCANEXP i); destruct (nth_error CPS i); split; intros HX; try exact HX;
      try (destruct HX as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [|split; [exact X3 | exact X4]]);
      first [exact (proj1 (U64V _ _ _ _ _ _ HHx) X2) | exact (proj2 (U64V _ _ _ _ _ _ HHx) X2) | exact (proj1 (U64V _ _ _ _ _ _ HHx) HX) | exact (proj2 (U64V _ _ _ _ _ _ HHx) HX)]. }

  assert (LEAF : forall i c ps E E' R1 R' A1 M1 m1 M2 m2, nth_error CPS i = Some c ->
            CCA.AtV segs c E R1 A1 M1 m1 -> CHA.aamb L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M1 m1 ->
            env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA segs c ps E' R' A1 M1 m1 M2 m2 ->
            CHA.aamb L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2).
  { intros i c ps E E' R1 R' A1 M1 m1 M2 m2 Hc HAt1 HA1 Hag HLF.
    refine (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M model A LB FF LK SP HD W W _ _ _ 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK i c ps E E' R1 R' A1 M1 m1 M2 m2 _ HAt1 HA1 Hag HLF).
    rewrite CPA.NOBnil, CPA.NOFnil. exact (CC.cps_all_sound _ _ FOOT_OK i c Hc). }
  assert (AMBP : forall i E A1 M1 m1, CHA.aamb L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M1 m1 ->
            CHA.amodel_ok A1 m1 /\ model_rt model m1 /\ incl A A1 /\ env_agree NF E0 E /\
            (exists LK1, ri_inv HI LB FF LK1 cr A1 M1 (vml_of m1) /\ incl LK1 LK /\ CHA.ffroom FF LK1 0) /\
            (forall a, CHA.akept L ar LB FF SP (CH.hd_scr HD) W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
            (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF SP 0 a -> M (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None) /\ DOSA.TV txt Q M (CCA.vis A1 m1 M1)).
  { intros i E A1 M1 m1 HA1. pose proof HA1 as (Hmo1 & Hrt1 & HA01 & HagE & (cr1 & LK1 & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
    unfold CHA.curB, CHA.curF in HH1, HRoom1. rewrite CPA.NOBnil, CPA.NOFnil in HH1. rewrite CPA.NOFnil in HRoom1. cbn [CH2.den CHA.denF map app length Z.of_nat] in HH1, HRoom1. unfold CPA.Cred0 in HC1. subst cr1.
    rewrite Z.sub_0_r in HRoom1.
    repeat (split; [assumption|]). split; [exists LK1; repeat (split; [assumption|]); assumption|]. split; [exact Hfr1|]. split; [exact Hdf1|]. exact (TVof _ _ _ _ _ HH1 Hfr1). }
  eapply (CHA.cert_soundA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK SP HD W W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            CPS K FPI XIA TAGS FPM PLANS TAGS_OK HEAP_OK _ _ _ i0 c0 fx E0 R A M model Hc0 HAt _ Hfp).
  Unshelve.
  -   intros i c k ps j s _ E E' R' M1 M2 cr1 _ _ _ HC. exact HC.
  -
    intros i c1 k ps j s IL E R1 E' R' A1 M1 m1 M2 m2 HAt1 HA1 Hag HLF HX.
    destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    destruct (CC.tags_chk_go_nth CPS NF CPS TAGS i c1 TAGS_OK Hc1) as (tags' & Htags' & Hlv). rewrite Htags in Htags'. injection Htags' as <-.
    destruct (CC.leaves_chk_nth CPS NF c1 _ tags k ps Hlv Hps) as (t & Ht & Hg). rewrite Htag in Ht. injection Ht as <-. destruct Hg as (cj & Hcj & Hg).
    pose proof (CH2.leaves_all_nth CPS TAGS gchk GOTOS_OK i c1 tags k ps _ Hc1 Htags Hps Htag) as G2. unfold gchk in G2. rewrite Hcj in G2.
    pose proof (LEAF i c1 ps E E' R1 R' A1 M1 m1 M2 m2 Hc1 HAt1 HA1 Hag HLF) as HA2.
    destruct (AMBP _ _ _ _ _ HA1) as (_ & _ & _ & HagE & (LK1 & HH1 & _) & _ & _ & TV1). destruct (AMBP _ _ _ _ _ HA2) as (_ & _ & _ & _ & (LK2 & HH2 & _) & _ & _ & TV2).
    apply (proj2 (XIV _ _ _ _ _ _ _ HH2)).
    exact (DOSA.xi_goto segs CPS RETS DKINDS SCANEXP ERRNO txt Q F SP E0 M U2 U21 U32 U47 R_SP R_F R_Q R_ERR U4 Tb Tn Tr T_dig Hfs i c1 ps j cj s E R1 (CCA.vis A1 m1 M1) E' R' (CCA.vis A1 m2 M2) Hc1 Hcj (CUT i c1 Hc1) (CUT j cj Hcj) Hg G2 HAt1 HagE TV1 (proj1 (XIV _ _ _ _ _ _ _ HH1) HX) Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) TV2).
  -
    intros i c1 k ps id IL. destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    pose proof (CC.others_all_sound _ _ _ OTHERS_OK i c1 tags k ps id Hc1 Htags Hps Htag) as X. unfold ochk, DOSA.other_chk in X. rewrite Hc1 in X.
    pose proof (CUT i c1 Hc1) as Ci. pose proof (NFle i c1 Hc1) as Hnf.
    apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
    +
      do 2 (apply andb_prop in X as [X ?Y]).
      intros fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 [HA1 HX] HFP Hag HLF _.
      pose proof (LEAF i c1 ps E E' R1 R' A1 M1 m1 M2 m2 Hc1 HAt1 HA1 Hag HLF) as HA2.
      destruct (AMBP _ _ _ _ _ HA1) as (_ & _ & _ & HagE & (LK1 & HH1 & _) & _ & _ & TV1).
      destruct (AMBP _ _ _ _ _ HA2) as (Hmo2 & Hrt2 & HA02 & HagE' & (LK2 & HH2 & HLK2 & HRoom2) & Hfr2 & Hdf2 & TV2).
      destruct (DOSA.exit_facts segs CPS RETS DKINDS SCANEXP ERRNO txt Q F SP E0 U2 R_SP R_F R_Q R_ERR U4 Hfs i c1 ps E R1 (CCA.vis A1 m1 M1) E' R' (CCA.vis A1 m2 M2) Hc1 Ci Y Y0 HAt1 HagE (proj1 (XIV _ _ _ _ _ _ _ HH1) HX) Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF)) as (Hsv & Hsp' & Hgp' & Htp' & Hrp').
      pose proof (CBA.amb_off L ar C HI HIok LY_below NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2 HA2) as Hoff.
      pose proof (CL5A.u64_full segs _ Hoff _ _ _ Hrp') as Hrp2. rewrite D_len in Hrp2.
      pose proof (CBA.exit_post L ar C HI HIok NF M model A LB FF SP HD W (CPA.NOB CPS) STKF NF32 DEF0 i E A1 M2 m2 cr LK2 FF Hmo2 Hrt2 HA02 Hfr2 Hdf2) as HP.
      unfold CHA.curB in HP. rewrite CPA.NOBnil in HP. cbn [CH2.den map app] in HP. specialize (HP HH2). rewrite SCRV in HP.
      assert (Hra : getr R' 1%bv = Z_to_bv 64 (sv 1%nat)).
      { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite (Hsv 1%nat 34%nat ltac:(unfold DOS.SAVE_VARS; cbn; tauto)). apply Esv. unfold DOS.SAVE_VARS; cbn; tauto. }

      assert (SHLO : forall p n a, 0 <= p -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> a < 140735332483072).
      { intros p n a Hp Hn Hs. unfold in_shadow_of, S, SB in Hs. pose proof (Z.div_le_mono (p + n - 1) (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as XD.
        change (2 ^ 47 / 8) with 17592186044416 in XD. lia. }

      assert (BELOW : forall a, aclient L ar LB FF (SP + 8416) (256 + 8416) a -> ~ (SP <= a < SP + 8416)).
      { intros a Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
        - destruct Hc as (b & Hb & Hb2). destruct (FLA.blk_facts L ar C HI HIok _ _ _ _ _ _ _ b HH Hb). lia.
        - lia.
        - lia.
        - destruct Hc as (f & Hf & Hf2). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (G1 & G2 & _). destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). lia.
        - pose proof (SHLO (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) Hc). lia.
        - destruct Hc as (f & Hf & Hs). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (G1 & G2 & _). destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _ & _) & G3 & _).
          pose proof (SHLO (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) Hs). lia.
        - destruct Hc as (b & Hb & Hs). destruct (FLA.blk_facts L ar C HI HIok _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & _). pose proof (SHLO (fst b) (snd b) a ltac:(lia) ltac:(lia) Hs). lia. }
      assert (HPW : forall M3, CHA.ahpres L ar LB FF SP 256 W M M3 -> CHA.ahpres L ar LB FF (SP + 8416) (256 + 8416) (PDCA.DW AD F) M M3).
      { intros M3 (P1 & P2 & P3). split; [|split].
        - intros a (Ha & Hc & Ho). apply P1. split; [exact Ha|]. split.
          + destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; lia | right; right; exact Hc].
          + intros w Hw. unfold W in Hw. cbn [In] in Hw. unfold L5.outside in Ho. destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd].
            * pose proof (BELOW a Hc). lia.
            * exact (Ho (F + 8, 8) ltac:(unfold PDCA.DW; cbn; tauto)).
            * exact (Ho (ERRNO, 4) ltac:(unfold PDCA.DW; cbn; tauto)).
        - intros kk Hk. destruct (Z_lt_le_dec kk 256) as [Hl|Hl].
          + replace (SP + 8416 - (256 + 8416) + kk) with (SP - 256 + kk) by lia. apply P2. lia.
          + apply P3; [lia | right; left; split; lia |]. replace (SP + 8416 - (256 + 8416) + kk) with (SP + 8416 - 8672 + kk) by lia. apply S5. lia.
        - intros a Ha Hc. apply P3; [exact Ha|]. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; lia | right; right; exact Hc]. }
      assert (POST : forall R2 (M3 : PDCA.mem), regs_preserved R' R2 -> (forall a, F + 8 <= a < F + 16 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
                PDCA.dec_postA L SP F Q sv txt R R2 M3).
      { intros R2 M3 HRP2 Hq8. unfold PDCA.dec_postA, PDC.FRAME.
        assert (Hcs : forall x : reg, In (bv_unsigned x) callee_saved_idx -> getr R2 x = getr R' x) by (intros x Hx; exact (HRP2 x Hx)).
        split; [|split; [|split; [|split]]].
        - unfold PDC.rz, PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 2))) by (cbn; tauto). replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact Hsp'.
        - intros r o Hin Hci. destruct (Hsaves r o Hin) as [_ Rsv]. unfold PDC.rz, PDC.reg_of.
          assert (Hv : exists v, In (r, v) DOS.SAVE_VARS /\ (r < 32)%nat).
          { unfold PDC.SAVES in Hin. cbn [In] in Hin.
            repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; eexists; split; [unfold DOS.SAVE_VARS; cbn [In]; tauto | lia]|]). contradiction. }
          destruct Hv as (v & Hv1 & Hv3).
          rewrite Hcs by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; exact Hci).
          rewrite (Hsv r v Hv1), (Esv r v Hv1). apply u64_of_Z. exact Rsv.
        - unfold PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 3))) by (cbn; tauto). replace (Z_to_bv 5 (Z.of_nat 3)) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Hgp'. exact (EV 3%bv).
        - unfold PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 4))) by (cbn; tauto). replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
          rewrite Htp'. exact V4.
        - apply (DOK.u64_at_same segs M2 M3 (F + 8) _ ltac:(lia) ltac:(lia)); [|exact Hrp2]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hq8. lia. }
      destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2 HA2) as (Hh2 & HMI2 & HAwf2 & Hoff2).
      apply orb_prop in X as [X|X]; apply Z.eqb_eq in X; rewrite X.
      *
        eapply (CCA.ret_cps segs fx' R' RET_PC M2 m2 A1 K RET_OK Hh2 HMI2 HAwf2 Hoff2 LY_nowrap).
        { rewrite Hra. exact Hret. }
        intros model2 HMI3 HS. rewrite Hra.
        assert (VML : vml_of model2 = vml_of m2) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
        apply (Hcont fx' R' M2 model2 LK2 A1 HFP); [| exact (HPW M2 HP) | exact (L5LZ.model_rt_trans _ _ _ Hrt2 (L5LZ.sbm_model_rt _ _ HS)) | exact HA02 | | exact HLK2 | rewrite VML; exact HH2].
        -- apply POST; [intros x Hx; reflexivity | intros; reflexivity].
        -- split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo2) | exact HMI3].
      *
        apply (SCALBNL_OK (sv 1%nat) (SP + 8416) LB FF LK2 cr A1 fx' R' M2 m2 K HH2 Hmo2 HKnil HFP Hra RAOK).
        -- apply bv_eq. rewrite Hsp'. rewrite u64_of_Z by lia. reflexivity.
        -- rewrite Htp'. exact TP0.
        -- split; [exact S1|]. split; [lia|]. split; [lia|]. split; [exact S4|]. split.
           ++ intros kk Hk. apply (proj2 (proj2 HP)); [lia | right; left; split; lia |]. replace (SP + 8416 - 112 + kk) with (SP + 8416 - 8672 + (8560 + kk)) by lia. apply S5. lia.
           ++ intros kk Hk. apply (proj2 (proj2 HP)); [lia | right; left; split; lia |]. apply S6. exact Hk.
        -- exact HRoom2.
        -- exact Hffrs.
        -- unfold CVF.img_pre_of. split; [lia|]. split; [lia|]. intros a Ha. rewrite (proj1 HP); [exact (Himg a Ha)|].
           split; [lia|]. split; [right; right; left; split; [lia | exact (IM3 a Ha)]|]. intros w Hw. unfold W in Hw. cbn [In] in Hw. unfold L5.in_rng.
           destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; [lia | lia |]. intros Hx. destruct (ERI a Hx); lia.
        -- intros fx2 R2 M3 model3 LB' cr' LBk W' LK3 A3 HFP2 (_ & -> & -> & -> & ->) HRP2 HP2 Hrt3 HA3 Hmo3 HLK3 HH3.
           apply (Hcont fx2 R2 M3 model3 LK3 A3 HFP2); [| | exact (L5LZ.model_rt_trans _ _ _ Hrt2 Hrt3) | exact (incl_tran HA02 HA3) | exact Hmo3 | exact (incl_tran HLK3 HLK2) | exact HH3].
           ++ apply POST; [exact HRP2|]. intros a Ha. apply (proj1 HP2). split; [lia|]. split; [right; left; split; lia | intros w []].
           ++ apply (CRB.ahpres_trans L ar LB LB LB FF (SP + 8416) (256 + 8416) 112 (PDCA.DW AD F) (PDCA.DW AD F) [] M M2 M3 (HPW M2 HP) HP2 (incl_refl _) (incl_refl _)); [lia | lia | lia | lia | |].
              ** intros w a Hw Ha. exists w. split; assumption.
              ** intros w a [].
    +
      apply andb_prop in X as [Xpc Xs]. apply Z.eqb_eq in Xpc.
      intros fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH. pose proof HAX as [HA1 HX].
      pose proof (LEAF i c1 ps E E' R1 R' A1 M1 m1 M2 m2 Hc1 HAt1 HA1 Hag HLF) as HA2.
      destruct (AMBP _ _ _ _ _ HA1) as (_ & _ & _ & HagE & (LK1 & HH1 & _) & _ & _ & TV1).
      destruct (AMBP _ _ _ _ _ HA2) as (Hmo2 & Hrt2 & HA02 & HagE' & (LK2 & HH2 & HLK2 & HRoom2) & Hfr2 & Hdf2 & TV2).
      pose proof (CBA.amb_off L ar C HI HIok LY_below NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2 HA2) as Hoff.
      assert (DT2 : forall d, 0 <= d < N + 1 -> M2 (Z_to_bv 64 (Q + d)) <> None).
      { intros d Hd. apply Hdf2; [lia | exact (FLA.txt_aclient_h L ar C HI HIok _ _ _ _ _ _ _ SP 0 Q (N + 1) (Q + d) HH ltac:(lia) HblkS ltac:(lia)) | apply Td; lia]. }
      assert (DTV2 : forall d, 0 <= d < N + 1 -> CCA.vis A1 m2 M2 (Z_to_bv 64 (Q + d)) <> None).
      { intros d Hd. unfold CCA.vis. rewrite (CL5A.vis_eq (ahid A1 m2) M2); [exact (DT2 d Hd)|].
        exact (FLA.txt_visr_h L ar C HI HIok LY_img _ _ _ _ _ _ _ (SP + 8416) Q (N + 1) HH2 ltac:(lia) Hblk d ltac:(lia)). }
      destruct (DOSA.scx_facts segs CPS RETS DKINDS SCANEXP ERRNO IMG_LO IMG_HI HD SCELLS GLO GHI txt Q F SP E0 M U2 U21 U32 U47 R_SP R_F R_Q R_ERR Tb Tn Tr
                  i c1 ps E R1 (CCA.vis A1 m1 M1) E' R' (CCA.vis A1 m2 M2) Hc1 Ci Xs HAt1 HagE TV1 (proj1 (XIV _ _ _ _ _ _ _ HH1) HX) Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) TV2 DTV2)
        as (kq & ra & ja & cja & cjb & Hk & Ltxe & HDx & G10 & G11 & G2 & G1 & Era & Rra & Era2 & Hrp' & H184 & H192 & Htxt & Hkimg & Hall & Hmeas & Hmv & Hcja & Hcjb & Kja & Kjb & Ya & Yb).
      cbv zeta in Hk, Ltxe, HDx, Hrp', Htxt. change (DOSA.N txt) with N in Hk, Ltxe, HDx, Hrp', Htxt.
      set (P' := Q + N + 1 - kq) in *. set (txe := skipn (Z.to_nat (N - kq + 1)) txt) in *.
      pose proof (CL5A.u64_full segs _ Hoff _ _ _ Hrp') as Hrp2. pose proof (CL5A.u64_full segs _ Hoff _ _ _ H184) as H184f. pose proof (CL5A.u64_full segs _ Hoff _ _ _ H192) as H192f.
      assert (TXTf : PDC.text_ok segs M2 P' txe).
      { destruct Htxt as (X1 & X2 & X3 & X4 & X5 & X6 & X7). split; [exact (CL5A.bytes_full segs _ Hoff _ _ _ X1)|]. split; [exact (CL5A.u8_full segs _ Hoff _ _ _ X2)|].
        split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact (CL5A.defined_full _ M2 _ _ X6) | exact X7]. }
      assert (IMGC2 : L5.img_clear M2 IMG_LO IMG_HI).
      { cbn [kentry_ok] in Hkimg. destruct Hkimg as (_ & _ & I3). intros a Ha. specialize (I3 a Ha). unfold CCA.vis, mrestrict in I3.
        rewrite (CHA.img_vis L ar C HI HIok LY_img NF SP NF32 _ _ _ _ _ _ _ a HH2 ltac:(lia)) in I3. exact I3. }
      pose proof D_len as HD'. rewrite HDx in HD'.

      assert (COMMONA : forall (lmin : bool) j cj, nth_error CPS j = Some cj -> DOSA.scx_ret_chk HD SCELLS GLO GHI lmin c1 ps ra cj = true ->
                 (if lmin then kind_of j = KRXa else kind_of j = KPost) -> (lmin = true <-> PD.exp_scan txe = None) ->
                 srealizes segs SCFG (mkCfg (mk fx' R' (SR.ps_pc ps) M2) m2) K).
      { intros lmin j cj Hcj Hrc Hkj Hlm. unfold DOSA.scx_ret_chk in Hrc. apply andb_prop in Hrc as [Hpc Hcu]. apply Z.eqb_eq in Hpc.
        destruct (DOSA.scx_custom HD SCELLS GLO GHI lmin c1 ps cj) as [ci|] eqn:Hci; [|discriminate Hcu]. unfold DOSA.scx_custom in Hci.
        refine (CVFA.callee_leafLB L ar C HI HIok LY_img LY_ro NF E0 M model A LB FF LK cr SP HD W W 0 STKF SCRP NF32 U2 TP0 (incl_refl _) WOK Hffrs0 CRS_OK WRS_OK IMG_OK
                  CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XIA HKnil SCANEXP 80 1 0 [(F + 8, 8)] DOSA.scx_wregs (DOSA.scx_news lmin ps cj) (if lmin then Some (ELit DOSA.LMIN) else None)
                  i c1 ps j cj ci (PDCA.scx_preA L ar AD (SP + CH2.ci_csp ci) F P' txe) (PDCA.scx_postA L F P' txe) Hcj Hci Xpc (Z.le_refl 0)
                  fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP Hag HLF HIH _ _).
        - intros LB' FF' LK' cr' A'. rewrite Hpc. exact (SCX ra (SP + CH2.ci_csp ci) F P' txe LB' FF' LK' cr' A').
        - intros LKu CF HHu HLKu.
          destruct (CHA.ca_sp L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 80 1 c1 ps cj ci i E E' R' A1 M2 m2 CF) as (Csp & C1 & C2 & C3).
          assert (Hcsp : CH2.ci_csp ci = 0).
          { unfold PDC.rz, PDC.reg_of in G2. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in G2 by (apply bv_eq; reflexivity). rewrite Csp in G2. rewrite u64_of_Z in G2 by lia. lia. }
          split.
          +
            unfold PDCA.scx_preA. split; [exact G10|]. split; [exact G11|]. split.
            { unfold PDC.file_ok, PDC.STK_FLOOR. split; [exact Hrp2|]. split; [exact H184f|]. split; [exact H192f|]. split; [|lia].
              apply (L5C.writable_of_defined segs M2 (F + 8) 8); [|lia|lia]. intros d Hd. apply Hdf2; [lia | right; left; split; lia | apply Hfd8; exact Hd]. }
            split; [rewrite Hcsp; lia|]. split; [intros d Hd; apply Hdf2; [lia | right; left; split; lia | apply Hfd8; exact Hd]|].
            split; [exact TXTf|]. split; [|split; [|exact IMGC2]].
            { apply (FLA.txt_home_mono ar LB FF (SP + 8416) Q (N + 1) _ _ _ Hblk); [rewrite Hcsp; lia | unfold P'; lia | rewrite Ltxe; unfold P'; lia]. }
            { unfold PDC.apart in *. rewrite Ltxe. unfold P'. lia. }
          +
            intros R2 M3 model3 LK3 A3 HPo HRP2 HP3 HH3.
            unfold PDCA.scx_postA in HPo.
            set (rpos2 := match PD.exp_scan txe with Some k2 => P' + k2 | None => P' end).
            assert (Hr2 : L5.u64_at segs M3 (F + 8) rpos2 /\ (if lmin then PDC.rz R2 10 = 2 ^ 63 else PDC.rz R2 10 <> 2 ^ 63)).
            { unfold rpos2. destruct (PD.exp_scan txe) as [k2|] eqn:Eexp; destruct HPo as [Hu Ha0]; split; try exact Hu.
              - destruct lmin; [exfalso; pose proof (proj1 Hlm eq_refl); congruence | exact Ha0].
              - destruct lmin; [exact Ha0 | exfalso; pose proof (proj2 Hlm eq_refl); congruence]. }
            destruct Hr2 as [Hu2 Ha02].
            assert (Rr2 : 0 <= rpos2 < 2 ^ 64).
            { unfold rpos2. pose proof (DOSA.D_range txt) as DR. unfold DOSA.N in DR. pose proof HDx as HD2. destruct (PD.exp_scan txe) as [k2|]; unfold P'; lia. }
            exists [Z_to_bv 64 rpos2]. split; [reflexivity|]. cbv zeta.
            pose proof (CHA.ca_vars L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 80 1 c1 ps cj ci i E E' R' A1 M2 m2 CF) as (W1 & W2 & W3 & W4 & W5).
            pose proof (CHA.ca_regs L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 80 1 c1 ps cj ci i E E' R' A1 M2 m2 CF) as HR.
            pose proof (CHA.ca_regs_eq L ar HI NF E0 M model A LB FF LK SP HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 80 1 c1 ps cj ci i E E' R' A1 M2 m2 CF) as Hreq.
            set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [Z_to_bv 64 rpos2] R2).
            pose proof (CH2.retEx_agree E' nx [Z_to_bv 64 rpos2] R2 : env_agree nx E' E2) as Hag2.
            assert (HagE1 : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
            assert (Hag02 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag2 | unfold nx; lia]]).
            assert (Gh : ev E2 nx = Z_to_bv 64 rpos2) by (unfold E2; rewrite <- (Nat.add_0_r nx) at 2; exact (CH2.retEx_ghost E' nx [Z_to_bv 64 rpos2] R2 0 ltac:(cbn; lia))).
            assert (UF2 : bv_unsigned (ev E2 21) = F) by (rewrite <- (proj1 Hag02 21%nat) by (unfold DOK.NF; lia); exact U21).
            assert (HR2 : regs_ok E2 (APC.sr_fresh (CH2.ci_regs ci) APC.caller_saved (nx + 1)) R2).
            { unfold E2, CH2.retEx. cbn [length]. apply (CH2.ret_regs (APS.ext_list E' nx [Z_to_bv 64 rpos2]) _ (nx + 1) R' R2).
              - intros r0. rewrite (HR r0). apply (SR.edenot_agree_AP nx); [apply APS.ext_list_agree|]. unfold sr_get. destruct (bv_eqb r0 0); [reflexivity | apply CH.nth_vars_lt; exact W1].
              - eapply APS.sr_vars_lt_mono; [exact W1 | lia].
              - exact (CH2.regs_preserved_kept R' R2 HRP2). }
            assert (NXc : DOSA.scx_nx cj = nx) by (unfold DOSA.scx_nx; unfold nx; lia).
            split; [|split; [|split; [|split]]].
            *   destruct lmin; [|exact I]. unfold PDC.rz, PDC.reg_of in Ha02. replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in Ha02 by (apply bv_eq; reflexivity). cbn [edenot].
              apply bv_eq. rewrite Ha02. unfold DOSA.LMIN. rewrite u64_of_Z by lia. reflexivity.
            *   intros w a [<-|[]] Hin. exists (EVar 21, 8, ELit 8). split; [left; reflexivity|].
              unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite <- (proj1 HagE1 21%nat) by (unfold DOK.NF; lia). rewrite U21. rewrite u64_of_Z by lia.
              unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
            *   intros w a [<-|[]] Hin [_ [_ Ho]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
              apply (Ho (F + 8, 8)); [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia].
            *   unfold XIA, DOSA.XI. fold kind_of. destruct lmin.
              -- rewrite Hkj. replace (Q + DOSA.D txt + 1) with rpos2; [exact Hu2|]. unfold rpos2. rewrite (proj1 Hlm eq_refl). rewrite HDx, (proj1 Hlm eq_refl). unfold P'. lia.
              -- rewrite Hkj. replace (Q + DOSA.D txt) with rpos2; [exact Hu2|]. unfold rpos2. rewrite HDx.
                 destruct (PD.exp_scan txe) as [k2|] eqn:Eexp; [unfold P'; lia | exfalso; pose proof (proj2 Hlm eq_refl); congruence].
            *
              intros X HXn _. unfold DOSA.scx_news in HXn. rewrite NXc in HXn. cbn [In] in HXn.
              assert (VF3 : CL5A.visr (ahid A3 model3) (F + 8) 8) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH3); lia).
              destruct HXn as [<-|HXn].
              -- apply (CL5.kword64_intro segs E2 _ _ _ (F + 8) rpos2); [exact (DOSA.estart_reg E2 21 8 F UF2) | lia | lia | cbn [edenot]; exact Gh |].
                 exact (CL5A.u64_vis segs (ahid A3 model3) M3 (F + 8) rpos2 ltac:(lia) ltac:(lia) VF3 Hu2).
              -- destruct lmin; [destruct HXn|]. destruct HXn as [<-|[]].
                 unfold DOSA.scx_a0v. rewrite NXc. rewrite <- Hreq.
                 pose proof (HR2 10%bv) as A10. unfold sr_get in A10. change (bv_eqb (10%bv : bv 5) 0) with false in A10. cbv iota in A10. change (ridx 10%bv) with 10%nat in A10.
                 unfold PDC.rz, PDC.reg_of in Ha02. replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in Ha02 by (apply bv_eq; reflexivity).
                 assert (NS : uE E2 (DAS.nmin_of (nth 10 (APC.sr_fresh (CH2.ci_regs ci) APC.caller_saved (nx + 1)) (ELit 0))) = 0).
                 { apply DOSA.nmin_sem. unfold uE. rewrite <- A10. unfold DOSA.LMIN. exact Ha02. }
                 cbn [kentry_ok]. unfold uE in NS. rewrite NS. lia. }
      destruct (PD.exp_scan txe) as [k2|] eqn:Eexp.
      * apply (COMMONA false (Datatypes.S ja) cjb Hcjb Yb Kjb). split; [discriminate | congruence].
      * apply (COMMONA true ja cja Hcja Ya Kja). split; [reflexivity | reflexivity].
    +
      apply existsb_exists in X as ([[[j i'] k'] pc] & _ & X). do 5 (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply Z.eqb_eq in Y3, Y2. subst i' pc.
      destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate Y].
      pose proof (CC.cps_all_sound _ _ FOOT_OK i c1 Hc1) as Hfoot. cbn beta in Hfoot.
      destruct (find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) id) INL) as [[pc' [[len hv] a0]]|] eqn:Hf.
      * apply find_some in Hf as [HinI Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
        pose proof (INL_OK _ HinI) as Hsem. cbn in Hsem. rewrite <- Y2 in Hsem.
        assert (XL : CVFA.xi_leafA NF E0 XIA i j c1).
        { intros Ea Eb Ec Aa Ab Ma Mb ma mb HXa Hag0 Hagc Hfr Hgr. unfold XIA in *.
          exact (DOSA.xi_leaf_ok segs CPS RETS DKINDS SCANEXP ERRNO txt Q F SP E0 U2 R_SP R_F R_ERR U4 Hfs i j c1 Y0 Ci Ea Eb Ec Ma Mb HXa Hag0 Hagc Hfr Hgr). }
        destruct a0 as [z|].
        -- destruct Hsem as [-> Hst].
           exact (CVFA.inl_leaf_ok_a0A L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK cr SP HD W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                    CPS K FPI XIA FPI_to FPM i c1 ps j cj len z Hcj Y Hfoot Hnf XL Hst).
        -- exact (CVFA.inl_leaf_okA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M model A LB FF LK cr SP HD W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                    CPS K FPI XIA FPI_to FPM i c1 ps j cj len hv Hcj Y Hfoot Hnf XL Hsem).
      * destruct (find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) id) CALLEES) as [[pc' [SCRc IMG']]|] eqn:Hg; [|discriminate Y].
        apply find_some in Hg as [HinC Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
        pose proof (CALLEES_OK _ _ _ HinC) as Hct. rewrite <- Y2 in Hct.
        assert (XC : CVFA.xi_callA L ar NF E0 LB FF SP HD XIA i j c1 SCRc).
        { intros Ea Eb Ec Aa Ab Ma Mb Mc ma mb csp HXa Hag0 Hagc Hfr Hgr C1 C2 C3 Hkept. unfold XIA in *. rewrite SCRV in C3.
          refine (DOSA.xi_callF_ok segs CPS RETS DKINDS SCANEXP ERRNO txt Q F SP E0 U2 R_SP R_F R_ERR U4 Hfs i j c1 Y0 Ci Ea Eb Ec Ma Mb Mc HXa Hag0 Hagc Hfr Hgr _).
          intros a Ha. apply Hkept. split; [lia|]. split; [right; left; split; lia | intros w []]. }
        exact (CVFA.call_leaf_okA L ar C HI HIok LY_img LY_ro NF E0 M model A LB FF LK cr SP HD W W 0 STKF SCRP NF32 U2 TP0 (incl_refl _) WOK Hffrs0 CRS_OK WRS_OK IMG_OK
                 CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XIA HKnil i c1 ps j cj SCRc IMG' Hcj Y (Z.le_refl 0) XC Hct).
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite CPA.NOBnil, CPA.NOFnil. cbn [CH2.den CHA.denF map app length]. rewrite Z.sub_0_r.
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + unfold XIA, DOSA.XI. unfold kind_of in Hk0. rewrite Hk0. exact I.
Qed.

End Run.
End DOLA.
