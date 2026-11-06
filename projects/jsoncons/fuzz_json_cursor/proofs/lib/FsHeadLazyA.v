(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  FrmInv PmHeapIfaceA CutVFXM DecIface DecJson DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA StrtodPure StrtodIface FloatLazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD DecAssume CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutPureA CutVFA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FHLA.
Definition NFh : nat := 34.

Definition hideP (P : Prop) : Prop := P.
Definition F0 : list SGP.region := [(EVar 2, -8672, ELit 8672); (EVar 10, 8, ELit 8)].
Fixpoint find_byte (kn : list kentry) (o : Z) : option nat :=
  match kn with
  | [] => None
  | KWord (SA (EVar 32) o') 1 (EVar v) :: r => if Z.eqb o' o then Some v else find_byte r o
  | _ :: r => find_byte r o
  end.
Lemma find_byte_In : forall kn o v, find_byte kn o = Some v -> In (KWord (SA (EVar 32) o) 1 (EVar v)) kn.
Proof.
  induction kn as [|K r IH]; intros o v H; [discriminate|]. cbn [find_byte] in H.
  destruct K as [[b o'] w x| | | | | | | | |]; try (right; exact (IH _ _ H)).
  destruct b as [|n| | | | | |]; try (right; exact (IH _ _ H)).
  do 33 (destruct n as [|n]; try (right; exact (IH _ _ H))).
  do 2 (destruct w as [|w]; try (right; exact (IH _ _ H))).
  destruct x as [|v'| | | | | |]; try (right; exact (IH _ _ H)).
  destruct (Z.eqb_spec o' o) as [->|]; [injection H as ->; left; reflexivity | right; exact (IH _ _ H)].
Qed.
Definition rawx (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_AND e (ELit (-33))) (ELit 88)) (ELit 1).

Definition live_chk (GA : Z) (e2 : bool) (q : Z) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_reg_is ps 2 (APC.eaddz (EVar 2) (-8416)) && CL.ps_reg_is ps 3 (EVar 3) && CL.ps_reg_is ps 4 (EVar 4) && CL.ps_reg_is ps 21 (EVar 10) && CL.ps_reg_is ps 23 (ELit 1)
   && CL.ps_reg_is ps 18 (ELit 53) && CL.ps_reg_is ps 22 (ELit 18446744073709550542) && CL.ps_reg_is ps 24 (ELit 1)
   && (CL.ps_reg_is ps 9 (ELit 1) || CL.ps_reg_is ps 9 (ELit 18446744073709551615)) && CL.ps_reg_is ps 20 (ELit GA)
   && forallb (fun ro : nat * Z => has cells (KWord (SA (EVar 2) (snd ro - 2032)) 8 (EVar (fst ro)))) PDC.SAVES
   && has cells (KWord (SA (EVar 2) (-120)) 8 (EVar 33)) && has cells (KWord (SA (ELit 0) GA) 8 (EVar 33))
   && has cells (KWord (SA (EVar 10) 8) 8 (APC.eaddz (EVar 32) (q + (if e2 then 2 else 1))))
   && has cells (KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615)) && has cells (KWord (SA (EVar 10) 192) 8 (ELit 0))
   && match find_byte cells q with
      | Some cv => if e2 then DOS.rng_in cells (EVar cv) 48 48 else (DOS.rng_in cells (EVar cv) 49 57 && CL.ps_reg_is ps 10 (EVar cv))%bool
      | None => false
      end)%bool.
Definition dead_chk (q : Z) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match find_byte cells q, find_byte cells (q + 1) with
  | Some c0, Some c2 => (DOS.rng_in cells (EVar c0) 48 48 && DOS.rng_in cells (EVar c2) 0 255 && has cells (KRange (rawx (EVar c2)) 1 1))%bool
  | _, _ => false
  end.

Definition leaf_chk (GA E1PC E2PC HEXPC : Z) (q : Z) (i0 : nat) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  if negb (Nat.eqb i i0) then true else
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb (SR.ps_pc ps) pc && regions_eqb (CC.cp_F c) F0 && Nat.leb NFh (CC.cp_nx c)
                     && ((Z.eqb pc HEXPC && dead_chk q ps) || (Z.eqb pc E1PC && live_chk GA false q ps) || (Z.eqb pc E2PC && live_chk GA true q ps)))%bool
  end.

Section Run.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable FPI : FPState -> Prop.
Abbreviation segs := (hl_segs L).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M', msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.
Variable AD : PDC.addrs.
Abbreviation ERRNO := (PDC.a_TP AD - 164).
Abbreviation GA := (PDC.a_G AD).
Abbreviation IMG_LO := (PDC.a_img_lo AD).
Abbreviation IMG_HI := (PDC.a_img_hi AD).
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable HD : CH.hdecl.
Variable HEXPC : Z.
Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis TAGS_OK : CC.tags_chk CPS TAGS NFh = true.
Hypothesis HEAP_OK : CHA.heap_chkA NFh HD (CPA.NOB CPS) (CPA.NOF CPS) CPS TAGS = true.
Hypothesis FOOT_OK : CC.cps_all CPS (fun _ c => CHA.foot_chk NFh HD c [] []) = true.
Hypothesis HSCR : CH.hd_scr HD = 8672.
Hypothesis HWRS : CH.hd_wrs HD = [(EVar 10, 8, ELit 8)].
Hypothesis HIMGD : CH.hd_img HD = [(IMG_LO, IMG_HI)].
Hypothesis DEC : forall e2, PDCA.decfloat_contractA L ar HI FPI AD e2.
Hypothesis IMGR : hl_img_lo L <= IMG_LO /\ IMG_HI <= hl_img_hi L /\ forall a, IMG_LO <= a < IMG_HI -> ~ hl_rt_static L a.
Hypothesis FL : PDCA.float_layoutA L AD.
Hypothesis ERRW : forall M : PDCA.mem, L5.writable segs M ERRNO 4.

Theorem head_runA : forall (i0 : nat) (q : Z) (c0 : CC.cutpoint)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (fx : FPState) (R : bvmap 5 word) (M : PDCA.mem) (model : Model) (K : TSet)
    (r sp F s CAN : Z) (txt : list Z) (E0 : env),
  (q = 0 \/ q = 1) -> nth_error CPS i0 = Some c0 -> CH2.leaves_all CPS TAGS (leaf_chk GA (PDC.a_E1 AD) (PDC.a_E2 AD) HEXPC q i0) = true ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> FPI fx ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
  CHA.astk ar M sp PSI.WIN -> CHA.ffroom FF LK 0 -> CHA.ffrs FF sp ->
  PDCA.fs_preA L ar AD sp F s CAN txt LB FF R M ->

  q < Z.of_nat (length txt) -> q + PD.dec_len (skipn (Z.to_nat q) txt) = Z.of_nat (length txt) ->
  (nth (Z.to_nat q) (txt ++ [0]) 0 = 48 -> PSP.after0_ok (nth (Z.to_nat (q + 1)) (txt ++ [0]) 0)) ->
  (forall x : reg, ev E0 (ridx x) = getr R x) -> bv_unsigned (ev E0 32) = s -> ev E0 33 = Z_to_bv 64 CAN ->
  CCA.AtV segs c0 E0 R A M model ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : PDCA.mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)),
      FPI fx' -> PDCA.fs_postA L F s txt R M R' M' -> regs_preserved R R' ->
      CHA.ahpres L ar LB FF sp PSI.WIN (PDCA.DW AD F) M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB FF LK' cr A' M' (vml_of model') ->
      srealizes segs SCFG (mkCfg (mk fx' R' r M') model') K) ->
  srealizes segs SCFG (mkCfg (mk fx R (CC.cp_pc c0) M) model) K.
Proof.
  intros i0 q c0 LB FF LK cr A fx R M model K r sp F s CAN txt E0 Hq01 Hc0 LEAVES HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre HqN Hfull Hafter0 EV EVs EVc HAt Hcont.
  destruct Hpre as (RF & R11 & R12 & Hfile & HspF & Hfd8 & Hguard & RCAN & Htext & Hblk & Hapf & Hnumf & Himg).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr).
  destruct FL as [TP CELLS]. destruct IMGR as (IM1 & IM2 & IM3).
  set (N := Z.of_nat (length txt)) in *. unfold PSI.WIN, PDC.STK_FLOOR in *.
  assert (HN0 : 0 <= N) by (unfold N; lia).
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. pose proof (CHA.wf_top L ar _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as TOP.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (FLA.txt_facts_h L ar C HI HIok LY_img _ _ _ _ _ _ _ sp s (N + 1) HH ltac:(lia) Hblk ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5).
  assert (TBS : hideP (s + (N + 1) <= sp - 8672 \/ sp <= s)) by (unfold hideP; lia). clear TB2.
  assert (TAF : hideP (s + (N + 1) <= F + 8 \/ F + 8 + 192 <= s)) by (unfold hideP, PDC.apart in *; lia). clear Hapf.
  assert (ER : hl_img_lo L <= ERRNO /\ ERRNO + 4 <= hl_img_hi L) by (destruct (CELLS ERRNO ltac:(lia)) as [X _]; destruct (CELLS (ERRNO + 3) ltac:(lia)) as [Y _]; lia).
  assert (GR : hl_img_lo L <= GA /\ GA + 8 <= hl_img_hi L) by (destruct (CELLS GA ltac:(lia)) as [X _]; destruct (CELLS (GA + 7) ltac:(lia)) as [Y _]; lia).
  pose proof LY_img as [LI0 LI1]. unfold BIGSHADOW_LO in LI1.

  assert (V2 : ev E0 2 = getr R 2%bv) by exact (EV 2%bv). assert (V4 : ev E0 4 = getr R 4%bv) by exact (EV 4%bv). assert (V10 : ev E0 10 = getr R 10%bv) by exact (EV 10%bv).
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; exact Usp).
  assert (U10 : bv_unsigned (ev E0 10) = F) by (rewrite V10; exact RF).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4; exact Htp).
  assert (U4 : bv_unsigned (ev E0 4) = ERRNO + 164) by (rewrite TP0, TP; rewrite u64_of_Z by lia; lia).

  assert (SCRV : CH.hd_scr HD = 8672) by exact HSCR.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr HD <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr HD) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= NFh)%nat) by (unfold NFh; lia).
  set (W := [(F + 8, 8); (ERRNO, 4)] : list L5.range).
  assert (WCL : forall a, (F + 8 <= a < F + 16 \/ ERRNO <= a < ERRNO + 4) ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr HD) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. rewrite SCRV. destruct Ha as [Ha|Ha].
    - split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
    - destruct (CELLS a ltac:(lia)) as (C1 & C2 & C3 & _). split; [lia|]. split; [right; right; left; split; [exact C1 | intros [X|X]; [exact (C2 X) | exact (C3 X)]]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia. }
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr HD) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a Hw Hin. unfold L5.in_rng in Hin. unfold W in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[]]]; cbn [fst snd] in Hin; apply WCL; lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HD) -> SGP.region_vars_lt NFh rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { rewrite HWRS. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (F + 8, 8). split; [unfold W; cbn; tauto | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr HD) (CH.hd_scr HD)) by (rewrite SCRV; exact S5).

  set (XIA := fun (i : nat) (_ : env) (_ : list (Z * Z)) (_ : PDCA.mem) (_ : Model) => i = i0).
  assert (LEAF : forall i c ps E E' R1 R' A1 M1 m1 M2 m2, nth_error CPS i = Some c ->
            CCA.AtV segs c E R1 A1 M1 m1 -> CHA.aamb L ar HI NFh E0 M model A LB FF LK sp HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M1 m1 ->
            env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA segs c ps E' R' A1 M1 m1 M2 m2 ->
            CHA.aamb L ar HI NFh E0 M model A LB FF LK sp HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2).
  { intros i c ps E E' R1 R' A1 M1 m1 M2 m2 Hc HAt1 HA1 Hag HLF.
    refine (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NFh E0 M model A LB FF LK sp HD W W _ _ _ 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK i c ps E E' R1 R' A1 M1 m1 M2 m2 _ HAt1 HA1 Hag HLF).
    rewrite CPA.NOBnil, CPA.NOFnil. exact (CC.cps_all_sound _ _ FOOT_OK i c Hc). }
  eapply (CHA.cert_soundA L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NFh E0 M model A LB FF LK sp HD W W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            CPS K FPI XIA TAGS FPM PLANS TAGS_OK HEAP_OK _ _ _ i0 c0 fx E0 R A M model Hc0 HAt _ Hfp).
  Unshelve.
  - intros i c k ps j sg _ E E' R' M1 M2 cr1 _ _ _ HC. exact HC.
  -
    intros i c1 k ps j sg IL E R1 E' R' A1 M1 m1 M2 m2 _ _ _ _ HXi. unfold XIA in HXi. subst i. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ LEAVES _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Nat.eqb_refl in X. cbn [negb] in X. discriminate X.
  -
    intros i c1 k ps pc IL fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 [HA1 HXi] HFP Hag HLF _. unfold XIA in HXi. subst i.
    pose proof (CH2.leaves_all_sound _ _ _ LEAVES _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Nat.eqb_refl in X. cbn [negb] in X.
    destruct IL as (tags & Hc1 & Htags & Hps & Htag). rewrite Hc0 in Hc1. injection Hc1 as <-.
    do 3 (apply andb_prop in X as [X ?Y]). apply Z.eqb_eq in X. apply regions_eqb_eq in Y1. apply Nat.leb_le in Y0. rename X into Hpc. rename Y1 into HF. rename Y0 into Hnf.
    pose proof (LEAF i0 c0 ps E E' R1 R' A1 M1 m1 M2 m2 Hc0 HAt1 HA1 Hag HLF) as HA2.
    pose proof HA1 as (_ & _ & _ & HagE & (cr1 & LK1 & HH1 & _) & Hfr1 & _).
    pose proof HA2 as (Hmo2 & Hrt2 & HA02 & _ & (cr2 & LK2 & HH2 & HLK2 & HC2 & HRoom2) & Hfr2 & Hdf2).
    unfold CHA.curB, CHA.curF in HH1, HH2, HRoom2. rewrite CPA.NOBnil, CPA.NOFnil in HH1, HH2. rewrite CPA.NOFnil in HRoom2. cbn [CH2.den CHA.denF map app length Z.of_nat] in HH1, HH2, HRoom2.
    unfold CPA.Cred0 in HC2. subst cr2. rewrite Z.sub_0_r in HRoom2.
    assert (HagE' : env_agree NFh E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
    pose proof (CBA.amb_off L ar C HI HIok LY_below NFh E0 M model A LB FF LK sp HD W (CPA.NOB CPS) (CPA.NOF CPS) (CPA.Cred0 cr) 0 i0 E A1 M2 m2 HA2) as Hoff.
    pose proof (CBA.exit_post L ar C HI HIok NFh M model A LB FF sp HD W (CPA.NOB CPS) STKF NF32 DEF0 i0 E A1 M2 m2 cr LK2 FF Hmo2 Hrt2 HA02 Hfr2 Hdf2) as HP.
    unfold CHA.curB in HP. rewrite CPA.NOBnil in HP. cbn [CH2.den map app] in HP. specialize (HP HH2). rewrite SCRV in HP. pose proof HP as (P1 & P2 & P3).
    assert (HK' : know_ok segs E' (CCA.vis A1 m2 M2) (SR.ps_cells ps)) by (apply Forall_forall; intros Z0 HZ; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Z0 HZ)).
    assert (EVf : forall n, (n < 34)%nat -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); exact Hn).
    assert (U2' : bv_unsigned (ev E' 2) = sp) by (rewrite EVf by lia; exact U2).
    assert (U10' : bv_unsigned (ev E' 10) = F) by (rewrite EVf by lia; exact U10).
    assert (U32' : bv_unsigned (ev E' 32) = s) by (rewrite EVf by lia; exact EVs).

    assert (TXTK : forall a, s <= a < s + (N + 1) -> CHA.akept L ar LB FF sp (CH.hd_scr HD) W a).
    { intros a Ha. rewrite SCRV. apply (FLA.txt_kept_h L ar C HI HIok LY_img _ _ _ _ _ _ _ sp s (N + 1) _ _ _ HH); [lia | lia | exact Hblk | | exact Ha].
      intros w Hw. unfold W in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; [unfold hideP in TAF; lia | lia]. }
    assert (TXTV : forall j, 0 <= j <= N -> L5.u8_at segs (CCA.vis A1 m2 M2) (s + j) (nth (Z.to_nat j) (txt ++ [0]) 0) /\ 0 <= nth (Z.to_nat j) (txt ++ [0]) 0 < 256).
    { intros j Hj.
      assert (Hm : L5.u8_at segs M (s + j) (nth (Z.to_nat j) (txt ++ [0]) 0) /\ 0 <= nth (Z.to_nat j) (txt ++ [0]) 0 < 256).
      { destruct (Z.eq_dec j N) as [->|Hne].
        - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact Tn | lia].
        - assert (Hlt : (Z.to_nat j < length txt)%nat) by (unfold N in *; lia). rewrite app_nth1 by exact Hlt. split.
          + pose proof (Tb (Z.to_nat j) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
          + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hlt. }
      destruct Hm as [Hm Rm]. split; [|exact Rm]. apply (CL5A.u8_vis segs (ahid A1 m2) M2); [lia | lia | |].
      - intros ii Hii. pose proof (FLA.txt_visr_h L ar C HI HIok LY_img _ _ _ _ _ _ _ sp s (N + 1) HH2 ltac:(lia) Hblk (j + ii) ltac:(lia)) as Vx.
        replace (s + (j + ii)) with (s + j + ii) in Vx by lia. exact Vx.
      - apply (CL5A.u8_same segs M M2 (s + j) _ ltac:(lia) ltac:(lia)); [|exact Hm]. apply Hfr2. apply TXTK. lia. }
    assert (BYTE : forall o cv, find_byte (SR.ps_cells ps) o = Some cv -> 0 <= o <= N -> 0 <= uE E' (EVar cv) <= 255 -> uE E' (EVar cv) = nth (Z.to_nat o) (txt ++ [0]) 0).
    { intros o cv Hf Ho Rc. apply find_byte_In in Hf. pose proof (proj1 (Forall_forall _ _) HK' _ Hf) as Yb.
      apply (CL5A.kword8_elim segs E' _ _ _ (s + o)) in Yb; [|apply (DOS.estart_reg E' 32 o s U32')]. unfold CL5A.uv, uE in *.
      destruct (TXTV o Ho) as [Ht Rt]. symmetry. exact (u8_at_inj segs (CCA.vis A1 m2 M2) _ _ _ Ht Yb Rt ltac:(lia)). }
    assert (ERI : forall a, ERRNO <= a < ERRNO + 4 -> a < IMG_LO \/ IMG_HI <= a) by (intros a Ha; exact (proj2 (proj2 (proj2 (CELLS a ltac:(lia)))))).
    assert (LIVE : forall e2, live_chk GA e2 q ps = true -> pc = (if e2 then PDC.a_E2 AD else PDC.a_E1 AD) ->
              srealizes segs SCFG (mkCfg (mk fx' R' (SR.ps_pc ps) M2) m2) K).
    { intros e2 HL Hpce. rewrite Hpc, Hpce. unfold live_chk in HL. do 16 (apply andb_prop in HL as [HL ?X]).
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (REG : forall n e, CL.ps_reg_is ps n e = true -> getr R' (Z_to_bv 5 (Z.of_nat n)) = edenot E' e) by (intros n e Hne; exact (CL.ps_reg_is_sound segs c0 ps E' R' _ _ n e HLFv Hne)).
      assert (RLIT : forall n z, CL.ps_reg_is ps n (ELit z) = true -> 0 <= z < 2 ^ 64 -> PDC.rz R' n = z) by (intros n z Hne Hz; unfold PDC.rz, PDC.reg_of; rewrite (REG n _ Hne); cbn [edenot]; apply u64_of_Z; exact Hz).
      set (SP := sp - 8416). set (dl := if e2 then 2 else 1). set (tq := skipn (Z.to_nat q) txt).
      assert (Ltq : Z.of_nat (length tq) = N - q) by (unfold tq; rewrite length_skipn; unfold N in *; lia).
      assert (Hdl : 1 <= dl <= 2) by (unfold dl; destruct e2; lia).
      destruct (find_byte (SR.ps_cells ps) q) as [cv|] eqn:Fb; [|discriminate X].

      assert (CELL : forall b o w v, In (KWord (SA b o) 8 v) (SR.ps_cells ps) -> estart E' (SA b o) = w -> L5.u64_at segs M2 w (CL5A.uv E' v)).
      { intros b o w v Hin Hw. exact (CL5A.u64_full segs _ Hoff _ _ _ (CL5A.kword64_elim segs E' _ _ _ w (proj1 (Forall_forall _ _) HK' _ Hin) Hw)). }
      unfold CL5A.uv in CELL.
      assert (DEFW : L5.defined M2 (SP - 256) (256 + 8416)) by (intros d Hd; replace (SP - 256 + d) with (sp - 8672 + d) by (unfold SP; lia); apply P2; lia).
      assert (DEF8 : L5.defined M2 (F + 8) 8) by (intros d Hd; apply Hdf2; [lia | right; left; split; lia | apply Hfd8; exact Hd]).
      assert (DTX : L5.defined M2 s (N + 1)).
      { intros d Hd. apply Hdf2; [lia | exact (FLA.txt_aclient_h L ar C HI HIok _ _ _ _ _ _ _ sp 0 s (N + 1) (s + d) HH ltac:(lia) Hblk ltac:(lia)) | apply Td; lia]. }
      assert (TXT2 : forall j, 0 <= j <= N -> L5.u8_at segs M2 (s + j) (nth (Z.to_nat j) (txt ++ [0]) 0)) by (intros j Hj; exact (CL5A.u8_full segs _ Hoff _ _ _ (proj1 (TXTV j Hj)))).
      assert (NTH : forall j, 0 <= j < N - q -> nth (Z.to_nat j) tq 0 = nth (Z.to_nat (q + j)) (txt ++ [0]) 0).
      { intros j Hj. unfold tq. rewrite nth_skipn. rewrite app_nth1 by (unfold N in *; lia). f_equal. lia. }
      assert (Rcv : 0 <= uE E' (EVar cv) <= 255 /\ (if e2 then uE E' (EVar cv) = 48 else 49 <= uE E' (EVar cv) <= 57)).
      { destruct e2; [pose proof (DOS.rng_in_sem segs E' _ _ _ _ _ HK' X) as Yc; lia|]. apply andb_prop in X as [X _]. pose proof (DOS.rng_in_sem segs E' _ _ _ _ _ HK' X) as Yc. lia. }
      pose proof (BYTE q cv Fb ltac:(lia) (proj1 Rcv)) as Bq.
      assert (Etq : tq = nth (Z.to_nat q) (txt ++ [0]) 0 :: skipn (Datatypes.S (Z.to_nat q)) txt).
      { unfold tq. rewrite (PDS.skipn_nth txt (Z.to_nat q) 0) by (unfold N in *; lia). f_equal. rewrite app_nth1 by (unfold N in *; lia). reflexivity. }
      assert (Hsv1 : PDC.rz R 1 = r) by (unfold PDC.rz, PDC.reg_of; replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Hra; apply u64_of_Z; destruct Hraok; lia).
      eapply (DEC e2 LB FF LK2 cr A1 fx' R' M2 m2 K SP F (s + q + dl) (s + q) CAN (fun r0 => PDC.rz R r0) tq HH2 Hmo2 HKnil HFP).
      -   unfold SP, PDC.FRAME, PDC.SCR_D. replace (sp - 8416 + 8416) with sp by lia. split; [exact S1|]. split; [lia|]. split; [exact S3|]. split; [exact S4|]. split.
        + intros d Hd. apply P2. lia.
        + intros d Hd. apply Hdf2; [lia | right; left; split; lia | apply S6; exact Hd].
      - exact HRoom2.
      - unfold SP, PDC.FRAME. replace (sp - 8416 + 8416) with sp by lia. exact Hffrs.
      -
        split; [|split; [unfold SP, PDC.FRAME; lia | split; [exact DEF8 | split; [| split; [exact RCAN | rewrite Hsv1; exact Hraok]]]]].
        2:{ apply (FLA.txt_home_mono ar LB FF sp s (N + 1) _ _ _ Hblk); [unfold SP, PDC.FRAME; lia | lia | rewrite Ltq; lia]. }
        unfold PDC.dec_pre, PDC.FRAME, PDC.SCR_D, PDC.STK_FLOOR.
        assert (G2 : PDC.rz R' 2 = SP).
        { unfold PDC.rz, PDC.reg_of. rewrite (REG 2%nat _ HL). unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite U2'. change (bv_unsigned (Z_to_bv 64 (-8416))) with (2 ^ 64 - 8416).
          replace (sp + (2 ^ 64 - 8416)) with (sp - 8416 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. unfold SP. lia. }
        split; [exact G2|]. split; [unfold SP; rewrite Zminus_mod, S1; reflexivity|]. split; [unfold SP; lia|]. split; [unfold SP; lia|].
        split; [unfold PDC.rz, PDC.reg_of; rewrite (REG 21%nat _ X12); cbn [edenot]; exact U10'|].
        split; [exact (RLIT 23%nat 1 X11 ltac:(lia))|]. split; [exact (RLIT 18%nat 53 X10 ltac:(lia))|].
        split; [exact (RLIT 22%nat _ X9 ltac:(lia))|]. split; [exact (RLIT 24%nat 1 X8 ltac:(lia))|].
        split; [apply orb_prop in X7 as [X7|X7]; [left; exact (RLIT 9%nat 1 X7 ltac:(lia)) | right; exact (RLIT 9%nat _ X7 ltac:(lia))]|].
        split; [exact (RLIT 20%nat GA X6 ltac:(lia))|].
        split; [unfold PDC.rz, PDC.reg_of; rewrite (REG 4%nat _ X13); cbn [edenot]; rewrite EVf by lia; lia|].
        split; [exact DEFW|]. split; [apply (L5C.writable_of_defined segs M2 _ _ DEFW); unfold SP; lia|].
        split.
        { intros r0 o Hin. rewrite forallb_forall in X5. pose proof (X5 _ Hin) as Yc. cbn [fst snd] in Yc. apply has_In in Yc.
          split; [|unfold PDC.rz; pose proof (u64_range (getr R (PDC.reg_of r0))) as B; unfold two64 in B; exact B].
          assert (Ho : 1928 <= o <= 2024 /\ (r0 < 32)%nat) by (unfold PDC.SAVES in Hin; cbn [In] in Hin; intuition (match goal with HH0 : (_, _) = (_, _) |- _ => injection HH0 as <- <- end; lia)).
          pose proof (CELL _ _ (SP + 6384 + o) _ Yc ltac:(rewrite (DOS.estart_reg E' 2 _ sp U2'); unfold SP; lia)) as Z0. cbn [edenot] in Z0. rewrite EVf in Z0 by lia.
          unfold PDC.rz, PDC.reg_of. rewrite <- (EV (Z_to_bv 5 (Z.of_nat r0))).
          replace (ridx (Z_to_bv 5 (Z.of_nat r0))) with r0; [exact Z0|]. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
        split; [rewrite Hsv1; apply Hoare.ret_ok_even; destruct Hraok as [R1' R2']; rewrite u64_of_Z by lia; exact R2'|].
        split.
        { apply has_In in X4. pose proof (CELL _ _ (SP + 8296) _ X4 ltac:(rewrite (DOS.estart_reg E' 2 _ sp U2'); unfold SP; lia)) as Z0. cbn [edenot] in Z0. rewrite EVf in Z0 by lia. rewrite EVc in Z0.
          rewrite u64_of_Z in Z0 by lia. exact Z0. }
        split.
        { apply has_In in X3. pose proof (CELL _ _ GA _ X3 ltac:(rewrite DOS.estart_lit by lia; lia)) as Z0. cbn [edenot] in Z0. rewrite EVf in Z0 by lia. rewrite EVc in Z0. rewrite u64_of_Z in Z0 by lia. exact Z0. }
        split; [unfold PDC.apart, SP; lia|].
        assert (Rq : 0 <= q + dl < 2 ^ 64) by lia.
        split.
        { unfold PDC.file_ok, PDC.STK_FLOOR. split; [|split; [|split; [|split; [apply (L5C.writable_of_defined segs M2 _ _ DEF8); lia | lia]]]].
          - apply has_In in X2. pose proof (CELL _ _ (F + 8) _ X2 (DOS.estart_reg E' 10 8 F U10')) as Z0.
            unfold APC.eaddz in Z0. rewrite mkAlu_denot, u_add64 in Z0. cbn [edenot] in Z0. rewrite U32' in Z0. fold dl in Z0. rewrite u64_of_Z in Z0 by exact Rq. rewrite Z.mod_small in Z0 by lia.
            replace (s + q + dl) with (s + (q + dl)) by lia. exact Z0.
          - apply has_In in X1. pose proof (CELL _ _ (F + 184) _ X1 (DOS.estart_reg E' 10 184 F U10')) as Z0. cbn [edenot] in Z0. rewrite u64_of_Z in Z0 by lia. exact Z0.
          - apply has_In in X0. pose proof (CELL _ _ (F + 192) _ X0 (DOS.estart_reg E' 10 192 F U10')) as Z0. cbn [edenot] in Z0. rewrite u64_of_Z in Z0 by lia. exact Z0. }
        split; [unfold PDC.apart, SP; lia|].
        split.
        { unfold PDC.text_ok. rewrite Ltq. split; [|split; [|split; [lia | split; [lia | split; [lia | split]]]]].
          - intros j Hj. pose proof (TXT2 (q + Z.of_nat j) ltac:(lia)) as Yc. replace (s + q + Z.of_nat j) with (s + (q + Z.of_nat j)) by lia.
            rewrite <- (NTH (Z.of_nat j)) in Yc by lia. rewrite Nat2Z.id in Yc. exact Yc.
          - replace (s + q + (N - q)) with (s + N) by lia. pose proof (TXT2 N ltac:(lia)) as Yc.
            rewrite app_nth2 in Yc by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat in Yc by (unfold N; lia). exact Yc.
          - intros d Hd. replace (s + q + d) with (s + (q + d)) by lia. apply DTX. lia.
          - apply Forall_forall. intros x Hx. rewrite Forall_forall in Tr. apply Tr. unfold tq in Hx. rewrite <- (firstn_skipn (Z.to_nat q) txt). apply in_or_app. right. exact Hx. }
        split; [unfold PDC.text_apart, PDC.apart; rewrite Ltq; cbv zeta; unfold SP; unfold hideP in TBS, TAF; lia|].
        split; [exact (ERRW M2)|].
        split.
        { intros a Ha. rewrite Hfr2; [exact (Himg a Ha)|]. rewrite SCRV. split; [lia|]. split; [right; right; left; split; [lia | exact (IM3 a Ha)]|].
          intros w Hw. unfold W in Hw. cbn [In] in Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; [lia|]. intros Hx. destruct (ERI a Hx); lia. }

        destruct e2.
        + split; [unfold dl; lia|]. exists (skipn (Datatypes.S (Z.to_nat q)) txt). rewrite Etq, <- Bq. f_equal. exact (proj2 Rcv).
        + split; [unfold dl; lia|]. exists (nth (Z.to_nat q) (txt ++ [0]) 0), (skipn (Datatypes.S (Z.to_nat q)) txt). split; [exact Etq|]. rewrite <- Bq. split; [exact (proj2 Rcv)|].
          apply andb_prop in X as [_ X]. unfold PDC.rz, PDC.reg_of. rewrite (REG 10%nat _ X). reflexivity.
      -
        intros fx2 R2 M3 model3 LK3 A3 HFP2 (Q1 & Q2 & Q3 & Q4 & Q5) HP3 Hrt3 HA3 Hmo3 HLK3 HH3.
        rewrite Hsv1. apply (Hcont fx2 R2 M3 model3 LK3 A3 HFP2).
        + unfold PDCA.fs_postA. replace (s + Z.of_nat (length txt)) with (s + q + PD.dec_len tq) by (unfold tq; fold N; lia). exact Q5.
        +
          assert (Hsv : forall r0 o, In (r0, o) PDC.SAVES -> In (Z.of_nat r0) callee_saved_idx -> getr R2 (PDC.reg_of r0) = getr R (PDC.reg_of r0)).
          { intros r0 o Hin Hci. apply bv_eq. exact (Q2 r0 o Hin Hci). }
          intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). unfold callee_saved_idx in Hx. cbn [In] in Hx.
          destruct Hx as [Hx|[Hx|[Hx|Hx]]]; [rewrite <- Hx | rewrite <- Hx | rewrite <- Hx |].
          * apply bv_eq. change (Z_to_bv 5 2) with (PDC.reg_of 2). fold (PDC.rz R2 2) (PDC.rz R 2). rewrite Q1. unfold SP, PDC.FRAME. unfold PDC.rz, PDC.reg_of.
            replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Usp. lia.
          * change (Z_to_bv 5 3) with (PDC.reg_of 3). rewrite Q3. unfold PDC.reg_of. rewrite (REG 3%nat _ X14). cbn [edenot]. rewrite EVf by lia. exact (EV 3%bv).
          * change (Z_to_bv 5 4) with (PDC.reg_of 4). rewrite Q4. unfold PDC.reg_of. rewrite (REG 4%nat _ X13). cbn [edenot]. rewrite EVf by lia. exact (EV 4%bv).
          * repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; match goal with |- getr R2 (Z_to_bv 5 ?z) = _ => change (Z_to_bv 5 z) with (PDC.reg_of (Z.to_nat z)) end;
                     eapply Hsv; [unfold PDC.SAVES; cbn; tauto | unfold callee_saved_idx; cbn; tauto] |]). destruct Hx.
        + apply (CRB.ahpres_trans L ar LB LB LB FF sp 8672 (256 + 8416) (PDCA.DW AD F) W (PDCA.DW AD F) M M2 M3); [exact HP | | apply incl_refl | apply incl_refl | lia | lia | lia | lia | |].
          * unfold SP, PDC.FRAME, PDC.SCR_D in HP3. replace (sp - 8416 + 8416) with sp in HP3 by lia. exact HP3.
          * intros w a Hw Ha. exists w. split; [|exact Ha]. unfold W in Hw. unfold PDCA.DW. exact Hw.
          * intros w a Hw Ha. exists w. split; assumption.
        + exact (L5LZ.model_rt_trans _ _ _ Hrt2 Hrt3).
        + exact (incl_tran HA02 HA3).
        + exact Hmo3.
        + exact (incl_tran HLK3 HLK2).
        + exact HH3. }
    apply orb_prop in Y as [Y|Y]; [apply orb_prop in Y as [Y|Y]|]; apply andb_prop in Y as [Ypc Y]; apply Z.eqb_eq in Ypc.
    +
      exfalso. unfold dead_chk in Y.
      destruct (find_byte (SR.ps_cells ps) q) as [cq|] eqn:F1; [|discriminate]. destruct (find_byte (SR.ps_cells ps) (q + 1)) as [c2|] eqn:F2; [|discriminate].
      do 2 (apply andb_prop in Y as [Y ?Z]).
      pose proof (DOS.rng_in_sem segs E' _ _ _ _ _ HK' Y) as R0. pose proof (DOS.rng_in_sem segs E' _ _ _ _ _ HK' Z0) as R2.
      pose proof (BYTE q cq F1 ltac:(lia) ltac:(lia)) as B0. pose proof (BYTE (q + 1) c2 F2 ltac:(lia) ltac:(lia)) as B2.
      pose proof (Hafter0 ltac:(lia)) as A0. rewrite <- B2 in A0. apply PSP.after0_not_x in A0. apply A0.
      pose proof (DOS.know_in segs E' _ _ _ HK' Z) as Yr. cbn [kentry_ok] in Yr. unfold rawx in Yr. cbn [edenot] in Yr. rewrite u_sltu64, u_sub64, u_and64 in Yr.
      change (bv_unsigned (Z_to_bv 64 (-33))) with (2 ^ 64 - 33) in Yr. change (bv_unsigned (Z_to_bv 64 88)) with 88 in Yr. change (bv_unsigned (Z_to_bv 64 1)) with 1 in Yr.
      unfold uE in *. cbn [edenot] in *. set (x := bv_unsigned (ev E' c2)) in *.
      pose proof (DOS.byte_enum (fun x => if (Z.land x (2 ^ 64 - 33) - 88) mod 2 ^ 64 <? 1 then Z.land x (2 ^ 64 - 33) =? 88 else true) ltac:(vm_compute; reflexivity) x R2) as Zb. cbv beta in Zb.
      destruct ((Z.land x (2 ^ 64 - 33) - 88) mod 2 ^ 64 <? 1); [apply Z.eqb_eq; exact Zb | lia].
    +   apply (LIVE false Y). exact Ypc.
    +   apply (LIVE true Y). exact Ypc.
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite CPA.NOBnil, CPA.NOFnil. cbn [CH2.den CHA.denF map app length]. rewrite Z.sub_0_r.
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + reflexivity.
Qed.
End Run.
End FHLA.
