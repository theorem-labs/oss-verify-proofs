(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_vis_end_array_cboth_T Cut_vis_end_array_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_vis_end_array_cboth.
Module GT := Cut_vis_end_array_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module VEndArrA.
Definition PC : Z := 830772.
Definition RETPC : Z := 830912.
Definition MEMSET : Z := 521936.
Definition MEMCPY : Z := 520756.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit 2147450880)].
Definition MSA : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)).
Definition MCD : expr := EAlu Instr.ALU_ADD (EVar 10) (ELit 17).
Definition MCS : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)).
Definition WR_MS : list SGP.region := [(MSA, 0, ELit 24)].
Definition WR_MC : list SGP.region := [(MCD, 0, ELit 31)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc MEMSET then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) MEMSET && Nat.eqb i 0 && Nat.eqb j 1 && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 [] [] WR_MS STAT (Some MSA) c ps cj [] [] [] [] with Some ci => Z.eqb (CH2.ci_csp ci) (-64) | None => false end
                                  && CL.ps_reg_is ps 10 MSA && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit 24))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc MEMCPY then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) MEMCPY && Nat.eqb i 1 && Nat.eqb j 2 && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 [] [] WR_MC STAT (Some MCD) c ps cj [] [] [] [] with Some ci => Z.eqb (CH2.ci_csp ci) (-64) | None => false end
                                  && CL.ps_reg_is ps 10 MCD && CL.ps_reg_is ps 11 MCS && CL.ps_reg_is ps 12 (ELit 31))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] && Nat.eqb i 2 && CH2.blocks_eqb (nth i G.BLS []) []
         && CL.ps_reg_is ps 10 (ELit 1) && CC.has_cell (SR.ps_cells ps) (KWord (SA (EVar 10) 8) 8 (ELit 2048)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true. Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC. Proof. CL.solve_is_ret. Qed.
Lemma bls_nil : forall i, nth i G.BLS [] = []. Proof. intros i. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma FFSnil : forall i, nth i FFS [] = []. Proof. intros i. unfold FFS. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
End VEndArrA.

Section VisitEndArrOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Abbreviation IC := PMLA.C_cboth.
Definition hid (P : Prop) : Prop := P.

Lemma rdn_def : forall (M : word -> option byte) (n : nat) (a : Z), L5.defined M a (Z.of_nat n) -> exists bs, rdn (hl_segs L) M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a H; [exists []; reflexivity|].
  destruct (IH (a + 1)) as (bs & Hr). { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hb; [|contradiction].
  exists (b :: bs). cbn [rdn]. rewrite Hb. rewrite CH.bv_succ_Z, Hr. reflexivity.
Qed.

Theorem visit_end_array_ok : PMSA.visit_end_array_specA L ar HI IC VEndArrA.PC.
Proof.
  unfold PMSA.visit_end_array_specA, PMSA.visit_scalar_specA.
  intros LB FF LK cr A V x sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & _ & HVIS & HOV & HSTKSH) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.VIS_SCR, PMSA.fobj, PMSA.vis_at, PMSA.stksh, PMLA.fobj, PMLA.vis_at, PMLA.stksh in *.
  destruct HOV as (Vfr & V8 & Vsh). destruct HVIS as (_ & VDEF). change (48 / 8) with 6 in Vsh.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF V 48 RFx Vfr ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in Q5. change (hid (V + 48 <= hl_img_lo L \/ hl_img_hi L <= V)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 CL SP1; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 2624) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (W := [(V + 8, 40)]).
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ V 48 a RFx Vfr ltac:(clear - Hin; lia)). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (V + 8, 40). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. cbv beta iota in Ha.
    rewrite ?CL5A.estart_srl3' in Ha. unfold estart, elenZ, CL5A.uv in Ha. cbn [a_base a_off edenot] in Ha. rewrite ?U10 in Ha. rewrite ?u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) V 48 a RFx Vfr ltac:(clear; lia) (CL5A.shreg_in_shadow V 6 a V8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (SHV := fun a => in_shadow_of V 48 a).
  set (SHS := fun a => S (sp - 2624) <= a < S (sp - 2624) + 328).
  assert (SHSK : forall a, SHS a -> CHA.akept L ar LB FF sp 2624 W a).
  { intros a Ha. unfold SHS, S, SB in Ha.
    assert (X : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a).
    { unfold in_shadow_of, S, SB. split; [|clear - Ha S2 S3 SP1 CL; lia].
      assert (ahl_ceil ar / 8 <= (sp - 2624) / 8) by (apply Z.div_le_mono; clear - S2; lia). clear - Ha H. lia. }
    pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 CL; lia) ltac:(clear - SP1 CL; lia) X) as SRa.
    split; [clear - SRa; lia|]. split; [do 4 right; left; exact X|]. intros w [<-|[]]. unfold L5.in_rng; cbn [fst snd]. unfold hid in Q5. clear - SRa Q5 Q3. lia. }
  assert (SHVK : forall a, SHV a -> CHA.akept L ar LB FF sp 2624 W a).
  { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 2624 V 48 a RFx Vfr ltac:(clear; lia) Ha) as (G1 & G2 & _).
    pose proof (CHA.shadow_range V 48 a Q3 ltac:(clear; lia) Q6 Ha) as SRa.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]]. unfold L5.in_rng; cbn [fst snd]. unfold hid in Q5. clear - SRa Q5 Q3. lia. }
  assert (SZS : shadow_zero M (sp - 2624) 328).
  { intros j Hj. apply HSTKSH. split; [clear - Hj; lia|]. pose proof (Z.le_max_l (ar_sptop ar) (ar_stack_top ar)) as MX.
    assert (Hg : 2624 / 8 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 2624)) / 8) by (apply Z.div_le_mono; clear - MX S3; lia).
    change (2624 / 8) with 328 in Hg. clear - Hj Hg. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ VEndArrA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  change VEndArrA.PC with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL W W G.BLS VEndArrA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact VEndArrA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ VEndArrA.leaf_ok _ _ _ _ _ IL) as X. unfold VEndArrA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL W W G.BLS VEndArrA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    assert (REGV : forall c0 ps0 E' R' (A1 : list (Z * Z)) (M0 M1 : word -> option byte) (m0 m1 : Model) (r0 : nat) e z, CCA.leaf_factsA (hl_segs L) c0 ps0 E' R' A1 M0 m0 M1 m1 -> CL.ps_reg_is ps0 r0 e = true ->
              CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat r0)) = Z_to_bv 64 z).
    { intros c0 ps0 E' R' A1 M0 M1 m0 m1 r0 e z HLF0 Hr Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ r0 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF0) Hr).
      rewrite <- Hz. unfold CL5A.uv. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    destruct (Z.eqb_spec pc VEndArrA.MEMSET) as [->|Hne1].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y5. rename Y5 into Ycsp.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
      refine (CALLEE VEndArrA.MEMSET 2560 0%nat [] VEndArrA.WR_MS VEndArrA.STAT (Some VEndArrA.MSA) 0 0%nat c ps 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !VEndArrA.FFSnil, !VEndArrA.bls_nil; exact Hchk | rewrite !VEndArrA.FFSnil; reflexivity | rewrite VEndArrA.FFSnil; cbn [length]; clear; lia |].
      intros cr1 LK1 CF HH1 HLK1 HC1.
      assert (HcB : CHA.curB LB G.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite VEndArrA.bls_nil; reflexivity).
      assert (HcF : CHA.curF FF sp VEndArrA.FFS 0%nat E = FF) by (unfold CHA.curF; rewrite VEndArrA.FFSnil; reflexivity).
      rewrite HcB, HcF in HH1 |- *. unfold Cred in HC1. subst cr1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & Hdf1).
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      set (dst := sp - 64 + 16).
      assert (UMS : CL5A.uv E' VEndArrA.MSA = dst).
      { unfold CL5A.uv, VEndArrA.MSA, dst. cbn [edenot]. rewrite u_add64, W2. rewrite u_lit64. unfold two64. rewrite Z.add_mod_idemp_r by (clear; lia). rewrite Z.mod_small by (clear - S2 S3 CL SP1; lia). clear; lia. }
      eexists. eexists. split.
      { unfold VEndArrA.MEMSET. rewrite <- (L5A.aly_memset L C LAY). rewrite Ycsp.
        exact (CRC.asan_memset_cps L ar C HI HIok PMSA.fp_ok 2560 LB FF LK1 cr A1 dst 0 24 (sp + -64) (CC.cp_pc cj) ltac:(rewrite (L5A.aly_scr_mem L C LAY); clear; lia)). }
      split.
      { unfold CRC.memset_pre. split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 10%nat _ dst HLF Y10 UMS)|].
        split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 11%nat (ELit 0) 0 HLF Y11 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|].
        split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 12%nat (ELit 24) 24 HLF Y12 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|].
        unfold CRC.mem_dst. split; [clear; lia|].
        split.
        { apply (CRC.aacc_blk M' (sp - 2624) 2624 dst 24); [|clear - S1; apply Z.mod_divide in S1; [|lia]; destruct S1 as [q ->]; replace (q * 16 - 2624) with ((2 * q - 328) * 8) by lia; apply Z.mod_mul; lia | clear - S2 CL; lia | unfold dst; clear; lia | unfold dst; clear; lia].
          split; [|change (2624 mod 8) with 0; intros Hm; exfalso; apply Hm; reflexivity]. change (2624 / 8) with 328. intros jj Hjj. unfold byte_at.
          rewrite (Hfr1 (S (sp - 2624) + jj)); [exact (SZS jj Hjj) | apply SHSK; unfold SHS; clear - Hjj; lia]. }
        split.
        { intros q Hq. right; left. split; [unfold dst; clear - Hq S2 S3 CL SP1; lia|]. intros Hb. unfold dst in Hb. clear - Hq Hb. lia. }
        split.
        { apply (L5C.writable_of_defined (hl_segs L) M' dst 24); [| unfold dst; clear - S2 CL; lia | unfold dst; clear - S3 SP1; lia].
          intros q Hq. apply (Hdf1 (dst + q)); [unfold dst; clear - Hq S2 S3 CL SP1; lia | right; left; split; [unfold dst; clear - Hq S2 S3 CL SP1; lia | clear; lia] |].
          replace (dst + q) with (sp - 2624 + (2624 - 64 + 16 + q)) by (unfold dst; clear; lia). apply S5. clear - Hq. lia. }
        unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. split; [unfold dst; clear - S2 CL; lia|]. split; [right; unfold dst; clear - S2 CL; lia|]. left. unfold dst. clear - S3. lia. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & _ & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      assert (UMS2 : CL5A.uv E2 VEndArrA.MSA = dst).
      { unfold CL5A.uv, VEndArrA.MSA. cbn [edenot]. rewrite <- (proj1 Hag2 2%nat) by (destruct HV as (_ & _ & HV3 & HV4 & _); unfold GT.NF in HV4; clear - HV3 HV4; lia).
        fold (CL5A.uv E' VEndArrA.MSA). exact UMS. }
      split; [rewrite Ha0'; rewrite <- UMS2; unfold CL5A.uv; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      split.
      { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (VEndArrA.MSA, 0, ELit 24). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. fold (CL5A.uv E' VEndArrA.MSA). rewrite UMS. cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
      split.
      { intros w a [<-|[]] Hin (Ka & Kc & Kw). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite SCRV in Kc.
        apply (CHA.client_high L ar LYI GT.NF sp G.HDECL STKF SCRP NF32 LB FF sp 2624 a RFx Kc); unfold dst in Hin; clear - Hin S2 CL; lia. }
      assert (HBj : CHA.curB LB G.BLS 1%nat E2 = LB) by (unfold CHA.curB; rewrite VEndArrA.bls_nil; reflexivity).
      split; [rewrite HBj; exact HH2|]. split; [reflexivity|]. split; [exact I|].
      intros X0 HX0 _. unfold VEndArrA.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }
    destruct (Z.eqb_spec pc VEndArrA.MEMCPY) as [->|Hne2].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y5. rename Y5 into Ycsp.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
      refine (CALLEE VEndArrA.MEMCPY 2560 0%nat [] VEndArrA.WR_MC VEndArrA.STAT (Some VEndArrA.MCD) 0 1%nat c ps 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !VEndArrA.FFSnil, !VEndArrA.bls_nil; exact Hchk | rewrite !VEndArrA.FFSnil; reflexivity | rewrite VEndArrA.FFSnil; cbn [length]; clear; lia |].
      intros cr1 LK1 CF HH1 HLK1 HC1.
      assert (HcB : CHA.curB LB G.BLS 1%nat E = LB) by (unfold CHA.curB; rewrite VEndArrA.bls_nil; reflexivity).
      assert (HcF : CHA.curF FF sp VEndArrA.FFS 1%nat E = FF) by (unfold CHA.curF; rewrite VEndArrA.FFSnil; reflexivity).
      rewrite HcB, HcF in HH1 |- *. unfold Cred in HC1. subst cr1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & Hdf1).
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (W10 : bv_unsigned (ev E' 10) = V) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
      set (src := sp - 64 + 9).
      assert (UMD : CL5A.uv E' VEndArrA.MCD = V + 17).
      { unfold CL5A.uv, VEndArrA.MCD. cbn [edenot]. rewrite u_add64, W10. rewrite u_lit64. unfold two64. rewrite Z.add_mod_idemp_r by (clear; lia). rewrite Z.mod_small by (clear - Q3 Q6; lia). clear; lia. }
      assert (UMS : CL5A.uv E' VEndArrA.MCS = src).
      { unfold CL5A.uv, VEndArrA.MCS, src. cbn [edenot]. rewrite u_add64, W2. rewrite u_lit64. unfold two64. rewrite Z.add_mod_idemp_r by (clear; lia). rewrite Z.mod_small by (clear - S2 S3 CL SP1; lia). clear; lia. }
      destruct HSTK as (T1 & T2 & T3 & T4 & T5 & T6). rewrite Ycsp in T6.
      destruct (rdn_def M' 31 src) as (bs & Hbs).
      { intros q Hq. cbn [Z.of_nat] in Hq. apply (Hdf1 (src + q)); [unfold src; clear - Hq S2 S3 CL SP1; lia | right; left; split; [unfold src; clear - Hq S2 S3 CL SP1; lia | unfold src; clear - Hq; lia] |].
        replace (src + q) with (sp - 2624 + (2624 - 64 + 9 + q)) by (unfold src; clear; lia). apply S5. clear - Hq. lia. }
      eexists. eexists. split.
      { unfold VEndArrA.MEMCPY. rewrite <- (L5A.aly_memcpy L C LAY). rewrite Ycsp.
        exact (CRC.asan_memcpy_cps L ar C HI HIok PMSA.fp_ok 2560 LB FF LK1 cr A1 (V + 17) src 31 bs (sp + -64) (CC.cp_pc cj) ltac:(rewrite (L5A.aly_scr_mem L C LAY); clear; lia)). }
      split.
      { unfold CRC.memcpy_pre. split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 10%nat _ (V + 17) HLF Y10 UMD)|].
        split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 11%nat _ src HLF Y11 UMS)|].
        split; [exact (REGV c ps E' R' A1 M1 M' m1 m' 12%nat (ELit 31) 31 HLF Y12 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|].
        split.
        { unfold CRC.mem_dst. split; [clear; lia|].
          split.
          { apply (CRC.aacc_blk M' V 48 (V + 17) 31); [|exact V8 | exact Q3 | clear; lia | clear; lia].
            split; [|change (48 mod 8) with 0; intros Hm; exfalso; apply Hm; reflexivity]. change (48 / 8) with 6. intros jj Hjj. unfold byte_at.
            rewrite (Hfr1 (S V + jj)); [exact (Vsh jj Hjj) | apply SHVK; unfold SHV; apply (CL5A.shreg_in_shadow V 6); [exact V8 | clear; lia | unfold S, SB; clear - Hjj; lia]]. }
          split; [intros q Hq; exact (CL5A.infr_clientw L ar LB FF _ _ V 48 (V + 17 + q) Vfr ltac:(clear - Hq; lia))|].
          split.
          { apply (L5C.writable_of_defined (hl_segs L) M' (V + 17) 31); [| clear - Q3; lia | clear - Q6; lia].
            intros q Hq. apply (Hdf1 (V + 17 + q)); [clear - Hq Q3 Q6; lia | exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp 0 V 48 (V + 17 + q) Vfr ltac:(clear - Hq; lia))) |].
            replace (V + 17 + q) with (V + (17 + q)) by (clear; lia). apply VDEF. clear - Hq. lia. }
          unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. split; [clear - Q3; lia|]. split; [unfold hid in Q5; clear - Q5; lia|]. left. clear - Q4 S3 SP1 CL. lia. }
        split.
        { unfold CRC.mem_src. split.
          { apply (CRC.aacc_blk M' (sp - 2624) 2624 src 31); [|clear - S1; apply Z.mod_divide in S1; [|lia]; destruct S1 as [q ->]; replace (q * 16 - 2624) with ((2 * q - 328) * 8) by lia; apply Z.mod_mul; lia | clear - S2 CL; lia | unfold src; clear; lia | unfold src; clear; lia].
            split; [|change (2624 mod 8) with 0; intros Hm; exfalso; apply Hm; reflexivity]. change (2624 / 8) with 328. intros jj Hjj. unfold byte_at.
            rewrite (Hfr1 (S (sp - 2624) + jj)); [exact (SZS jj Hjj) | apply SHSK; unfold SHS; clear - Hjj; lia]. }
          split; [unfold src; clear - S2 S3 CL SP1; lia|].
          split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; split; [unfold src; clear - S2 CL; lia|]; split; [right; unfold src; clear - S2 CL; lia|]; left; unfold src; clear - S3; lia|].
          split; [intros q Hq; right; right; left; split; [unfold src; clear - Hq S2 S3 CL SP1; lia | intros Hb; unfold src in Hb; clear - Hq Hb; lia]|].
          exact Hbs. }
        left. unfold src. clear - Q4 S2 CL. lia. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & _ & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      assert (UMD2 : CL5A.uv E2 VEndArrA.MCD = V + 17).
      { unfold CL5A.uv, VEndArrA.MCD. cbn [edenot]. rewrite <- (proj1 Hag2 10%nat) by (destruct HV as (_ & _ & HV3 & HV4 & _); unfold GT.NF in HV4; clear - HV3 HV4; lia).
        fold (CL5A.uv E' VEndArrA.MCD). exact UMD. }
      split; [rewrite Ha0'; rewrite <- UMD2; unfold CL5A.uv; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      split.
      { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (VEndArrA.MCD, 0, ELit 31). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. fold (CL5A.uv E' VEndArrA.MCD). rewrite UMD. cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
      split.
      { intros w a [<-|[]] Hin (Ka & Kc & Kw). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (Kw (V + 8, 40)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Hin; lia]. }
      assert (HBj : CHA.curB LB G.BLS 2%nat E2 = LB) by (unfold CHA.curB; rewrite VEndArrA.bls_nil; reflexivity).
      split; [rewrite HBj; exact HH2|]. split; [reflexivity|]. split; [exact I|].
      intros X0 HX0 _. unfold VEndArrA.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }

    apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Ya0]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Yi]. apply andb_prop in X as [Xbase Xfoot].
    apply Nat.eqb_eq in Yi. subst i. apply CC.has_cell_In in Y8.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL W W G.BLS VEndArrA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              K DEF0 R r EV Hra Hraok VEndArrA.RETPC 2%nat c ps _ Xbase _ (VEndArrA.FFSnil 2%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact VEndArrA.ret_at | rewrite VEndArrA.FFSnil; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    unfold Cred in HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS 2%nat E = LB) by (unfold CHA.curB; rewrite VEndArrA.bls_nil; reflexivity).
    rewrite HB in HH1.
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL W G.BLS VEndArrA.FFS Cred 0 2%nat E A1 M' m' HA') as Hoff.
    assert (W10 : bv_unsigned (ev E' 10) = V) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
    pose proof HP as (_ & _ & HP3).
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB W LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split.
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Ya0). reflexivity. }
    split; [|repeat split; reflexivity].
    unfold PMCUR.ev_at. split.
    { intros j Hj. apply (HP3 (V + 8 + j)); [clear - Hj Q3 Q6; lia | |].
      - exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp 2624 V 48 (V + 8 + j) Vfr ltac:(clear - Hj; lia))).
      - replace (V + 8 + j) with (V + (8 + j)) by (clear; lia). apply VDEF. clear - Hj; lia. }
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (V + 8) (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ Y8) ltac:(ev_start)) as G0.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite u64_of_Z in G0 by (clear; lia). exact G0.
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VV : CL5A.visr (ahid A model) V 48).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 V 48 (V + k) RFx Vfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSV : forall a, in_shadow_of V 48 a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 V 48 a RFx Vfr ltac:(clear; lia) Ha) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 2624) 2624).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 2624) 2624) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DV : L5.defined Mv (V + 8) 40) by (apply (CL5A.defined_vis _ M _ _ (CL5A.visr_sub _ V 48 (V + 8) 40 VV ltac:(clear; lia) ltac:(clear; lia))); intros j Hj; replace (V + 8 + j) with (V + (8 + j)) by (clear; lia); apply VDEF; clear - Hj; lia).
    assert (UVV : CL5A.uv E0 (EVar 10) = V) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kunk_intro with (A := V + 8) (N := 40); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DV].
    + eapply CL5.kwr_intro with (A := V + 8) (N := 40); [ev_start | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DV].
    + eapply CL5.krange_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := V); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact V8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 6 V UVV); [clear; lia | clear - Q3 Q6; lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VSV; apply (CL5A.shreg_in_shadow V 6); [exact V8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Vsh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := V) (N2 := 48); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in Q5; clear - Q5; lia].
    + eapply CL5.kunk_intro with (A := sp - 2624) (N := 2624); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 2624) (N := 2624); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 2624) (N1 := 2624) (A2 := V) (N2 := 48); [ev_start | reflexivity | ev_start | reflexivity | clear - Q4 S2; lia].
  -
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite VEndArrA.bls_nil, VEndArrA.FFSnil. cbn [app CH2.den CHA.denF map length].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.
End VisitEndArrOk.

