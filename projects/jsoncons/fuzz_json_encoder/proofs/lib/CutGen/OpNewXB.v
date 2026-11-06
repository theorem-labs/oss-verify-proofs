(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_opnew_xboth_T Cut_opnew_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_opnew_xboth.
Module GT := Cut_opnew_xboth_T.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

Module ONA.
Definition PC_MALLOC : Z := 534164.   (* [comment removed for export] *)
Definition RETPC : Z := 1429300.      (* [comment removed for export] *)
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition kind (j : nat) : Z :=
  match find (fun r : nat * nat * nat * Z => Nat.eqb (fst (fst (fst r))) j) G.RETS with Some (_, _, _, pc) => pc | None => 0 end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition news_of (ci_nx : nat) (cj : CC.cutpoint) : list kentry :=
  List.filter (fun X => negb (APC.kentry_vars_lt (ci_nx + 4) X)) (CC.cp_know cj).
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_MALLOC then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj =>
                        let nx := (CC.cp_nx cj - APC.NCS)%nat in
                        let news := news_of nx cj in
                        (Z.eqb (SR.ps_pc ps) PC_MALLOC && Z.eqb (kind i) 0 && Z.eqb (kind j) PC_MALLOC
                         && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) [(EVar (nx + 4), EVar 10)]
                         && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] [] news None c ps cj (nth i G.BLS []) [] (nth j G.BLS []) [])
                         && CRB.fresh_news_ok 65536 7094272 G.HDECL GT.SCELLS GT.GLO GT.GHI (SR.ps_cells ps) nx [] [] (nx + 4) (EVar 10) news
                         && CL.ps_reg_is ps 10 (EVar 10))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] && Z.eqb (kind i) PC_MALLOC
         && CH2.blocks_eqb (nth i G.BLS []) [(EVar (CC.cp_nx c - APC.NCS + 4), EVar 10)] && Nat.ltb (CC.cp_nx c - APC.NCS + 4) (CC.cp_nx c) && Nat.leb (GT.NF + APC.NCS) (CC.cp_nx c)
         && CL.ps_reg_is ps 10 (EVar (CC.cp_nx c - APC.NCS + 4))
         && CC.has_cell (SR.ps_cells ps) (KUnk (SA (EVar (CC.cp_nx c - APC.NCS + 4)) 0) (EVar 10)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End ONA.

Section OpNewOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Lemma FFSnil : forall i, nth i ONA.FFS [] = [].
Proof. intros i. unfold ONA.FFS. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.

Theorem opnew_ok : PMSA.opnew_specA L ar HI 1429232.
Proof.
  intros LB FF LK cr A n sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hn & Hcred) Hcont.
  unfold PMSA.a0, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : hl_img_lo L <= 65536 /\ 7094272 <= hl_img_hi L) by (rewrite ILO, IHI; lia).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 n) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = n) by (rewrite V10; apply u64_of_Z; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 4112) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)) by (intros rg []).
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a) by (intros rg a []).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [] | constructor]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. lia. }
  (* [comment removed for export] *)
  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if Z.eqb (ONA.kind i) ONA.PC_MALLOC then cr1 = adebit L cr n else cr1 = cr).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M' : word -> option byte) (_ : Model) =>
               if Z.eqb (ONA.kind i) ONA.PC_MALLOC then
                 match nth i G.BLS [] with (be, _) :: _ => PMLA.afresh L ar LB FF M' (CL5A.uv E be) n | [] => False end
               else True).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ ONA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  change 1429232 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL [] [] G.BLS ONA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact ONA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - (* [comment removed for export] *)
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ ONA.leaf_ok _ _ _ _ _ IL) as X. unfold ONA.leaf_chk in X.
    destruct (Z.eqb_spec pc ONA.PC_MALLOC) as [->|Hne1].
    { (* [comment removed for export] *)
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      cbv zeta in X. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := ONA.news_of nx cj) in *.
      apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0, Y1, Y2. apply CH2.blocks_eqb_eq in Y3, Y4.
      lazymatch type of Y5 with ONA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
      assert (HcB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity).
      assert (HcF : CHA.curF FF sp ONA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
      refine (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL [] [] G.BLS ONA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil
                ONA.PC_MALLOC 4096 0%nat [] [] news None 0 i c ps j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Y1 in HC1; exact HC1). subst cr1.
      assert (W10 : bv_unsigned (ev E' 10) = n) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
      assert (NXeq : CH2.ci_nx ci = nx) by (destruct HV as (_ & _ & _ & _ & HV5); unfold nx; rewrite HV5; unfold APC.NCS; clear; lia).
      eexists. eexists. split.
      { unfold ONA.PC_MALLOC. rewrite <- (L5A.aly_malloc L C LAY). apply (CRC.malloc_cps L ar C HI HIok PMSA.fp_ok 4096 LB FF LK1 cr A1 n (sp + CH2.ci_csp ci) (CC.cp_pc cj)).
        rewrite (L5A.aly_scr_malloc L C LAY). clear; lia. }
      split.
      { (* [comment removed for export] *)
        split; [|split; [exact Hn | exact Hcred]].
        replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
        rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7). cbn [edenot].
        rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity). exact V10. }
      { (* [comment removed for export] *)
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hrng & Hbap & Hfap & Hdef & Hsh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (destruct Hrng as (Q0 & _ & _ & Q3 & Q4 & _); clear - Q0 Q3 Q4 CL SP1; lia).
        assert (Hvu : CL5A.uv E2 (EVar (nx + 4)) = u).
        { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite <- NXeq, G0, Hu. apply u64_of_Z. exact UR. }
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        assert (V10' : bv_unsigned (ev E2 10) = n) by (rewrite <- (proj1 HagE2 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
        assert (FA : fframes_apart u n FF) by (intros f Hf; apply Hfap; apply in_or_app; left; exact Hf).
        split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS j E2 = (u, n) :: LB).
        { unfold CHA.curB. rewrite Y4. unfold CH2.den. cbn [map fst snd app]. unfold CL5A.uv in Hvu. rewrite Hvu. cbn [edenot]. rewrite V10'. reflexivity. }
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; rewrite Y2, Z.eqb_refl; reflexivity|]. split.
        { unfold XI. rewrite Y2, Z.eqb_refl, Y4. rewrite Hvu. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact FA|]. split; [exact Hdef | exact Hsh]. }
        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7094272 LYH GT.NF E0 LB FF sp G.HDECL [] STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps) [] [] (nx + 4)%nat (EVar 10) M' M2 A1 A2 m' m2 LB ((u, n) :: LB) FF FF LK1 LK2 cr (adebit L cr n) u n news
                  HagE' Hag2 HK HH1 eq_refl eq_refl Hvu _ _ Hrng Hbap FA Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0).
        - cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. destruct HV as (_ & _ & HV3 & HV4 & _). unfold GT.NF in HV4. clear - HV3 HV4. lia.
        - unfold elenZ. cbn [edenot]. exact W10.
        - rewrite NXeq. exact Y6. } }
    (* [comment removed for export] *)
    apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2].
    apply andb_prop in X as [Xbase Xfoot]. apply Z.eqb_eq in Y2. apply CH2.blocks_eqb_eq in Y3. apply Nat.ltb_lt in Y4. apply Nat.leb_le in Y5.
    set (a0v := (CC.cp_nx c - APC.NCS + 4)%nat) in *.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
    assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL [] [] G.BLS ONA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              K DEF0 R r EV Hra Hraok ONA.RETPC i c ps _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact ONA.ret_at | rewrite FFSnil; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = adebit L cr n) by (unfold Cred in HC1; rewrite Y2, Z.eqb_refl in HC1; exact HC1). subst cr1.
    assert (HXi' : PMLA.afresh L ar LB FF M1 (CL5A.uv E (EVar a0v)) n) by (unfold XI in HXi; rewrite Y2, Z.eqb_refl, Y3 in HXi; exact HXi).
    set (u := CL5A.uv E (EVar a0v)) in *. destruct HXi' as (Hrng & Hbap & Hfap & Hdef & Hsh).
    assert (Hu' : CL5A.uv E' (EVar a0v) = u) by (unfold u, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag a0v Y4); reflexivity).
    assert (W10 : bv_unsigned (ev E' 10) = n) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
    assert (HB : CHA.curB LB G.BLS i E = (u, n) :: LB).
    { unfold CHA.curB. rewrite Y3. unfold CH2.den. cbn [map fst snd app edenot]. rewrite <- (proj1 HagE 10%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U10. reflexivity. }
    rewrite HB in HH1.
    pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL [] G.BLS ONA.FFS Cred 0 i E A1 M' m' HA') as Hoff.
    pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
    apply (Hcont fx' R' M' model2 ((u, n) :: LB) (adebit L cr n) LB [] LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    exists u. split.
    { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y6). unfold CL5A.uv in Hu'. rewrite <- Hu'. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    split; [|repeat split; reflexivity].
    split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split.
    + (* [comment removed for export] *)
      apply CC.has_cell_In in Y7. pose proof (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ Y7) as KU. cbn [kentry_ok] in KU. destruct KU as [_ KU].
      unfold estart, elenZ in KU. cbn [a_base a_off edenot] in KU. unfold CL5A.uv in Hu'. cbn [edenot] in Hu'. rewrite Hu', W10, Z.add_0_r in KU.
      exact (CL5A.defined_full _ _ _ _ KU).
    + (* [comment removed for export] *)
      assert (FRS : forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. pose proof (CHA.shadow_range u n a ltac:(clear - Q0; lia) Q3 Q7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL [] [] G.BLS ONA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                  i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil; exact Xfoot|].
        rewrite FFSnil, Y3. intros [X|[X|[X|[X|X]]]].
        * rewrite SCRV in X. clear - X SRa S2 CL. lia.
        * destruct X as (w & [] & _).
        * destruct X as (bb & [<-|[]] & Hin). cbn [CH2.den map fst snd] in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
          fold (CL5A.uv E (EVar a0v)) in Hin. fold u in Hin. cbn [edenot] in Hin. rewrite <- (proj1 HagE 10%nat) in Hin by (apply Nat.ltb_lt; reflexivity). rewrite U10 in Hin. clear - Hin SRa Q5 Q6. lia.
        * destruct X as (f & [] & _).
        * destruct X as (f & [] & _). }
      destruct Hsh as [Z0 P0]. split.
      * intros jj Hj. unfold byte_at. rewrite FRS; [exact (Z0 jj Hj)|]. apply (CL5A.blk_shadow_in u n); [exact (CHA.mod8_of_16 _ Q16) | exact Q3 |].
        assert ((n + 7) / 8 >= n / 8) by (apply Z.le_ge, Z.div_le_mono; lia). unfold S. clear - Hj H. lia.
      * intros NZ. unfold byte_at. rewrite FRS; [exact (P0 NZ)|]. apply (CL5A.blk_shadow_in u n); [exact (CHA.mod8_of_16 _ Q16) | exact Q3 |].
        assert (n / 8 < (n + 7) / 8).
        { pose proof (Z_div_mod_eq_full n 8) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rm. apply Z.div_lt_upper_bound; [lia|].
          pose proof (Z.mul_div_le (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z_div_mod_eq_full (n + 7) 8). lia. }
        pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). unfold S. lia.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (VS : CL5A.visr (ahid A model) (sp - 4112) 4112).
    { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 _ HH); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    assert (DS : L5.defined (CCA.vis A model M) (sp - 4112) 4112) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.krange_intro with (v := n); [lin_eval; rw_atoms; clear; lia | clear - Hn; lia | clear - Hn; lia].
    + eapply CL5.kunk_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
  - (* [comment removed for export] *)
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. cbn [nth G.BLS Cut_opnew_xboth_T.BL0 CH2.den map app]. rewrite FFSnil. cbn [app CHA.denF map length].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.
Print Assumptions opnew_ok.
End OpNewOk.
