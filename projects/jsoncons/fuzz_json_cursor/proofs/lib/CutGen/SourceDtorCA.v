(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA HeapIfaceANull L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_sdtor_casan_T Cut_sdtor_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_sdtor_casan.
Module GT := Cut_sdtor_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module SDA.
Definition PC_OPDEL : Z := 975272.
Definition PC_FREE : Z := 526836.
Definition SBz : Z := 2147450880.
Definition RE := EVar 10. Definition chE := EVar 32.
Definition BLK0 : list (expr * expr) := [(chE, ELit 16384)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              if Z.eqb pc PC_OPDEL then
                (Z.eqb (SR.ps_pc ps) PC_OPDEL && Nat.eqb i 0 && Nat.eqb j 1 && CH2.blocks_eqb (nth i G.BLS []) BLK0 && CH2.blocks_eqb (nth j G.BLS []) []
                 && CHA.foot_chk GT.NF G.HDECL c BLK0 []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] [] STAT None c ps cj BLK0 [] [] [])
                 && CL.ps_reg_is ps 10 chE)%bool
              else if Z.eqb pc PC_FREE then
                (Z.eqb (SR.ps_pc ps) PC_FREE && Nat.leb 1 i && Nat.leb i 3 && Nat.eqb j (i + 1) && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                 && CHA.foot_chk GT.NF G.HDECL c [] []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] [] STAT None c ps cj [] [] [] [])
                 && CL.ps_reg_is ps 10 (ELit 0))%bool
              else false
          | None => false
          end
      | None =>
          (Z.eqb pc PC_FREE && CRB.tail_base_chk GT.NF PC_FREE c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && Nat.eqb i 4 && CH2.blocks_eqb (nth i G.BLS []) []
           && CL.ps_reg_is ps 10 (ELit 0))%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
End SDA.

Section SourceDtorOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI SDA.PC_OPDEL.
Hypothesis FN : HeapIfaceANull.afree_null_spec L ar SCFG HI.

Lemma FFSnil : forall i, nth i SDA.FFS [] = [].
Proof. intros i. unfold SDA.FFS. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem source_dtor_ok : PMSA.source_dtor_specA L ar HI IC 726828.
Proof.
  intros LB FF LK cr A Rr ch sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & HSRC & HinLB & RO & (Rfr & R8 & Rsh) & Hstksh) Hcont.
  unfold PMSA.a0, PMSA.SDTOR_SCR, PMSA.MALLOC_SCR, PMSA.fobj, PMSA.stksh, PMLA.stksh in *. change (128 + 4096) with 4224 in *.
  destruct HSRC as (S264 & S272 & (st0 & (I32 & I36 & I40 & I48 & IZ & IDEF)) & S32 & SDEF).
  change (PMLA.CLASSIC_IMP IC) with 6879376 in *.
  replace (Rr + 88 + 48) with (Rr + 136) in I48 by (clear; lia).
  assert (IZK : forall k off, 0 <= k < 10 -> off = 144 + 8 * k -> L5.u64_at (hl_segs L) M (Rr + off) 0).
  { intros k off Hk ->. replace (Rr + (144 + 8 * k)) with (Rr + 88 + 56 + 8 * k) by (clear; lia). exact (IZ k Hk). }

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (ch, 16384) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ FF Rr 592 RFx Rfr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (Rr + 592 <= 2147446784 \/ 17594333495296 <= Rr)) in O5. change (hid (Rr + 592 <= hl_img_lo L \/ hl_img_hi L <= Rr)) in O7.
  change (hid (ch + 16384 <= 2147446784 \/ 17594333495296 <= ch)) in B6. change (hid (ch + 16384 <= hl_img_lo L \/ hl_img_hi L <= ch)) in B1.
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  destruct Rfr as (f0 & Hf0 & F01 & F02).
  assert (Rfr : CL5A.ainfr FF Rr 592) by (exists f0; split; [exact Hf0 | split; [exact F01 | exact F02]]).
  pose proof (Bfap f0 (in_or_app _ _ _ (or_introl Hf0))) as BFP. change (hid (ch + 16384 <= ff_addr f0 \/ ff_addr f0 + ff_bytes (ff_class f0) <= ch)) in BFP.
  assert (RDEF : L5.defined M Rr 592).
  { destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f0 Hf0) as (_ & _ & _ & _ & Fdef & _). intros k Hk. replace (Rr + k) with (ff_addr f0 + (Rr - ff_addr f0 + k)) by (clear; lia). apply Fdef. clear - Hk F01 F02. lia. }
  assert (RFr : CHA.rng_facts L ar (lb_remove ch LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove ch y LB Hy) | apply incl_refl]. }

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [ch] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 Rr) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 ch) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = Rr) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = ch) by (rewrite V32; apply u64_of_Z; clear - B5 B7; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4224) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(Rr, 592)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove ch LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove ch LB) FF sp _ Rr 592 a RFr Rfr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (Rr, 592). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove ch LB) FF sp G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. unfold CHA.sclientA.
    cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow Rr 74 a R8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 74) with 592 in SH.
    destruct (CL5A.infr_sh_wok L ar (lb_remove ch LB) FF sp (CH.hd_scr G.HDECL) Rr 592 a RFr Rfr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ SDA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (DEN0 : forall E, env_agree GT.NF E0 E -> CH2.den E SDA.BLK0 = [(ch, 16384)]).
  { intros E HagE. unfold CH2.den, SDA.BLK0, SDA.chE. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 32%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, u64_of_Z by (clear; lia). reflexivity. }
  rewrite <- LS in FPM.
  change 726828 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS SDA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SDA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SDA.leaf_ok _ _ _ _ _ HIL) as X. unfold SDA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS SDA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      destruct (Z.eqb_spec pc SDA.PC_OPDEL) as [->|Hne1].
      {
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4.
        lazymatch type of Y5 with SDA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB (lb_remove ch LB) G.BLS 0 E = (ch, 16384) :: lb_remove ch LB) by (unfold CHA.curB; rewrite Y3, (DEN0 E HagE); reflexivity).
        assert (HcF : CHA.curF FF sp SDA.FFS 0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE SDA.PC_OPDEL 4096 0%nat [] [] SDA.STAT None 0 0%nat c ps0 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        unfold SDA.chE in *.
        eexists. eexists. split; [exact (OPDEL_OK ((ch, 16384) :: lb_remove ch LB) FF LK1 cr A1 ch 16384 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0. split; [|left; reflexivity].
          replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
          rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Y10). cbn [edenot]. rewrite (FZ 32%nat eq_refl). exact V32. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          assert (RM : lb_remove ch ((ch, 16384) :: lb_remove ch LB) = lb_remove ch LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
          rewrite RM in HP, HH2 |- *.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
          split; [unfold CHA.curB; rewrite Y4; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|]. split; [exact I|].
          intros X0 HX0 _. unfold SDA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
      destruct (Z.eqb_spec pc SDA.PC_FREE) as [->|Hne2]; [|discriminate X].
      {
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1']. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y2. subst j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.leb_le in Y1, Y1'.
        lazymatch type of Y5 with SDA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB (lb_remove ch LB) G.BLS i E = lb_remove ch LB) by (unfold CHA.curB; rewrite Y3; reflexivity).
        assert (HcF : CHA.curF FF sp SDA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE SDA.PC_FREE 4096 0%nat [] [] SDA.STAT None 0 i c ps0 (i + 1)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        eexists. eexists. split.
        { unfold SDA.PC_FREE. rewrite <- (L5A.aly_free L C LAY). apply (CRC.free_null_cps L ar HI PMSA.fp_ok FN 4096 (lb_remove ch LB) FF LK1 cr A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj)).
          rewrite (L5A.aly_scr_free L C LAY). clear; lia. }
        split.
        { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
          rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Y10). reflexivity. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
          split; [unfold CHA.curB; rewrite Y4; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|]. split; [exact I|].
          intros X0 HX0 _. unfold SDA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
    +
      apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Y0 Y1].
      apply Z.eqb_eq in Y0. subst pc. apply Nat.eqb_eq in Y2. subst i. apply CH2.blocks_eqb_eq in Y3.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      refine (CRB.tail_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS SDA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs WRS_OK
                K PMSA.fp_ok DEF0 S6 HKnil R r EV Hra Hraok SDA.PC_FREE 4096 0 4%nat c ps0 Y1 _ (FFSnil 4%nat) _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HA HFP Hag HLF _);
        [rewrite FFSnil, Y3; exact YF | rewrite SCRV; clear; lia | clear; lia |].
      intros cr1 LK1 HRP HP HH1 HLK1 HC1 HagE' HA'. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB (lb_remove ch LB) G.BLS 4 E = lb_remove ch LB) by (unfold CHA.curB; rewrite Y3; reflexivity). rewrite HB in *.
      eexists. eexists. split.
      { unfold SDA.PC_FREE. rewrite <- (L5A.aly_free L C LAY). apply (CRC.free_null_cps L ar HI PMSA.fp_ok FN 4096 (lb_remove ch LB) FF LK1 cr A1 sp r).
        rewrite (L5A.aly_scr_free L C LAY). clear; lia. }
      split.
      { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
        rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10). reflexivity. }
      intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 (-> & -> & -> & ->) HRP2 HP2 Hrt2 HA2 Hmo2 HLK2 HH2.
      apply (Hcont fx2 R2 M2 model2 (lb_remove ch LB) cr (lb_remove ch LB) WW LK2 A2 HFP2); [repeat split; reflexivity | exact HRP2 | | exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
      rewrite SCRV in HP.
      apply (CRB.ahpres_trans L ar (lb_remove ch LB) (lb_remove ch LB) (lb_remove ch LB) FF sp 4224 4096 WW WW [] M M' M2 HP HP2 (incl_refl _) (incl_refl _));
        [clear; lia | clear - S3 SP1; lia | clear - CL; lia | clear - S2; lia | intros w a Hw Hin; exists w; split; assumption | intros w a []].
  - reflexivity.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) Rr 592).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 Rr 592 (Rr + k) RFx Rfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 74 -> ahid A model (Z_to_bv 64 (S Rr + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 Rr 592 (S Rr + j) RFx Rfr ltac:(clear; lia) (CL5A.shreg_in_shadow Rr 74 (S Rr + j) R8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4224) 4224).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv Rr 592) by (apply (CL5A.defined_vis _ M Rr 592 VO); exact RDEF).
    assert (DS : L5.defined Mv (sp - 4224) 4224) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (U64V : forall k v, 0 <= k -> k + 8 <= 592 -> L5.u64_at (hl_segs L) M (Rr + k) v -> L5.u64_at (hl_segs L) Mv (Rr + k) v).
    { intros k v K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ Rr 592 (Rr + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := Rr + 32) (z := 6879376); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 32 _ ltac:(clear; lia) ltac:(clear; lia) S32)].
    + eapply CL5.kword64_intro with (A := Rr + 264) (z := ch); [ev0 | clear - O3; lia | clear - O6; lia | exact V32 | exact (U64V 264 _ ltac:(clear; lia) ltac:(clear; lia) S264)].
    + eapply CL5.kword64_intro with (A := Rr + 272) (z := 16384); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 272 _ ltac:(clear; lia) ltac:(clear; lia) S272)].
    + eapply CL5.kword64_intro with (A := Rr + 136) (z := 6879376); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 136 _ ltac:(clear; lia) ltac:(clear; lia) I48)].
    + eapply CL5.kword64_intro with (A := Rr + 144) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 144 _ ltac:(clear; lia) ltac:(clear; lia) (IZK 0 144 ltac:(clear; lia) eq_refl))].
    + eapply CL5.kword64_intro with (A := Rr + 152) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 152 _ ltac:(clear; lia) ltac:(clear; lia) (IZK 1 152 ltac:(clear; lia) eq_refl))].
    + eapply CL5.kword64_intro with (A := Rr + 160) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 160 _ ltac:(clear; lia) ltac:(clear; lia) (IZK 2 160 ltac:(clear; lia) eq_refl))].
    + eapply CL5.kword64_intro with (A := Rr + 176) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 176 _ ltac:(clear; lia) ltac:(clear; lia) (IZK 4 176 ltac:(clear; lia) eq_refl))].
    + eapply CL5.kword64_intro with (A := Rr + 200) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 200 _ ltac:(clear; lia) ltac:(clear; lia) (IZK 7 200 ltac:(clear; lia) eq_refl))].
    + eapply CL5.kunk_intro with (A := Rr) (N := 32); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros k Hk; apply DO; clear - Hk; lia].
    + eapply CL5.kunk_intro with (A := Rr + 88) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros k Hk; replace (Rr + 88 + k) with (Rr + (88 + k)) by (clear; lia); apply DO; clear - Hk; lia].
    + eapply CL5.kwr_intro with (A := Rr) (N := 592); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := Rr); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := Rr); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact R8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 74 Rr); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Rsh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := Rr) (N2 := 592); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - B5 B7; lia | clear - B0 B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - B5 B7; lia | clear; lia | exact B16].
    + eapply CL5.kunk_intro with (A := sp - 4224) (N := 4224); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4224) (N := 4224); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4224) (N1 := 4224) (A2 := Rr) (N2 := 592); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4224) (N1 := 4224) (A2 := ch) (N2 := 16384); [ev0 | reflexivity | ev0 | reflexivity | clear - B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := Rr) (N1 := 592) (A2 := ch) (N2 := 16384); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in BFP; clear - BFP F01 F02; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := ch) (N2 := 16384); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in B6; clear - B6; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with SDA.BLK0. rewrite (DEN0 E0 (CC.env_agree_refl _ _)), FFSnil. cbn [app CHA.denF map length].
      split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ ch 16384 HH HinLB)|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + exact I.
  - exact Hfp.
Qed.

End SourceDtorOk.
