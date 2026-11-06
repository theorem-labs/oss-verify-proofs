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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_opdel_plain_cboth_T Cut_opdel_plain_cboth Cut_opdel_sized_cboth_T Cut_opdel_sized_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module ODA.
Definition PC_FREE : Z := 527796.
Definition good (NF : nat) (HDECL : CH.hdecl) (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (BLS : list CA.blocks) : bool :=
  (CH2.leaves_all CPS TAGS (fun i c k ps t => match t with
      | CC.TOther pc => (Z.eqb pc PC_FREE && CRB.tail_base_chk NF PC_FREE c ps && CHA.foot_chk NF HDECL c (nth i BLS []) [] && CL.ps_reg_is ps 10 (EVar 10))%bool
      | _ => false end)
   && CHA.heap_chkA NF HDECL BLS (map (fun _ => []) CPS) CPS TAGS && CH2.blocks_eqb (nth 0 BLS []) [(EVar 10, EVar 32)] && Nat.eqb NF 33 && Z.eqb (CH.hd_scr HDECL) 4096
   && match CH.hd_crs HDECL, CH.hd_wrs HDECL, CH.hd_img HDECL with [], [], [] => true | _, _, _ => false end
   && match CPS with [c] => (CA.regs_eqb (CC.cp_regs c) sr_id && APC.kentry_eqb (nth 0 (CC.cp_know c) (KImg 0 0)) (KUnk (SA (EVar 2) (-4096)) (ELit 4096))
                            && APC.kentry_eqb (nth 1 (CC.cp_know c) (KImg 0 0)) (KWr (SA (EVar 2) (-4096)) (ELit 4096))
                            && APC.kentry_eqb (nth 2 (CC.cp_know c) (KImg 0 0)) (KRange (EVar 2) 140735332487168 140737488355328)
                            && APC.kentry_eqb (nth 3 (CC.cp_know c) (KImg 0 0)) (KAlign (EVar 2) 16) && Nat.eqb (length (CC.cp_know c)) 4)%bool | _ => false end)%bool.
Lemma goodP : good Cut_opdel_plain_cboth_T.NF Cut_opdel_plain_cboth.HDECL Cut_opdel_plain_cboth.CPS Cut_opdel_plain_cboth.TAGS Cut_opdel_plain_cboth.BLS = true.
Proof. vmc_refl. Qed.
Lemma goodS : good Cut_opdel_sized_cboth_T.NF Cut_opdel_sized_cboth.HDECL Cut_opdel_sized_cboth.CPS Cut_opdel_sized_cboth.TAGS Cut_opdel_sized_cboth.BLS = true.
Proof. vmc_refl. Qed.
End ODA.

Section OpDelOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Lemma opdel_ok_at : forall (NF : nat) (HDECL : CH.hdecl) (c0 : CC.cutpoint) (TAGS : list (list CC.tag)) (BLS : list CA.blocks),
  (forall i c, nth_error [c0] i = Some c -> CC.plan_sound RSEGS c) -> CC.tags_chk [c0] TAGS NF = true -> ODA.good NF HDECL [c0] TAGS BLS = true ->
  PMSA.opdel_specA L ar HI (CC.cp_pc c0).
Proof.
  intros NF HDECL c0 TAGS BLS Hplans Htags Hgood.
  unfold ODA.good in Hgood. apply andb_prop in Hgood as [Hgood G7]. apply andb_prop in Hgood as [Hgood G6]. apply andb_prop in Hgood as [Hgood G5]. apply andb_prop in Hgood as [Hgood G4].
  apply andb_prop in Hgood as [Hgood G3]. apply andb_prop in Hgood as [G1 G2]. apply CH2.blocks_eqb_eq in G3. apply Nat.eqb_eq in G4. apply Z.eqb_eq in G5. subst NF.
  destruct (CH.hd_crs HDECL) as [|] eqn:HCRS; [|discriminate]. destruct (CH.hd_wrs HDECL) as [|] eqn:HWRS; [|discriminate]. destruct (CH.hd_img HDECL) as [|] eqn:HIMG; [|discriminate]. clear G6.
  apply andb_prop in G7 as [G7 K5]. apply andb_prop in G7 as [G7 K4]. apply andb_prop in G7 as [G7 K3]. apply andb_prop in G7 as [G7 K2]. apply andb_prop in G7 as [K0 K1].
  apply CH2.regs_eqb_eq in K0. apply APS.kentry_eqb_eq in K1, K2, K3, K4. apply Nat.eqb_eq in K5.
  assert (KNOW : CC.cp_know c0 = [KUnk (SA (EVar 2) (-4096)) (ELit 4096); KWr (SA (EVar 2) (-4096)) (ELit 4096); KRange (EVar 2) 140735332487168 140737488355328; KAlign (EVar 2) 16]).
  { destruct (CC.cp_know c0) as [|x0 [|x1 [|x2 [|x3 [|x4 l]]]]]; cbn [length] in K5; try discriminate K5. cbn [nth] in K1, K2, K3, K4. subst. reflexivity. }
  set (FFS := map (fun _ : CC.cutpoint => @nil (expr * Z * Z)) [c0]) in *.
  assert (FFSnil : forall i, nth i FFS [] = []) by (intros [|[|i]]; reflexivity).
  intros LB FF LK cr A q n sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & HinLB) Hcont.
  unfold PMSA.a0, PMSA.OPDEL_SCR, PMSA.MALLOC_SCR in *.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (q, n) HinLB) as ((B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)) & _). cbn [fst snd] in *.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [n] 0))) (fun id => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 q) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = q) by (rewrite V10; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = n) by (change (ev E0 32) with (Z_to_bv 64 n); apply u64_of_Z; lia).
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite G5; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr HDECL) by (rewrite G5; lia).
  assert (NF32 : (32 <= 33)%nat) by lia.
  assert (WOK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove q LB) FF sp (CH.hd_scr HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HDECL) -> SGP.region_vars_lt 33 rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (rewrite HWRS; intros rg []).
  assert (DEF0 : L5.defined M (sp - CH.hd_scr HDECL) (CH.hd_scr HDECL)) by (rewrite G5; exact S5).
  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M' : word -> option byte) (_ : Model) => True).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf [c0] TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ G1 _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN 33 E0 M model A (lb_remove q LB) FF LK sp HDECL [] [] BLS FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            [c0] K PMSA.fp_ok XI TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact Hplans.
  - exact Htags.
  - exact G2.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ G1 _ _ _ _ _ IL) as X. cbv beta iota in X.
    apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0. subst pc.
    assert (Hi0 : i = 0%nat) by (destruct IL as (tg & IL1 & _); destruct i as [|[|i]]; [reflexivity | discriminate IL1 | discriminate IL1]). subst i.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
    assert (HagE : env_agree 33 E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    refine (CRB.tail_leaf L ar C HI HIok LYI LYR 33 E0 M model A (lb_remove q LB) FF LK sp HDECL [] [] BLS FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs WRS_OK
              K PMSA.fp_ok DEF0 S6 HKnil R r EV Hra Hraok ODA.PC_FREE 4096 0 0%nat c ps Y1 _ (FFSnil 0%nat) _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HA HFP Hag HLF _);
      [rewrite FFSnil; exact Y2 | rewrite G5; clear; lia | clear; lia |].
    intros cr1 LK1 HRP HP HH1 HLK1 HC1 HagE' HA'. unfold Cred in HC1. subst cr1.
    assert (HB : CHA.curB (lb_remove q LB) BLS 0 E = (q, n) :: lb_remove q LB).
    { unfold CHA.curB. rewrite G3. unfold CH2.den. cbn [map fst snd app edenot]. rewrite <- (proj1 HagE 10%nat), <- (proj1 HagE 32%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U10, U32. reflexivity. }
    rewrite HB in *.
    eexists. eexists. split.
    { unfold ODA.PC_FREE. rewrite <- (L5A.aly_free L C LAY). apply (CRC.free_cps L ar C HI HIok PMSA.fp_ok 4096 ((q, n) :: lb_remove q LB) FF LK1 cr A1 q n sp r).
      rewrite (L5A.aly_scr_free L C LAY). clear; lia. }
    split.
    { split; [|left; reflexivity].
      replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y3). cbn [edenot].
      rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity). exact V10. }
    intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 (-> & -> & -> & ->) HRP2 HP2 Hrt2 HA2 Hmo2 HLK2 HH2.
    assert (RM : lb_remove q ((q, n) :: lb_remove q LB) = lb_remove q LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    rewrite RM in *.
    apply (Hcont fx2 R2 M2 model2 (lb_remove q LB) cr (lb_remove q LB) [] LK2 A2 HFP2); [repeat split; reflexivity | exact HRP2 | | exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
    rewrite G5 in HP.
    apply (CRB.ahpres_trans L ar (lb_remove q LB) (lb_remove q LB) (lb_remove q LB) FF sp 4096 4096 [] [] [] M M' M2 HP HP2 (incl_refl _) (incl_refl _));
      [clear; lia | clear - S3 SP1; lia | clear - CL; lia | clear - S2; lia | intros w a [] | intros w a []].
  - reflexivity.
  -
    assert (VS : CL5A.visr (ahid A model) (sp - 4096) 4096).
    { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 _ HH); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    assert (DS : L5.defined (CCA.vis A model M) (sp - 4096) 4096) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [rewrite K0; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite KNOW. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kunk_intro with (A := sp - 4096) (N := 4096); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4096) (N := 4096); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
  -
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite G3, FFSnil. unfold CH2.den. cbn [map fst snd app edenot CHA.denF length]. rewrite U10, U32.
    split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ q n HH HinLB)|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.

Theorem opdel_ok : PMSA.opdel_specA L ar HI 980676.
Proof. exact (opdel_ok_at _ _ Cut_opdel_plain_cboth.cp0 _ _ Cut_opdel_plain_cboth.plans Cut_opdel_plain_cboth.tags_ok ODA.goodP). Qed.
Theorem opdel_sized_ok : PMSA.opdel_specA L ar HI 980680.
Proof. exact (opdel_ok_at _ _ Cut_opdel_sized_cboth.cp0 _ _ Cut_opdel_sized_cboth.plans Cut_opdel_sized_cboth.tags_ok ODA.goodS). Qed.
End OpDelOk.

