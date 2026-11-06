(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtCpsA CutRtA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CRSH.
Definition mem := (word -> option byte).
Section Tail.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Hypothesis KNIL : K [].

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

Variables (PCSH VSH SCR0 : Z).
Hypothesis SETSH : aset_shadow_spec L ar SCFG HI PCSH VSH SCR0.

Lemma setsh_leaf : forall scr news i c ps j cj ci Fe k c0 fle e10,
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr 0 (nth i BLS []) (nth i FFS []) [(CHA.SRL3 Fe, SB, ELit (ff_bytes k / 8))] news None c ps cj
                 (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = PCSH -> 0 <= SCR0 <= scr ->
  nth i FFS [] = [(Fe, k, c0)] -> CHA.frames_eqb (nth j FFS []) (nth i FFS []) = true -> CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true -> 0 <= D0 - 1 ->
  CL.ps_reg_is ps 10 e10 = true -> (forall Ex, CL5A.uv Ex e10 = CL5A.uv Ex Fe / 8 + SB) ->
  CL.ps_reg_is ps 11 (ELit (ff_bytes k / 8)) = true ->
  (forall X, In X news -> CHA.static_chk SCELLS GLO GHI X = true \/ X = KWord (SA Fe (ff_bytes k - 8)) 8 fle \/ X = KWr (SA fle 0) (ELit 1)) ->
  CC.has_cell (SR.ps_cells ps) (KWord (SA Fe (ff_bytes k - 8)) 8 fle) = true ->
  (CC.cp_nx c <= CC.cp_nx c)%nat ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    ar_fs ar <= CL5A.uv E' fle < ar_fs ar + FS_BYTES -> (forall Ea Eb, env_agree (CC.cp_nx c) Ea Eb -> CL5A.uv Eb fle = CL5A.uv Ea fle) ->
    (forall R2 M2 model2 A2 LK2 cr, regs_preserved R' R2 ->
        let F := CL5A.uv E Fe in
        (forall a, CHA.akept L ar (curB i E) (curF i E) (sp0 + CH2.ci_csp ci) scr [(S F, ff_bytes k / 8)] a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (curB i E) (curF i E) (sp0 + CH2.ci_csp ci) scr a -> M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None) ->
        (forall j0, 0 <= j0 < ff_bytes k / 8 -> byte_at M2 (S F + j0) VSH) ->
        incl A A2 -> CHA.amodel_ok A2 model2 -> model_rt model1 model2 ->
        ri_inv HI (curB i E) (curF i E) LK2 cr A2 M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [] R2) A2 M2 model2) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros scr news i c ps j cj ci Fe k c0 fle e10 Hcj Hchk Hpc Hscr HFi Hfeq Hbeq HD0 Ha0 Hu10 Ha1 Hnews Hflc _ HCred fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH HFLR Hflv HUSER.
  pose proof HAX as [HA HX].
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { pose proof Hchk as Hchk'. unfold CHA.custom_chk in Hchk'. destruct (CHA.common_chk NF d scr 0 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk' with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk' as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV]. apply CH2.blocks_eqb_eq in Hbeq.
  pose proof (CBA.callee_leaf L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
                CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI KNIL) as CALLEE.
  refine (CALLEE PCSH scr 0%nat (nth i BLS []) [(CHA.SRL3 Fe, SB, ELit (ff_bytes k / 8))] news None 0 i c ps j cj ci Hcj Hchk Hpc Hfeq _ fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH _);
    [rewrite HFi; cbn [length Z.of_nat]; lia |].
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & _ & Hfr1 & Hdf1).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as WF1. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF1) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _).
  set (F := CL5A.uv E Fe) in *.
  assert (HFcur : curF i E = (F, k, sp0 + c0 + 32) :: FFrest) by (unfold CHA.curF; rewrite HFi; reflexivity).
  assert (HinF : In (F, k, sp0 + c0 + 32) (curF i E)) by (rewrite HFcur; left; reflexivity).
  assert (HFE' : CL5A.uv E' Fe = F) by (rewrite HFi in HdenF; cbn [CHA.denF map fst snd] in HdenF; injection HdenF as HF1; exact HF1).
  destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF1 _ HinF) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [ff_addr ff_class fst snd] in Q1, Q2, Q3, Q4, Q5, Q6.
  destruct (CHA.frm_align L ar _ _ _ _ _ _ _ WF1 HinF) as (FA & FB & FC). cbn [ff_addr ff_class fst snd] in FA, FB, FC.
  destruct (CHA.wf_fs _ _ _ _ _ _ _ _ WF1) as ((S0a & S0b & S0c) & S1a & S1b). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  pose proof (CHA.mod8_of_64 _ FA) as F8.
  set (B := ff_bytes k) in *.
  assert (B8 : B mod 8 = 0) by (apply Z.mod_divide in FB; [|lia]; destruct FB as [q Hq]; rewrite Hq; replace (q * 64) with (q * 8 * 8) by lia; apply Z_mod_mult).
  pose proof (Z_div_mod_eq_full B 8) as DB. rewrite B8 in DB.
  assert (Hoff : H_off_segments (hl_segs L) (ahid A model1)).
  { rewrite (L5LZ.sbm_ahid A model model1 (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)). exact (CBA.amb_off L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M model HA). }
  assert (US : CL5A.uv E' e10 = S F) by (rewrite (Hu10 E'), HFE'; reflexivity).
  eexists. eexists. split; [exact (CRC.setsh_cps L ar HI FPI PCSH VSH SCR0 SETSH scr (curB i E) (curF i E) LK cr A (F, k, sp0 + c0 + 32) (S F) (B / 8) (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) Hscr)|]. split.
  {
    unfold CRC.setsh_pre. cbn [ff_addr ff_class fst snd]. fold B.
    split; [|split; [|split; [exact HinF | split; [apply Z.div_pos; lia | split; lia]]]].
    - replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Ha0). unfold CL5A.uv in US. rewrite <- US. symmetry. apply Z_to_bv_bv_unsigned.
    - replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Ha1). cbn [edenot]. reflexivity. }

  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 (Hby & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  exists []. split; [reflexivity|]. cbv zeta.
  pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  pose proof HP as (HP1 & HP2 & HP3).

  assert (RFr : CHA.rng_facts L ar LBrest FFrest).
  { apply (CHA.rng_incl L ar _ _ _ _ RF1); [unfold CHA.curB; apply incl_appr, incl_refl | rewrite HFcur; apply incl_tl, incl_refl]. }
  assert (NOTCL : forall a, in_shadow_of F B a -> ~ aclient L ar LBrest FFrest sp0 SCR a).
  { intros a Ha. apply (CHA.obj_not_client L ar LY_img LBrest FFrest _ _ F B a RFr); [| lia | exact F8 | lia | | | | right; exact Ha].
    - unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. repeat split; lia.
    - destruct S1b as [S1b|S1b]; [left | right]; lia.
    - intros b Hb. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF1 b ltac:(unfold CHA.curB; apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BF). specialize (BF _ (in_or_app _ _ _ (or_introl HinF))). cbn [ff_addr ff_class fst snd] in BF. fold B in BF. lia.
    - intros f Hf. apply Q6. apply in_or_app. left. rewrite HFcur. cbn [ff_remove ff_addr fst]. rewrite Z.eqb_refl. exact Hf. }
  split; [exact I|].
  split; [rewrite HdenB; unfold CHA.curB; apply incl_refl|].
  split.
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 Fe, SB, ELit (B / 8)). split; [left; reflexivity|].
    unfold CHA.in_reg. cbn [fst snd]. rewrite CL5A.estart_srl3, HFE'. unfold elenZ. cbn [edenot]. rewrite L5.unsigned_lit by (pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound B 8 256 ltac:(lia) ltac:(lia)); lia).
    unfold S, SB in Hin |- *. lia. }
  split.
  { intros w a [<-|[]] Hin (_ & Hcl & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (NOTCL a); [|exact Hcl].
    apply (CL5A.blk_shadow_in F B a F8 ltac:(lia)). replace (B + 7) with (B / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. rewrite Z.add_0_r. exact Hin. }
  split; [unfold CHA.curB; rewrite Hbeq, (CH2.den_agree (CH2.ci_nx ci) E' E2 _ Hag2 BV), HdenB; unfold CHA.curB in HH2; exact HH2|].
  assert (HagEE2 : env_agree NF E E2).
  { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | clear - V3 V4; lia]. }
  split; [exact (HCred E E2 cr HC1 HagEE2)|].
  split; [exact (HUSER R2 M2 model2 A2 LK2 cr HRP HP1 HP3 Hby HA2 Hmo2 Hrt2 ltac:(unfold CHA.curB in HH2 |- *; exact HH2))|].

  assert (T53 : CL5A.uv E2 Fe = F).
  { pose proof (CHA.denF_agree sp0 (CH2.ci_nx ci) E' E2 _ Hag2 FV) as DA. rewrite HFi in DA. cbn [CHA.denF map fst snd] in DA. injection DA as DA1. unfold CL5A.uv in HFE' |- *. rewrite DA1. exact HFE'. }
  assert (T48 : CL5A.uv E2 fle = CL5A.uv E' fle) by (apply Hflv; eapply CC.env_agree_le; [exact Hag2 | exact V3]).
  set (fl := CL5A.uv E' fle) in *.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
  assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 model2 (Z_to_bv 64 y) = false).
  { intros y Hy. apply (CHA.fs_vis L ar C HI HIok NF 0 NF32 _ _ _ _ _ _ model2 y HH2); [lia | unfold FS_BYTES; exact Hy]. }
  intros X HXn _. destruct (Hnews X HXn) as [HS|[->| ->]].
  - exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 _ HH2 HS).
  -
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + (B - 8)) (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ (CC.has_cell_In _ _ Hflc))
                  ltac:(unfold estart; cbn [a_base a_off]; unfold CL5A.uv in HFE'; rewrite HFE'; reflexivity)) as G0.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. fold fl in G0.
    pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F k (sp0 + c0 + 32) (sp0 + c0 + 32) fl HH1 HH2 HinF HinF) as FP.
    fold B in FP. replace (F + B - 8) with (F + (B - 8)) in FP by lia. specialize (FP G0).
    eapply CL5.kword64_intro with (A := F + (B - 8)) (z := fl); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in T53; rewrite T53; reflexivity | lia | lia | |].
    + unfold CL5A.uv in T48. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 fle)). f_equal. exact T48.
    + apply (CL5A.u64_vis (hl_segs L)); [lia | lia | | exact FP]. intros y Hy. apply VFS. lia.
  - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart; cbn [a_base a_off]; unfold CL5A.uv in T48; rewrite T48; unfold fl, CL5A.uv; lia | reflexivity | lia | lia | lia |].
    intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(lia))).
    pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by lia. apply FD. unfold FS_BYTES. lia.
Qed.

End Tail.
End CRSH.
