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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_pop_state_cboth_T Cut_pop_state_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PmLibSpecsBLocal.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_pop_state_cboth.
Module GT := Cut_pop_state_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module PPA.
Definition PC_SM : Z := 413656.
Definition PC_ASH : Z := 727976.
Definition RETPC : Z := 781352.
Definition SBz : Z := 2147450880.
Definition IMGHI : Z := 7028736.
Definition PE := EVar 10. Definition bE := EVar 32. Definition lnE := EVar 33. Definition sheE := EVar 34. Definition xvE := EVar 35. Definition capE := EVar 36.
Definition FR : expr * Z * Z := (EVar 53, 1, -96).
Definition FFS : list (list (expr * Z * Z)) := [[]; []; [FR]; [FR]; [FR]; [FR]].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition WSH : list SGP.region := [(CHA.SRL3 bE, SBz, CHA.SRL3 (APC.eaddz capE 7))].
Definition NEWS_ASH : list kentry := STAT ++ [KWord (SA (EVar 53) 120) 8 (EVar 48); KWr (SA (EVar 48) 0) (ELit 1)].
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 48 (nth i G.BLS []) (nth i FFS []) 1 53 48 X)%bool.
Definition kind (j : nat) : Z :=
  match find (fun r : nat * nat * nat * Z => Nat.eqb (fst (fst (fst r))) j) G.RETS with Some (_, _, _, pc) => pc | None => 0 end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition lastE : expr := EAlu Instr.ALU_ADD (APC.eadd bE lnE) (ELit (-1)).

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_SM then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_SM && Z.eqb (kind i) 0 && Z.eqb (kind j) PC_SM && Nat.ltb i 2
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj
                                             (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => (Nat.eqb (CH2.ci_nx ci) 48 && Z.eqb (CH2.ci_csp ci) (-96))%bool | None => false end
                                  && CHA.frames_eqb (nth j FFS []) (FR :: nth i FFS []) && CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS []))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_ASH then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_ASH && Z.eqb (kind i) PC_SM && Z.eqb (kind j) PC_ASH && Nat.ltb 53 (CC.cp_nx c)
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4128 0 [] (nth i FFS []) WSH NEWS_ASH None c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []))
                                  && CHA.frames_eqb (nth i FFS []) [FR] && CHA.frames_eqb (nth j FFS []) [FR]
                                  && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                                  && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD PE (ELit 248)) && CL.ps_reg_is ps 11 lnE
                                  && has cells (KWord (SA PE 248) 8 bE) && has cells (KWord (SA PE 256) 8 lastE) && has cells (KWord (SA (EVar 53) 120) 8 (EVar 48)))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && Z.eqb (kind i) PC_ASH && Nat.ltb 53 (CC.cp_nx c)
         && CHA.frames_eqb (nth i FFS []) [FR] && CH2.blocks_eqb (nth i G.BLS []) []
         && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fle => expr_eqb fle (EVar 48) | None => false end
         && has cells (KWord (SA (EVar 48) 0) 1 (ELit 0))
         && CBA.regions_eqb (CC.cp_F c) [(EVar 2, -4256, ELit 4256); (PE, 256, ELit 8); (EVar 53, 0, ELit 24); (EVar 53, 32, ELit 88); (CHA.SRL3 (EVar 53), SBz, ELit 16); (EVar 48, 0, ELit 1)]
         && CL.ps_reg_is ps 10 xvE && has cells (KWord (SA PE 248) 8 bE) && has cells (KWord (SA PE 256) 8 lastE))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End PPA.

Section PopStateOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ASH_OK : PMSB.annotate_shrink_spec L ar HI PPA.PC_ASH.

Definition al (x m : Z) : Prop := x mod m = 0.
Definition eqz (a b : Z) : Prop := a = b.
Definition hid (P : Prop) : Prop := P.

Lemma cont_last_byte : forall (M : word -> option byte) b cap ln, 0 < ln -> shadow_cont M b cap ln -> byte_at M (S b + (ln - 1) / 8) (ln mod 8).
Proof.
  intros M b cap ln Hl (Z0 & P0 & _). pose proof (Z.div_mod ln 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound ln 8 ltac:(lia)) as R.
  pose proof (Z.div_mod (ln - 1) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (ln - 1) 8 ltac:(lia)) as R1.
  destruct (Z.eq_dec (ln mod 8) 0) as [e|ne].
  - rewrite e. apply Z0. lia.
  - replace ((ln - 1) / 8) with (ln / 8) by lia. exact (P0 ne).
Qed.

Theorem pop_state_ok : PMSB.pop_state_specA L ar HI 780820.
Proof.
  intros LB FF LK cr A P b cap x sp r rest. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hsp32 & Hvec & Hbytes & Hxr) Hcont.
  destruct Hvec as ((Hw0 & Hw8 & Hw16) & Hofr & Ho8 & Hosh & HinLB & Hlen & Hcap & Hshc).
  set (ln := Z.of_nat (length rest) + 1) in *. set (o := P + 248) in *.
  unfold PMSA.a0, PMSA.u64, PMSA.u8, PMSB.POP_SCR, PMSB.AINC_SCR, PMSA.ainfr in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : PPA.IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold PPA.IMGHI, FS_BYTES; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (b, cap) HinLB ltac:(cbn [snd]; lia)) as BHI. cbn [fst] in BHI.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  change (al sp 16) in S1. change (al sp 32) in Hsp32. change (al o 8) in Ho8. change (al b 16) in B16. change (al (ahl_ceil ar) 8) in C8. change (al (ar_sptop ar) 16) in SP16.
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Hofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (B1' : hl_img_hi L <= b) by (rewrite ILO, IHI in *; lia). clear B1 B6.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  pose proof (Z.mod_pos_bound ln 8 ltac:(lia)) as SHE. remember (ln mod 8) as she eqn:Eshe. change (eqz she (ln mod 8)) in Eshe.
  assert (LN1 : 1 <= ln) by (unfold ln; lia).

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; ln; she; x; cap] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 P) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 ln) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 she) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 x) by reflexivity.
  assert (V36 : ev E0 36 = Z_to_bv 64 cap) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite V10; apply u64_of_Z; unfold o in *; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = ln) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = she) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = x) by (rewrite V35; apply u64_of_Z; lia).
  assert (U36 : bv_unsigned (ev E0 36) = cap) by (rewrite V36; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4256) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(P + 256, 8); (S b, (cap + 7) / 8)] : list L5.range).
  assert (WINC : incl [(P + 256, 8)] WW) by (intros y [<-|[]]; left; reflexivity).
  assert (WOK : forall (w : L5.range) (a : Z), In w [(P + 256, 8)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (CL5A.infr_wok L ar LB FF sp _ o 24 a RFx Hofr). unfold o. clear - Hin. lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(P + 256, 8)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (P + 256, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (ULAST : CL5A.uv E0 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 32) (EVar 33)) (ELit (-1))) = b + ln - 1).
  { apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap LN1; lia]. }
  assert (UO : CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit 248)) = o) by (apply CL5.u_lin; [lin_eval; rw_atoms; unfold o; clear; lia | clear - O3 O6; lia]).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha; unfold CHA.sclientA.
    - unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(unfold o; clear - Ha; lia)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - rewrite CL5A.estart_srl3', UO in Ha. unfold elenZ in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow o 2 a Ho8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 2) with 16 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 16 a RFx (CL5A.ainfr_sub FF o 24 o 16 Hofr ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - assert (Ea : a = b + ln - 1).
      { unfold estart, elenZ in Ha. cbn [a_base a_off] in Ha. replace (bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 32) (EVar 33)))) with (b + ln) in Ha
          by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]). cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia). clear - Ha. lia. }
      subst a. split; [clear - B0 B7 Hlen Hcap LN1; lia|]. split; [left; exists (b, cap); split; [exact HinLB | cbn [fst snd]; clear - Hlen LN1; lia]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - BHI LN1. lia.
    - rewrite CL5A.estart_srl3', ULAST in Ha. unfold elenZ in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      assert (SH : in_shadow_of b cap a).
      { apply (CL5A.in_shadow_mono (b + ln - 1) 1 b cap a); [clear - LN1; lia | clear - Hlen; lia | clear; lia | apply CL5A.shreg1_in_shadow; unfold SB in *; clear - Ha; lia]. }
      pose proof (CHA.shadow_range b cap a ltac:(clear - B0; lia) B3 B7 SH) as SRa.
      split; [clear - SRa; lia|]. split; [do 6 right; exists (b, cap); split; [exact HinLB | exact SH]|].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b cap a RFx ltac:(clear - B0; lia) B3 B4 SH). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (FLF := fun (E : env) => ar_fs ar <= CL5A.uv E (EVar 48) < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF sp (CH.hd_scr G.HDECL) (CL5A.uv E (EVar 48))).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M' : word -> option byte) (_ : Model) =>
               if Z.eqb (PPA.kind i) PPA.PC_ASH then shadow_cont M' b cap (ln - 1) /\ FLF E
               else if Z.eqb (PPA.kind i) PPA.PC_SM then shadow_cont M' b cap ln /\ FLF E else shadow_cont M' b cap ln).

  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (OSH : forall a, in_shadow_of o 24 a -> in_shadow_of b cap a -> False).
  { intros a X Y. destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & FC).
    destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (G1 & _). destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _).
    refine (CL5A.sh_apart2 b cap (ff_addr f) (ff_bytes (ff_class f)) a ltac:(clear - B0; lia) ltac:(clear - G0 G1; lia) B3 ltac:(clear - FC; lia) (CHA.mod8_of_16 _ B16) (CHA.mod8_of_64 _ FA) QF Y _).
    apply (CL5A.in_shadow_mono o 24); [clear - F1; lia | clear - F2; lia | clear; lia | exact X]. }
  assert (KSHO : forall a, in_shadow_of o 24 a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(clear; lia) Ha) as (G1 & G2 & _). pose proof (SHR o 24 a O3 ltac:(clear; lia) O6 Ha) as SRa.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    - unfold hid in O5. unfold o in *. clear - Hin SRa O5. lia.
    - exact (OSH a Ha (CL5A.blk_shadow_in b cap a (CHA.mod8_of_16 _ B16) B3 Hin)). }
  assert (KCAP : forall a, o + 16 <= a < o + 24 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(clear - Ha; lia)) as (G1 & G2 & _).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    - unfold o in *. clear - Hin Ha. lia.
    - destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G3 & G4). unfold hid in O5. unfold S, SB in *. clear - Hin Ha O5 G3 G4. lia. }
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ PPA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  assert (MAIN : forall i c, nth_error G.CPS i = Some c -> (i < 2)%nat -> CC.cp_pc c = 780820 -> CCA.AtV (hl_segs L) c E0 R A M model ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 780820) M (seg_rom (hl_segs L))) model) K).
  { intros i0 c0 Hc0 Hi0 Hpc0 HAt0. rewrite <- Hpc0.
    eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
              G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
    - rewrite LS. exact FPM.
    - rewrite LS. exact G.plans.
    - exact G.tags_ok.
    - exact PPA.heap_ok.
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    -
      intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ PPA.leaf_ok _ _ _ _ _ IL) as X. unfold PPA.leaf_chk in X.
      destruct (Z.eqb_spec pc PPA.PC_SM) as [->|Hne1].
      {
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
        apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0, Y1, Y2. apply Nat.ltb_lt in Y3.
        lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
        apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
        assert (HFi : nth i PPA.FFS [] = []) by (do 2 (destruct i as [|i]; [reflexivity|]); clear - Y3; lia).
        assert (HBi : nth i G.BLS [] = []) by (do 2 (destruct i as [|i]; [reflexivity|]); clear - Y3; lia).
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HXi' : shadow_cont M1 b cap ln) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi).
        pose proof (CRA.smalloc_leaf L ar C HI HIok LYI LYR PPA.IMGHI LYH GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                      G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil 1 (List.filter (PPA.sm_ok ps i) (CC.cp_know cj)) i c ps j cj ci) as SML.
        rewrite (L5A.aly_scr_sm L C LAY), (L5A.aly_sm1 L C LAY) in SML.
        refine (SML ltac:(right; left; reflexivity) Hcj Hchk Y0 _ Y7 _ _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
        - rewrite Ynx, Ycsp. exact Y6.
        - rewrite Ynx. exact (CL5A.forallb_filter_self (PPA.sm_ok ps i) _).
        - rewrite HFi. cbn [length]. clear. lia.
        - intros Ea Eb cr1 Hc _. exact Hc.
        - intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. rewrite HBi, HFi in SMF. cbn [CH2.den CHA.denF map app] in SMF.
          destruct SMF as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Qp]. rewrite Ynx.
          unfold XI. rewrite Y2. split.
          +
            apply (CL5A.shadow_cont_same M1 M2 b cap ln ltac:(clear - Hlen; lia) (CHA.mod8_of_16 _ B16)); [|exact HXi']. intros a Ha.
            pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
            rewrite (proj1 Qp a ltac:(clear - SRa; lia) ltac:(do 6 right; exists (b, cap); split; [exact HinLB | exact Ha])).
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' Y4 HAt HA Hag HLF a ltac:(clear - SRa; lia) _).
            rewrite HBi, HFi. cbn [CH2.den CHA.denF map]. intros [Z0|[Z0|[Z0|[Z0|Z0]]]].
            * rewrite SCRV in Z0. clear - Z0 SRa S2 CL. lia.
            * destruct Z0 as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. unfold o in *. clear - Hin SRa O5. lia.
            * destruct Z0 as (bb & [] & _).
            * destruct Z0 as (f & [] & _).
            * destruct Z0 as (f & [] & _).
          + pose proof (CH2.retEx_ghost E' 48 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G48. cbn [nth Nat.add] in G48.
            assert (T48 : CL5A.uv (CH2.retEx E' 48 [Z_to_bv 64 fl] R2) (EVar 48) = fl).
            { unfold CL5A.uv. cbn [edenot]. rewrite G48. apply u64_of_Z. unfold FS_BYTES in Q7. destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3. clear - Q7 G0 G3 CL SP1. lia. }
            unfold FLF. rewrite T48. split; [unfold FS_BYTES in Q7; exact Q7|]. intros Hc. apply Q8.
            eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia]. }

      assert (FRM : forall E A1 M1 m1, CHA.frames_eqb (nth i PPA.FFS []) [PPA.FR] = true -> CH2.blocks_eqb (nth i G.BLS []) [] = true ->
                CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PPA.FFS Cred 2 i E A1 M1 m1 ->
                let F := CL5A.uv E (EVar 53) in
                CHA.curB LB G.BLS i E = LB /\ CHA.curF FF sp PPA.FFS i E = (F, 1, sp + -96 + 32) :: FF /\ env_agree GT.NF E0 E /\
                0 <= F /\ F + 128 <= 140737488355328 /\ al F 8 /\ (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\ (b + cap <= F \/ F + 128 <= b) /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + 11571200).
      { intros E A1 M1 m1 Hf Hb HA. apply CHA.frames_eqb_eq in Hf. apply CH2.blocks_eqb_eq in Hb. cbv zeta.
        assert (HcB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite Hb; reflexivity).
        assert (HcF : CHA.curF FF sp PPA.FFS i E = (CL5A.uv E (EVar 53), 1, sp + -96 + 32) :: FF) by (unfold CHA.curF; rewrite Hf; reflexivity).
        pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _). rewrite HcB, HcF in HHa.
        pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
        destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 1) with 128 in G2.
        destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
        destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFa (b, cap) HinLB) as (_ & _ & _ & _ & Bf). cbn [fst snd] in Bf. pose proof (Bf (CL5A.uv E (EVar 53), 1, sp + -96 + 32) (in_or_app _ _ _ (or_introl (in_eq _ _)))) as QF0.
        unfold ff_addr, ff_class in QF0. cbn [fst snd] in QF0. change (ff_bytes 1) with 128 in QF0.
        split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact (CHA.mod8_of_64 _ G3)|].
        split; [clear - G1 G2 G4; lia|]. split; [exact QF0|]. split; [exact G1 | exact G2]. }
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
      destruct (Z.eqb_spec pc PPA.PC_ASH) as [->|Hne2].
      {
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
        apply andb_prop in X as [X Y14]. apply andb_prop in X as [X Y13]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
        apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6]. apply andb_prop in X as [X Y5].
        apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0, Y1, Y2. apply Nat.ltb_lt in Y3.
        lazymatch type of Y5 with PPA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (FRM E A1 M1 m1 Y6 Y8 HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & QF0 & F3 & F4). set (F := CL5A.uv E (EVar 53)) in *.
        assert (HXi' : shadow_cont M1 b cap ln /\ FLF E) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi). destruct HXi' as [HSC HFL].
        pose proof (CHA.frames_eqb_eq _ _ Y6) as EFi. pose proof (CHA.frames_eqb_eq _ _ Y7) as EFj. pose proof (CH2.blocks_eqb_eq _ _ Y9) as EBj.
        refine (CALLEE PPA.PC_ASH 4128 0%nat [] PPA.WSH PPA.NEWS_ASH None 0 i c ps j cj ci Hcj Hchk Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite EFi, EFj; reflexivity | rewrite EFi; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
        assert (W33 : bv_unsigned (ev E' 33) = ln) by (rewrite (FZ 33%nat eq_refl); exact U33).
        assert (W36 : bv_unsigned (ev E' 36) = cap) by (rewrite (FZ 36%nat eq_refl); exact U36).
        assert (W53 : bv_unsigned (ev E' 53) = F) by (rewrite <- (proj1 Hag 53%nat) by exact Y3; reflexivity).
        assert (CELL : forall X0, PPA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PPA.FFS Cred 2 i E A1 M' m' HA') as Hoff.
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        unfold PPA.lastE in *. unfold PPA.PE, PPA.bE, PPA.lnE, PPA.capE in *.
        eexists. eexists. split; [exact (ASH_OK LB ((F, 1, sp + -96 + 32) :: FF) LK1 cr A1 o b (ln - 1) ln cap (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0, PMSA.a1, PMSA.vec_at, PMSA.u64, PMSA.ainfr.
          split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10); rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)); f_equal;
                  apply CL5.u_lin; [lin_eval; rw_atoms; unfold o; clear; lia | clear - O3 O6; lia]|].
          split; [replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y11); cbn [edenot]; rewrite (FZ 33%nat eq_refl); exact V33|].
          split.
          { split; [|split].
            - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Y12) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as G0.
              unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
            - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Y13) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W10; unfold o; clear; lia)) as G0.
              replace (CL5A.uv E' (EAlu Instr.ALU_ADD (APC.eadd (EVar 32) (EVar 33)) (ELit (-1)))) with (b + (ln - 1)) in G0; [exact G0|].
              symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap LN1; lia].
            - apply (CL5A.u64_same (hl_segs L) M M' (o + 16) (b + cap)); [clear - O3; lia | clear - O6; lia | | exact Hw16]. intros y Hy. apply Hfr1. apply KCAP. clear - Hy. lia. }
          split; [destruct Hofr as (f & Hf & G1 & G2); exists f; split; [right; exact Hf | split; assumption]|]. split; [exact Ho8|]. split.
          { apply (CL5A.shadow_zero_same M M' o 3); [|exact Hosh]. intros jj Hj. apply Hfr1. apply KSHO.
            apply (CL5A.shreg_in_shadow o 3); [exact Ho8 | clear; lia | unfold S; clear - Hj; lia]. }
          split; [exact HinLB|]. split; [clear - LN1; lia|]. split; [clear - Hlen; lia|]. split; [|clear - B0 Hcap; lia].
          apply (CL5A.shadow_cont_same M1 M' b cap ln ltac:(clear - Hlen; lia) (CHA.mod8_of_16 _ B16)); [|exact HSC]. intros a Ha.
          pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 WRS_OK
                    i c ps E E' R1 R' A1 M1 m1 M' m' Y4 HAt HA Hag HLF a ltac:(clear - SRa; lia) _).
          rewrite EFi, (CH2.blocks_eqb_eq _ _ Y8). cbn [CH2.den map]. unfold CHA.denF, PPA.FR. cbn [map fst snd]. change (bv_unsigned (edenot E (EVar 53))) with F. intros [Z0|[Z0|[Z0|[Z0|Z0]]]].
          - rewrite SCRV in Z0. clear - Z0 SRa S2 CL. lia.
          - destruct Z0 as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. unfold o in *. clear - Hin SRa O5. lia.
          - destruct Z0 as (bb & [] & _).
          - destruct Z0 as (f & [<-|[]] & Hin & _). unfold ff_addr, ff_class in Hin. cbn [fst snd] in Hin. change (ff_bytes 1) with 128 in Hin. clear - Hin SRa F2. lia.
          - destruct Z0 as (f & [<-|[]] & Hin). unfold ff_addr, ff_class in Hin. cbn [fst snd] in Hin. change (ff_bytes 1) with 128 in Hin.
            exact (CL5A.sh_apart2 b cap F 128 a ltac:(clear - B0; lia) F0 B3 ltac:(clear; lia) (CHA.mod8_of_16 _ B16) F8 QF0 Ha Hin). }
        { intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsc2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *. destruct HV as (_ & _ & HV3 & HV4 & _).
          assert (T53 : bv_unsigned (ev E2 53) = F) by (rewrite <- (proj1 Hag2 53%nat) by (clear - HV3 Y3; lia); exact W53).
          assert (T48 : CL5A.uv E2 (EVar 48) = CL5A.uv E (EVar 48)).
          { unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag2 48%nat) by (clear - HV3 Y3; lia). rewrite <- (proj1 Hag 48%nat) by (clear - Y3; lia). reflexivity. }
          split; [cbn [CH2.den map app]; apply incl_refl|]. split.
          { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 32), PPA.SBz, CHA.SRL3 (APC.eaddz (EVar 36) 7)). split; [left; reflexivity|].
            unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W32.
            replace (bv_unsigned (edenot E' (APC.eaddz (EVar 36) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
            unfold S, SB, PPA.SBz in *. exact Hin. }
          split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko _ (or_intror (or_introl eq_refl)) Hin)|].
          split; [unfold CHA.curB; rewrite EBj; exact HH2|]. split; [reflexivity|].
          split; [unfold XI; rewrite Y2; split; [exact Hsc2 | unfold FLF; rewrite T48; exact HFL]|].
          intros X0 HX0 _. unfold PPA.NEWS_ASH, PPA.STAT in HX0. cbn [app In] in HX0.
          pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2. destruct HFL as (HFL1 & HFL2). set (fl := CL5A.uv E (EVar 48)) in *.
          assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
          { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _); unfold FS_BYTES in G3; clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
          destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]].
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          -
            pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + 120) (CELL _ Y14) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W53; reflexivity)) as G0.
            apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0.
            assert (G48 : CL5A.uv E' (EVar 48) = fl) by (unfold CL5A.uv, fl; cbn [edenot]; rewrite <- (proj1 Hag 48%nat) by (clear - Y3; lia); reflexivity). rewrite G48 in G0.
            pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 1 (sp + -96 + 32) (sp + -96 + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
            change (ff_bytes 1) with 128 in FP. replace (F + 128 - 8) with (F + 120) in FP by (clear; lia). specialize (FP G0).
            eapply CL5.kword64_intro with (A := F + 120) (z := fl); [unfold estart; cbn [a_base a_off edenot]; rewrite T53; reflexivity | clear - F0; lia | clear - F1; lia | |].
            + cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E2 48)). f_equal. exact T48.
            + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
          - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart; cbn [a_base a_off edenot]; unfold CL5A.uv in T48; cbn [edenot] in T48; rewrite T48; fold fl; clear; lia | reflexivity | | | |].
            + destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _). clear - HFL1 G0. lia.
            + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
            + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
            + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy HFL1; lia))).
              pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy HFL1. lia. } }

      apply andb_prop in X as [X Y13]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yh0].
      apply andb_prop in X as [X Yr]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y6]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [Xbase Y1].
      apply Z.eqb_eq in Y1. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
      destruct (CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i PPA.FFS [])) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      destruct (FRM E A1 M1 m1 Y6 Y8 HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & QF0 & F3 & F4). set (F := CL5A.uv E (EVar 53)) in *.
      assert (HXi' : shadow_cont M1 b cap (ln - 1) /\ FLF E) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi). destruct HXi' as [HSC (HFL1 & HFL2)]. set (fl := CL5A.uv E (EVar 48)) in *.
      refine (CRA.exit_retire L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P + 256, 8)] G.BLS PPA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
                K DEF0 R r EV Hra Hraok PPA.RETPC i c ps (EVar 48) (EVar 53) 1 (-96) _ Xbase (CHA.frames_eqb_eq _ _ Y6) Hrc Yh0 fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
        [rewrite LS; exact PPA.ret_at |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'. rewrite HcB in HH1. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2).
      assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
      assert (W33 : bv_unsigned (ev E' 33) = ln) by (rewrite (FZ 33%nat eq_refl); exact U33).
      assert (W53 : bv_unsigned (ev E' 53) = F) by (rewrite <- (proj1 Hag 53%nat) by exact Y3; reflexivity).
      assert (W48 : bv_unsigned (ev E' 48) = fl) by (rewrite <- (proj1 Hag 48%nat) by (clear - Y3; lia); reflexivity).
      assert (CELL : forall X0, PPA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
      assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')).
      { rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)).
        exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PPA.FFS Cred 2 i E A1 M1 m1 HA). }
      unfold PPA.lastE in *. unfold PPA.PE, PPA.bE, PPA.lnE, PPA.xvE in *.
      apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      replace (Z.of_nat (length rest)) with (ln - 1) by (unfold ln; clear; lia).
      split; [unfold PMSA.a0; replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
              rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10); cbn [edenot]; rewrite (FZ 35%nat eq_refl); exact V35|].
      split.
      { unfold PMSA.vec_at, PMSA.u64. fold o. split; [|split].
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Y12) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as G0.
          unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Y13) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W10; unfold o; clear; lia)) as G0.
          replace (CL5A.uv E' (EAlu Instr.ALU_ADD (APC.eadd (EVar 32) (EVar 33)) (ELit (-1)))) with (b + (ln - 1)) in G0; [exact G0|].
          symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap LN1; lia].
        - apply (CL5A.u64_same (hl_segs L) M M' (o + 16) (b + cap)); [clear - O3; lia | clear - O6; lia | | exact Hw16]. intros y Hy. apply (proj1 HP). apply KCAP. clear - Hy. lia. }
      split; [|repeat split; reflexivity].
      apply (CL5A.shadow_cont_same M1 M' b cap (ln - 1) ltac:(clear - Hlen LN1; lia) (CHA.mod8_of_16 _ B16)); [|exact HSC]. intros a Ha.
      pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
      apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - SRa; lia).
      repeat (apply Forall_cons); [.. | apply Forall_nil]; cbv beta iota.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W2. rewrite u64_of_Z by (clear; lia). clear - SRa S2 CL. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W10. rewrite u64_of_Z by (clear; lia). unfold hid in O5. unfold o in *. clear - SRa O5. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W53. rewrite u64_of_Z by (clear; lia). clear - SRa F2. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W53. rewrite u64_of_Z by (clear; lia). clear - SRa F2. lia.
      + rewrite CL5A.estart_srl3. unfold CL5A.uv, elenZ. cbn [edenot]. rewrite W53. rewrite u64_of_Z by (clear; lia).
        destruct (Z_lt_dec a (F / 8 + PPA.SBz)) as [G|G]; [left; exact G|]. destruct (Z_le_dec (F / 8 + PPA.SBz + 16) a) as [G'|G']; [right; exact G'|]. exfalso.
        pose proof (CL5A.shreg_in_shadow F 16 a F8 ltac:(clear; lia) ltac:(unfold SB, PPA.SBz in *; clear - G G'; lia)) as SHF. change (8 * 16) with 128 in SHF.
        exact (CL5A.sh_apart2 b cap F 128 a ltac:(clear - B0; lia) F0 B3 ltac:(clear; lia) (CHA.mod8_of_16 _ B16) F8 QF0 Ha SHF).
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite W48. rewrite u64_of_Z by (clear; lia).
        destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & G4 & _) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in G4. clear - SRa HFL1 G4. lia.
    - exact Hc0.
    - exact HAt0.
    - assert (Hk0 : PPA.kind i0 = 0) by (do 2 (destruct i0 as [|i0]; [reflexivity|]); lia).
      assert (HB0 : nth i0 G.BLS [] = []) by (do 2 (destruct i0 as [|i0]; [reflexivity|]); lia).
      assert (HF0 : nth i0 PPA.FFS [] = []) by (do 2 (destruct i0 as [|i0]; [reflexivity|]); lia).
      split.
      + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
        split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
        exists cr, LK. unfold CHA.curB, CHA.curF. rewrite HB0, HF0. cbn [app CHA.denF CH2.den map length]. split; [exact HH|].
        split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
      + unfold XI. rewrite Hk0. exact Hshc.
    - exact Hfp. }

  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VO : CL5A.visr (ahid A model) o 24).
  { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
  { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
    exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VB : CL5A.visr (ahid A model) b cap).
  { intros k Hk. apply CLV; [clear - Hk B0 B7; lia | left; exists (b, cap); split; [exact HinLB | cbn [fst snd]; clear - Hk; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk BHI. lia. }
  assert (INSL : in_shadow_of b cap (S (b + ln - 1))).
  { apply (CL5A.in_shadow_mono (b + ln - 1) 1 b cap); [clear - LN1; lia | clear - Hlen; lia | clear; lia | apply CL5A.shreg1_in_shadow; reflexivity]. }
  assert (VSL : ahid A model (Z_to_bv 64 (S (b + ln - 1))) = false).
  { pose proof (SHR b cap _ ltac:(clear - B0; lia) B3 B7 INSL) as SRa. apply CLV; [clear - SRa; lia | do 6 right; exists (b, cap); split; [exact HinLB | exact INSL] |].
    exact (CL5A.not_stk_shadow_sh L ar LB FF b cap _ RFx ltac:(clear - B0; lia) B3 B4 INSL). }
  assert (VS : CL5A.visr (ahid A model) (sp - 4256) 4256).
  { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
  set (Mv := CCA.vis A model M).
  assert (DO : L5.defined Mv o 24).
  { apply (CL5A.defined_vis _ M o 24 VO). destruct Hofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
    intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
  assert (DS : L5.defined Mv (sp - 4256) 4256) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
  assert (HAND : forall e v, bv_unsigned (edenot E0 e) = v -> bv_unsigned (edenot E0 (EAlu Instr.ALU_AND e (ELit 7))) = v mod 8) by (intros e v <-; apply CL5A.u_and7).
  assert (SHEQ : forall e : expr, CL5A.uv E0 e = cap + 7 -> CL5A.uv E0 e / 8 = (cap + 7) / 8) by (intros e ->; reflexivity).
  assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn 27 (CC.cp_know G.cp0))).
  { cbn [firstn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := b); [unfold estart; cbn [a_base a_off edenot]; rewrite U10; reflexivity | clear - O3; lia | clear - O6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + ln); [unfold estart; cbn [a_base a_off edenot]; rewrite U10; unfold o; clear; lia | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 8) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw8].
    + eapply CL5.kwr_intro with (A := o + 8) (N := 8); [unfold estart; cbn [a_base a_off edenot]; rewrite U10; unfold o; clear; lia | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia |].
      apply (L5.defined_sub Mv o 24 (o + 8) 8 DO); clear; lia.
    + eapply CL5.krange_intro with (v := P); [lin_eval; rw_atoms; clear; lia | unfold o in *; clear - O3 O6 O1 FSLO; lia | unfold o in *; clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := P); [lin_eval; rw_atoms; clear; lia | unfold o in *; clear - O3 O6 O1 FSLO; lia | clear; lia | unfold al, o in Ho8; clear - Ho8; lia].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 o); [exact UO | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j ltac:(clear - Hj; lia)) | exact (Hosh j ltac:(clear - Hj; lia))].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 16);
        [reflexivity | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U10; reflexivity | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5A.kword8_intro with (A := b + ln - 1) (z := x); [rewrite (CL5.estart_lin E0 _ (-1) (b + ln)); [clear; lia | lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]
        | clear - B0 LN1; lia | clear - B7 Hlen; lia | exact V35 | clear - Hxr; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - B0 LN1; lia | clear - B7 Hlen; lia | exact (CL5A.visr_sub _ b cap (b + ln - 1) 1 VB ltac:(clear - LN1; lia) ltac:(clear - Hlen; lia)) |].
      pose proof (Hbytes (length rest) ltac:(rewrite length_app; cbn [length]; clear; lia)) as G. rewrite app_nth2 in G by (clear; lia). rewrite Nat.sub_diag in G. cbn [nth] in G.
      replace (b + ln - 1) with (b + Z.of_nat (length rest)) by (unfold ln; clear; lia). exact G.
    + eapply CL5.krange_intro with (v := x); [lin_eval; rw_atoms; clear; lia | clear - Hxr; lia | clear - Hxr; lia].
    + apply (CL5A.shbyte_intro (hl_segs L) E0 Mv _ _ (b + ln - 1) she); [exact ULAST | exact V34 | clear - SHE; lia | clear - B0 B7 Hlen LN1; lia |].
      apply CL5A.byte_vis; [exact VSL|]. replace (b + ln - 1) with (b + (ln - 1)) by (clear; lia). rewrite (CL5A.S_add_al b (ln - 1) (CHA.mod8_of_16 _ B16)).
      unfold eqz in Eshe. rewrite Eshe. exact (cont_last_byte M b cap ln ltac:(clear - LN1; lia) Hshc).
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BHI B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.krange_intro with (v := ln); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap LN1; lia].
    + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.krange_intro with (v := cap - ln); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap LN1; lia].
    + eapply CL5.kunk_intro with (A := sp - 4256) (N := 4256); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4256) (N := 4256); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp32].
    + eapply CL5.kdisj_intro with (A1 := sp - 4256) (N1 := 4256) (A2 := o) (N2 := 16); [ev_start | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U10; reflexivity | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4256) (N1 := 4256) (A2 := b + ln - 1) (N2 := 1);
        [ev_start | reflexivity | rewrite (CL5.estart_lin E0 _ (-1) (b + ln)); [clear; lia | lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia] | reflexivity | clear - B4 S2 Hlen; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF.
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 16) (A2 := b + ln - 1) (N2 := 1);
        [unfold estart; cbn [a_base a_off edenot]; rewrite U10; reflexivity | reflexivity
        | rewrite (CL5.estart_lin E0 _ (-1) (b + ln)); [clear; lia | lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia] | reflexivity | clear - QF F1 F2 Hlen LN1; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _).
      eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 2) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3', UO; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; apply SHEQ; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB. destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) o ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le o 2 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 16) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [unfold estart; cbn [a_base a_off edenot]; rewrite U10; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; apply SHEQ; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in O5. unfold SB in *. clear - O5 G1 G2. lia. }
  assert (CE0 : she = 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 34) 0 0)) by (intros Hz; eapply CL5.krange_intro with (v := she); [lin_eval; rw_atoms; clear; lia | clear - SHE; lia | clear - Hz; lia]).
  assert (CE1 : she <> 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 34) 1 7)) by (intros Hz; eapply CL5.krange_intro with (v := she); [lin_eval; rw_atoms; clear; lia | clear - SHE; lia | clear - Hz SHE; lia]).
  assert (CE2 : she <> 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EAlu Instr.ALU_ADD (EVar 34) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EVar 33) (ELit 7)) (ELit 7)))) 1 7)).
  { intros Hz. unfold eqz in Eshe. assert (G : she - (ln + 7) mod 8 = 1) by (clear - Hz Eshe LN1; subst she; lia).
    assert (U337 : bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 33) (ELit 7))) = ln + 7) by (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia]).
    eapply CL5.krange_intro with (v := she - (ln + 7) mod 8); [lin_form; rewrite (HAND _ _ U337); cbn [edenot]; rw_atoms; clear; lia | clear - G; lia | clear - G; lia]. }
  assert (ATI : forall c tl, firstn 27 (CC.cp_know c) = firstn 27 (CC.cp_know G.cp0) -> skipn 27 (CC.cp_know c) = tl -> CC.cp_regs c = CC.cp_regs G.cp0 ->
            Forall (kentry_ok (hl_segs L) E0 Mv) tl -> CCA.AtV (hl_segs L) c E0 R A M model).
  { intros c tl H1 H2 H3 HT. split; [rewrite H3; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 27 (CC.cp_know c)), H1, H2. apply Forall_app. split; [exact COMMON | exact HT]. }
  destruct (Z.eq_dec she 0) as [He0|He1].
  - apply (MAIN 0%nat G.cp0 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp0 [_] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CE0 He0) | apply Forall_nil].
  - apply (MAIN 1%nat G.cp1 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp1 [_; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CE1 He1) | apply Forall_cons; [exact (CE2 He1) | apply Forall_nil]].
Qed.
End PopStateOk.

