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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_tce_cboth_T Cut_tce_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_tce_cboth.
Module GT := Cut_tce_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module TCA.
Definition PC_SM : Z := 413656.
Definition PC_ERRH : Z := 824952.
Definition PC_SETEC : Z := 749196.
Definition RETPC : Z := 816844.
Definition SBz : Z := 2147450880.
Definition IMGHI : Z := 7028736.
Definition SLOT2 : Z := 1370536.
Definition ISH2 : Z := 2147622197.
Definition GD : Z := 6882184.
Definition AXT : Z := 7020000.
Definition PE := EVar 10. Definition EE := EVar 12. Definition FLE := EVar 48. Definition FE := EVar 53.

Definition arm (i : nat) : nat := Nat.modulo i 5.
Definition slot (a : nat) : Z := nth a [96; 64; 80; 48; 32] 0.
Definition acode (a : nat) : Z := nth a [26; 25; 29; 28; 27] 0.

Definition NKC : nat := 29.
Lemma kn_common : forall i, (i <= 4)%nat -> firstn NKC (CC.cp_know (nth i G.CPS G.cp0)) = CC.cp_know G.cp0 /\ CC.cp_pc (nth i G.CPS G.cp0) = 815932.
Proof. intros i Hi. do 5 (destruct i as [|i]; [vm_compute; split; reflexivity|]). exfalso; clear - Hi; lia. Qed.
Lemma kn4_eq : skipn NKC (CC.cp_know G.cp4) = [KRange (EVar 11) 5 6].
Proof. vmc_refl. Qed.
Lemma kn_len : forall i, (i <= 3)%nat -> length (CC.cp_know (nth i G.CPS G.cp0)) = NKC.
Proof. intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso; clear - Hi; lia. Qed.
Lemma regs_lit : forall i, (i <= 3)%nat -> CC.cp_regs (nth i G.CPS G.cp0) = sr_upd sr_id 11 (ELit (Z.of_nat i + 1)).
Proof. intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso; clear - Hi; lia. Qed.
Lemma regs4 : CC.cp_regs G.cp4 = sr_id.
Proof. vmc_refl. Qed.

Lemma regs_ok_upd11 : forall E sr (R : bvmap 5 word) e, regs_ok E sr R -> getr R 11%bv = edenot E e -> regs_ok E (sr_upd sr 11 e) R.
Proof.
  intros E sr R e HR He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) 11) as [e11|ne].
    + assert (r = 11%bv) as -> by (rewrite <- (CC.reg_of_ridx r), e11; apply bv_eq; reflexivity). exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
Qed.
Definition FR : expr * Z * Z := (FE, 1, -96).
Definition FFS : list (list (expr * Z * Z)) := [[]; []; []; []; []; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]; [FR]].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition ISHL : list kentry := [KZero (SA (ELit 0) ISH2) (ELit 1)].
Definition NEWS_F : list kentry := STAT ++ [KWord (SA FE 120) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition SETEC_W : list SGP.region := [(EE, 0, ELit 16); (ELit 0, GD, ELit 2); (ELit 0, AXT, ELit 544)].
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 48 (nth i G.BLS []) (nth i FFS []) 1 53 48 X || CC.has_cell ISHL X)%bool.
Definition has := CC.has_cell.

Definition CPF0 : list SGP.region := [(EVar 2, -1120, ELit 1120); (PE, 211, ELit 1)].
Definition FRM3 : list SGP.region := [(FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].
Definition FLR : SGP.region := (FLE, 0, ELit 1).
Definition CPF2 : list SGP.region := CPF0 ++ FRM3.
Definition CPF4 : list SGP.region := CPF0 ++ FRM3 ++ [FLR].
Definition KZF : kentry := KZero (SA (CHA.SRL3 FE) SBz) (ELit 16).

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in let a := arm i in
      if Z.eqb pc PC_SM then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_SM && Nat.leb i 4 && Nat.eqb j (i + 5) && CBA.regions_eqb (CC.cp_F c) CPF0
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj
                                             (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => (Nat.eqb (CH2.ci_nx ci) 48 && Z.eqb (CH2.ci_csp ci) (-96))%bool | None => false end)%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_ERRH then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_ERRH && Nat.leb 5 i && Nat.leb i 9 && Nat.eqb j (i + 5) && Nat.ltb 53 (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) CPF2
                                  && CC.has_cell (CC.cp_know c) KZF
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 16 0 [] (nth i FFS []) [] NEWS_F (Some (ELit 0)) c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => Z.eqb (CH2.ci_csp ci) (-96) | None => false end
                                  && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD FE (ELit (slot a)))
                                  && has cells (KWord (SA FE (slot a)) 4 (ELit (acode a))) && has cells (KWord (SA (CHA.SRL3 FE) (SBz + slot a / 8)) 1 (ELit 4)) && has cells (KWord (SA FE 120) 8 FLE))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_SETEC then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_SETEC && Nat.leb 10 i && Nat.leb i 14 && Nat.eqb j (i + 5) && Nat.ltb 53 (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) CPF2
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 1024 0 [] (nth i FFS []) SETEC_W NEWS_F None c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => Z.eqb (CH2.ci_csp ci) (-96) | None => false end
                                  && CL.ps_reg_is ps 10 EE && CL.ps_reg_is ps 11 (ELit (acode a)) && has cells (KWord (SA FE 120) 8 FLE) && has cells (KWord (SA PE 211) 1 (ELit 0)))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && Nat.leb 15 i && Nat.leb i 19 && Nat.ltb 53 (CC.cp_nx c)
         && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fle => expr_eqb fle FLE | None => false end
         && has cells (KWord (SA FLE 0) 1 (ELit 0)) && CBA.regions_eqb (CC.cp_F c) CPF4 && has cells (KWord (SA PE 211) 1 (ELit 0)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Lemma ffs_i : forall i, (5 <= i <= 19)%nat -> nth i FFS [] = [FR].
Proof. intros i Hi. do 20 (destruct i as [|i]; [first [reflexivity | exfalso; clear - Hi; lia] |]). exfalso; clear - Hi; lia. Qed.
Lemma ffs_0 : forall i, (i <= 4)%nat -> nth i FFS [] = [].
Proof. intros i Hi. do 5 (destruct i as [|i]; [reflexivity|]). exfalso; clear - Hi; lia. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. do 20 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma arm_ret : forall i, arm (i + 5) = arm i.
Proof. intros i. unfold arm. rewrite Nat.Div0.add_mod, Nat.Div0.mod_same, Nat.add_0_r, Nat.Div0.mod_mod. reflexivity. Qed.
Lemma slot_rng : forall a, (a <= 4)%nat -> 32 <= slot a <= 96 /\ slot a mod 8 = 0 /\ 0 <= acode a < 2 ^ 31 /\ acode a <> 24 /\ 1 <= acode a <= 31.
Proof. intros a Ha. do 5 (destruct a as [|a]; [cbn; clear; lia|]). exfalso; clear - Ha; lia. Qed.
End TCA.

Section TceOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL0 : icpt_layout.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI2 : Forall (fun r : Z * Z => TCA.SLOT2 + 8 <= fst r \/ snd r <= TCA.SLOT2) (icl_poison IL0).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ERRH_OK : PMSA.errh_specA L ar HI TCA.PC_ERRH.
Hypothesis SETEC_OK : PMSA.set_ec_specA L ar HI IC TCA.PC_SETEC.

Definition hid (P : Prop) : Prop := P.

Lemma uv_add_lit : forall (E1 : env) (F k : Z) (v : nat), bv_unsigned (ev E1 v) = F -> 0 <= F -> 0 <= k -> F + k < 2 ^ 64 -> CL5A.uv E1 (EAlu Instr.ALU_ADD (EVar v) (ELit k)) = F + k.
Proof.
  intros E1 F k v Hv F0 K0 FK. unfold CL5A.uv. cbn. rewrite bv_add_unsigned, Hv. rewrite L5.unsigned_lit; [|lia].
  unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem tce_ok : PMSA.translate_conv_errc_specA L ar HI IC 815932.
Proof.
  unfold PMSA.translate_conv_errc_specA.
  intros LB FF LK cr A P E cls sp r g. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha2 & HCLS & Hsp32 & Hstksh & A12 & A13 & OP & OE & AP2 & HEC & HLS & HG) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.TCE_SCR, PMSA.SETEC_SCR, PMSA.fobj in *. change (96 + 1024) with 1120 in *.
  destruct OP as (Pfr & P8 & Psh). destruct OE as (Efr & E8 & Esh). unfold PMSA.u64 in A12, A13.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : TCA.IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold TCA.IMGHI, FS_BYTES; clear; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5. change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (CLS64 : 0 <= cls < 2 ^ 64) by (clear - HCLS; lia).

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => @nil (bv 8))).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 P) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 cls) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 E) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = cls) by (rewrite V11; apply u64_of_Z; exact CLS64).
  assert (U12 : bv_unsigned (ev E0 12) = E) by (rewrite V12; apply u64_of_Z; clear - Q3 Q6; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 1120) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(P + 211, 1); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES)]). set (Wo := [(P + 211, 1); (E, 16)]).
  assert (WINC : incl Wo WW) by (intros y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [exact (CL5A.infr_wok L ar LB FF sp _ P 272 a RFx Pfr ltac:(clear - Hin; lia)) | exact (CL5A.infr_wok L ar LB FF sp _ E 16 a RFx Efr Hin)]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U10, ?U12 in Ha; rewrite u64_of_Z in Ha by (clear; lia).
    - exists (P + 211, 1). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia].
    - exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U10, ?U12 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
    - destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) P 272 a RFx Pfr ltac:(clear - Ha; lia)) as (G1 & G2 & G3). split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
    - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (CL5A.shreg_in_shadow P 34 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
      split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
    - destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) E 16 a RFx Efr ltac:(clear; lia) (CL5A.shreg_in_shadow E 2 a E8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3).
      split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[<-|[]]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (inW := fun a : Z => exists w, In w WW /\ L5.in_rng w a).
  assert (FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
  { intros a Hf. assert (RG : 65536 <= a < 7028736) by (destruct Hf as (iv & Hiv & Hr); cbn in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]); destruct Hiv).
    split; [exact RG|]. intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - RG; lia | exact (FOOTC a Hf)]. }
  assert (WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                             /\ ((a = P + 211 \/ E <= a < E + 16) \/ a < 7028736)).
  { intros a (w & Hw & Hin). unfold L5.in_rng in Hin. unfold WW in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin.
    - split; [clear - Hin O3; lia|]. split; [clear - Hin O4; lia|]. split; [unfold hid in O5; clear - Hin O5; lia|].
      split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' P 272 a Pfr ltac:(clear - Hin; lia))) | left; left; clear - Hin; lia].
    - split; [clear - Hin Q3; lia|]. split; [clear - Hin Q4; lia|]. split; [unfold hid in Q5; clear - Hin Q5; lia|].
      split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' E 16 a Efr Hin)) | left; right; exact Hin].
    - destruct (FOOTCL a) as (RG & CLa); [exists (0x690388, 0x69038a); split; [left; reflexivity | cbn [fst snd]; cbn in Hin; clear - Hin; lia]|].
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; clear - RG; lia].
    - destruct (FOOTCL a) as (RG & CLa); [exists (0x6b1de0, 0x6b2000); split; [do 5 right; left; reflexivity | cbn [fst snd]; cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin; lia]|].
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; clear - RG; lia]. }
  assert (INWE : forall y, E <= y < E + 16 -> inW y) by (intros y Hy; exists (E, 16); split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Hy; lia]).

  assert (KSHO : forall o n a, CL5A.ainfr FF o n -> 0 < n -> o + n <= 2 ^ 47 -> in_shadow_of o n a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros o n a Hfr Hn Hon Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o n a RFx Hfr Hn Ha) as (G1 & G2 & _).
    destruct (CL5A.infr_rng L ar LB FF o n RFx Hfr Hn) as (_ & _ & X3 & _). pose proof (SHR o n a X3 Hn Hon Ha) as SRa.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _). clear - C2 SRa. lia. }
  assert (KP : forall a, P <= a < P + 272 -> a <> P + 211 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha Hne. destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) P 272 a RFx Pfr Ha) as (G1 & G2 & _). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|].
    intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & _ & _ & [[Hp|He]|Himg]); [exact (Hne Hp) | unfold PMLA.apart in AP2; clear - He Ha AP2; lia | clear - Himg Ha O1 FSLO; lia]. }
  assert (AL : (sp - 1120) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 1120) with ((2 * (sp / 16) - 140) * 8) by lia; apply Z_mod_mult).
  assert (KSTK : forall a, S (sp - 1120) <= a < S (sp - 1120) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 1120)) / 8 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (PTA.stksh_rng ar sp 1120 a ltac:(clear - S2; lia) AL C8 (proj2 SP1) (CHA.wf_top _ _ _ _ _ _ _ _ WFT) ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [do 4 right; left; exact G2|]. intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _).
    unfold in_shadow_of, S, SB in G2. clear - Hin G2 C2 CL. lia. }

  assert (DECW : forall a, a < 7028736 -> inW a \/ L5.outside WW a).
  { intros a Ha. destruct (Z_le_dec 0x690388 a) as [G1|G1]; [destruct (Z_lt_dec a 0x69038a) as [G2|G2]|].
    - left. exists (PMLA.ERRCAT_GUARD IC, 2). split; [right; right; left; reflexivity | unfold L5.in_rng; cbn; clear - G1 G2; lia].
    - destruct (Z_le_dec 0x6b1de0 a) as [G3|G3]; [destruct (Z_lt_dec a 0x6b2000) as [G4|G4]|].
      + left. exists (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES). split; [do 3 right; left; reflexivity | unfold L5.in_rng, PmIcptIfaceA.ATEXIT_TAB_BYTES; cbn; clear - G3 G4; lia].
      + right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G4; lia].
      + right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G3; lia].
    - right. intros w Hw Hin. unfold WW in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
      destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G1; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G1; lia]. }
  assert (PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                   \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                   \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a).
  { intros a Ha. pose proof PMTA.C_cboth_wf as [T1 T2 T3 _ T5 T6 T7 T8 _ _ T9]. unfold PMTA.cell_in_foot, PmIcptIfaceA.ATEXIT_TAB_BYTES in *.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
      [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha | apply (proj2 (proj2 T7)); exact Ha | apply (proj2 (proj2 T8)); exact Ha
      | apply (proj2 (proj2 T1)); exact Ha | subst a; apply (proj2 (proj2 T2)); clear; lia | apply (proj2 (proj2 T3)); exact Ha | apply (proj2 (proj2 T9)); exact Ha]. }
  assert (IMGCL : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
  { intros a [Ha|Ha]; [|exact (FOOTCL a Ha)]. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha. split; [clear - Ha; lia|].
    intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia]. }

  assert (WFR : forall a F, inW a -> ar_fs ar <= F -> fframes_apart F 128 FF -> ~ (F <= a < F + 128)).
  { intros a F Ha HF0 FAP Hin. destruct (WCL a Ha) as (_ & _ & _ & _ & [[Hp|He]|Himg]).
    - destruct Pfr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP Hp Hin F1 F2. lia.
    - destruct Efr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP He Hin F1 F2. lia.
    - clear - Himg Hin HF0 FSLO. lia. }

  assert (HI0 : exists i0 : nat, (i0 <= 4)%nat /\ (((i0 <= 3)%nat /\ cls = Z.of_nat i0 + 1) \/ (i0 = 4%nat /\ 5 <= cls <= 6)) /\ PMSA.tce_code cls = TCA.acode i0).
  { unfold PMSA.tce_code. destruct (Z.eq_dec cls 1) as [->|N1]; [exists 0%nat; split; [clear; lia | split; [left; split; [clear; lia | reflexivity] | reflexivity]]|].
    destruct (Z.eq_dec cls 2) as [->|N2]; [exists 1%nat; split; [clear; lia | split; [left; split; [clear; lia | reflexivity] | reflexivity]]|].
    destruct (Z.eq_dec cls 3) as [->|N3]; [exists 2%nat; split; [clear; lia | split; [left; split; [clear; lia | reflexivity] | reflexivity]]|].
    destruct (Z.eq_dec cls 4) as [->|N4]; [exists 3%nat; split; [clear; lia | split; [left; split; [clear; lia | reflexivity] | reflexivity]]|].
    exists 4%nat. split; [clear; lia|]. split; [right; split; [reflexivity | clear - HCLS N1 N2 N3 N4; lia]|].
    destruct (Z.eqb_spec cls 1); [exfalso; exact (N1 e)|]. destruct (Z.eqb_spec cls 2); [exfalso; exact (N2 e)|]. destruct (Z.eqb_spec cls 3); [exfalso; exact (N3 e)|]. destruct (Z.eqb_spec cls 4); [exfalso; exact (N4 e)|]. reflexivity. }
  destruct HI0 as (i0 & Hi04 & Hi0 & HCODE).

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (AGX := fun (i : nat) (M1 : word -> option byte) => forall a, inW a -> a <> P + 211 -> (i <= 14)%nat -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  set (FLF := fun (E1 : env) => ar_fs ar <= CL5A.uv E1 TCA.FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF sp (CH.hd_scr G.HDECL) (CL5A.uv E1 TCA.FLE)).
  set (ECF := fun (i : nat) (M1 : word -> option byte) => PMLA.ec_at (hl_segs L) IC M1 E (TCA.acode (TCA.arm i)) /\ PMLA.ls_ok (hl_segs L) IC (PML.regJ g) M1).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               AGX i M1 /\ ((i <= 4)%nat \/ FLF E1) /\ ((15 <= i)%nat -> ECF i M1) /\ TCA.arm i = i0).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg IL. pose proof (CH2.leaves_all_sound _ _ _ TCA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  assert (Hc0 : nth_error G.CPS i0 = Some (nth i0 G.CPS G.cp0) /\ CC.cp_pc (nth i0 G.CPS G.cp0) = 815932) by (do 5 (destruct i0 as [|i0]; [split; reflexivity|]); exfalso; clear - Hi04; lia).
  destruct Hc0 as (Hc0 & HPC0). rewrite <- HPC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS TCA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact TCA.heap_ok.
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ TCA.leaf_ok _ _ _ _ _ IL) as X. unfold TCA.leaf_chk in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hci & _); exact Hci).
    destruct (Z.eqb_spec pc TCA.PC_SM) as [->|Hne1].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yj]. apply andb_prop in X as [Y0 Yi].
      apply Z.eqb_eq in Y0. apply Nat.leb_le in Yi. apply Nat.eqb_eq in Yj. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
      assert (FFSi : nth i TCA.FFS [] = []) by (apply TCA.ffs_0; exact Yi).
      assert (FFSj : nth j TCA.FFS [] = [TCA.FR]) by (apply TCA.ffs_i; rewrite Yj; clear - Yi; lia).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXW & _ & _ & HARM)].
      pose proof (CRA.smalloc_leaf_u L ar C HI HIok LYI LYR TCA.IMGHI LYH GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS TCA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil (fun X0 => In X0 TCA.ISHL) 1 (List.filter (TCA.sm_ok ps0 i) (CC.cp_know cj)) i c ps0 j cj ci) as SML.
      rewrite (L5A.aly_scr_sm L C LAY), (L5A.aly_sm1 L C LAY) in SML.
      refine (SML ltac:(right; left; reflexivity) Hcj Hchk Y0 _ _ _ _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
      - rewrite FFSi, FFSj, Ynx, Ycsp. reflexivity.
      - rewrite !TCA.bls_i. reflexivity.
      -
        intros X0 HX0. apply filter_In in HX0 as [_ HX0]. unfold TCA.sm_ok in HX0. rewrite Ynx.
        apply orb_prop in HX0. destruct HX0 as [HX0|HX0]; [left; exact HX0 | right; exact (CC.has_cell_In _ _ HX0)].
      -
        intros X0 E2 LB2 FF2 LK2 cr2 A2 M2 m2 HX0 HH2. cbn [In TCA.ISHL] in HX0.
        destruct HX0 as [<-|[]].
        destruct (ISH _ _ _ _ _ _ _ HH2 TCA.SLOT2 8 ltac:(rewrite ILO; unfold TCA.SLOT2; clear; lia) ltac:(rewrite IHI; unfold TCA.SLOT2; clear; lia) ltac:(clear; lia) POI2) as [BZ BA].
        assert (ISX : in_shadow_of TCA.SLOT2 8 TCA.ISH2) by (unfold in_shadow_of, S, TCA.SLOT2, TCA.ISH2, SB; clear; split; reflexivity).
        eapply CL5A.kzero_intro with (A := TCA.ISH2) (N := 1); [reflexivity | reflexivity | unfold TCA.ISH2; clear; lia | unfold TCA.ISH2; clear; lia | unfold TCA.ISH2; clear; lia |].
        intros jj Hjj. replace (TCA.ISH2 + jj) with TCA.ISH2 by (clear - Hjj; lia). apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ ISX) | exact (BZ _ ISX)].
      - rewrite FFSi. cbn [length]. clear. lia.
      - intros Ea Eb cr1 Hc _. exact Hc.
      -
        intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. rewrite FFSi, TCA.bls_i in SMF. cbn [CH2.den CHA.denF map app] in SMF.
        destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. rewrite Ynx.
        pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
        assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
        assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
        unfold XI. split; [|split; [right | split; [intros H15; exfalso; rewrite Yj in H15; clear - H15 Yi; lia | rewrite Yj, TCA.arm_ret; exact HARM]]].
        + intros a Ha Hnw _. destruct (WCL a Ha) as (C0 & C1 & C2 & C3 & _).
          rewrite (proj1 Zp a ltac:(clear - C0 C1 CL SP1; lia) (C3 _ _)). rewrite <- (HXW a Ha Hnw ltac:(clear - Yi; lia)).
          apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite L5.unsigned_lit by (clear - C0 C1 CL SP1; lia).
          rewrite YF. unfold TCA.CPF0, TCA.PE; cbn [app]; repeat (apply Forall_cons); try (apply Forall_nil);
            cbn [fst snd]; unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite ?W2, ?W10; rewrite u64_of_Z by (clear; lia); first [clear - C1 S2; lia | clear - Hnw; lia].
        + pose proof (CH2.retEx_ghost E' 48 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G48. cbn [nth Nat.add] in G48.
          assert (T48 : CL5A.uv (CH2.retEx E' 48 [Z_to_bv 64 fl] R2) TCA.FLE = fl).
          { unfold CL5A.uv, TCA.FLE. cbn [edenot]. rewrite G48. apply u64_of_Z. unfold FS_BYTES in Z7. destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3. clear - Z7 G0 G3 CL SP1. lia. }
          unfold FLF. rewrite T48. split; [unfold FS_BYTES in Z7; exact Z7|]. intros Hc. apply Z8.
          eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia]. }

    assert (FRM : forall E1 A1 M1 m1, (5 <= i <= 19)%nat ->
              CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M1 m1 ->
              let F := CL5A.uv E1 TCA.FE in
              CHA.curB LB G.BLS i E1 = LB /\ CHA.curF FF sp TCA.FFS i E1 = (F, 1, sp + -96 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
              0 <= F /\ F + 128 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + 11571200 /\ fframes_apart F 128 FF).
    { intros E1 A1 M1 m1 Hi HA. cbv zeta.
      assert (HcB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite TCA.bls_i; reflexivity).
      assert (HcF : CHA.curF FF sp TCA.FFS i E1 = (CL5A.uv E1 TCA.FE, 1, sp + -96 + 32) :: FF) by (unfold CHA.curF; rewrite (TCA.ffs_i i Hi); reflexivity).
      pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _). rewrite HcB, HcF in HHa.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
      destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 1) with 128 in G2.
      destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
      destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFa _ (or_introl eq_refl)) as (_ & _ & _ & _ & _ & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP. rewrite Z.eqb_refl in FAP. change (ff_bytes 1) with 128 in FAP.
      split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact (CHA.mod8_of_64 _ G3)|].
      split; [clear - G1 G2 G4; lia|]. split; [exact G1|]. split; [exact G2|]. intros f Hf. apply FAP. apply in_or_app. left. exact Hf. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS TCA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (LEAFK : forall E1 A1 M1 m1 E' R' M' m', (5 <= i <= 19)%nat -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M1 m1 ->
              env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> (53 < CC.cp_nx c)%nat ->
              (CC.cp_F c = TCA.CPF2 \/ CC.cp_F c = TCA.CPF4) -> ar_fs ar <= CL5A.uv E1 TCA.FLE ->
              bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = P /\ bv_unsigned (ev E' 12) = E
              /\ bv_unsigned (ev E' 53) = CL5A.uv E1 TCA.FE /\ bv_unsigned (ev E' 48) = CL5A.uv E1 TCA.FLE
              /\ (forall X0, TCA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
              /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
              /\ (forall a, 0 <= a < 7028736 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))).
    { intros E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y53 YF HFL0.
      pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
      assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); unfold GT.NF; apply Nat.ltb_lt; exact Hn).
      destruct (FRM E1 A1 M1 m1 Hi HA) as (_ & _ & _ & F0 & F1 & _ & F2 & F3 & _).
      split; [rewrite (FZ 2%nat eq_refl); exact U2|]. split; [rewrite (FZ 10%nat eq_refl); exact U10|]. split; [rewrite (FZ 12%nat eq_refl); exact U12|].
      split; [rewrite <- (proj1 Hag 53%nat) by exact Y53; reflexivity|]. split; [rewrite <- (proj1 Hag 48%nat) by (clear - Y53; lia); reflexivity|].
      split; [intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
      split; [intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned|].
      intros a Ha. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite L5.unsigned_lit by (clear - Ha; lia).
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2). assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W53 : bv_unsigned (ev E' 53) = CL5A.uv E1 TCA.FE) by (rewrite <- (proj1 Hag 53%nat) by exact Y53; reflexivity).
      assert (W48 : bv_unsigned (ev E' 48) = CL5A.uv E1 TCA.FLE) by (rewrite <- (proj1 Hag 48%nat) by (clear - Y53; lia); reflexivity).
      pose proof (Z.div_pos (CL5A.uv E1 TCA.FE) 8 F0 ltac:(clear; lia)) as D0.
      destruct YF as [-> | ->]; unfold TCA.CPF4, TCA.CPF2, TCA.CPF0, TCA.FRM3, TCA.FLR, TCA.PE, TCA.FE, TCA.FLE, TCA.SBz; cbn [app]; repeat (apply Forall_cons); try (apply Forall_nil);
        cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; unfold CL5A.uv in W53, W48, D0, F3, HFL0; rewrite ?W2, ?W10, ?W53, ?W48;
        rewrite u64_of_Z by (clear; lia); clear - Ha S2 CL O1 FSLO F3 D0 HFL0; lia. }

    assert (NEWSF : forall E' E2 A1 A2 M' m' M2 m2 LKa LKb cra crb LBa F fl,
              ri_inv HI LB ((F, 1, sp + -96 + 32) :: FF) LKa cra A1 M' (vml_of m') -> ri_inv HI LBa ((F, 1, sp + -96 + 32) :: FF) LKb crb A2 M2 (vml_of m2) ->
              H_off_segments (hl_segs L) (ahid A1 m') ->
              0 <= F -> F + 128 <= 140737488355328 -> ar_fs ar <= F -> F + 128 <= ar_fs ar + 11571200 -> ar_fs ar <= fl < ar_fs ar + 11571200 ->
              bv_unsigned (ev E' 53) = F -> bv_unsigned (ev E' 48) = fl -> bv_unsigned (ev E2 53) = F -> bv_unsigned (ev E2 48) = fl ->
              kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA TCA.FE 120) 8 TCA.FLE) ->
              forall X0, In X0 TCA.NEWS_F -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E' E2 A1 A2 M' m' M2 m2 LKa LKb cra crb LBa F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W53 W48 T53 T48 KFL X0 HX0.
      unfold TCA.NEWS_F, TCA.STAT in HX0. cbn [app In] in HX0.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
      assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
      { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _); unfold FS_BYTES in G3; clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
      destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      -
        pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + 120) KFL ltac:(unfold estart, TCA.FE; cbn [a_base a_off edenot]; rewrite W53; reflexivity)) as G0.
        apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, TCA.FLE in G0. cbn [edenot] in G0. rewrite W48 in G0.
        pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 1 (sp + -96 + 32) (sp + -96 + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
        change (ff_bytes 1) with 128 in FP. replace (F + 128 - 8) with (F + 120) in FP by (clear; lia). specialize (FP G0).
        eapply CL5.kword64_intro with (A := F + 120) (z := fl); [unfold estart, TCA.FE; cbn [a_base a_off edenot]; rewrite T53; reflexivity | clear - F0; lia | clear - F1; lia | |].
        + unfold TCA.FLE. cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E2 48)). f_equal. exact T48.
        + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
      - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart, TCA.FLE; cbn [a_base a_off edenot]; rewrite T48; clear; lia | reflexivity | | | |].
        + destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _). clear - HFL1 G0. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy HFL1; lia))).
          pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy HFL1. lia. }

    assert (AGW2 : forall E1 A1 M1 m1 E' R' M' m', (5 <= i <= 19)%nat -> (i <= 14)%nat ->
              CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M1 m1 -> AGX i M1 ->
              env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> CC.cp_F c = TCA.CPF2 -> (53 < CC.cp_nx c)%nat -> ar_fs ar <= CL5A.uv E1 TCA.FLE ->
              forall a, inW a -> a <> P + 211 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros E1 A1 M1 m1 E' R' M' m' Hi H14 HA HXW Hag HLF YF Y53 HFL0 a Ha Hnw.
      destruct (FRM E1 A1 M1 m1 Hi HA) as (_ & _ & _ & F0 & F1 & F8 & F2 & F3 & F4 & FAP).
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y53 (or_introl YF) HFL0) as (W2 & W10 & _ & W53 & _).
      destruct (WCL a Ha) as (C0' & C1 & C2 & C3 & _). rewrite <- (HXW a Ha Hnw H14).
      apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - C0' C1 CL SP1; lia).
      pose proof (WFR a _ Ha F3 FAP) as NF0.
      pose proof (Z.div_pos (CL5A.uv E1 TCA.FE) 8 F0 ltac:(clear; lia)) as D0. assert (D1 : CL5A.uv E1 TCA.FE / 8 <= 2 ^ 44 - 16) by (apply Z.div_le_upper_bound; clear - F1; lia).
      unfold TCA.CPF2, TCA.CPF0, TCA.FRM3, TCA.PE, TCA.FE, TCA.SBz. cbn [app]. repeat (apply Forall_cons); try (apply Forall_nil);
        cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; unfold CL5A.uv, TCA.FE in W53, D0, D1, NF0; rewrite ?W2, ?W10, ?W53;
        rewrite u64_of_Z by (clear; lia); clear - C1 C2 S2 Hnw NF0 D0 D1; lia. }
    assert (ARM4 : (TCA.arm i <= 4)%nat) by (unfold TCA.arm; pose proof (Nat.mod_upper_bound i 5 ltac:(clear; lia)); clear - H; lia).
    destruct (TCA.slot_rng (TCA.arm i) ARM4) as (SL1 & SL8 & SC1 & SC24 & SC31). set (a := TCA.arm i) in *.
    destruct (Z.eqb_spec pc TCA.PC_ERRH) as [->|Hne3].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y13]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9].
      apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [X YKZ]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Yj]. apply andb_prop in X as [X Yi2].
      apply andb_prop in X as [Y0 Yi1].
      apply Z.eqb_eq in Y0. apply Nat.leb_le in Yi1, Yi2. apply Nat.eqb_eq in Yj. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y9 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y9. rename Y9 into Ycsp.
      assert (Hi : (5 <= i <= 19)%nat) by (clear - Yi1 Yi2; lia).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXW & HXF & _ & HARM)].
      destruct HXF as [HXF|(HFL1 & HFL2)]; [exfalso; clear - HXF Yi1; lia|].
      destruct (FRM E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP). set (F := CL5A.uv E1 TCA.FE) in *. set (fl := CL5A.uv E1 TCA.FLE) in *.
      assert (FFSi : nth i TCA.FFS [] = [TCA.FR]) by (apply TCA.ffs_i; exact Hi).
      assert (FFSj : nth j TCA.FFS [] = [TCA.FR]) by (apply TCA.ffs_i; rewrite Yj; clear - Yi1 Yi2; lia).
      rewrite FFSi in Hchk.
      refine (CALLEE TCA.PC_ERRH 16 0%nat [] [] TCA.NEWS_F (Some (ELit 0)) 0 i c ps0 j cj ci Hcj ltac:(rewrite FFSi; exact Hchk) Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite FFSi, FFSj; reflexivity | rewrite FFSi; cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y3 (or_introl YF) (proj1 HFL1)) as (W2 & W10 & W12 & W53 & W48 & CELL & REG & LOWF). fold F in W53. fold fl in W48.
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M' m' HA') as Hoff.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
      assert (UT : CL5A.uv E' (EAlu Instr.ALU_ADD TCA.FE (ELit (TCA.slot a))) = F + TCA.slot a) by (apply (uv_add_lit E' F (TCA.slot a) 53 W53); clear - F0 F1 SL1; lia).
      eexists. eexists. split; [exact (ERRH_OK LB ((F, 1, sp + -96 + 32) :: FF) LK1 cr A1 (F + TCA.slot a) (TCA.acode a) (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
      {
        unfold PMSA.a1, PMSA.ainfr, PMSA.u32.
        split; [exact (REG 11%nat _ (F + TCA.slot a) Y10 UT)|].
        split; [exists (F, 1, sp + -96 + 32); split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (ff_bytes 1) with 128; clear - SL1; lia]|].
        split; [rewrite <- Zplus_mod_idemp_l, F8; exact SL8|].
        split.
        -
          pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (S F + TCA.slot a / 8) (CELL _ Y12) ltac:(rewrite CL5A.estart_srl3; unfold CL5A.uv, S, SB, TCA.SBz, TCA.FE; cbn [edenot]; rewrite W53; clear; lia)) as G0.
          apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia).
          rewrite (CL5A.S_add_al F (TCA.slot a) F8). apply (CL5A.u8_byte_at (hl_segs L)); [|exact G0].
          apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF).
          pose proof (proj1 (Forall_forall _ _) (proj2 HAt) _ (CC.has_cell_In _ _ YKZ)) as KZ.
          pose proof (CL5A.kzero_elim (hl_segs L) E1 _ _ _ (S F) 16 KZ ltac:(rewrite CL5A.estart_srl3; unfold S, SB, TCA.SBz; reflexivity) eq_refl (TCA.slot a / 8) ltac:(clear - SL1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as BZ.
          apply CL5A.byte_full in BZ. unfold byte_at in BZ. rewrite BZ. discriminate.
        - split; [|exact SC1].
          pose proof (CL5A.kword32_elim (hl_segs L) E' _ _ _ (F + TCA.slot a) (CELL _ Y11) ltac:(unfold estart, TCA.FE; cbn [a_base a_off edenot]; rewrite W53; reflexivity)) as G0.
          apply (CL5A.u32_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear - SC1; lia). exact G0. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      destruct HV as (_ & _ & HV3 & _).
      assert (T53 : bv_unsigned (ev E2 53) = F) by (rewrite <- (proj1 Hag2 53%nat) by (clear - HV3 Y3; lia); exact W53).
      assert (T48 : bv_unsigned (ev E2 48) = fl) by (rewrite <- (proj1 Hag2 48%nat) by (clear - HV3 Y3; lia); exact W48).
      split; [unfold PMSA.a0 in Ha0'; cbn [edenot]; rewrite Ha0'; rewrite (proj2 (Z.eqb_neq _ _) SC24); reflexivity|].
      split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a' []|]. split; [intros w a' []|].
      split; [unfold CHA.curB; rewrite TCA.bls_i; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|].
      split.
      { unfold XI. split; [|split; [right | split; [intros H15; exfalso; rewrite Yj in H15; clear - H15 Yi2; lia | rewrite Yj, TCA.arm_ret; exact HARM]]].
        - intros a' Ha Hnw H14. destruct (WCL a' Ha) as (C0' & C1 & C2 & C3 & _). rewrite (proj1 HP a'); [|split; [clear - C0' C1 CL SP1; lia | split; [|intros w []]]].
          2:{ eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact (C3 _ _)]. }
          exact (AGW2 E1 A1 M1 m1 E' R' M' m' Hi ltac:(clear - Yi2; lia) HA HXW Hag HLF YF Y3 (proj1 HFL1) a' Ha Hnw).
        - unfold FLF. replace (CL5A.uv E2 TCA.FLE) with fl by (unfold CL5A.uv, TCA.FLE; cbn [edenot]; symmetry; exact T48). split; [exact HFL1 | exact HFL2]. }
      intros X0 HX0 _. exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W53 W48 T53 T48 (CELL _ Y13) X0 HX0). }
    destruct (Z.eqb_spec pc TCA.PC_SETEC) as [->|Hne4].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10r]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9].
      apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Yj]. apply andb_prop in X as [X Yi2]. apply andb_prop in X as [Y0 Yi1].
      apply Z.eqb_eq in Y0. apply Nat.leb_le in Yi1, Yi2. apply Nat.eqb_eq in Yj. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y9 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y9. rename Y9 into Ycsp.
      assert (Hi : (5 <= i <= 19)%nat) by (clear - Yi1 Yi2; lia). assert (H14 : (i <= 14)%nat) by exact Yi2.
      assert (FFSi : nth i TCA.FFS [] = [TCA.FR]) by (apply TCA.ffs_i; exact Hi).
      assert (FFSj : nth j TCA.FFS [] = [TCA.FR]) by (apply TCA.ffs_i; rewrite Yj; clear - Yi1 Yi2; lia).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXW & HXF & _ & HARM)].
      destruct HXF as [HXF|(HFL1 & HFL2)]; [exfalso; clear - HXF Yi1; lia|].
      destruct (FRM E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP). set (F := CL5A.uv E1 TCA.FE) in *. set (fl := CL5A.uv E1 TCA.FLE) in *.
      rewrite FFSi in Hchk.
      refine (CALLEE TCA.PC_SETEC 1024 0%nat [] TCA.SETEC_W TCA.NEWS_F None 0 i c ps0 j cj ci Hcj ltac:(rewrite FFSi; exact Hchk) Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite FFSi, FFSj; reflexivity | rewrite FFSi; cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y3 (or_introl YF) (proj1 HFL1)) as (W2 & W10 & W12 & W53 & W48 & CELL & REG & LOWF). fold F in W53. fold fl in W48.
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M' m' HA') as Hoff.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
      pose proof (AGW2 E1 A1 M1 m1 E' R' M' m' Hi H14 HA HXW Hag HLF YF Y3 (proj1 HFL1)) as AGW5.
      set (Sg := fun a' => CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a' \/ (inW a' /\ a' <> P + 211)).
      assert (AG : forall a', Sg a' -> M' (Z_to_bv 64 a') = M (Z_to_bv 64 a')) by (intros a' [Ha|(Ha & Hnw)]; [exact (Hfr1 a' Ha) | exact (AGW5 a' Ha Hnw)]).
      eexists. eexists. split; [exact (SETEC_OK LB ((F, 1, sp + -96 + 32) :: FF) LK1 cr A1 E (TCA.acode a) (sp + CH2.ci_csp ci) (CC.cp_pc cj) g)|]. split.
      {
        unfold PMSA.a0, PMSA.a1, PMSA.fobj, PMSA.stksh, PMSA.ls_ok, PMSA.SETEC_SCR.
        split; [exact (REG 10%nat _ E Y10 ltac:(cbn [edenot]; exact W12))|].
        split; [exact (REG 11%nat _ (TCA.acode a) Y10r ltac:(cbn [edenot]; apply L5.unsigned_lit; clear - SC1; lia))|].
        split; [exact SC31|].
        split.
        { apply (CL5A.defined_same M M' E 16); [|exact (proj1 (proj2 HEC))]. intros y Hy. apply AGW5; [apply INWE; exact Hy | unfold PMLA.apart in AP2; clear - Hy AP2; lia]. }
        split.
        { split; [destruct Efr as (f & Hf & G1 & G2); exists f; split; [right; exact Hf | exact (conj G1 G2)]|]. split; [exact E8|].
          intros jj Hjj. unfold byte_at. rewrite (Hfr1 _ (KSHO E 16 (S E + jj) Efr ltac:(clear; lia) Q6 (CL5A.shreg_in_shadow E 2 (S E + jj) E8 ltac:(clear; lia) ltac:(unfold S; clear - Hjj; lia)))).
          exact (Esh jj Hjj). }
        split.
        { apply (PTA.stksh_mono ar M' sp 1120 (sp + CH2.ci_csp ci) 1024); [| exact AL | | rewrite Ycsp; clear; lia].
          - apply (PTA.stksh_ag ar M M' sp 1120); [|exact Hstksh]. intros a' Ha. exact (Hfr1 a' (KSTK a' Ha)).
          - rewrite Ycsp. clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D.
            replace (16 * (sp / 16) + -96 - 1024) with ((2 * (sp / 16) - 140) * 8) by lia. apply Z_mod_mult. }
        split; [|exact HG].
        apply (PTA.ls_ok_ag (hl_segs L) IC M M' Sg AG g HG); [|intros a' Ha; exact (PTKF a' Ha) | exact HLS].
        intros a' Ha. destruct (IMGCL a' Ha) as (RG & CLa). split; [clear - RG; lia|]. destruct (DECW a' (proj2 RG)) as [Hw|Ho].
        - right. split; [exact Hw | clear - RG O1 FSLO; lia].
        - left. split; [clear - RG; lia|]. split; [exact (CLa _ _) | exact Ho]. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (XEC & XLS & Ha0' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      destruct HV as (_ & _ & HV3 & _).
      assert (T53 : bv_unsigned (ev E2 53) = F) by (rewrite <- (proj1 Hag2 53%nat) by (clear - HV3 Y3; lia); exact W53).
      assert (T48 : bv_unsigned (ev E2 48) = fl) by (rewrite <- (proj1 Hag2 48%nat) by (clear - HV3 Y3; lia); exact W48).
      split; [exact I|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      split.
      { intros w a' Hw Hin. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hin.
        - exists (TCA.EE, 0, ELit 16). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, TCA.EE. cbn [a_base a_off edenot]. rewrite W12. rewrite u64_of_Z by (clear; lia). clear - Hin. lia.
        - exists (ELit 0, TCA.GD, ELit 2). split; [right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, TCA.GD. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (clear; lia). cbn in Hin. clear - Hin. lia.
        - exists (ELit 0, TCA.AXT, ELit 544). split; [right; right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, TCA.AXT. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (clear; lia).
          cbn in Hin. unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin. clear - Hin. lia. }
      split.
      { intros w a' Hw Hin (_ & _ & Ko). destruct Hw as [<-|[<-|[<-|[]]]].
        - exact (Ko (E, 16) (or_intror (or_introl eq_refl)) Hin).
        - exact (Ko _ (or_intror (or_intror (or_introl eq_refl))) Hin).
        - exact (Ko _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) Hin). }
      split; [unfold CHA.curB; rewrite TCA.bls_i; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|].
      split.
      { unfold XI. split; [|split; [right | split; [intros _ | rewrite Yj, TCA.arm_ret; exact HARM]]].
        - intros a' Ha Hnw H14'. exfalso. rewrite Yj in H14'. clear - H14' Yi1. lia.
        - unfold FLF. replace (CL5A.uv E2 TCA.FLE) with fl by (unfold CL5A.uv, TCA.FLE; cbn [edenot]; symmetry; exact T48). split; [exact HFL1 | exact HFL2].
        - unfold ECF. rewrite Yj, TCA.arm_ret. fold a. split; [exact XEC | exact XLS]. }
      intros X0 HX0 _. exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W53 W48 T53 T48 (CELL _ Y11) X0 HX0). }

    apply andb_prop in X as [X YP]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Yr]. apply andb_prop in X as [X Y3].
    apply andb_prop in X as [X Yi2]. apply andb_prop in X as [Xbase Yi1]. apply Nat.ltb_lt in Y3. apply Nat.leb_le in Yi1, Yi2. apply CBA.regions_eqb_eq in YF.
    assert (Hi : (5 <= i <= 19)%nat) by (clear - Yi1 Yi2; lia).
    destruct (CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i TCA.FFS [])) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA (HXW & HXF & HXE & HARM)].
    destruct HXF as [HXF|(HFL1 & HFL2)]; [exfalso; clear - HXF Yi1; lia|]. specialize (HXE Yi1).
    destruct (FRM E1 A1 M1 m1 Hi HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP). set (F := CL5A.uv E1 TCA.FE) in *. set (fl := CL5A.uv E1 TCA.FLE) in *.
    refine (CRA.exit_retire L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS TCA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok TCA.RETPC i c ps0 TCA.FLE TCA.FE 1 (-96) _ Xbase (TCA.ffs_i i Hi) Hrc Yfl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
      [rewrite LS; exact TCA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'. rewrite HcB in HH1. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    destruct (LEAFK E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y3 (or_intror YF) (proj1 HFL1)) as (W2 & W10 & W12 & W53 & W48 & CELL & REG & LOWF). fold F in W53. fold fl in W48.
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')).
    { rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)). exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS TCA.FFS Cred 2 i E1 A1 M1 m1 HA). }

    assert (HMORE : L5.u8_at (hl_segs L) M' (P + 211) 0).
    { pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (P + 211) (CELL _ YP) ltac:(unfold estart, TCA.PE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as G0.
      apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0. }

    destruct HXE as (XEC & XLS).
    assert (AGE : forall a', E <= a' < E + 16 -> M' (Z_to_bv 64 a') = M1 (Z_to_bv 64 a')).
    { intros a' Ha. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite L5.unsigned_lit by (clear - Ha Q3 Q6; lia).
      destruct (WCL a' (INWE a' Ha)) as (C0' & C1 & C2 & C3 & _). pose proof (WFR a' F (INWE a' Ha) F3 FAP) as NF0.
      pose proof (Z.div_pos F 8 F0 ltac:(clear; lia)) as D0. assert (D1 : F / 8 <= 2 ^ 44 - 16) by (apply Z.div_le_upper_bound; clear - F1; lia).
      assert (NFL : a' <> fl) by (intros Heq; apply HFL2; rewrite <- Heq; exact (C3 _ _)).
      rewrite YF. unfold TCA.CPF4, TCA.CPF2, TCA.CPF0, TCA.FRM3, TCA.FLR, TCA.PE, TCA.FE, TCA.FLE, TCA.SBz; cbn [app]; repeat (apply Forall_cons); try (apply Forall_nil);
        cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; unfold CL5A.uv in W53, W48; rewrite ?W2, ?W10, ?W53, ?W48;
        rewrite u64_of_Z by (clear; lia); unfold PMLA.apart in AP2; clear - C1 C2 S2 Ha AP2 NF0 D0 D1 NFL; lia. }
    assert (PEC : PMSA.ec_at L IC M' E (PMSA.tce_code cls)).
    { rewrite HCODE, <- HARM. apply (PTA.ec_at_ag (hl_segs L) IC M1 M' (fun a' => M' (Z_to_bv 64 a') = M1 (Z_to_bv 64 a')) (fun a' Ha => Ha) E (TCA.acode (TCA.arm i))); [|exact XEC].
      split; [clear - Q3; lia|]. split; [clear - Q6; lia|]. exact AGE. }
    assert (PLS : PMSA.ls_ok L IC (PML.regJ g) M').
    { apply (PTA.ls_ok_ag (hl_segs L) IC M1 M' (fun a' => M' (Z_to_bv 64 a') = M1 (Z_to_bv 64 a')) (fun a' Ha => Ha) (PML.regJ g) ltac:(destruct g; discriminate)); [|intros a' Ha; exact (PTKF a' Ha) | exact XLS].
      intros a' Ha. destruct (IMGCL a' Ha) as (RG & _). split; [clear - RG; lia|]. apply LOWF. clear - RG. lia. }
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [exact PEC|]. split; [exact HMORE|]. split; [exact PLS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - exact Hc0.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VOB : forall o n, CL5A.ainfr FF o n -> 0 < n -> CL5A.visr (ahid A model) o n /\ (forall a, in_shadow_of o n a -> ahid A model (Z_to_bv 64 a) = false)).
    { intros o n Hfr Hn. split.
      - intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o n (o + k) RFx Hfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3).
      - intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o n a RFx Hfr Hn Ha) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    destruct (VOB P 272 Pfr ltac:(clear; lia)) as (VP & VSP). destruct (VOB E 16 Efr ltac:(clear; lia)) as (VE & VSE).
    assert (VS : CL5A.visr (ahid A model) (sp - 1120) 1120).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DEFV : forall o n, CL5A.ainfr FF o n -> CL5A.visr (ahid A model) o n -> L5.defined Mv o n).
    { intros o n Hfr Hv. apply (CL5A.defined_vis _ M o n Hv). destruct Hfr as (f & Hf & G1 & G2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFT f Hf) as (_ & _ & _ & _ & Fdef & _).
      intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk G1 G2. lia. }
    pose proof (DEFV P 272 Pfr VP) as DP. pose proof (DEFV E 16 Efr VE) as DE.
    assert (DS : L5.defined Mv (sp - 1120) 1120) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (PD : 0 <= P / 8 <= 2 ^ 44 - 34) by (split; [apply Z.div_pos; clear - O3; lia | apply Z.div_le_upper_bound; clear - O6; lia]).
    assert (UVP : CL5A.uv E0 (EVar 10) = P) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    assert (UVE : CL5A.uv E0 (EVar 12) = E) by (unfold CL5A.uv; cbn [edenot]; exact U12).
    change (272 / 8) with 34 in Psh. change (16 / 8) with 2 in Esh.
    cbn [PMLA.VT_FUNC PMLA.C_cboth] in A12.
    assert (IR : L5.img_clear M 65536 1400832) by (pose proof HLS as (IR0 & _); exact IR0).
    assert (KIMG : forall lo hi, 65536 <= lo -> hi <= 1400832 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hlo Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (IR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (CC.cp_know G.cp0)).
    { let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l. repeat (apply Forall_cons); try (apply Forall_nil).
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + destruct (ISH _ _ _ _ _ _ _ HH TCA.SLOT2 8 ltac:(rewrite ILO; unfold TCA.SLOT2; clear; lia) ltac:(rewrite IHI; unfold TCA.SLOT2; clear; lia) ltac:(clear; lia) POI2) as [BZ BA].
        assert (ISX : in_shadow_of TCA.SLOT2 8 TCA.ISH2) by (unfold in_shadow_of, S, TCA.SLOT2, TCA.ISH2, SB; clear; split; reflexivity).
        eapply CL5A.kzero_intro with (A := TCA.ISH2) (N := 1); [reflexivity | reflexivity | unfold TCA.ISH2; clear; lia | unfold TCA.ISH2; clear; lia | unfold TCA.ISH2; clear; lia |].
        intros jj Hjj. replace (TCA.ISH2 + jj) with TCA.ISH2 by (clear - Hjj; lia). apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ ISX) | exact (BZ _ ISX)].
      + apply KIMG; clear; lia.
      + apply KIMG; clear; lia.
      + eapply CL5.kwr_intro with (A := P) (N := 272); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DP].
      + eapply CL5.kword64_intro with (A := P + 96) (z := 1370488); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity |].
        apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ P 272 (P + 96) 8 VP ltac:(clear; lia) ltac:(clear; lia)) | exact A12].
      + eapply CL5.kword64_intro with (A := P + 128) (z := P + 96); [ev0 | clear - O3; lia | clear - O6; lia | |].
        * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia].
        * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ P 272 (P + 128) 8 VP ltac:(clear; lia) ltac:(clear; lia)) | exact A13].
      + eapply CL5.krange_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
      + eapply CL5.kalign_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact P8].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 34 P UVP); [clear; lia | clear - O3 O6; lia |].
        intros j Hj. apply CL5A.byte_vis; [apply VSP; apply (CL5A.shreg_in_shadow P 34); [exact P8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Psh j Hj)].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := P) (N2 := 272); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
      + eapply CL5.kwr_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DE].
      + eapply CL5.kunk_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DE].
      + eapply CL5.krange_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO CL SP1; lia].
      + eapply CL5.kalign_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | exact E8].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 E UVE); [clear; lia | clear - Q3 Q6; lia |].
        intros j Hj. apply CL5A.byte_vis; [apply VSE; apply (CL5A.shreg_in_shadow E 2); [exact E8 | clear; lia | unfold S, SB; clear - Hj; lia] | exact (Esh j Hj)].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := E) (N2 := 16); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in Q5; clear - Q5; lia].
      + eapply CL5.kunk_intro with (A := sp - 1120) (N := 1120); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.kwr_intro with (A := sp - 1120) (N := 1120); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp32].
      + eapply CL5.kdisj_intro with (A1 := sp - 1120) (N1 := 1120) (A2 := P) (N2 := 272); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
      + eapply CL5.kdisj_intro with (A1 := sp - 1120) (N1 := 1120) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | clear - Q4 S2; lia].
      + eapply CL5.kdisj_intro with (A1 := P) (N1 := 272) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | unfold PMLA.apart in AP2; clear - AP2; lia].
      + eapply CL5.kdisj_intro with (A1 := P / 8 + SB) (N1 := 34) (A2 := E) (N2 := 16); [rewrite CL5A.estart_srl3', UVP; reflexivity | reflexivity | ev0 | reflexivity | unfold hid in Q5; unfold SB; clear - Q5 PD; lia].
      + eapply CL5.kdisj_intro with (A1 := P / 8 + SB) (N1 := 34) (A2 := 6882184) (N2 := 2); [rewrite CL5A.estart_srl3', UVP; reflexivity | reflexivity | reflexivity | reflexivity | unfold SB; clear - PD; lia].
      + eapply CL5.kdisj_intro with (A1 := P / 8 + SB) (N1 := 34) (A2 := 7020000) (N2 := 544); [rewrite CL5A.estart_srl3', UVP; reflexivity | reflexivity | reflexivity | reflexivity | unfold SB; clear - PD; lia]. }
    destruct (TCA.kn_common i0 Hi04) as (KNC & _).
    split.
    + destruct Hi0 as [(Hi3 & Hcls)|(-> & Hcls)].
      * rewrite (TCA.regs_lit i0 Hi3). apply TCA.regs_ok_upd11; [exact (regs_ok_id R _ _) | cbn [edenot]; rewrite <- Hcls; exact Ha1].
      * change (nth 4%nat G.CPS G.cp0) with G.cp4. rewrite TCA.regs4. exact (regs_ok_id R _ _).
    + unfold know_ok. rewrite <- (firstn_skipn TCA.NKC (CC.cp_know (nth i0 G.CPS G.cp0))), KNC. apply Forall_app. split; [exact COMMON|].
      destruct Hi0 as [(Hi3 & Hcls)|(-> & Hcls)].
      * rewrite skipn_all2; [apply Forall_nil | rewrite (TCA.kn_len i0 Hi3); apply le_n].
      * change (nth 4%nat G.CPS G.cp0) with G.cp4. rewrite TCA.kn4_eq. apply Forall_cons; [|apply Forall_nil].
        eapply CL5.krange_intro with (v := cls); [lin_eval; rw_atoms; clear; lia | exact CLS64 | exact Hcls].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite TCA.bls_i, (TCA.ffs_0 i0 Hi04).
      cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub]. split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | replace (2 - 0) with 2 by (clear; lia); exact Hroom].
    + unfold XI. split; [intros a _ _ _; reflexivity|]. split; [left; exact Hi04|]. split; [intros H15; exfalso; clear - H15 Hi04; lia|].
      unfold TCA.arm. rewrite Nat.mod_small by (clear - Hi04; lia). reflexivity.
  - exact Hfp.
Qed.
End TceOk.

