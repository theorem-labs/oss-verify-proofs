(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA CutShB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_to_codepoint_xboth_T Cut_to_codepoint_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_to_codepoint_xboth.
Module GT := Cut_to_codepoint_xboth_T.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

Module ETCA.
Definition RETPC : Z := 822928.        (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition TABLO : Z := 151792.        (* [comment removed for export] *)
Definition TABN : Z := 288.            (* [comment removed for export] *)
Definition TABSH : Z := 2147469854.    (* [comment removed for export] *)
Definition OFFSH : Z := 2147469887.    (* [comment removed for export] *)
Definition FFS : list (list (expr * Z * Z)) := [[]].
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Z.eqb pc RETPC && Nat.eqb i 0 && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                     && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (EVar 10) (ELit 1)) && CL.ps_reg_is ps 11 (ELit 0)
                     && has cells (KWord (SA (EVar 12) 0) 4 (EVar 32)))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true. Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true. Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = []. Proof. intros [|[|i]]; reflexivity. Qed.
Lemma ffs_i : forall i, nth i FFS [] = []. Proof. intros [|[|i]]; reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC. Proof. CL.solve_is_ret. Qed.
End ETCA.

Section ToCodepointOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL0 : icpt_layout.
Abbreviation IC := PMLA.C_xboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI_TAB : Forall (fun r : Z * Z => ETCA.TABLO + ETCA.TABN <= fst r \/ snd r <= ETCA.TABLO) (icl_poison IL0).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

(* [comment removed for export] *)
Definition to_codepoint_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (it e cpc c sp r : Z),
    PMSA.cps_asan L ar HI pc r sp 16 LB FF LK cr A 0
      (fun R M => PMLA.img_ro IC M /\ PMSA.a0 R it /\ PMSA.a1 R e /\ PMSA.a2 R cpc /\ PMSA.a3 R 0 /\ PMSA.u8 L M it c /\ 0 <= c <= 127 /\ it + 1 <= e < 2 ^ 47 /\
                  PMSA.text_inA M LB it 1 /\ L5.defined M (cpc - cpc mod 8) 8 /\ PMSA.acobj ar FF sp (cpc - cpc mod 8) 8 /\ cpc mod 8 <= 4 /\ shadow_zero M cpc 1)
      (fun R M R' M' LB' cr' LBk W => PMSA.a0 R' (it + 1) /\ PMSA.a1 R' 0 /\ PMSA.u32 L M' cpc c /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(cpc - cpc mod 8, 8)]).

Theorem to_codepoint_ok : to_codepoint_specA 822120.
Proof.
  intros LB FF LK cr A it e cpc c sp r. unfold PMSA.cps_asan, PMSA.text_inA.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (HIR & Ha0 & Ha1 & Ha2 & Ha3 & HBY & HC & HE & (b & n & HinB & N8 & HBS & HSN & HBZ) & HVD & HVO & HV8 & HVZ) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.a3, PMSA.acobj in *.
  set (cg := cpc - cpc mod 8) in *.
  assert (CG8 : cg mod 8 = 0) by (unfold cg; rewrite Zminus_mod, Z.mod_mod by (clear; lia); rewrite Z.sub_diag; reflexivity).
  assert (CGR : cg <= cpc /\ cpc + 4 <= cg + 8) by (unfold cg; pose proof (Z.mod_pos_bound cpc 8 ltac:(clear; lia)) as MB; clear - MB HV8; lia).
  assert (CGD : cpc / 8 = cg / 8) by (unfold cg; rewrite (Z.mod_eq cpc 8) by (clear; lia); replace (cpc - (cpc - 8 * (cpc / 8))) with (cpc / 8 * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
  assert (SCG : S cpc = S cg) by (unfold S; rewrite CGD; reflexivity).
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (b, n) HinB) as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap). cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap.
  pose proof (CHA.mod8_of_16 _ KB16) as KB8.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6. change (hid (b + n <= 2147446784 \/ 17594333495296 <= b)) in KB6.
  assert (N8' : n = 8 * (n / 8)) by (pose proof (Z_div_mod_eq_full n 8) as D; rewrite N8 in D; clear - D; lia).
  assert (G1 : 1 <= n / 8) by (clear - N8' KB3; lia).
  destruct (CL5A.acobj_rng L ar LB FF sp cg 8 RFx CSP HVO ltac:(clear; lia)) as (O3 & O6 & O5 & O1 & O4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in O5. change (hid (cg + 8 <= 2147446784 \/ 17594333495296 <= cg)) in O5. change (hid (ar_fs ar + 32 <= cg \/ ahl_ceil ar <= cg)) in O1. change (hid (cg + 8 <= ahl_ceil ar \/ sp <= cg)) in O4.
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 c)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 it) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 e) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 cpc) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V13 : ev E0 13 = Z_to_bv 64 0) by (rewrite <- Ha3; exact (EV 13%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 c) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = it) by (rewrite V10; apply u64_of_Z; clear - HBS HSN KB0 KB7; lia).
  assert (U11 : bv_unsigned (ev E0 11) = e) by (rewrite V11; apply u64_of_Z; clear - HE HBS KB0; lia).
  assert (U12 : bv_unsigned (ev E0 12) = cpc) by (rewrite V12; apply u64_of_Z; clear - O3 O6 CGR; lia).
  assert (U13 : bv_unsigned (ev E0 13) = 0) by (rewrite V13; apply u64_of_Z; clear; lia).
  assert (U32 : bv_unsigned (ev E0 32) = c) by (rewrite V32; apply u64_of_Z; clear - HC; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 16) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(cg, 8)]).
  assert (WINC : incl WW WW) by (apply incl_refl).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.acobj_wok L ar LB FF sp _ cg 8 a RFx CSP HVO ltac:(clear - Hin; lia)). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U12 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    exists (cg, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha CGR; lia]. }
  assert (SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U10, ?U11, ?U12 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
    - (* [comment removed for export] *)
      split; [clear - Ha HBS HSN KB0 KB7; lia|]. split; [left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Ha HBS HSN; lia]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Ha KB6 HBS HSN. lia.
    - (* [comment removed for export] *)
      assert (Hsh : in_shadow_of b n a).
      { pose proof (Z.div_le_mono b it 8 ltac:(clear; lia) HBS) as D1.
        assert (D2 : it / 8 < b / 8 + n / 8) by (apply Z.div_lt_upper_bound; [clear; lia | pose proof (Z_div_mod_eq_full b 8) as Db; clear - Db KB8 HSN N8'; lia]).
        pose proof (CL5A.shreg_in_shadow b (n / 8) a KB8 ltac:(clear - G1; lia) ltac:(unfold SB; clear - Ha D1 D2; lia)) as Hsh. rewrite <- N8' in Hsh. exact Hsh. }
      pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Hsh) as RG. split; [clear - RG; lia|]. split; [do 6 right; exists (b, n); split; [exact HinB | exact Hsh]|].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Hsh).
    - (* [comment removed for export] *)
      destruct (CL5A.acobj_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) cg 8 a RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow cg 1 a CG8 ltac:(clear; lia) ltac:(unfold SB; rewrite <- CGD; clear - Ha; lia))) as (G1' & G2 & G3).
      split; [exact G1' | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a Hrg Ha. let l := eval vm_compute in (CH.hd_img G.HDECL) in change (CH.hd_img G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros j Hj; apply S5; clear - Hj; lia).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c0 : Z * Z * Z => 0 <= fst (fst c0) /\ fst (fst c0) + snd (fst c0) <= hl_img_hi L /\ 0 <= snd (fst c0) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok) as AIOWF.
  rewrite <- LS in FPM.
  change 822120 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS ETCA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact ETCA.heap_ok.
  - intros i c0 kk ps0 j sg IL E1 E' R' Mq Mq' cr1 _ _ _ HCR. exact HCR.
  - intros i c0 kk ps0 j sg IL E1 R1 E' R' A1 M1 m1 M' m' _ _ _ _ _. exact I.
  - (* [comment removed for export] *)
    intros i c0 kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ ETCA.leaf_ok _ _ _ _ _ IL) as X. unfold ETCA.leaf_chk in X. cbn beta iota in X.
    apply andb_prop in X as [X XCELL]. apply andb_prop in X as [X XA1]. apply andb_prop in X as [X XA0]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Xpc Xi].
    apply Z.eqb_eq in Xpc. apply Nat.eqb_eq in Xi. subst pc i.
    assert (Hci : nth_error G.CPS 0 = Some c0) by (destruct IL as (tg & Hci & _); exact Hci).
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS ETCA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok ETCA.RETPC 0%nat c0 ps0 _ Xbase _ (ETCA.ffs_i 0%nat) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact ETCA.ret_at | exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS 0 E1 = LB) by (unfold CHA.curB; rewrite ETCA.bls_i; reflexivity). rewrite HB in HH1.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS ETCA.FFS Cred 0 0%nat c0 E1 E' A1 M1 m1 HA (G.NF_le 0%nat c0 Hci) Hag) as HagE1.
    assert (FZ : forall n0, (n0 <? 33)%nat = true -> ev E' n0 = ev E0 n0) by (intros n0 Hn; symmetry; apply (proj1 HagE1); unfold GT.NF; apply Nat.ltb_lt; exact Hn).
    assert (CELL : forall X0, ETCA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
      by (intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)).
    assert (REG : forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
      by (intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')).
    { rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)). exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS ETCA.FFS Cred 0 0%nat E1 A1 M1 m1 HA). }
    split; [|split; [|split; [|repeat split; reflexivity]]].
    + unfold PMSA.a0. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). apply (REG 10%nat _ _ XA0).
      apply CL5.u_lin; [lin_eval; rewrite (FZ 10%nat eq_refl); rewrite U10; clear; lia | clear - HBS HSN KB0 KB7 HE; lia].
    + unfold PMSA.a1. replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply (REG 11%nat _ _ XA1). cbn [edenot]. apply L5.unsigned_lit. clear; lia.
    + pose proof (CL5A.kword32_elim (hl_segs L) E' _ _ _ cpc (CELL _ XCELL) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite (FZ 12%nat eq_refl); rewrite U12; clear; lia)) as G0.
      apply (CL5A.u32_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite (FZ 32%nat eq_refl), U32 in G0. exact G0.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VS : CL5A.visr (ahid A model) (sp - 16) 16).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VB : CL5A.visr (ahid A model) b n).
    { intros q Hq. apply CLV; [clear - Hq KB0 KB7; lia | left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq KB6. lia. }
    assert (VBS : forall a, in_shadow_of b n a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Ha) as RG. apply CLV; [clear - RG; lia | do 6 right; exists (b, n); split; [exact HinB | exact Ha] |].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Ha). }
    assert (VO : CL5A.visr (ahid A model) cg 8).
    { intros q Hq. destruct (CL5A.acobj_wok L ar LB FF sp 0 cg 8 (cg + q) RFx CSP HVO ltac:(clear - Hq; lia)) as (G1' & G2 & G3). exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 1 -> ahid A model (Z_to_bv 64 (S cpc + j)) = false).
    { intros j Hj. rewrite SCG. destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 cg 8 (S cg + j) RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow cg 1 (S cg + j) CG8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1' & G2 & G3).
      exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 16) 16) by (apply (CL5A.defined_vis _ M _ _ VS); intros j Hj; apply S5; clear - Hj; lia).
    assert (DVP : L5.defined Mv cg 8) by (apply (CL5A.defined_vis _ M cg 8 VO); exact HVD).
    assert (DVP4 : L5.defined Mv cpc 4) by (intros j Hj; replace (cpc + j) with (cg + (cpc - cg + j)) by (clear; lia); apply DVP; clear - Hj CGR; lia).
    assert (UCP : CL5A.uv E0 (EVar 12) = cpc) by (unfold CL5A.uv; cbn [edenot]; exact U12).
    assert (UIT : CL5A.uv E0 (EVar 10) = it) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    unfold PMLA.img_ro in HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xboth] in HIR.
    assert (IMGK : forall lo hi, 65536 <= lo -> hi <= 1466368 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (HIR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    destruct (ISH _ _ _ _ _ _ _ HH ETCA.TABLO ETCA.TABN ltac:(rewrite ILO; unfold ETCA.TABLO; clear; lia) ltac:(rewrite IHI; unfold ETCA.TABLO, ETCA.TABN; clear; lia) ltac:(unfold ETCA.TABN; clear; lia) POI_TAB) as [BZ BA].
    assert (ISX : forall jj, 0 <= jj < 36 -> in_shadow_of ETCA.TABLO ETCA.TABN (ETCA.TABSH + jj)) by (intros jj Hjj; unfold in_shadow_of, S, ETCA.TABLO, ETCA.TABN, ETCA.TABSH, SB; clear - Hjj; lia).
    (* [comment removed for export] *)
    assert (ITG : 0 <= it / 8 - b / 8 < n / 8).
    { pose proof (Z.div_le_mono b it 8 ltac:(clear; lia) HBS) as D1.
      assert (D2 : it / 8 < b / 8 + n / 8) by (apply Z.div_lt_upper_bound; [clear; lia | pose proof (Z_div_mod_eq_full b 8) as Db; clear - Db KB8 HSN N8'; lia]). clear - D1 D2. lia. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply IMGK; clear; lia.
    + eapply CL5A.kzero_intro with (A := ETCA.TABSH) (N := 17); [unfold estart, ETCA.TABSH; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear; lia | reflexivity | unfold ETCA.TABSH; clear; lia | unfold ETCA.TABSH; clear; lia | unfold ETCA.TABSH; clear; lia |].
      intros jj Hjj. apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ (ISX jj ltac:(clear - Hjj; lia))) | exact (BZ _ (ISX jj ltac:(clear - Hjj; lia)))].
    + eapply CL5A.kzero_intro with (A := ETCA.OFFSH) (N := 3); [unfold estart, ETCA.OFFSH; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear; lia | reflexivity | unfold ETCA.OFFSH; clear; lia | unfold ETCA.OFFSH; clear; lia | unfold ETCA.OFFSH; clear; lia |].
      intros jj Hjj. replace (ETCA.OFFSH + jj) with (ETCA.TABSH + (33 + jj)) by (unfold ETCA.OFFSH, ETCA.TABSH; clear; lia).
      apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ (ISX (33 + jj) ltac:(clear - Hjj; lia))) | exact (BZ _ (ISX (33 + jj) ltac:(clear - Hjj; lia)))].
    + eapply CL5A.kword8_intro with (A := it) (z := c); [ev0 | clear - HBS KB0; lia | clear - HSN KB7; lia | exact V32 | clear - HC; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - HBS KB0; lia | clear - HSN KB7; lia | exact (CL5A.visr_sub _ b n it 1 VB HBS HSN) | exact HBY].
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - HC; lia | clear - HC; lia].
    + eapply CL5.krange_intro with (v := 0); [lin_eval; rw_atoms; clear; lia | clear; lia | clear; lia].
    + eapply CL5.krange_intro with (v := it); [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7; lia | clear - HBS HSN KB0 KB4 HE SP1; lia].
    + eapply CL5.krange_intro with (v := e - it); [lin_eval; rw_atoms; clear - HE HBS KB0; lia | clear - HE HBS KB0; lia | clear - HE HBS KB0; lia].
    + eapply CL5.krange_intro with (v := e); [lin_eval; rw_atoms; clear; lia | clear - HE HBS KB0; lia | clear - HE HBS KB0; lia].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 it UIT); [clear; lia | clear - HBS HSN KB0 KB7 HE; lia |].
      intros j Hj. unfold S. replace (it / 8 + SB + j) with (S b + (it / 8 - b / 8)) by (unfold S; clear - Hj; lia).
      apply CL5A.byte_vis; [apply VBS; rewrite N8'; apply (CL5A.shreg_in_shadow b (n / 8)); [exact KB8 | clear - G1; lia | unfold S, SB; clear - ITG; lia] | exact (HBZ _ ITG)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := it) (N2 := 1); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in KB6; clear - KB6 HBS HSN; lia].
    + eapply CL5.kunk_intro with (A := cpc) (N := 4); [ev0 | reflexivity | clear - O3 CGR; lia | clear - O6 CGR; lia | clear - O6 CGR; lia | exact DVP4].
    + eapply CL5.kwr_intro with (A := cpc) (N := 4); [ev0 | reflexivity | clear - O3 CGR; lia | clear - O6 CGR; lia | clear - O6 CGR; lia | exact DVP4].
    + eapply CL5.krange_intro with (v := cpc); [lin_eval; rw_atoms; clear; lia | clear - O3 O6 CGR; lia | unfold hid in O1; clear - O1 O6 FSLO CL CGR; lia].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 cpc UCP); [clear; lia | clear - O3 O6 CGR; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (HVZ j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := cpc) (N2 := 4); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5 CGR; lia].
    + eapply CL5.kwr_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kunk_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := sp - 16) (N2 := 16); [reflexivity | reflexivity | ev0 | reflexivity | clear - S2 CL; lia].
    + (* [comment removed for export] *)
      assert (DJ : cg + 8 <= it \/ it + 1 <= cg).
      { destruct HVO as [(f & Hf & F1 & F2)|[Q1 Q2]].
        - pose proof (KBfap f ltac:(apply in_or_app; left; exact Hf)) as AP. clear - AP F1 F2 HBS HSN. lia.
        - clear - Q1 KB4 CSP HBS HSN. lia. }
      eapply CL5.kdisj_intro with (A1 := cpc) (N1 := 4) (A2 := it) (N2 := 1); [ev0 | reflexivity | ev0 | reflexivity | clear - DJ CGR; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 16) (N1 := 16) (A2 := cpc) (N2 := 4); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in O4; clear - O4 S2 CGR; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 16) (N1 := 16) (A2 := it) (N2 := 1); [ev0 | reflexivity | ev0 | reflexivity | clear - KB4 S2 HBS HSN; lia].
  - (* [comment removed for export] *)
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite ETCA.bls_i, ETCA.ffs_i. cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.
Print Assumptions to_codepoint_ok.
End ToCodepointOk.
