(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm5PlanKit Pm5L5DefsA FrmInv Pm5FrmInv PmHeapIfaceA PmLibDefsA PmLibSpecsA
  CutVFXM DecIface DecOkDefsM DecOkSemM ScanexpSemM ScanexpSemA DecIfaceA FloatLazyA Pm5ScanexpLems.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA Pm5CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_scanexp_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SXOA.
Module G := Cut_scanexp_xboth.
Definition RET_PC : Z := 0x153354.
Definition lchk := SXS.leaf_chk G.CPS RET_PC.
Lemma cuts_ok : CC.cps_all G.CPS (fun _ c => SXS.cut_chk c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaves_ok : CH2.leaves_all G.CPS G.TAGS lchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma heap_ok : CHA.heap_chkA SXS.NF G.HDECL (CPA.NOB G.CPS) (CPA.NOF G.CPS) G.CPS G.TAGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma pure_ok : CH2.leaves_all G.CPS G.TAGS (CPA.pure_leaf_chk SXS.NF G.HDECL [RET_PC]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition tagpc (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => true | CC.TOther pc => Z.eqb pc RET_PC end.
Lemma tagpc_ok : CH2.leaves_all G.CPS G.TAGS tagpc = true.
Proof. vm_compute. reflexivity. Qed.
Lemma foot_ok : CC.cps_all G.CPS (fun _ c => CHA.foot_chk SXS.NF G.HDECL c [] []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.

Definition ghost (Q N : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 Q | 33 => Z_to_bv 64 N | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (Q N : Z) : env := Env (reg_ev R (ghost Q N)) (fun _ => []).
Definition entry_ix (N : Z) : nat := if N =? 0 then 0%nat else if N =? 1 then 1%nat else 2%nat.
Definition entry_cp (N : Z) : CC.cutpoint := if N =? 0 then G.cp0 else if N =? 1 then G.cp1 else G.cp2.

Section Run.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.

Theorem scanexp_okA : PDCA.scanexp_contractA L ar HI PMSA.fp_ok PDCA.xboth.
Proof.
  intros r sp F P' txt LB FF LK cr A fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs Hpre Hcont.
  destruct Hpre as (RF & Ra1 & Hfile & HspF & Hfd8 & Htext & Hblk & Hapf & Himg).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr).
  cbn [PDC.a_scanexp PDC.a_img_lo PDC.a_img_hi PDCA.xboth] in *. unfold PDC.STK_FLOOR in *.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (FPM : forall (fx fx' : FPState) R0 pc M0 R' pc' M', msteps (hl_segs L) (@mkst fx R0 (Z_to_bv 64 pc) M0 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx').
  { rewrite LS. intros fx0 fx' R0 pc M0 R' pc' M' H Hf. exact (Pm5FrmInv.msteps_fp_ok fx0 fx' R0 _ M0 _ R' _ M' _ H Hf). }
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  set (N := Z.of_nat (length txt)) in *. assert (HN0 : 0 <= N) by (unfold N; lia).
  destruct (FLA.txt_facts_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp P' (N + 1) HH ltac:(lia) Hblk ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5).
  assert (TBS : P' + (N + 1) <= sp - 80 \/ sp <= P') by lia. clear TB2. unfold PDC.apart in Hapf.
  set (E0 := mkE R P' N). set (c := entry_cp N).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Hsp; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Usp.
  assert (U10 : bv_unsigned (ev E0 10) = F) by exact RF.
  assert (U32 : bv_unsigned (ev E0 32) = P') by (change (ev E0 32) with (Z_to_bv 64 P'); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = N) by (change (ev E0 33) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (R_SP : PDC.STK_FLOOR + 80 <= sp <= 2 ^ 47) by (unfold PDC.STK_FLOOR; lia).
  assert (R_F : PDC.STK_FLOOR <= F /\ F + 256 <= 2 ^ 47) by (unfold PDC.STK_FLOOR; lia).
  assert (R_Q : 4096 <= P' /\ P' + N < 2 ^ 47 /\ N < 2 ^ 26) by lia.
  assert (SCRV : CH.hd_scr G.HDECL = 80) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= SXS.NF)%nat) by (unfold SXS.NF; lia).
  set (W := [(F + 8, 8)] : list L5.range).
  assert (FCL : forall a, F + 8 <= a < F + 16 -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. rewrite SCRV. split; [lia|]. split; [right; left; split; lia|]. apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia. }
  assert (WOK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (FCL a ltac:(lia)). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt SXS.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (F + 8, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  (* [comment removed for export] *)
  assert (VS : CL5A.visr (ahid A model) (sp - 80) 80) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VF : CL5A.visr (ahid A model) (F + 8) 192) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr (ahid A model) P' (N + 1)) by (exact (FLA.txt_visr_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp _ _ HH ltac:(lia) Hblk)).
  (* [comment removed for export] *)
  assert (TXTK : forall a, P' <= a < P' + (N + 1) -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) W a).
  { intros a Ha. rewrite SCRV. apply (FLA.txt_kept_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp P' (N + 1) _ _ _ HH); [lia | lia | exact Hblk | | exact Ha].
    intros w [<-|[]]. cbn [fst snd]. lia. }
  assert (TVof : forall A' m' (M' : PDCA.mem) LKx crx, ri_inv HI LB FF LKx crx A' M' (vml_of m') ->
            (forall a, CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> SXA.TV txt P' M (CCA.vis A' m' M')).
  { intros A' m' M' LKx crx HHx Hfr x Hx. unfold SXA.N in Hx.
    unfold CCA.vis. rewrite <- (Z_to_bv_bv_unsigned _ x). rewrite (CL5A.vis_eq (ahid A' m') M'); [apply Hfr; apply TXTK; lia|].
    pose proof (FLA.txt_visr_h L ar C HI HIok LYI _ _ _ _ _ _ _ sp P' (N + 1) HHx ltac:(lia) Hblk (bv_unsigned x - P') ltac:(lia)) as Vx.
    replace (P' + (bv_unsigned x - P')) with (bv_unsigned x) in Vx by lia. exact Vx. }
  assert (CUT : forall i0 c0, nth_error G.CPS i0 = Some c0 -> SXS.cut_chk c0 = true) by (intros i0 c0 Hc0; exact (CC.cps_all_sound _ _ cuts_ok i0 c0 Hc0)).
  assert (Hci : nth_error G.CPS (entry_ix N) = Some c /\ SXS.kind_of c = SXS.KE /\ CC.cp_pc c = 0x1530e8).
  { unfold c, entry_cp, entry_ix. destruct (N =? 0); [|destruct (N =? 1)]; (split; [reflexivity | split; vm_compute; reflexivity]). }
  destruct Hci as (Hci & Hki & Hpc). rewrite <- Hpc.
  eapply (CPA.pure_cert_soundA L ar C HI HIok LYI LYR LYB LYN SXS.NF E0 M model A LB FF LK cr sp G.HDECL W W 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS G.TAGS K PMSA.fp_ok DEF0 (fun i E _ Mx _ => SXS.XI G.CPS txt i E Mx) R r EV Hra Hraok [RET_PC] FPM) with (i := entry_ix N).
  - rewrite LS. exact (G.plans Pm5ScanexpLems.lems_ok).
  - exact G.tags_ok.
  - exact heap_ok.
  - exact pure_ok.
  - rewrite LS. intros pc [<-|[]]. exact ret_pc_ok.
  - (* [comment removed for export] *)
    intros i c1 k ps j s IL E R1 E' R' A1 M1 m1 M2 m2 HAt1 HA1 Hag HLF HX.
    destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    destruct (CC.tags_chk_go_nth G.CPS SXS.NF G.CPS G.TAGS i c1 G.tags_ok Hc1) as (tags' & Htags' & Hlv). rewrite Htags in Htags'. injection Htags' as <-.
    destruct (CC.leaves_chk_nth G.CPS SXS.NF c1 _ tags k ps Hlv Hps) as (t & Ht & Hg). rewrite Htag in Ht. injection Ht as <-. destruct Hg as (cj & Hcj & Hg).
    pose proof (CH2.leaves_all_nth G.CPS G.TAGS lchk leaves_ok i c1 tags k ps _ Hc1 Htags Hps Htag) as G2. unfold lchk, SXS.leaf_chk in G2. rewrite Hcj in G2.
    pose proof HA1 as (_ & _ & _ & HagE & (cr1 & LK1 & HH1 & _) & Hfr1 & _).
    assert (HA2 : CHA.aamb L ar HI SXS.NF E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2).
    { refine (CHA.leaf_amb L ar C HI HIok LYI LYR SXS.NF E0 M model A LB FF LK sp G.HDECL W W _ _ _ 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK i c1 ps E E' R1 R' A1 M1 m1 M2 m2 _ HAt1 HA1 Hag HLF).
      rewrite CPA.NOBnil, CPA.NOFnil. exact (CC.cps_all_sound _ _ foot_ok i c1 Hc1). }
    pose proof HA2 as (_ & _ & _ & _ & (cr2 & LK2 & HH2 & _) & Hfr2 & _).
    unfold CHA.curB, CHA.curF in HH1, HH2. rewrite CPA.NOBnil, CPA.NOFnil in HH1, HH2. cbn [CH2.den CHA.denF map app] in HH1, HH2.
    refine (SXA.xi_goto (hl_segs L) G.CPS txt P' F sp E0 M U2 U10 U32 U33 R_SP R_F R_Q Tb Tn Tr i c1 ps j cj s E R1 (CCA.vis A1 m1 M1) E' R' (CCA.vis A1 m2 M2)
              Hc1 Hcj (CUT i c1 Hc1) (CUT j cj Hcj) Hg G2 HAt1 HagE _ HX Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _).
    + exact (TVof _ _ _ _ _ HH1 Hfr1).
    + exact (TVof _ _ _ _ _ HH2 Hfr2).
  - (* [comment removed for export] *)
    intros i c1 k ps pc IL Hne. exfalso. pose proof (CH2.leaves_all_sound _ _ _ tagpc_ok _ _ _ _ _ IL) as X. unfold tagpc in X. apply Z.eqb_eq in X. subst pc.
    vm_compute in Hne. discriminate Hne.
  - (* [comment removed for export] *)
    intros i c1 k ps pc IL Hin fx' E R1 A1 M1 m1 E' R' M2 m2 HAt1 HAX HFP1 Hag HLF model2 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HagE' HA'.
    pose proof HAX as [HA1 HX]. destruct IL as (tags & Hc1 & Htags & Hps & Htag).
    pose proof (CH2.leaves_all_nth G.CPS G.TAGS lchk leaves_ok i c1 tags k ps _ Hc1 Htags Hps Htag) as X. unfold lchk, SXS.leaf_chk in X.
    pose proof HA1 as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & Hfra & _). pose proof HA' as (_ & _ & _ & _ & (crb & LKb & HHb & _) & Hfrb & _).
    unfold CHA.curB, CHA.curF in HHa, HHb. rewrite CPA.NOBnil, CPA.NOFnil in HHa, HHb. cbn [CH2.den CHA.denF map app] in HHa, HHb.
    destruct (SXA.exit_ok (hl_segs L) G.CPS RET_PC txt P' F sp E0 M U2 U10 U32 U33 R_SP R_F R_Q Tb Tn Tr i c1 ps E R1 (CCA.vis A1 m1 M1) E' R' (CCA.vis A1 m2 M2)
                Hc1 (CUT i c1 Hc1) X HAt1 HagE (TVof _ _ _ _ _ HHa Hfra) HX Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) (TVof _ _ _ _ _ HHb Hfrb)) as (Hpc' & Hcs & Hpost).
    pose proof (CBA.amb_off L ar C HI HIok LYB SXS.NF E0 M model A LB FF LK sp G.HDECL W (CPA.NOB G.CPS) (CPA.NOF G.CPS) (CPA.Cred0 cr) 0 i E A1 M2 m2 HA') as Hoff.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M2 model2 LB cr LB W LK1 A1 HFP1); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [| repeat split; reflexivity]. unfold PDCA.scx_postA. cbn [PDC.a_img_lo PDC.a_img_hi PDCA.xboth].
    destruct (PD.exp_scan txt) as [kk|]; destruct Hpost as [Hu Ha0]; (split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hu) | exact Ha0]).
  - exact Hci.
  - (* [comment removed for export] *)
    split.
    + apply DOK.regs_ok_tmpl. intros n Hn. pose proof (DOK.rz_word R 11 1 Ra1) as W11.
      unfold c, entry_cp. destruct (N =? 0); [|destruct (N =? 1)]; (do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; exact W11)]|]); lia).
    + set (H := ahid A model). set (Mv := CCA.vis A model M). change (CCA.vis A model M) with Mv.
      assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
      assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = P' + o) by (intros o; apply (DOS.estart_reg E0 32 o P' U32)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      assert (ELN : elenZ E0 (EVar 33) = N) by exact U33.
      assert (ELN1 : elenZ E0 (EAlu ALU_ADD (EVar 33) (ELit 1)) = N + 1).
      { unfold elenZ. cbn [edenot]. rewrite u_add64, U33. rewrite u64_of_Z by lia. apply Z.mod_small. lia. }
      assert (ESN : estart E0 (SA (EAlu ALU_ADD (EVar 32) (EVar 33)) 0) = P' + N).
      { unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32, U33. rewrite Z.mod_small by lia. lia. }
      assert (KN : forall lo hi, lo <= N <= hi -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 33) lo hi)) by (intros lo hi Hr; cbn [kentry_ok edenot]; rewrite U33; exact Hr).
      assert (DS : L5.defined Mv (sp - 80) 80) by (exact (CL5A.defined_vis H M _ _ VS S5)).
      assert (DT : L5.defined Mv P' (N + 1)) by (exact (CL5A.defined_vis H M _ _ VT Td)).
      assert (WF8 : L5.writable (hl_segs L) Mv (F + 8) 8) by (apply (CPA.writable_vis (hl_segs L) H M); [lia | lia | exact (CL5A.visr_sub _ (F + 8) 192 (F + 8) 8 VF ltac:(lia) ltac:(lia)) | exact Hfw]).
      assert (U64 : forall o v, 8 <= o -> o + 8 <= 200 -> L5.u64_at (hl_segs L) M (F + o) v -> L5.u64_at (hl_segs L) Mv (F + o) v).
      { intros o v H1 H2 Hu. apply (CL5A.u64_vis (hl_segs L) H M); [lia | lia | apply (CL5A.visr_sub _ (F + 8) 192 (F + o) 8 VF); lia | exact Hu]. }
      assert (REST : forall lo hi, lo <= N <= hi -> know_ok (hl_segs L) E0 Mv
                [KRange (EVar 2) 140735332483152 140737488355328; KAlign (EVar 2) 16; KImg 65536 1466368; KWr (SA (EVar 2) (-80)) (ELit 80); KWr (SA (EVar 10) 8) (ELit 8);
                 KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-80)) (ELit 80); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) lo hi;
                 KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615); KWord (SA (EVar 10) 192) 8 (ELit 0); KUnk (SA (EVar 32) 0) (EVar 33);
                 KZero (SA (EAlu ALU_ADD (EVar 32) (EVar 33)) 0) (ELit 1); KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 33) (ELit 1)) (SA (EVar 2) (-80)) (ELit 80);
                 KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 33) (ELit 1)) (SA (EVar 10) 8) (ELit 192); KWord (SA (EVar 10) 8) 8 (EVar 32); KUnk (SA (EVar 2) (-80)) (ELit 80)]).
      { intros lo hi Hr. unfold know_ok.
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact S1]|].
        apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia |]]; intros a Ha; unfold Mv, CCA.vis, mrestrict; destruct (ahid A model (Z_to_bv 64 a)); [reflexivity | exact (Himg a Ha)]|].
        apply Forall_cons; [apply (CL5.kwr_intro (hl_segs L) E0 Mv _ _ (sp - 80) 80); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS]|].
        apply Forall_cons; [apply (DOK.kwr_of_writable (hl_segs L) E0 Mv _ _ (F + 8) 8); [rewrite ES10; lia | apply EL; lia | lia | lia | lia | lia | exact WF8]|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES10, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
        apply Forall_cons; [exact (KN lo hi Hr)|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES10; lia | lia | lia | reflexivity | apply U64; [lia | lia | exact Hf184]]|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 192) 0); [rewrite ES10; lia | lia | lia | reflexivity | apply U64; [lia | lia | exact Hf192]]|].
        apply Forall_cons; [apply (CL5.kunk_intro (hl_segs L) E0 Mv _ _ P' N); [rewrite ES32; lia | exact ELN | lia | lia | lia | intros d Hd; apply DT; lia]|].
        apply Forall_cons; [apply (DOK.kzero1_intro (hl_segs L) E0 Mv _ (P' + N)); [rewrite ESN; lia | lia | lia | | apply DT; lia]|].
        { apply (CL5A.u8_vis (hl_segs L) H M); [lia | lia | apply (CL5A.visr_sub _ P' (N + 1) (P' + N) 1 VT); lia | exact Tn]. }
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, ELN1, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, ELN1, !EL by lia; lia|].
        apply Forall_cons; [apply (CL5.kword64_intro (hl_segs L) E0 Mv _ _ (F + 8) P'); [rewrite ES10; lia | lia | lia | reflexivity | apply U64; [lia | lia | exact Hf8]]|].
        apply Forall_cons; [apply (CL5.kunk_intro (hl_segs L) E0 Mv _ _ (sp - 80) 80); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact DS] | constructor]. }
      unfold c, entry_cp. destruct (Z.eqb_spec N 0); [|destruct (Z.eqb_spec N 1)].
      * exact (REST 0 0 ltac:(lia)).
      * exact (REST 1 1 ltac:(lia)).
      * exact (REST 2 67108864 ltac:(lia)).
  - unfold SXS.XI. rewrite Hci, Hki. exact I.
  - exact HH.
  - exact Hmo.
  - exact Hroom.
  - exact Hfp.
Qed.
End Run.
End SXOA.
