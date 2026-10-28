(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EON.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition OPNEW_SCR : Z := 8240.     (* [comment removed for export] *)

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Hypothesis OPNEWX : opnew_x_spec L HI.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Lemma FLOOR : hl_sptop L - 2 ^ 23 + CH.hd_scr d <= sp0.
Proof. destruct STK as (_ & S2 & _). unfold hl_ceil in S2. lia. Qed.

Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Definition opnew_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  let n := nth 10 regs (ELit 0) in
  if (CH2.blocks_eqb BLj ((EVar nx, n) :: BLi) && CH2.blocks_vars_lt nx BLi && APC.expr_vars_lt nx n
      && forallb (CH2.fresh_fact_ok d ESU.HULL_LO ESU.HULL_HI cells nx BLi nx n) (ESU.blk_facts_n d nx n BLi))%bool
  then CH2.custom_chk NF d OPNEW_SCR 1 BLi [] (ESU.blk_facts_n d nx n BLi) (Some (EVar nx)) c ps cj BLi
  else None.

Lemma opnew_leaf_ok : forall i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_OPNEW) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_OPNEW ->
  opnew_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (* [comment removed for export] *)
  (forall E E' R' (M M' : mem) cr, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
     0 < uv E' (nth 10 (CA.ps_reglist ps) (ELit 0)) < 2 ^ 48 /\ hl_k_per_malloc L <= fst cr /\
     forall E2, env_agree (CH2.ci_nx ci) E' E2 -> Cred j E2 (debit_k L cr)) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) LBk spc, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XI i E M ->
     L5C.hpres L LBk spc OPNEW_SCR [] M' M2 -> incl LBrest LBk -> XI j E2 M2) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros i c k ps j cj ci IL Hret Hcj Hpc Hchk CRED XIBL fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold opnew_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply CH2.blocks_eqb_eq in B1.
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *. set (cells := SR.ps_cells ps) in *. set (ne := nth 10 (CA.ps_reglist ps) (ELit 0)) in *.
  set (BLi := nth i BLS []) in *.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              OPNEW_SCR 1%nat BLi _ _ (Some (EVar nx)) i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.
  destruct (CRED E E' R' M M' cr HagE' Hag HLF HC) as (Hn & Hkpm & HC2). fold ne in Hn. set (n := uv E' ne) in *.
  unfold CH2.cur in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. set (LBc := CH2.den E' BLi ++ LBrest) in *.
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 n).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq. fold ne.
    unfold n, uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hpc. rewrite LS.
  apply (OPNEWX LBc cr n (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Hn | exact Hkpm]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (A & HA0 & HFB & -> & -> & -> & ->) HRP HPRES Hbv2 HH2.
  destruct (CH2.first_block_facts L HI HIok A n LBc (debit_k L cr) M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 A] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (G0 : bv_unsigned (ev E2 nx) = A).
  { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 A] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite Hnx in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
  assert (Un : elenZ E2 ne = n).
  { unfold elenZ. fold (PB.uv E2 ne). rewrite (PB.uv_agree (CH2.ci_nx ci) E' E2 ne Hag2) by (rewrite Hnx; exact B3). reflexivity. }
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 A] LBc [] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. exact Hb.
  - intros w a [].
  - (* [comment removed for export] *)
    intros X HX _. fold E2. rewrite forallb_forall in B4. specialize (B4 X HX).
    exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok ESU.HULL_LO ESU.HULL_HI (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
             E' E2 nx M' M2 BLi cells nx ne A n X HagE' HK0 (eq_ind _ (fun z => env_agree z E' E2) Hag2 _ Hnx) G0 Un BR BA BD B4).
  - (* [comment removed for export] *)
    fold E2.
    assert (Hcur : CH2.cur LBrest BLS j E2 = (A, n) :: LBc).
    { unfold CH2.cur. rewrite B1. unfold CH2.den at 1. cbn [map fst snd edenot]. rewrite G0. fold (CH2.den E2 BLi). fold (elenZ E2 ne). rewrite Un.
      rewrite (CH2.den_agree nx E' E2 BLi (eq_ind _ (fun z => env_agree z E' E2) Hag2 _ Hnx) B2). reflexivity. }
    split; [|apply (XIBL E E' R' M M' E2 M2 LBc (sp0 + CH2.ci_csp ci) HagE' Hag HLF HXI0 HPRES); intros b0 Hb0; unfold LBc; apply in_or_app; right; exact Hb0].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 FLOOR OPNEW_SCR 1%nat c ps cj ci i j E E' R' M' model E2 M2 model2 LBc [] (debit_k L cr) CF HPRES).
    + intros b Hb. unfold LBc. apply in_or_app. right. exact Hb.
    + intros w a [].
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + exact Hag2.
    + apply HC2. exact Hag2.
  Unshelve. cbv beta iota. fold E2. rewrite HA0. symmetry. cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E2 nx)). rewrite G0. reflexivity.
Qed.
End Inst.
End EON.
