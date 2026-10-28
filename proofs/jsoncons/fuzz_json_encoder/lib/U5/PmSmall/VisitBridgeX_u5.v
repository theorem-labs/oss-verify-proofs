(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBX.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition VIS_SCR : Z := 10624.     (* [comment removed for export] *)
Definition S2V : expr := EVar 52.     (* [comment removed for export] *)

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable LBo : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
(* [comment removed for export] *)
Definition gB (g : eghost) : list (Z * Z) := g_lbv g.
Variable CredV : eghost -> nat -> env -> credit -> Prop.
Variable XIv : eghost -> nat -> env -> mem -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - CH.hd_scr d) (CH.hd_scr d).
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis W_ENC : forall w, In w (W_enc V S2) -> In w W.
(* [comment removed for export] *)
Variable VB : expr.
Hypothesis VB_frozen : APC.expr_vars_lt NF VB = true.
Hypothesis VADDR : uv E0 VB = V.
Hypothesis S2_frozen : (52 < NF)%nat.
Hypothesis S2ADDR : uv E0 S2V = S2.
Hypothesis LITLEN : PML.LIT_HI - PML.LIT_LO = VSX.LIT_LEN.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS eghost gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

(* [comment removed for export] *)
Definition vis_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  match split_lit (nth 10 regs (ELit 0)) with
  | (vb, vk) =>
      if (expr_eqb vb VB && Z.eqb vk 0 && CH2.blocks_eqb BLj BLi)%bool
      then CH2.custom_chk NF d VIS_SCR 0 BLi (VSX.wregs vb vk PML.LIT_LO) [] (Some (ELit 1)) c ps cj BLi
      else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vis_leaf_ok : forall (pc : Z) (Post : env -> eghost -> mem -> Prop) (RetC : env -> eghost -> credit -> Prop) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  vis_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost gB g) sp0 d W BLS (CredV g) VIS_SCR 0 c ps cj ci i E E' R' M' model ->
     getr R' 10%bv = Z_to_bv 64 V ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g) cr M' (m_vmmaps model) -> CredV g i E cr -> PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc, PML.fp_ok fx2 ->
           (exists g', PML.a0 R2 1 /\ Post E g' M2 /\ LB' = (CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g' /\ LBk = CH2.den E' (nth i BLS []) ++ LBo /\
                       Wc = W_enc V S2 /\ RetC E g' cr') ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) VIS_SCR Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g' cr', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo) (sp0 + CH2.ci_csp ci) VIS_SCR (W_enc V S2) M' M2 ->
     hl_sptop L - 2 ^ 23 + VIS_SCR <= sp0 + CH2.ci_csp ci -> sp0 + CH2.ci_csp ci <= sp0 ->
     Post E g' M2 -> RetC E g' cr' -> XIv g' j E2 M2 /\ CredV g' j E2 cr') ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc Post RetC i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk CALL XIRET fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0].
  unfold vis_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [vb vk] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. subst vb vk.
  apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c VIS_SCR 0%nat BLi _ _ (Some (ELit 1)) i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d VIS_SCR 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  assert (HV : PB.uv E' VB = V) by (rewrite (PB.uv_agree NF E0 E' VB HagE' VB_frozen); exact VADDR).
  assert (HS2 : bv_unsigned (ev E' 52) = S2).
  { pose proof HagE' as [X _]. rewrite <- (X 52%nat S2_frozen). exact S2ADDR. }
  pose proof STK as (S1 & S2' & S3 & S4 & S5).
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 V).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. unfold estart. cbn [a_base a_off]. rewrite Z.add_0_r. exact HV. }
  unfold PB.uv in HV.
  assert (HH' : hi_heap HI ((own ++ LBo) ++ g_lbv g) cr M' (m_vmmaps model)) by (rewrite <- app_assoc; exact HH).
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF Ga0 HH' HC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (g' & HA1 & HPost & -> & -> & HWc & HRC) HRP HPRES Hbv2 HH2.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  (* [comment removed for export] *)
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  eapply (RET fx2 R2 M2 model2 [] (own ++ LBo) Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. exact Hb.
  - (* [comment removed for export] *)
    intros w a Hw Hin. subst Wc. unfold W_enc in Hw. unfold VSX.wregs.
    destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (VB, 0 + 264, ELit 40). split; [left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite HV. rewrite u64_of_Z by lia. unfold O_STACK in Hin. lia.
    + exists (VB, 0 + 400, ELit 4). split; [right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite HV. rewrite u64_of_Z by lia. unfold O_DEPTH in Hin. lia.
    + exists (S2V, 0, ELit 24). split; [right; right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ, S2V. cbn [a_base a_off edenot]. rewrite HS2. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, PML.LIT_LO, ELit VSX.LIT_LEN). split; [right; right; right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (unfold VSX.LIT_LEN; lia). rewrite <- LITLEN. lia.
  - intros X [].
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo eghost gB g') BLS j E2 = own ++ LBo ++ g_lbv g').
    { unfold CH2.cur, CH2V.LBr, gB. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    assert (Hspc : hl_sptop L - 2 ^ 23 + VIS_SCR <= sp0 + CH2.ci_csp ci /\ sp0 + CH2.ci_csp ci <= sp0).
    { destruct Hstk as (_ & Q2 & Q3 & _). split; [exact Q2 | lia]. }
    subst Wc.
    destruct (XIRET E E' R' M M' E2 M2 g' cr' HXI0 HagE' Hag HLF Hag2 V3 HPRES (proj1 Hspc) (proj2 Hspc) HPost HRC) as [HXI2 HC2].
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV STK SCR_pos NF32 DEF0 g g' M0c VIS_SCR 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo) (W_enc V S2) cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). exact (Hout w (W_ENC w Hw) Hin).
    + exact Hbv2.
    + rewrite Hcur. rewrite app_assoc. exact HH2.
    + exact Hag2.
    + exact HC2.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv g' M2 j E2 M2 model2 OK2).
      split; [exact HA2 | exact HXI2].
  Unshelve. cbv beta iota. rewrite HA1. reflexivity.
Qed.
End Inst.
End VBX.
