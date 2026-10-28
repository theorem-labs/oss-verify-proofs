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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridgesU EncStrans_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EHCU.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

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
Variable GR : list (Z * Z).
Variable kx bx : Z.
Variable XIv : eghost -> nat -> env -> mem -> Prop.
Abbreviation gB := (EBU.gB GR).
Abbreviation CredV := (EBU.CredV L kx bx).

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
Variables V S2 : Z.
Hypothesis OBJS : objs_enc L sp0 V S2.
Hypothesis W_S2 : In (S2, 24) W.
Hypothesis W_COL : forall a, V + O_COLUMN <= a < V + O_COLUMN + 8 -> exists w, In w W /\ L5.in_rng w a.
(* [comment removed for export] *)
Variable S2E : expr.
Hypothesis S2E_frozen : APC.expr_vars_lt NF S2E = true.
Hypothesis S2ADDR : uv E0 S2E = S2.
Hypothesis V10 : uv E0 (EVar 10) = V.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS eghost gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Lemma objs_facts : sp0 <= V /\ V + 408 <= hl_sptop L /\ V mod 8 = 0 /\ sp0 <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0 /\ PML.apart V 408 S2 24.
Proof. destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE in *. repeat split; assumption. Qed.

(* [comment removed for export] *)
Definition hcol_chk (scr : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (CH2.blocks_eqb BLj BLi && expr_eqb (nth 10 regs (ELit 0)) (EVar 10))%bool
  then CH2.custom_chk NF d scr 0 BLi [(EVar 10, 296, ELit 8); (S2E, 0, ELit 24)] [] None c ps cj BLi
  else None.

(* [comment removed for export] *)
Lemma hcol_leaf_okV : forall (pc scr : Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  hcol_chk scr c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost gB g) sp0 d W BLS (CredV g) scr 0 c ps cj ci i E E' R' M' model ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) cr M' (m_vmmaps model) -> ecreditU L cr g kx bx -> PML.fp_ok fx' ->
     getr R' 10%bv = Z_to_bv 64 V ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc (g' : eghost), PML.fp_ok fx2 ->
           g_sb g' = g_sb g -> g_scap g' = g_scap g ->
           LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g') -> LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR -> Wc = W_h V S2 ->
           ecreditU L cr' g' kx bx ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           XIv g' j (CH2.retEx E' (CH2.ci_nx ci) [] R2) M2 ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk CALL fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0]. unfold hcol_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [B3 R10]. apply CH2.blocks_eqb_eq in B3. apply expr_eqb_eq in R10.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c scr 0%nat BLi _ _ None i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  (* [comment removed for export] *)
  assert (PERMG : forall g1, Permutation (own ++ LBo ++ gB g1) ((own ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g1))).
  { intros g1. unfold EBU.gB. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH (PERMG g)) as HH1.
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 V).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq, R10. cbn [edenot].
    destruct HagE' as [AG _]. rewrite <- (AG 10%nat) by lia. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E0 10)). f_equal. exact V10. }
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HH1 HC HFP Ga0) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc g' HFP2 Gsb Gscap -> -> -> HCe' HRP HPRES Hbv2 HH2 HXI2.
  assert (GBEQ : forall g1, g_sb g1 = g_sb g -> g_scap g1 = g_scap g -> gB g1 = PML.srep_blocks (g_rep g1) ++ GR) by (intros g1 _ _; reflexivity).
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 (Permutation_sym (PERMG g'))) as HH2'.
  assert (HC' : CredV g' j (CH2.retEx E' (CH2.ci_nx ci) [] R2) cr') by exact HCe'.
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (HV10 : uv E' (EVar 10) = V) by (destruct HagE' as [AG _]; unfold uv, PB.uv; cbn [edenot]; rewrite <- (AG 10%nat) by lia; exact V10).
  assert (HS2E : uv E' S2E = S2) by (unfold uv; rewrite (PB.uv_agree NF E0 E' S2E HagE' S2E_frozen); exact S2ADDR).
  eapply (RET fx2 R2 M2 model2 [] (own ++ LBo ++ GR) (W_h V S2) eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros bb Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng, O_COLUMN in Hin; cbn [fst snd] in Hin.
    + exists (EVar 10, 296, ELit 8). split; [left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. change (bv_unsigned (ev E' 10)) with (uv E' (EVar 10)). rewrite HV10.
      rewrite u64_of_Z by lia. lia.
    + exists (S2E, 0, ELit 24). split; [right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. change (bv_unsigned (edenot E' S2E)) with (uv E' S2E). rewrite HS2E.
      rewrite u64_of_Z by lia. lia.
  - intros X [].
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo eghost gB g') BLS j E2 = own ++ LBo ++ gB g').
    { unfold CH2.cur, CH2V.LBr. rewrite B3. fold BLi. unfold own.
      rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV STK SCR_pos NF32 DEF0 g g' M0c scr 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo ++ GR) (W_h V S2) cr' HOKV CF HPRES) as [OK2 HA2].
    + intros bb Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct Hw as [<-|[<-|[]]].
      * destruct (W_COL a ltac:(unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia)) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
      * exact (Hout (S2, 24) W_S2 Hin).
    + exact Hbv2.
    + rewrite Hcur. exact HH2'.
    + exact Hag2.
    + exact HC'.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv g' M2 j E2 M2 model2 OK2). split; [exact HA2 | exact HXI2].
Qed.
End Inst.
End EHCU.
