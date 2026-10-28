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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ESBU.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Record sghost : Type := SG { s_rep : PML.srep; s_len : Z }.
(* [comment removed for export] *)
Definition sink_inv (M : mem) (S2 : Z) (g : sghost) : Prop := sink_at M S2 (s_rep g) /\ len (PML.srep_chars (s_rep g)) = s_len g.

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
Variable GR : list (Z * Z).
Definition gB (g : sghost) : list (Z * Z) := PML.srep_blocks (s_rep g) ++ GR.
Variable kx bx : Z.
Definition CredV (g : sghost) (i : nat) (E : env) (cr : credit) : Prop := screditU L cr (s_rep g) kx bx.
Variable XIv : sghost -> nat -> env -> mem -> Prop.

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
Variable S2 : Z.
Hypothesis S2OBJ : PML.obj_on_stack L sp0 S2 24.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : estart E0 (SA OB OK) = S2.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS sghost gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Definition STR_SCR : Z := 8496.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition g_upd (g : sghost) (rep' : PML.srep) (n : Z) : sghost := SG rep' (s_len g + n).

(* [comment removed for export] *)
Definition sink_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  match split_lit (nth 10 regs (ELit 0)) with
  | (ob, ok) =>
      if (expr_eqb ob OB && Z.eqb ok OK && CH2.blocks_eqb BLj BLi)%bool
      then CH2.custom_chk NF d STR_SCR 0 BLi [(ob, ok, ELit 24)] [] None c ps cj BLi
      else None
  end.

Lemma objs_facts : sp0 <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0.
Proof. exact S2OBJ. Qed.

Lemma den_app_nodup : forall (own : list (Z * Z)) rep cr (M : mem) VM, hi_heap HI (own ++ LBo ++ PML.srep_blocks rep ++ GR) cr M VM ->
  lb_drop rep (own ++ LBo ++ PML.srep_blocks rep ++ GR) = own ++ LBo ++ GR.
Proof.
  intros own rep cr M VM HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  destruct rep as [s|cap p s]; cbn [lb_drop PML.srep_blocks app] in *; [reflexivity|].
  rewrite app_assoc. rewrite EK.lb_remove_app.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. rewrite <- app_assoc. reflexivity.
  - rewrite app_assoc, map_app in Hnd. apply (EK.nodup_app_l' _ _ p Hnd). cbn [map fst In]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grow_leaf_ok : forall (pc n : Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  sink_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     sink_inv M' S2 g /\ s_len g + n <= CLU) ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo sghost gB g) sp0 d W BLS (CredV g) STR_SCR 0 c ps cj ci i E E' R' M' model ->
     sink_inv M' S2 g -> s_len g + n <= CLU -> getr R' 10%bv = Z_to_bv 64 S2 ->
     hi_heap HI (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr M' (m_vmmaps model) -> CredV g i E cr -> PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc, PML.fp_ok fx2 ->
           (exists rep' s', len s' = s_len g + n /\
              x_grownU L (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr M2 S2 (s_rep g) s' LB' cr' LBk rep' /\ Wc = [(S2, 24)]) ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) STR_SCR Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> sink_inv M2 S2 g' -> s_len g' = s_len g + n ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc n i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk XILEAF CALL XIRET fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0].
  unfold sink_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. subst ob ok.
  apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c STR_SCR 0%nat BLi _ _ None i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  (* [comment removed for export] *)
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d STR_SCR 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  destruct (XILEAF E R M model E' R' M' HAt HAmbH HXI0 Hag HLF) as [HINV HROOM].
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  assert (Ho : estart E' (SA OB OK) = S2) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct objs_facts as (O3 & O4 & O5). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 S2).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV HROOM Ga0 HH HC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & s' & Hls' & Hgrown & HWc) HRP HPRES Hbv2 HH2.
  (* [comment removed for export] *)
  pose proof (den_app_nodup own (s_rep g) cr M' _ HH) as Hdrop. unfold gB in Hgrown, HH. fold own in Hgrown.
  pose proof (PmLayout.ly_kpm L LAY) as KPM. pose proof (PmLayout.ly_bov L LAY) as BOV.
  assert (Hrep8 : match s_rep g with PML.SShort _ => True | PML.SLong cap _ _ => 8 <= cap /\ cap mod 8 = 0 end).
  { destruct HINV as ((Hs1 & _ & Hs3) & _). destruct (s_rep g) as [s|cap p s]; [exact I|]. cbn [rep_ok PML.str_at] in *. destruct Hs1 as (_ & Hm & _). split; [lia | exact Hm]. }
  assert (Hcl : len s' <= CLU) by lia.
  pose proof (EK.grown_screditU L KPM BOV _ _ _ _ _ _ _ _ _ _ kx bx Hgrown Hrep8 Hcl HC) as HC'.
  assert (FACTS : sink_at M2 S2 rep' /\ len (PML.srep_chars rep') = s_len g + n /\ LBk = own ++ LBo ++ GR /\ Permutation LB' (own ++ LBo ++ PML.srep_blocks rep' ++ GR)).
  { destruct Hgrown as [(F & -> & Hs & -> & _ & ->)|(NFt & p' & Gx)].
    - split; [exact Hs|]. split; [destruct (s_rep g); cbn [same_rep PML.srep_chars]; exact Hls'|]. split; [exact Hdrop|].
      destruct (s_rep g); cbn [same_rep PML.srep_blocks]; apply Permutation_refl.
    - cbv zeta in Gx. destruct Gx as (-> & Hs & FB & -> & _ & ->). split; [exact Hs|]. split; [cbn [PML.srep_chars]; exact Hls'|]. split; [exact Hdrop|].
      rewrite Hdrop. cbn [PML.srep_blocks app]. rewrite !app_assoc. apply Permutation_middle. }
  destruct FACTS as (Hsink2 & Hlen2 & -> & Hperm).
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 Hperm) as HH2'.
  assert (Hbr : forall b, In b (own ++ LBo ++ GR) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). apply (Hwf b).
    apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; right; exact Hb]. }
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HINV2 : sink_inv M2 S2 (g_upd g rep' n)) by (split; [exact Hsink2 | exact Hlen2]).
  (* [comment removed for export] *)
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  eapply (RET fx2 R2 M2 model2 [] (own ++ LBo ++ GR) Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  - intros X [].
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo sghost gB (g_upd g rep' n)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
    { unfold CH2.cur, CH2V.LBr, gB, g_upd. cbn [s_rep]. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV STK SCR_pos NF32 DEF0 g (g_upd g rep' n) M0c STR_SCR 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo ++ GR) Wc cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. exact (Hout (S2, 24) W_S2 Hin).
    + exact Hbv2.
    + rewrite Hcur. exact HH2'.
    + exact Hag2.
    + exact HC'.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv (g_upd g rep' n) M2 j E2 M2 model2 OK2).
      split; [exact HA2|].
      apply (XIRET E E' R' M M' E2 M2 (g_upd g rep' n) HXI0 HagE' Hag HLF Hag2 V3 HINV2). reflexivity.
Qed.

Lemma strx_scr : STRX_SCR = STR_SCR.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Hypothesis PUSHB : str_push_back_x_specU L HI.
Definition pushb_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  if APC.fact_ok (SR.ps_cells ps) (KRange (nth 11 (CA.ps_reglist ps) (ELit 0)) 0 255) then sink_chk c ps cj BLi BLj else None.

Lemma pushb_leaf_ok : forall i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther PML.PC_STR_PUSH_BACK) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_STR_PUSH_BACK ->
  pushb_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     sink_inv M' S2 g /\ s_len g + 1 <= CLU) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> sink_inv M2 S2 g' -> s_len g' = s_len g + 1 ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk XILEAF XIRET.
  unfold pushb_chk in Hchk. destruct (APC.fact_ok (SR.ps_cells ps) (KRange (nth 11 (CA.ps_reglist ps) (ELit 0)) 0 255)) eqn:B5; [|discriminate].
  apply (grow_leaf_ok PML.PC_STR_PUSH_BACK 1 i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk XILEAF); [|exact XIRET].
  intros E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV Hroom Ga0 HH HC HFP.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  destruct HA' as (Hmo & _).
  pose proof HK as HK0. rewrite LS in HK.
  pose proof (PB.fact_ok' E' M' _ _ HK B5) as Hc255. cbn [kentry_ok] in Hc255. set (cv := bv_unsigned (edenot E' (nth 11 (CA.ps_reglist ps) (ELit 0)))) in *.
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 cv).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold cv. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct objs_facts as (O3 & O4 & O5).
  pose proof HINV as (Hsink & Hlen).
  intros Hk.
  apply (PUSHB (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr S2 cv (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) (s_rep g) fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | rewrite strx_scr; exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hsink|].
    split; [unfold gB; destruct (s_rep g) as [s|cap p s]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; apply in_or_app; right; left; reflexivity]|].
    split; [unfold PML.obj_on_stack; lia|].
    intros HNF. apply (EK.grow_okU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr (s_rep g) kx bx _ HC (EK.rep8_of_sink _ _ _ Hsink));
      [unfold len; lia | lia | exact HNF]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & Hgr & HWc) HRP HPRES Hbv2 HH2.
  apply (Hk fx2 R2 M2 model2 LB' cr' LBk Wc HFP2); [| exact HRP | rewrite <- strx_scr; exact HPRES | exact Hbv2 | exact HH2].
  exists rep', (PML.srep_chars (s_rep g) ++ [cv]). split; [|split; [exact Hgr | exact HWc]].
  unfold len in *. rewrite length_app, Nat2Z.inj_add. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Hypothesis APPEND : str_append_x_specU L HI.
Lemma append_leaf_ok : forall (n : Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther PML.PC_STR_APPEND) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = PML.PC_STR_APPEND ->
  sink_chk c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     sink_inv M' S2 g /\ s_len g + n <= CLU) ->
  (forall E R (M : mem) model E' R' (M' : mem) cr, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo sghost gB g) sp0 d W BLS (CredV g) STR_SCR 0 c ps cj ci i E E' R' M' model ->
     sink_inv M' S2 g -> hi_heap HI (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr M' (m_vmmaps model) ->
     exists q src, PML.a1 R' q /\ PML.a2 R' (len src) /\ len src = n /\ L5.bytes_at RSEGS M' q src /\
                   src_ok L M' (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) (sp0 + CH2.ci_csp ci) S2 (s_rep g) q (len src) /\
                   len (PML.srep_chars (s_rep g)) + len src < 2 ^ 47) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> sink_inv M2 S2 g' -> s_len g' = s_len g + n ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros n i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk XILEAF SRC XIRET.
  apply (grow_leaf_ok PML.PC_STR_APPEND n i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk XILEAF); [|exact XIRET].
  intros E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV Hroom Ga0 HH HC HFP.
  destruct (SRC E R M model E' R' M' cr HAt HAmbH HXI0 Hag HLF CF HINV HH) as (q & src & Ga1 & Ga2 & Hn & Hbytes & Hsrc & Hlt).
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  destruct HA' as (Hmo & _).
  destruct objs_facts as (O3 & O4 & O5).
  pose proof HINV as (Hsink & Hlen).
  intros Hk.
  apply (APPEND (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr S2 q (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) (s_rep g) src fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | rewrite strx_scr; exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [exact Hsink|].
    split; [unfold gB; destruct (s_rep g) as [s|cap p s]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; apply in_or_app; right; left; reflexivity]|].
    split; [unfold PML.obj_on_stack; lia|].
    split; [exact Hbytes|]. split; [exact Hsrc|]. split; [exact Hlt|].
    intros HNF. apply (EK.grow_okU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr (s_rep g) kx bx _ HC (EK.rep8_of_sink _ _ _ Hsink));
      [unfold len; lia | lia | exact HNF]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & s' & Hls' & Hgr & HWc) HRP HPRES Hbv2 HH2.
  apply (Hk fx2 R2 M2 model2 LB' cr' LBk Wc HFP2); [| exact HRP | rewrite <- strx_scr; exact HPRES | exact Hbv2 | exact HH2].
  exists rep', s'. split; [lia | split; [exact Hgr | exact HWc]].
Qed.

(* [comment removed for export] *)
Definition PAYMAX : Z := 2 ^ 50.
(* [comment removed for export] *)
Definition strans_chk (scr : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if CH2.blocks_eqb BLj BLi
  then CH2.custom_chk NF d scr 1 BLi [(OB, OK, ELit 24)] [KRange (EVar nx) 0 PAYMAX] (Some (EVar nx)) c ps cj BLi
  else None.

(* [comment removed for export] *)
Lemma strans_leaf_ok : forall (pc scr : Z) (PayP : Z -> Prop) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  strans_chk scr c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall pay, PayP pay -> 0 <= pay < PAYMAX) ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     sink_inv M' S2 g) ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo sghost gB g) sp0 d W BLS (CredV g) scr 1 c ps cj ci i E E' R' M' model ->
     sink_inv M' S2 g ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (s_rep g)) cr M' (m_vmmaps model) -> screditU L cr (s_rep g) kx bx ->
     PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc, PML.fp_ok fx2 ->
           (exists (rep' : PML.srep) (pay : Z), PayP pay /\ PML.a0 R2 pay /\ sink_at M2 S2 rep' /\
              len (PML.srep_chars rep') = len (PML.srep_chars (s_rep g)) + pay /\
              LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks rep' /\ LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR /\ Wc = [(S2, 24)] /\
              screditU L cr' rep' kx bx) ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  (forall E R (M : mem) model E' R' (M' : mem) E2 (M2 : mem) g' pay, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree NF E0 E' ->
     env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (sp0 + CH2.ci_csp ci) scr [(S2, 24)] M' M2 ->
     sink_inv M2 S2 g' -> s_len g' = s_len g + pay -> PayP pay -> uv E2 (EVar (CH2.ci_nx ci)) = pay ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr PayP i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk PAYB XILEAF CALL XIRET fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0].
  unfold strans_chk in Hchk.
  set (nx := (CC.cp_nx cj - APC.NCS - 1)%nat) in *.
  destruct (CH2.blocks_eqb (nth j BLS []) (nth i BLS [])) eqn:B3; [|discriminate]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c scr 1%nat BLi _ _ (Some (EVar nx)) i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  (* [comment removed for export] *)
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr 1 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof (XILEAF E R M model E' R' M' HAt HAmbH HXI0 Hag HLF) as HINV.
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  assert (Ho : estart E' (SA OB OK) = S2) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct objs_facts as (O3 & O4 & O5). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  (* [comment removed for export] *)
  assert (PERM1 : Permutation (own ++ LBo ++ gB g) ((own ++ LBo ++ GR) ++ PML.srep_blocks (s_rep g))).
  { unfold gB. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH PERM1) as HH1.
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV HH1 HC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & Ha0' & Hsink2 & Hlen' & -> & -> & -> & HSC') HRP HPRES Hbv2 HH2.
  pose proof (PAYB pay HPay) as PR.
  pose proof (PmLayout.ly_kpm L LAY) as KPM.
  assert (Hlen2 : len (PML.srep_chars rep') = s_len g + pay) by (destruct HINV as (_ & I4); lia).
  assert (PERM2 : Permutation ((own ++ LBo ++ GR) ++ PML.srep_blocks rep') (own ++ LBo ++ PML.srep_blocks rep' ++ GR)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 PERM2) as HH2'.
  assert (Hbr : forall b, In b (own ++ LBo ++ GR) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). apply in_or_app. left. exact Hb. }
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HINV2 : sink_inv M2 S2 (g_upd g rep' pay)) by (split; [exact Hsink2 | exact Hlen2]).
  assert (HC' : CredV (g_upd g rep' pay) j (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 pay] R2) cr').
  { exact HSC'. }
  (* [comment removed for export] *)
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 pay] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (G0 : ev E2 nx = Z_to_bv 64 pay).
  { pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci) [Z_to_bv 64 pay] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite Hnx in G. rewrite G. reflexivity. }
  assert (U0 : bv_unsigned (ev E2 nx) = pay) by (rewrite G0; apply u64_of_Z; unfold PAYMAX in PR; lia).
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 pay] (own ++ LBo ++ GR) [(S2, 24)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  - (* [comment removed for export] *)
    intros X [<-|[]] _. fold E2. cbn [kentry_ok edenot]. rewrite U0. unfold PAYMAX in *. lia.
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo sghost gB (g_upd g rep' pay)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
    { unfold CH2.cur, CH2V.LBr, gB, g_upd. cbn [s_rep]. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV STK SCR_pos NF32 DEF0 g (g_upd g rep' pay) M0c scr 1%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo ++ GR) [(S2, 24)] cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct Hw as [<-|[]]. exact (Hout (S2, 24) W_S2 Hin).
    + exact Hbv2.
    + rewrite Hcur. exact HH2'.
    + exact Hag2.
    + exact HC'.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS sghost gB CredV XIv (g_upd g rep' pay) M2 j E2 M2 model2 OK2).
      split; [exact HA2|].
      apply (XIRET E R M model E' R' M' E2 M2 (g_upd g rep' pay) pay HAt HAmbH HXI0 HagE' Hag HLF Hag2 V3 HPRES HINV2); [reflexivity | exact HPay|].
      unfold uv, PB.uv. cbn [edenot]. rewrite Hnx. exact U0.
  Unshelve. cbv beta iota. fold E2. rewrite Ha0'. symmetry. cbn [edenot]. rewrite G0. reflexivity.
Qed.
End Inst.
End ESBU.
