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
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EPU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

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
Variable G : Type.
Variable gB : G -> list (Z * Z).
Variable CredV : G -> nat -> env -> credit -> Prop.
Variable XIv : G -> nat -> env -> mem -> Prop.

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
Hypothesis CredV_iE : forall g i j E E' cr, CredV g i E cr -> CredV g j E' cr.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS G gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

(* [comment removed for export] *)
Definition wfree (a : Z) : Prop :=
  (sp0 - CH.hd_scr d <= a < sp0) \/ (0 <= a < 2 ^ 64 /\ (forall LB, ~ alloc_private L LB a) /\ ~ L5C.kept L LBo sp0 (CH.hd_scr d) W a).

(* [comment removed for export] *)
Lemma stack_not_private : forall LB a, hl_ceil L <= a -> a < hl_sptop L -> ~ alloc_private L LB a.
Proof.
  intros LB a H1 H2 [(P & _)|P]; [lia|]. destruct (LYR a P) as [Q|Q]; [|lia].
  pose proof (PmLayout.ly_img_hi L LAY) as IH. destruct LYI as [_ I2]. unfold hl_ceil in H1. lia.
Qed.

(* [comment removed for export] *)
Lemma pure_leaf_okV : forall (pc scr : Z) wregs news a0x i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  CH2.custom_chk NF d scr 0 (nth i BLS []) wregs news a0x c ps cj (nth i BLS []) = Some ci ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo G gB g) sp0 d W BLS (CredV g) scr 0 c ps cj ci i E E' R' M' model ->
     hi_heap HI (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) cr M' (m_vmmaps model) -> CredV g i E cr -> PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) Wc, PML.fp_ok fx2 ->
           (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
           match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) [] R2) e | None => True end ->
           L5.frame_but ((sp0 + CH2.ci_csp ci - scr, scr) :: Wc) M' M2 -> mem_grows M' M2 ->
           (forall w a, In w Wc -> L5.in_rng w a -> (exists r, In r wregs /\ CH2.in_reg E' r a) /\ wfree a) ->
           (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) M2 X) ->
           XIv g j (CH2.retEx E' (CH2.ci_nx ci) [] R2) M2 ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr wregs news a0x i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk B3 CALL fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c scr 0%nat BLi _ _ a0x i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  set (LBk := own ++ LBo ++ gB g) in *.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof STK as (S1 & S2' & S3 & S4).
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HH)) as Hwf.
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HH HC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 Wc HFP2 Hkeep Ha0 HFB HGR HWc Hnews HXI2.
  (* [comment removed for export] *)
  assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> (forall w, In w Wc -> ~ L5.in_rng w a) -> ~ (sp0 + CH2.ci_csp ci - scr <= a < sp0 + CH2.ci_csp ci) ->
                 M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hout Hns. apply HFB. rewrite L5.unsigned_lit by exact Ha. intros r [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; lia | exact (Hout r Hr)]. }
  assert (HPRES : L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2).
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (OUTF a K1); [intros w Hw Hin; exact (K4 w Hw Hin)|].
      destruct K2 as [(b & Hb & Hin)|[[C1 C2]|[C1 C2]]]; [|exact C2|].
      + destruct (Hwf b Hb) as ((R0 & R1 & R2' & R3 & R4) & _). lia.
      + pose proof (PmLayout.ly_img_hi L LAY) as IH. destruct LYI as [_ I2]. unfold hl_ceil in *. lia.
    - intros q Hq. apply HGR. destruct Hstk as (_ & _ & _ & _ & T5). apply T5. exact Hq.
    - intros a _ _ _ Hd. apply HGR. exact Hd. }
  assert (HWk : forall w a, In w Wc -> L5.in_rng w a -> ~ L5C.kept L LBo sp0 (CH.hd_scr d) W a).
  { intros w a Hw Hin HKP. destruct (HWc w a Hw Hin) as [_ [X|(_ & _ & X)]]; [|exact (X HKP)].
    destruct HKP as (K1 & K2 & K3 & K4). destruct K2 as [(b & Hb & Hinb)|[[C1 C2]|[C1 C2]]]; [| apply C2; exact X |].
    + destruct (Hwf b ltac:(unfold LBk; apply in_or_app; right; apply in_or_app; left; exact Hb)) as ((R0 & R1 & R2' & R3 & R4) & _). lia.
    + pose proof (PmLayout.ly_img_hi L LAY) as IH. destruct LYI as [_ I2]. unfold hl_ceil in *. lia. }
  (* [comment removed for export] *)
  assert (HH2 : hi_heap HI LBk cr M2 (m_vmmaps model)).
  { apply (hio_frame L SCFG HI HIok LBk cr M' M2 _ HH); [|intros x Hx; apply HGR; exact Hx].
    intros a Ha Hpriv. apply (OUTF a Ha).
    - intros w Hw Hin. destruct (HWc w a Hw Hin) as [_ [X|(_ & X & _)]]; [|exact (X LBk Hpriv)].
      apply (stack_not_private LBk a); [lia | lia | exact Hpriv].
    - intros Hin. apply (stack_not_private LBk a); [lia | lia | exact Hpriv]. }
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  eapply (RET fx2 R2 M2 model [] LBk Wc eq_refl HFP2 Hkeep Ha0 HPRES).
  - intros b Hb. unfold LBk. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. exact (proj1 (HWc w a Hw Hin)).
  - exact Hnews.
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo G gB g) BLS j E2 = LBk).
    { unfold CH2.cur, CH2V.LBr, LBk. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    pose proof (CredV_iE g i j E E2 cr HC) as HC2.
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS G gB CredV STK SCR_pos NF32 DEF0 g g M0c scr 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model LBk Wc cr HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. unfold LBk. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + exact HWk.
    + apply L5C.model_but_vm_refl.
    + rewrite Hcur. exact HH2.
    + exact Hag2.
    + exact HC2.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv g M2 j E2 M2 model OK2). split; [exact HA2 | exact HXI2].
Qed.

End Inst.
End EPU.
