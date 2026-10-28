(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Arr FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import WdHead_u WdTail_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require Import TuWdBr_u TuWdGl_u TuWdCert_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TWD.
Definition REGS16 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp16.
Definition KNOW16 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp16.
Lemma regs16 : CC.cp_regs Cut_cwd_csrc_u.cp16 = REGS16. Proof. vmc_refl. Qed.
Lemma know16 : CC.cp_know Cut_cwd_csrc_u.cp16 = KNOW16. Proof. vmc_refl. Qed.
Section TuWdOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis SNP : PMFC.snprintf_g_spec L.
Hypothesis DSG : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.

Lemma ro1_of_u8 : forall (M : PML.mem) a v, L5.u8_at PML.RSEGS M a v -> 0 <= a -> a + 1 <= 2 ^ 64 -> ro_cells rsegs M a [C1 (Z_to_bv 8 v)].
Proof.
  intros M a v H H0 H1. split; [cbn; tauto|]. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i. cbn [cells_bytes cbytes app nth_error]. rewrite Z.add_0_r.
  unfold L5.u8_at in H. cbn [rdn] in H. unfold mrd, wa. destruct (M (Z_to_bv 64 a)); [injection H as <-; reflexivity|].
  destruct (seg_rom _ (Z_to_bv 64 a)); [injection H as <-; reflexivity | discriminate].
Qed.

Lemma regs_ok_of : forall E (sr : list expr) (R : bvmap 5 word),
  (forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0).
    unfold getr. rewrite Hr0. reflexivity.
  - rewrite <- (ridx_roundtrip r) at 1. apply H. split; [|exact (ridx_range r)].
    destruct (Nat.eq_dec (ridx r) 0) as [E0|E0]; [|lia].
    exfalso. assert (r = 0%bv) as -> by (rewrite <- (ridx_roundtrip r), E0; apply bv_eq; reflexivity). discriminate Hr0.
Qed.

Lemma rp_intro : forall R R2 : bvmap 5 word,
  (forall k, In k callee_saved_idx -> getr R2 (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)) -> regs_preserved R R2.
Proof. intros R R2 H y Hy. rewrite <- (definitions.Z_to_bv_bv_unsigned _ y). apply H. exact Hy. Qed.
Lemma getr_lit2 : forall R : bvmap 5 word, getr R (Z_to_bv 5 2) = getr R 2%bv. Proof. intros R. reflexivity. Qed.
Lemma getr_lit8 : forall R : bvmap 5 word, getr R (Z_to_bv 5 8) = getr R 8%bv. Proof. intros R. reflexivity. Qed.
Lemma getr_lit9 : forall R : bvmap 5 word, getr R (Z_to_bv 5 9) = getr R 9%bv. Proof. intros R. reflexivity. Qed.

Section Call.
Variables (LB : list (Z * Z)) (cr : credit) (wd o dp0 sp r : Z).
Variables (fx : FPState) (R : bvmap 5 word) (M : PML.mem) (model : Model) (K : TSet).
Hypothesis HH : hi_heap HI LB cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HK : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis PRE : PML.entry L R M sp r (PMFC.WD_SCR PML.STRTOD_SCR_V) /\ PML.a0 R wd /\ PML.a1 R o /\ sp <= wd /\ wd + 9 <= hl_sptop L /\
                 PML.u8 M wd 0 /\ PML.u32 M (wd + 4) 0 /\ PML.u8 M (wd + 8) dp0 /\ PML.str_at M o (PML.SShort []) /\ L5.defined M o 24 /\
                 PML.obj_on_stack L sp o 24 /\ PML.img_ro M /\ credit_ok L cr 48.
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : PML.mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
  PML.fp_ok fx' -> (PML.a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ PMFC.num_str L LB cr M' o s' LB' cr') /\ LBk = LB /\ W = [(o, 24)]) ->
  regs_preserved R R' -> L5C.hpres L LBk sp (PMFC.WD_SCR PML.STRTOD_SCR_V) W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
  srealizes PML.RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Definition dp : Z := dp0 mod 256.
Lemma ro4_of_u32 : forall (M0 : PML.mem) a, PML.u32 M0 a 0 -> 0 <= a -> a + 4 <= 2 ^ 64 -> ro_cells rsegs M0 a [C4 (Z_to_bv 64 0)].
Proof.
  intros M0 a H H0 H1. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. unfold PML.u32, L5.u32_at in H.
  exact (TWB.rdn_bytes_at M0 4 a _ H H0 ltac:(lia)).
Qed.

Lemma main_entry : (forall ms1 ms1', wpost (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                                         (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o dp M ms1 -> ms_eqv ms1 ms1' ->
                                  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K) ->
  srealizes PML.RSEGS SCFG (@PML.cfg fx R PMFC.PC_WRITE_DOUBLE M model) K.
Proof.
  intros CASES.
  destruct PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMFC.WD_SCR, PMFC.DTOA_TRUE_SCR, PMFC.DTOA_FALSE_SCR, PMFC.SNPRINTF_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR,
    PML.HEAP_STACK, PML.STRTOD_SCR_V in *.
  destruct Hobj as (O1 & O2 & O3). destruct Hmo as (Hh & Hl & _).
  assert (DPR : 0 <= dp < 256) by (unfold dp; apply Z.mod_pos_bound; lia).
  unfold PML.cfg. eapply TWB.cj_evt_srz; [exact Hh | exact Hl | | exact CASES].
  unfold canon_regs. rewrite Hsp. unfold PML.a0, PML.a1 in Ha0, Ha1. rewrite Ha0, Ha1.
  eapply (wh_entry (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                   (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o dp M).
  all: try lia.
  - exact Hfp.
  - apply ro1_of_u8; [exact Hf0 | lia | lia].
  - apply ro4_of_u32; [exact Hp0 | lia | lia].
  - apply ro1_of_u8; [unfold dp; apply (proj1 (GK.u8_at_mod M (wd + 8) dp0)); exact Hd0 | lia | lia].
  - apply u8arr_of_rw_cells with (n := 24%nat). apply TWB.defined_rw_cells; [exact Hdo | lia | lia].
  - split; [apply TWB.ovl_bytes_length|].
    destruct Hstr as (_ & Hb0 & _ & Hb1). cbn [length Z.of_nat] in Hb0, Hb1. rewrite Z.mul_0_r in Hb0. rewrite Z.add_0_r in Hb1.
    pose proof (Hdo 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. pose proof (Hdo 1 ltac:(lia)) as D1.
    unfold L5.u8_at in Hb0, Hb1. pose proof (CL5.overlay_byte _ _ _ _ Hb0 D0) as E0. pose proof (CL5.overlay_byte _ _ _ _ Hb1 D1) as E1.
    split.
    + rewrite <- (TWB.ovl_bytes_nth M o 24 0 ltac:(lia)); [unfold wa; rewrite Z.add_0_r; exact E0 | unfold wa; rewrite Z.add_0_r; exact D0].
    + rewrite <- (TWB.ovl_bytes_nth M o 24 1 ltac:(lia)); [unfold wa; exact E1 | unfold wa; exact D1].
  - apply TWB.stk_of_defined; [replace (sp - (sp - 9600)) with 9600 by lia; exact S5 | lia | lia].
  - apply TWB.mem_inv_of_clear. intros i Hi. apply Himg. unfold PML.IMG_RO_HI. lia.
  - reflexivity.
Qed.

Ltac kw8 FR := lazymatch goal with |- kentry_ok _ ?E ?M (KWord {| a_base := EVar 2; a_off := ?off |} 8 ?v) =>
  let k := eval vm_compute in (Z.to_nat off) in
  eapply (TWB.kw8_of_cell E M _ _ k); [exact FR | reflexivity | unfold estart, WdHead_u.SPB; cbn [a_base a_off edenot]; rw_atoms; lia | unfold WdHead_u.SPB; lia | unfold WdHead_u.SPB; lia |
    first [reflexivity | assumption | symmetry; assumption]] end.

Definition EW (R' : bvmap 5 word) (gh : nat -> word) : env := Env (fun n =>
  match n with
  | 2%nat => Z_to_bv 64 (sp - 400) | 8%nat => Z_to_bv 64 o | 9%nat => Z_to_bv 64 dp
  | 3%nat | 4%nat | 18%nat | 19%nat | 20%nat | 21%nat | 22%nat | 23%nat | 24%nat | 25%nat | 26%nat | 27%nat => getr R (Z_to_bv 5 (Z.of_nat n))
  | 32%nat => Z_to_bv 64 wd | 33%nat => Z_to_bv 64 r | 34%nat => getr R 8 | 35%nat => getr R 9
  | _ => if (n <? 32)%nat then getr R' (Z_to_bv 5 (Z.of_nat n)) else gh n end) (fun _ => []).

Lemma finish : forall (i : nat) (c : CC.cutpoint) (fx1 : FPState) (gh : nat -> word) (R1 : bvmap 5 word) (m1 : PML.mem),
  TWC.phase i = true -> nth_error TWC.U.CPS i = Some c -> CC.At GK.RSEGS c (EW R1 gh) R1 m1 ->
  PML.fp_ok fx1 -> (forall x : word, ~ TWG.inreg sp o (bv_unsigned x) -> m1 x = M x) ->
  L5.defined m1 (sp - 9600) 9600 -> L5.defined m1 o 24 ->
  srealizes PML.RSEGS SCFG (@PML.cfg fx1 R1 (CC.cp_pc c) m1 model) K.
Proof.
  intros i c fx1 gh R1 m1 Hph Hc HAt Hfp1 Hfr DALL DOB.
  destruct PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMFC.WD_SCR, PMFC.DTOA_TRUE_SCR, PMFC.DTOA_FALSE_SCR, PMFC.SNPRINTF_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR,
    PML.HEAP_STACK, PML.STRTOD_SCR_V in *.
  destruct Hobj as (O1 & O2 & O3).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  assert (U2 : bv_unsigned (ev (EW R1 gh) 2) = sp - 400) by (apply L5.unsigned_lit; lia).
  assert (U8 : bv_unsigned (ev (EW R1 gh) 8) = o) by (apply L5.unsigned_lit; lia).
  assert (U33 : bv_unsigned (ev (EW R1 gh) 33) = r) by (apply L5.unsigned_lit; lia).
  assert (HKE' : forall y : reg, In (ridx y) TWC.KEPT -> ev (EW R1 gh) (ridx y) = getr R y).
  { intros y Hy. rewrite <- (ridx_roundtrip y) at 2.
    cbn [TWC.KEPT In] in Hy. repeat (destruct Hy as [Hy|Hy]; [rewrite <- Hy; reflexivity|]). destruct Hy. }
  eapply (TWC.wd_cert L HI HIok LAY FPM i c fx1 (EW R1 gh) R1 m1 model K LB cr Hph Hc HAt).
  -
    apply (TWG.heap_keep L HI HIok LAY sp o ltac:(lia) LB cr M m1 (m_vmmaps model) HH).
    + exact Hfr.
    + intros a [Ha|Ha].
      * pose proof (DALL (a - (sp - 9600)) ltac:(lia)) as X. replace (sp - 9600 + (a - (sp - 9600))) with a in X by lia. exact X.
      * pose proof (DOB (a - o) ltac:(lia)) as X. replace (o + (a - o)) with a in X by lia. exact X.
  - exact Hmo.
  - exact HK.
  - exact Hfp1.
  - exact Hcr.
  - rewrite U2. rewrite Zminus_mod, S1. reflexivity.
  - rewrite U2. lia.
  - rewrite U2, U8. lia.
  - rewrite U8. lia.
  - lia.
  - pose proof (HKE' (Z_to_bv 5 4) ltac:(vm_compute; tauto)) as X. change (ridx (Z_to_bv 5 4)) with 4%nat in X. rewrite X. exact Htp.
  - rewrite U33. exact Hraok.
  - rewrite U2. eapply L5.defined_sub; [exact DALL | lia | lia].
  - rewrite U8. exact DOB.
  -
    intros fx2 R2 M2 model2 LB2 cr2 Hfp2 WP Hbv2 HH2. unfold TWC.wd_post in WP.
    destruct WP as (Ha02 & NS & Hra2 & Hsp2 & Hs02 & Hs12 & KEEP & HP).
    rewrite U2, U8 in HP. rewrite U8 in NS. rewrite U2 in Hsp2. rewrite U33.
    apply (Hcont fx2 R2 M2 model2 LB2 cr2 LB [(o, 24)] Hfp2).
    + split; [exact Ha02|]. split; [exact NS|]. split; reflexivity.
    + apply rp_intro. intros k Hk. unfold callee_saved_idx in Hk. cbn [In] in Hk.
      repeat destruct Hk as [<-|Hk]; try destruct Hk.
      all: first [ (lazymatch goal with |- getr _ ?y = _ => rewrite (KEEP y ltac:(vm_compute; tauto)); exact (HKE' y ltac:(vm_compute; tauto)) end)
                 | (rewrite (getr_lit8 R2), Hs02; reflexivity) | (rewrite (getr_lit9 R2), Hs12; reflexivity)
                 | (rewrite (getr_lit2 R2), Hsp2, (getr_lit2 R), Hsp; f_equal; lia) ].
    + apply (TWG.hpres_comp L LAY sp o ltac:(lia) LB M m1 M2).
      * intros b Hb. destruct (hio_wf L SCFG HI HIok LB cr M (m_vmmaps model) HH) as (WF & _). destruct (WF b Hb) as ((_ & _ & _ & _ & X) & _). exact X.
      * exact Hfr.
      * intros a Ha. pose proof (DALL (a - (sp - 9600)) ltac:(lia)) as X. replace (sp - 9600 + (a - (sp - 9600))) with a in X by lia. exact X.
      * intros a Ha. pose proof (DOB (a - o) ltac:(lia)) as X. replace (o + (a - o)) with a in X by lia. exact X.
      * exact HP.
    + exact Hbv2.
    + exact HH2.
Qed.

Lemma case_A : forall ms1 ms1', wpA (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                                   (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o dp M ms1 -> ms_eqv ms1 ms1' ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros ms1 ms1' HA EQV. unfold wpA in HA.
  destruct HA as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & fs0w & ja & j3 & bs & -> & FRM & FRA1 & BU & ES & ST & MU & WM & MI).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  destruct PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMFC.WD_SCR, PMFC.DTOA_TRUE_SCR, PMFC.DTOA_FALSE_SCR, PMFC.SNPRINTF_SCR, PMFC.STR_SCR, PMS.STR_SCR, PMS.OPNEW_SCR,
    PML.HEAP_STACK, PML.STRTOD_SCR_V in *.
  destruct Hobj as (O1 & O2 & O3).
  assert (DPR : 0 <= dp < 256) by (unfold dp; apply Z.mod_pos_bound; lia).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  change (mkCfg (MS R' F' (Z_to_bv 64 0x450cc) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp16) m' model).
  assert (RG : forall n, getr (mkR (Z_to_bv 64 0x436fc) (Z_to_bv 64 (WdHead_u.SPB sp)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 wd)
                  (Z_to_bv 64 dp) (Z_to_bv 64 1) a2' a3' a4' a5' a6' a7' (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23)
                  (getr R 24) (getr R 25) (getr R 26) (getr R 27) t3' t4' t5' t6') n = getr R' n) by (intros n; apply getr_eqv; exact REQ).

  assert (DST : L5.defined m' (sp - 9600) (sp - 400 - (sp - 9600))) by (apply TWB.stk_defined; [exact ST | lia | unfold WdHead_u.SPB; lia]).
  assert (DFR : L5.defined m' (sp - 400) 400) by (pose proof (TWB.rw_defined _ _ _ FRA1 ltac:(unfold WdHead_u.SPB; lia)) as X; unfold WdHead_u.SPB in X; exact X).
  assert (DOB : L5.defined m' o 24) by (destruct ES as [BL _]; pose proof (TWB.u8arr_defined _ _ _ BU ltac:(lia)) as X; rewrite BL in X; exact X).
  assert (DALL : L5.defined m' (sp - 9600) 9600).
  { intros j Hj. destruct (Z_lt_dec j 9200); [apply DST; lia | replace (sp - 9600 + j) with (sp - 400 + (j - 9200)) by lia; apply DFR; lia]. }
  set (gh := fun n : nat => match n with 36%nat => fs0w | _ => Z_to_bv 64 0 end).
  apply (finish 16 Cut_cwd_csrc_u.cp16 (mkFP F' fc') gh R' m').
  - vm_compute. reflexivity.
  - reflexivity.
  -
    unfold CC.At. rewrite regs16, know16. split.
    + apply regs_ok_of. intros n Hn.
      assert (Hn' : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16
               \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31)%nat) by lia.
      repeat destruct Hn' as [->|Hn']; try subst n; cbn [nth REGS16 edenot ev EW]; rewrite <- RG; reflexivity.
    + unfold know_ok, KNOW16.
      assert (U2 : bv_unsigned (ev (EW R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (EW R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (EW R' gh) 9) = dp) by (cbn; apply L5.unsigned_lit; lia).
      assert (A8 : o mod 8 = 0) by exact O3. assert (A16 : (sp - 400) mod 16 = 0) by (rewrite Zminus_mod, S1; reflexivity).
      assert (B0 : L5.u8_at RSEGS m' o 0).
      { destruct ES as [_ [E0 _]]. pose proof (TWB.u8_of_u8arr m' o bs 0 _ BU E0) as X. rewrite Z.add_0_r in X. exact X. }
      clear Hcont RG REQ EQV Ems.
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply GK.kword8_intro with (A := o) (z := 0); [ev_start | lia | lia | reflexivity | lia | exact B0].
      * e_range.
      * kw8 FRA1. * kw8 FRA1. * kw8 FRA1. * kw8 FRA1. * kw8 FRA1. * kw8 FRA1. * kw8 FRA1.
      * e_unk. * e_wr.
      * e_range. * e_align A8.
      * e_unk. * e_unk.
      * e_wr. * e_wr. * e_wr. * e_wr. * e_wr. * e_wr. * e_wr. * e_wr.
      * e_range. * e_align A16. * e_disj.
  - exact FRM.
  - intros x Hx. apply MU. unfold WdHead_u.WH_W, TWG.inreg in *. cbn [outside]. lia.
  - exact DALL.
  - exact DOB.
Qed.

End Call.
End TuWdOk.
End TWD.
