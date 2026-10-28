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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Lem_u WdHead_u WdTail_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require Import TuWdBr_u TuWdGl_u TuWdCert_u TuWd_u TuWdC_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TWDS.
Definition REGS17 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp17.
Definition KNOW17 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp17.
Lemma regs17 : CC.cp_regs Cut_cwd_csrc_u.cp17 = REGS17. Proof. vmc_refl. Qed.
Lemma know17 : CC.cp_know Cut_cwd_csrc_u.cp17 = KNOW17. Proof. vmc_refl. Qed.

Lemma defined_grows : forall (M M' : word -> option byte) a n, L5.defined M a n -> mem_grows M M' -> L5.defined M' a n.
Proof. intros M M' a n D G i Hi. apply G. apply D. exact Hi. Qed.
Lemma stk_grows : forall (m m' : word -> option byte) lo hi, stk TWB.CSEGS m lo hi -> 0xf8000 <= lo -> lo <= hi -> hi <= 2 ^ 64 -> mem_grows m m' ->
  stk TWB.CSEGS m' lo hi.
Proof.
  intros m m' lo hi ST Hlo Hle Hhi G. apply TWB.stk_of_defined; [| lia | lia].
  apply (defined_grows m); [apply TWB.stk_defined; [exact ST | lia | lia] | exact G].
Qed.
Lemma u8arr_agree : forall (m m' : word -> option byte) A bs, u8arr TWB.CSEGS m A bs -> agree_on A (A + Z.of_nat (length bs)) m m' -> wmono TWB.CSEGS m m' ->
  u8arr TWB.CSEGS m' A bs.
Proof. intros m m' A bs [HB HW] HA WM. split; [eapply bytes_at_agree; [exact HB | exact HA] | eapply wr_at_wmono; [exact HW | exact WM]]. Qed.
Lemma ro_errno : forall k, 0 <= k < 4 -> ro_addr TWB.CSEGS (Z_to_bv 64 (0xd675c + k)) = false.
Proof. intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia; vm_compute; reflexivity. Qed.
Lemma mem_inv_frame : forall (m m' : word -> option byte), mem_inv TWB.CSEGS m ->
  (forall x : word, m' x <> m x -> 0xf8000 <= bv_unsigned x \/ 0xd675c <= bv_unsigned x < 0xd6760) -> mem_inv TWB.CSEGS m'.
Proof.
  intros m m' MI H a b E. destruct (classic (m' a = m a)) as [Eq|Ne].
  - apply (MI a b). rewrite <- Eq. exact E.
  - destruct (H a Ne) as [Ha|Ha].
    + unfold ro_addr. rewrite TWB.fs_off_image by lia. reflexivity.
    + rewrite <- (Z_to_bv_bv_unsigned a). replace (bv_unsigned a) with (0xd675c + (bv_unsigned a - 0xd675c)) by lia. apply ro_errno. lia.
Qed.

Lemma frt_rebuild : forall (m M2 : word -> option byte) A (TAIL : list cell) (ja jb jc : list byte),
  rw_cells TWB.CSEGS m A ([CB 8 ja; CB 4 jb; CB 100 jc] ++ TAIL) -> 0 <= A -> A + 112 + Z.of_nat (cells_size TAIL) <= 2 ^ 64 ->
  L5.defined M2 A 112 -> agree_on (A + 112) (A + 112 + Z.of_nat (cells_size TAIL)) m M2 -> wmono TWB.CSEGS m M2 ->
  rw_cells TWB.CSEGS M2 A ([CB 8 (TWB.ovl_bytes M2 A 8); CB 4 (TWB.ovl_bytes M2 (A + 8) 4); CB 100 (TWB.ovl_bytes M2 (A + 12) 100)] ++ TAIL).
Proof.
  intros m M2 A TAIL ja jb jc FR H0 H1 D AG WM.
  apply (proj1 (G3Lem_u.rw_cells_app m A _ TAIL)) in FR. destruct FR as [_ FT]. cbn [cells_size csize Nat.add] in FT.
  apply (proj2 (G3Lem_u.rw_cells_app M2 A _ TAIL)). cbn [cells_size csize Nat.add]. split.
  - change [CB 8 (TWB.ovl_bytes M2 A 8); CB 4 (TWB.ovl_bytes M2 (A + 8) 4); CB 100 (TWB.ovl_bytes M2 (A + 12) 100)]
      with ([CB 8 (TWB.ovl_bytes M2 A 8)] ++ [CB 4 (TWB.ovl_bytes M2 (A + 8) 4)] ++ [CB 100 (TWB.ovl_bytes M2 (A + 12) 100)]).
    apply (proj2 (G3Lem_u.rw_cells_app M2 A _ _)). cbn [cells_size csize Nat.add]. split.
    + apply TWB.defined_rw_cells; [eapply L5.defined_sub; [exact D | lia | lia] | lia | lia].
    + apply (proj2 (G3Lem_u.rw_cells_app M2 _ _ _)). cbn [cells_size csize Nat.add]. split.
      * replace (A + Z.of_nat 8) with (A + 8) by lia. apply TWB.defined_rw_cells; [eapply L5.defined_sub; [exact D | lia | lia] | lia | lia].
      * replace (A + Z.of_nat 8 + Z.of_nat 4) with (A + 12) by lia. apply TWB.defined_rw_cells; [eapply L5.defined_sub; [exact D | lia | lia] | lia | lia].
  - replace (A + Z.of_nat 112) with (A + 112) in * by lia. eapply rw_cells_agree; [exact FT | exact AG | exact WM].
Qed.
Lemma agree_of_frame : forall F (m m' : word -> option byte) lo hi, L5.frame_but F m m' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> L5.outside F a) -> agree_on lo hi m m'.
Proof. intros F m m' lo hi FB H0 H1 HO a Ha. apply FB. unfold wa. rewrite unsigned_lit by lia. apply HO. exact Ha. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis SNP : PMFC.snprintf_g_spec L.
Hypothesis DSG : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.
Variables (LB : list (Z * Z)) (cr : credit) (wd o dp0 sp r : Z).
Variables (R : bvmap 5 word) (M : PML.mem) (model : Model) (K : TSet).
Hypothesis HH : hi_heap HI LB cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HK : K [].
Hypothesis PRE : PML.entry L R M sp r (PMFC.WD_SCR PML.STRTOD_SCR_V) /\ PML.a0 R wd /\ PML.a1 R o /\ sp <= wd /\ wd + 9 <= hl_sptop L /\
                 PML.u8 M wd 0 /\ PML.u32 M (wd + 4) 0 /\ PML.u8 M (wd + 8) dp0 /\ PML.str_at M o (PML.SShort []) /\ L5.defined M o 24 /\
                 PML.obj_on_stack L sp o 24 /\ PML.img_ro M /\ credit_ok L cr 48.
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : PML.mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
  PML.fp_ok fx' -> (PML.a0 R' 0 /\ (exists s', 1 <= Z.of_nat (length s') <= 47 /\ PMFC.num_str L LB cr M' o s' LB' cr') /\ LBk = LB /\ W = [(o, 24)]) ->
  regs_preserved R R' -> L5C.hpres L LBk sp (PMFC.WD_SCR PML.STRTOD_SCR_V) W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
  srealizes PML.RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Lemma finish_e : forall (i : nat) (c : CC.cutpoint) (fx1 : FPState) (gh : nat -> word) (R1 : bvmap 5 word) (m1 : PML.mem),
  TWC.phase i = true -> nth_error TWC.U.CPS i = Some c -> CC.At GK.RSEGS c (TWD.EW wd o dp0 sp r R R1 gh) R1 m1 ->
  PML.fp_ok fx1 -> (forall x : word, ~ TWG.inreg sp o (bv_unsigned x) -> ~ in_errno L (bv_unsigned x) -> m1 x = M x) ->
  (forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
  L5.defined m1 (sp - 9600) 9600 -> L5.defined m1 o 24 ->
  srealizes PML.RSEGS SCFG (@PML.cfg fx1 R1 (CC.cp_pc c) m1 model) K.
Proof.
  intros i c fx1 gh R1 m1 Hph Hc HAt Hfp1 Hfr Herr DALL DOB.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R1 gh) 2) = sp - 400) by (apply L5.unsigned_lit; lia).
  assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R1 gh) 8) = o) by (apply L5.unsigned_lit; lia).
  assert (U33 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R1 gh) 33) = r) by (apply L5.unsigned_lit; lia).
  assert (HKE' : forall y : reg, In (ridx y) TWC.KEPT -> ev (TWD.EW wd o dp0 sp r R R1 gh) (ridx y) = getr R y).
  { intros y Hy. rewrite <- (ridx_roundtrip y) at 2.
    cbn [TWC.KEPT In] in Hy. repeat (destruct Hy as [Hy|Hy]; [rewrite <- Hy; reflexivity|]). destruct Hy. }
  eapply (TWC.wd_cert L HI HIok LAY FPM i c fx1 (TWD.EW wd o dp0 sp r R R1 gh) R1 m1 model K LB cr Hph Hc HAt).
  - apply (TWG.heap_keep_e L HI HIok LAY sp o ltac:(lia) LB cr M m1 (m_vmmaps model) HH).
    + exact Hfr.
    + intros a [Ha|Ha].
      * pose proof (DALL (a - (sp - 9600)) ltac:(lia)) as X. replace (sp - 9600 + (a - (sp - 9600))) with a in X by lia. exact X.
      * pose proof (DOB (a - o) ltac:(lia)) as X. replace (o + (a - o)) with a in X by lia. exact X.
    + exact Herr.
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
  - intros fx2 R2 M2 model2 LB2 cr2 Hfp2 WP Hbv2 HH2. unfold TWC.wd_post in WP.
    destruct WP as (Ha02 & NS & Hra2 & Hsp2 & Hs02 & Hs12 & KEEP & HP).
    rewrite U2, U8 in HP. rewrite U8 in NS. rewrite U2 in Hsp2. rewrite U33.
    apply (Hcont fx2 R2 M2 model2 LB2 cr2 LB [(o, 24)] Hfp2).
    + split; [exact Ha02|]. split; [exact NS|]. split; reflexivity.
    + apply TWD.rp_intro. intros k Hk. unfold callee_saved_idx in Hk. cbn [In] in Hk.
      repeat destruct Hk as [<-|Hk]; try destruct Hk.
      all: first [ (lazymatch goal with |- getr _ ?y = _ => rewrite (KEEP y ltac:(vm_compute; tauto)); exact (HKE' y ltac:(vm_compute; tauto)) end)
                 | (rewrite (TWD.getr_lit8 R2), Hs02; reflexivity) | (rewrite (TWD.getr_lit9 R2), Hs12; reflexivity)
                 | (rewrite (TWD.getr_lit2 R2), Hsp2, (TWD.getr_lit2 R), Hsp; f_equal; lia) ].
    + replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 by vmc_refl.
      apply (TWG.hpres_comp_e L LAY sp o ltac:(lia) LB M m1 M2).
      * intros b Hb. destruct (hio_wf L SCFG HI HIok LB cr M (m_vmmaps model) HH) as (WF & _). destruct (WF b Hb) as ((_ & _ & _ & _ & X) & _). exact X.
      * exact Hfr.
      * intros a Ha. pose proof (DALL (a - (sp - 9600)) ltac:(lia)) as X. replace (sp - 9600 + (a - (sp - 9600))) with a in X by lia. exact X.
      * intros a Ha. pose proof (DOB (a - o) ltac:(lia)) as X. replace (o + (a - o)) with a in X by lia. exact X.
      * exact HP.
    + exact Hbv2.
    + exact HH2.
Qed.

Ltac k_tac2 FR d RG oo zb B0 B1 A8 A16 := lazymatch goal with
  | |- kentry_ok _ ?E _ (KWord {| a_base := EAlu _ (EVar 8) (ELit (-23)); a_off := 24 |} 1 _) =>
      eapply GK.kword8_intro with (A := oo + 1) (z := 0);
      [ rewrite (CL5.estart_lin E _ 24 (oo - 23)); [lia | lin_eval; rw_atoms; lia | lia] | lia | lia | reflexivity | lia | exact B1 ]
  | _ => TWDC.k_tac FR d RG oo zb B0 A8 A16
  end.

Lemma case_DBE : forall (mD : PML.mem) (nt : Z) (bits : word) ms1 ms1',
  wpDBE (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
        (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M mD nt bits ms1 -> ms_eqv ms1 ms1' ->
  (forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> mD (Z_to_bv 64 a) <> None) ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros mD nt bits ms1 ms1' HD EQV Herr. unfold wpDBE in HD.
  destruct HD as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & -> & Hnt & FRM & TM).
  destruct TM as ((jd & jg & txt & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). clear Hf0 Hp0 Hd0 Hstr Himg Hcr Ha0 Ha1.
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  assert (ERR : hl_errno L = 0xd675c) by exact (PmLayout.ly_errno L LAY).
  change (WdTail_u.SPD sp) with (sp - 560) in *.
  assert (RG : forall k, getr (mkR (Z_to_bv 64 0x4528c) (Z_to_bv 64 (sp - 560)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (TWD.dp dp0))
                  (Z_to_bv 64 (sp - 560 + 12)) (Z_to_bv 64 nt) (Z_to_bv 64 (TWD.dp dp0)) (Z_to_bv 64 o) a4' a5' a6' a7' bits (Z_to_bv 64 nt)
                  (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') k = getr R' k) by (intros k; apply getr_eqv; exact REQ).
  assert (DST : L5.defined mD (sp - 9600) (sp - 560 - (sp - 9600))) by (apply TWB.stk_defined; [exact ST | lia | lia]).
  assert (DFR : L5.defined mD (sp - 560) 560) by (exact (TWB.rw_defined _ _ _ FR ltac:(lia))).
  assert (DOB : L5.defined mD o 24) by (destruct ES as [BL _]; pose proof (TWB.u8arr_defined _ _ _ BU ltac:(lia)) as X; rewrite BL in X; exact X).
  assert (DALL : L5.defined mD (sp - 9600) 9600).
  { intros j Hj. destruct (Z_lt_dec j 9040).
    - apply DST. lia.
    - replace (sp - 9600 + j) with (sp - 560 + (j - 9040)) by lia. apply DFR. lia. }
  assert (B0 : L5.u8_at RSEGS mD o 0).
  { destruct ES as [_ [E0 _]]. pose proof (TWB.u8_of_u8arr mD o bs 0 _ BU E0) as X. rewrite Z.add_0_r in X. exact X. }
  assert (B1 : L5.u8_at RSEGS mD (o + 1) 0).
  { destruct ES as [_ [_ E1]]. exact (TWB.u8_of_u8arr mD o bs 1 _ BU E1). }
  assert (A8 : o mod 8 = 0) by exact O3. assert (A16 : (sp - 400) mod 16 = 0) by (rewrite Zminus_mod, S1; reflexivity).
  assert (HFR : forall x : word, ~ TWG.inreg sp o (bv_unsigned x) -> ~ in_errno L (bv_unsigned x) -> mD x = M x).
  { intros x Hx He. apply MU. unfold WdTail_u.WT_W, TWG.inreg, in_errno in *. rewrite ERR in He. cbn [outside]. lia. }
  clear EQV Ems REQ O3 S1 S5 Hdo ES MU WM MI ST.
  change (mkCfg (MS R' F' (Z_to_bv 64 0x43d90) fc' None mD (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp17) mD model).
  set (gh := fun k : nat => match k with 36%nat => fs0w | 37%nat => lw | 40%nat => bits | 43%nat => fs0b | 50%nat => t0' | 51%nat => t1' | 52%nat => t2'
                                    | 57%nat => a4' | 58%nat => a5' | 59%nat => a6' | 60%nat => a7' | 61%nat => t3' | 62%nat => t4' | 63%nat => t5' | 64%nat => t6'
                                    | 66%nat => Z_to_bv 64 nt | _ => Z_to_bv 64 0 end).
  apply (finish_e 17 Cut_cwd_csrc_u.cp17 (mkFP F' fc') gh R' mD).
  - vm_compute. reflexivity.
  - reflexivity.
  - unfold CC.At. rewrite regs17, know17.
    assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
    assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
    assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
    assert (U66 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 66) = nt) by (cbn; apply L5.unsigned_lit; lia).
    split.
    + TWDC.regs_tac RG REGS17.
    + unfold know_ok, KNOW17. repeat (apply Forall_cons); [.. | apply Forall_nil].
      all: k_tac2 FR (-160) RG o 0 B0 B1 A8 A16.
  - exact FRM.
  - exact HFR.
  - exact Herr.
  - exact DALL.
  - exact DOB.
Qed.

Definition TAILT (fs0b : word) (j2 dig : list byte) (kw lw fs0w : word) (j3 : list byte) : list cell :=
  [C8 fs0b; C8 (getr R 19); C8 (getr R 18); C8 (Z_to_bv 64 (TWD.dp dp0)); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x45178);
   CB 4 j2; CB 100 dig; C4 kw; C4 lw; C8 fs0w; C8 (Z_to_bv 64 wd); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 0x436fc); CB 232 j3; C8 (getr R 9); C8 (getr R 8); C8 (getr R 1)].
Lemma tmem_core : forall (m M2 X : PML.mem) (HEAD : list cell) fs0b j2 dig kw lw fs0w j3 bs (F : list L5.range),
  cells_size HEAD = 112%nat ->
  rw_cells TWB.CSEGS m (sp - 560) (HEAD ++ TAILT fs0b j2 dig kw lw fs0w j3) -> u8arr TWB.CSEGS m o bs -> estr bs -> stk TWB.CSEGS m (sp - 9600) (sp - 560) ->
  munch (WT_W sp o) M m -> wmono TWB.CSEGS M m -> mem_inv TWB.CSEGS m ->
  L5.frame_but F m M2 -> mem_grows m M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ L5.outside F a -> (sp - 9600 <= a < sp - 448) \/ (0xd675c <= a < 0xd6760)) ->
  tmem (getr R 1) (getr R 8) (getr R 9) (getr R 18) (getr R 19) sp wd o (TWD.dp dp0) M X M2.
Proof.
  intros m M2 X HEAD fs0b j2 dig kw lw fs0w j3 bs F HS FR BU ES ST MU WM MI FB MG HF.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & _ & _ & Hwd1 & Hwd2 & _ & _ & _ & _ & _ & Hobj & _ & _).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3).
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> (sp - 448 <= a < sp \/ o <= a < o + 24 \/ a < sp - 9600 \/ sp <= a) -> ~ (0xd675c <= a < 0xd6760) -> L5.outside F a).
  { intros a Ha H1 H2. destruct (classic (L5.outside F a)) as [Y|Y]; [exact Y|]. exfalso. destruct (HF a Ha Y); lia. }
  assert (DH : L5.defined m (sp - 560) 560).
  { pose proof (TWB.rw_defined _ _ _ FR ltac:(lia)) as X1. rewrite cells_size_app, HS in X1. exact X1. }
  unfold tmem. split; [|split; [|split; [|split; [|split]]]].
  - exists (TWB.ovl_bytes M2 (sp - 560) 8), (TWB.ovl_bytes M2 (sp - 560 + 8) 4), (TWB.ovl_bytes M2 (sp - 560 + 12) 100), fs0b, j2, dig, kw, lw, fs0w, j3.
    change (WdTail_u.SPD sp) with (sp - 560).
    apply (proj1 (G3Lem_u.rw_cells_app m (sp - 560) HEAD _)) in FR. destruct FR as [_ FT]. rewrite HS in FT.
    apply (proj2 (G3Lem_u.rw_cells_app M2 (sp - 560) [CB 8 _; CB 4 _; CB 100 _] (TAILT fs0b j2 dig kw lw fs0w j3))). cbn [cells_size csize Nat.add]. split.
    + change [CB 8 (TWB.ovl_bytes M2 (sp - 560) 8); CB 4 (TWB.ovl_bytes M2 (sp - 560 + 8) 4); CB 100 (TWB.ovl_bytes M2 (sp - 560 + 12) 100)]
        with ([CB 8 (TWB.ovl_bytes M2 (sp - 560) 8)] ++ [CB 4 (TWB.ovl_bytes M2 (sp - 560 + 8) 4)] ++ [CB 100 (TWB.ovl_bytes M2 (sp - 560 + 12) 100)]).
      apply (proj2 (G3Lem_u.rw_cells_app M2 _ _ _)). cbn [cells_size csize Nat.add]. split.
      * apply TWB.defined_rw_cells; [apply (defined_grows m); [eapply L5.defined_sub; [exact DH | lia | lia] | exact MG] | lia | lia].
      * apply (proj2 (G3Lem_u.rw_cells_app M2 _ _ _)). cbn [cells_size csize Nat.add]. split.
        -- replace (sp - 560 + Z.of_nat 8) with (sp - 560 + 8) by lia.
           apply TWB.defined_rw_cells; [apply (defined_grows m); [eapply L5.defined_sub; [exact DH | lia | lia] | exact MG] | lia | lia].
        -- replace (sp - 560 + Z.of_nat 8 + Z.of_nat 4) with (sp - 560 + 12) by lia.
           apply TWB.defined_rw_cells; [apply (defined_grows m); [eapply L5.defined_sub; [exact DH | lia | lia] | exact MG] | lia | lia].
    + eapply rw_cells_agree; [exact FT | | exact (wmono_of_grows _ _ _ MG)].
      intros a Ha. cbn [TAILT cells_size csize Nat.add] in Ha. apply FB. unfold wa. rewrite unsigned_lit by lia. apply OUT; lia.
  - exists bs. split; [|exact ES]. eapply u8arr_agree; [exact BU | | exact (wmono_of_grows _ _ _ MG)].
    destruct ES as [BL _]. rewrite BL. intros a Ha. apply FB. unfold wa. rewrite unsigned_lit by lia. apply OUT; lia.
  - change (WdTail_u.SPD sp) with (sp - 560). apply (stk_grows m); [exact ST | lia | lia | lia | exact MG].
  - intros x Hx. rewrite <- (MU x Hx). apply FB. unfold WdTail_u.WT_W in Hx. cbn [outside] in Hx. pose proof (u64_range x). apply OUT; lia.
  - exact (wmono_trans _ _ _ _ WM (wmono_of_grows _ _ _ MG)).
  - apply (mem_inv_frame m); [exact MI|]. intros x Hx. pose proof (u64_range x).
    destruct (classic (L5.outside F (bv_unsigned x))) as [Y|Y]; [exfalso; exact (Hx (FB x Y))|]. destruct (HF (bv_unsigned x) ltac:(lia) Y); lia.
Qed.
Lemma pres_val : forall (R0 R2 : bvmap 5 word) (k : reg) (v : word), regs_preserved R0 R2 -> In (bv_unsigned k) callee_saved_idx -> getr R0 k = v -> getr R2 k = v.
Proof. intros R0 R2 k v Hrp Hk E. rewrite (Hrp k Hk). exact E. Qed.

Lemma sn2_chain : forall (m5 : PML.mem) (bits : word) ms1 ms1',
  wpSN2 (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
        (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M m5 bits ms1 -> ms_eqv ms1 ms1' ->
  (forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> m5 (Z_to_bv 64 a) <> None) ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros m5 bits ms1 ms1' HS EQV Herr. unfold wpSN2 in HS.
  destruct HS as (t0' & t1' & t2' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & s3' & -> & FRM & TM).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). destruct Hmo as (Hh & Hl & _).
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  change (WdTail_u.SPD sp) with (sp - 560) in *.
  assert (RG : forall k, getr (mkR (Z_to_bv 64 0x45270) (Z_to_bv 64 (sp - 560)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (TWD.dp dp0))
                  (Z_to_bv 64 (sp - 560 + 12)) (Z_to_bv 64 100) (Z_to_bv 64 0x130d8) (Z_to_bv 64 17) bits a5' a6' a7' bits s3'
                  (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') k = getr R' k) by (intros k; apply getr_eqv; exact REQ).
  destruct TM as ((jd & jg & txt & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  change (WdTail_u.SPD sp) with (sp - 560) in FR, ST.
  assert (DFR : L5.defined m5 (sp - 560) 560) by (exact (TWB.rw_defined _ _ _ FR ltac:(lia))).
  assert (DST : L5.defined m5 (sp - 9600) 9040) by (pose proof (TWB.stk_defined _ _ _ ST ltac:(lia) ltac:(lia)) as X; replace (sp - 560 - (sp - 9600)) with 9040 in X by lia; exact X).
  change (mkCfg (MS R' F' (Z_to_bv 64 0xacd08) fc' None m5 (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' PMFC.PC_SNPRINTF m5 model).
  apply (SNP (sp - 560 + 12) 17 (bv_unsigned bits) (sp - 560) 0x45270 (mkFP F' fc') R' m5 model K Hh Hl HK FRM).
  -
    unfold PML.entry, PML.a0, PML.a1, PML.a2, PML.a3, PMFC.SNPRINTF_SCR, PML.img_ro, L5.img_clear.
    repeat split.
    all: first [ (transitivity bits; [rewrite <- RG; reflexivity | symmetry; apply definitions.Z_to_bv_bv_unsigned])
               | (rewrite <- RG; reflexivity) | (rewrite <- RG; exact Htp)
               | (right; reflexivity) | (rewrite Zminus_mod, S1; reflexivity) | (pose proof (u64_range bits); lia) | lia
               | (eapply L5.defined_sub; [exact DST | lia | lia]) | (eapply L5.defined_sub; [exact DFR | lia | lia])
               | (intros i Hi; unfold PML.IMG_RO_HI in Hi; rewrite (MU (Z_to_bv 64 i));
                  [apply Himg; unfold PML.IMG_RO_HI; lia | unfold WdTail_u.WT_W; cbn [outside]; rewrite unsigned_lit by lia; lia]) ].
  -
    intros fx2 R2 M2 Hfp2 (txt2 & GT & LEN & A02 & BA & NUL & DEF2) Hrp FB MG.
    unfold PML.cfg. eapply TWB.cj_evt_srz; [exact Hh | exact Hl | |].
    + unfold canon_regs. unfold PML.a0 in A02. rewrite A02.
      rewrite (pres_val R' R2 2%bv (Z_to_bv 64 (sp - 560)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 3%bv (getr R 3) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 4%bv (getr R 4) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 8%bv (Z_to_bv 64 o) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 9%bv (Z_to_bv 64 (TWD.dp dp0)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 18%bv bits Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 20%bv (getr R 20) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 21%bv (getr R 21) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 22%bv (getr R 22) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 23%bv (getr R 23) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 24%bv (getr R 24) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 25%bv (getr R 25) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 26%bv (getr R 26) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 27%bv (getr R 27) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      replace (Z_to_bv 64 (sp - 560)) with (Z_to_bv 64 (WdTail_u.SPD sp)) by reflexivity.
      eapply (wt_sn2 (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                     (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M DPR).
      * exact Hfp2.
      * lia.
      * apply (tmem_core m5 M2 M [CB 8 jd; CB 4 jg; CB 100 txt] fs0b j2 dig kw lw fs0w j3 bs _ ltac:(reflexivity) FR BU ES ST MU WM MI FB MG).
        intros a Ha Y. unfold L5.outside in Y. apply NNPP. intros Z. apply Y. intros rg Hrg. cbn [In] in Hrg.
        destruct Hrg as [<- | [<- | []]]; unfold L5.in_rng; cbn [fst snd]; unfold PMFC.SNPRINTF_SCR; lia.
    + intros ms3 ms3' HD EQV3. apply (case_DBE M2 _ bits ms3 ms3' HD EQV3).
      intros a Ha HN. apply MG. apply Herr; assumption.
Qed.

Lemma ds_chain : forall (M2 : PML.mem) (txt : list Z) (bits : word) ms1 ms1',
  wpDS (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
       (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M M2 (Z.of_nat (length txt)) bits ms1 -> ms_eqv ms1 ms1' ->
  1 <= Z.of_nat (length txt) <= 25 -> PMFC.gtext txt ->
  L5.bytes_at RSEGS M2 (sp - 560 + 12) txt -> PML.u8 M2 (sp - 560 + 12 + Z.of_nat (length txt)) 0 ->
  (forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None) ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros M2 txt bits ms1 ms1' HS EQV Hlen GT BA NUL Herr. unfold wpDS in HS.
  destruct HS as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m3 & -> & FRM & TM & MU1).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). destruct Hmo as (Hh & Hl & _).
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  change (WdTail_u.SPD sp) with (sp - 560) in *.
  set (nt := Z.of_nat (length txt)) in *.
  assert (RG : forall k, getr (mkR (Z_to_bv 64 0x45218) (Z_to_bv 64 (sp - 560)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (TWD.dp dp0))
                  (Z_to_bv 64 (sp - 560 + 12)) (Z_to_bv 64 nt) (Z_to_bv 64 (sp - 560)) a3' a4' a5' a6' a7' bits (Z_to_bv 64 nt)
                  (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') k = getr R' k) by (intros k; apply getr_eqv; exact REQ).
  destruct TM as ((jd & jg & txt0 & fs0b & j2 & dig & kw & lw & fs0w & j3 & FR) & (bs & BU & ES) & ST & MU & WM & MI).
  change (WdTail_u.SPD sp) with (sp - 560) in FR, ST.
  assert (DFR : L5.defined m3 (sp - 560) 560) by (exact (TWB.rw_defined _ _ _ FR ltac:(lia))).
  assert (DST : L5.defined m3 (sp - 9600) 9040) by (pose proof (TWB.stk_defined _ _ _ ST ltac:(lia) ltac:(lia)) as X; replace (sp - 560 - (sp - 9600)) with 9040 in X by lia; exact X).
  assert (AG : forall a, sp - 552 <= a < 2 ^ 64 -> m3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. apply MU1. cbn [outside]. rewrite unsigned_lit by lia. lia. }
  change (mkCfg (MS R' F' (Z_to_bv 64 0x3f4e8) fc' None m3 (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' PML.PC_DECSTR_DOUBLE m3 model).
  apply (DSG (sp - 560 + 12) (sp - 560) (sp - 560) 0x45218 txt (mkFP F' fc') R' m3 model K Hh Hl HK FRM).
  -
    unfold PML.entry, PML.a0, PML.a1, PML.a2, PML.img_ro, L5.img_clear, PML.STRTOD_SCR_V, PML.u8. fold nt.
    repeat split.
    all: first [ (rewrite <- RG; reflexivity) | (rewrite <- RG; exact Htp)
               | (rewrite Zminus_mod, S1; reflexivity) | lia
               | (eapply L5.defined_sub; [exact DST | lia | lia]) | (eapply L5.defined_sub; [exact DFR | lia | lia])
               | (apply (L5C.bytes_at_agree RSEGS M2 m3); [intros i Hi; apply AG; lia | lia | lia | exact BA])
               | (apply (L5C.u8_at_agree RSEGS M2 m3); [intros i Hi; apply AG; lia | lia | lia | exact NUL])
               | exact GT | (right; lia) | (right; unfold PML.TP; lia)
               | (intros i Hi; unfold PML.IMG_RO_HI in Hi; rewrite (MU (Z_to_bv 64 i));
                  [apply Himg; unfold PML.IMG_RO_HI; lia | unfold WdTail_u.WT_W; cbn [outside]; rewrite unsigned_lit by lia; lia]) ].
  -
    intros fx4 R4 M4 Hfp4 (A04 & c & Hc & Hcin) Hrp FB MG.
    unfold PML.cfg. eapply TWB.cj_evt_srz; [exact Hh | exact Hl | |].
    + unfold canon_regs. rewrite Hc.
      rewrite (pres_val R' R4 2%bv (Z_to_bv 64 (sp - 560)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 3%bv (getr R 3) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 4%bv (getr R 4) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 8%bv (Z_to_bv 64 o) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 9%bv (Z_to_bv 64 (TWD.dp dp0)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 18%bv bits Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 19%bv (Z_to_bv 64 nt) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 20%bv (getr R 20) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 21%bv (getr R 21) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 22%bv (getr R 22) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 23%bv (getr R 23) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 24%bv (getr R 24) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 25%bv (getr R 25) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 26%bv (getr R 26) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R4 27%bv (getr R 27) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      replace (Z_to_bv 64 (sp - 560)) with (Z_to_bv 64 (WdTail_u.SPD sp)) by reflexivity.
      eapply (wt_ds (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                    (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M DPR).
      * exact Hfp4.
      * exact Hlen.
      * cbn [In] in Hcin. lia.
      * apply (tmem_core m3 M4 M [CB 8 jd; CB 4 jg; CB 100 txt0] fs0b j2 dig kw lw fs0w j3 bs _ ltac:(reflexivity) FR BU ES ST MU WM MI FB MG).
        intros a Ha Y. unfold L5.outside in Y. apply NNPP. intros Z. apply Y. intros rg Hrg. cbn [In] in Hrg.
        destruct Hrg as [<- | [<- | [<- | []]]]; unfold L5.in_rng; cbn [fst snd]; unfold PML.STRTOD_SCR_V, PML.TP; lia.
    + assert (Herr4 : forall a, in_errno L a -> M (Z_to_bv 64 a) <> None -> M4 (Z_to_bv 64 a) <> None).
      { intros a Ha HN. apply MG. unfold in_errno in Ha. rewrite (PmLayout.ly_errno L LAY) in Ha.
        rewrite (MU1 (Z_to_bv 64 a)); [apply Herr; [unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | exact HN] |].
        cbn [outside]. rewrite unsigned_lit by lia. lia. }
      intros ms5 ms5' [HD|HD] EQV5.
      * exact (case_DBE M4 _ bits ms5 ms5' HD EQV5 Herr4).
      * exact (sn2_chain M4 bits ms5 ms5' HD EQV5 Herr4).
Qed.

Lemma case_SN : forall ms1 ms1', wpSN (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                                     (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M ms1 -> ms_eqv ms1 ms1' ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros ms1 ms1' HS EQV. unfold wpSN in HS.
  destruct HS as (t0' & t1' & t2' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & fs0b & fs0w & kw & lw & bits & jf & txt & j2 & dig & j3 & bs & -> &
                  FRM & FR & BU & ES & ST & MU & WM & MI).
  replace (WdHead_u.SPB sp - 160) with (sp - 560) in * by (unfold WdHead_u.SPB; lia).
  replace (WdHead_u.SPB sp - 148) with (sp - 560 + 12) in * by (unfold WdHead_u.SPB; lia).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). destruct Hmo as (Hh & Hl & _).
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  assert (RG : forall k, getr (mkR (Z_to_bv 64 0x451fc) (Z_to_bv 64 (sp - 560)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (TWD.dp dp0))
                  (Z_to_bv 64 (sp - 560 + 12)) (Z_to_bv 64 100) (Z_to_bv 64 0x130d8) (Z_to_bv 64 15) bits a5' a6' a7' bits (getr R 19)
                  (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') k = getr R' k) by (intros k; apply getr_eqv; exact REQ).
  assert (DFR : L5.defined m' (sp - 560) 560) by (exact (TWB.rw_defined _ _ _ FR ltac:(lia))).
  assert (DST : L5.defined m' (sp - 9600) 9040) by (pose proof (TWB.stk_defined _ _ _ ST ltac:(lia) ltac:(lia)) as X; replace (sp - 560 - (sp - 9600)) with 9040 in X by lia; exact X).
  assert (MUT : munch (WdTail_u.WT_W sp o) M m').
  { intros x Hx. apply MU. unfold WdTail_u.WT_W, WdHead_u.WH_W in *. cbn [outside] in *. tauto. }
  change (mkCfg (MS R' F' (Z_to_bv 64 0xacd08) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' PMFC.PC_SNPRINTF m' model).
  apply (SNP (sp - 560 + 12) 15 (bv_unsigned bits) (sp - 560) 0x451fc (mkFP F' fc') R' m' model K Hh Hl HK FRM).
  -
    unfold PML.entry, PML.a0, PML.a1, PML.a2, PML.a3, PMFC.SNPRINTF_SCR, PML.img_ro, L5.img_clear.
    repeat split.
    all: first [ (transitivity bits; [rewrite <- RG; reflexivity | symmetry; apply definitions.Z_to_bv_bv_unsigned])
               | (rewrite <- RG; reflexivity) | (rewrite <- RG; exact Htp)
               | (left; reflexivity) | (rewrite Zminus_mod, S1; reflexivity) | (pose proof (u64_range bits); lia) | lia
               | (eapply L5.defined_sub; [exact DST | lia | lia]) | (eapply L5.defined_sub; [exact DFR | lia | lia])
               | (intros i Hi; unfold PML.IMG_RO_HI in Hi; rewrite (MU (Z_to_bv 64 i));
                  [apply Himg; unfold PML.IMG_RO_HI; lia | unfold WdHead_u.WH_W; cbn [outside]; rewrite unsigned_lit by lia; lia]) ].
  -
    intros fx2 R2 M2 Hfp2 (txt1 & GT & LEN & A02 & BA & NUL & DEF2) Hrp FB MG.
    unfold PML.cfg. eapply TWB.cj_evt_srz; [exact Hh | exact Hl | |].
    + unfold canon_regs. unfold PML.a0 in A02. rewrite A02.
      rewrite (pres_val R' R2 2%bv (Z_to_bv 64 (sp - 560)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 3%bv (getr R 3) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 4%bv (getr R 4) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 8%bv (Z_to_bv 64 o) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 9%bv (Z_to_bv 64 (TWD.dp dp0)) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 18%bv bits Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 19%bv (getr R 19) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 20%bv (getr R 20) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 21%bv (getr R 21) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 22%bv (getr R 22) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 23%bv (getr R 23) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 24%bv (getr R 24) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 25%bv (getr R 25) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 26%bv (getr R 26) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      rewrite (pres_val R' R2 27%bv (getr R 27) Hrp ltac:(vm_compute; tauto) ltac:(rewrite <- RG; reflexivity)).
      replace (Z_to_bv 64 (sp - 560)) with (Z_to_bv 64 (WdTail_u.SPD sp)) by reflexivity.
      eapply (wt_sn1 (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                     (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M ltac:(lia) ltac:(lia) DPR).
      * exact Hfp2.
      * exact LEN.
      * apply (tmem_core m' M2 M [CB 12 jf; CB 100 txt] fs0b j2 dig kw lw fs0w j3 bs _ ltac:(reflexivity) FR BU ES ST MUT WM MI FB MG).
        intros a Ha Y. unfold L5.outside in Y. apply NNPP. intros Z. apply Y. intros rg Hrg. cbn [In] in Hrg.
        destruct Hrg as [<- | [<- | []]]; unfold L5.in_rng; cbn [fst snd]; unfold PMFC.SNPRINTF_SCR; lia.
    + intros ms3 ms3' HD EQV3. apply (ds_chain M2 txt1 bits ms3 ms3' HD EQV3 LEN GT BA NUL).
      intros a Ha HN. unfold in_errno in Ha. rewrite (PmLayout.ly_errno L LAY) in Ha.
      rewrite (FB (Z_to_bv 64 a)).
      * rewrite (MU (Z_to_bv 64 a)); [exact HN|]. unfold WdHead_u.WH_W. cbn [outside]. rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia. intros rg Hrg. cbn [In] in Hrg. destruct Hrg as [<- | [<- | []]]; unfold L5.in_rng; cbn [fst snd]; unfold PMFC.SNPRINTF_SCR; lia.
Qed.

End S.
End TWDS.
