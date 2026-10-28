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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require Import TuWdBr_u TuWdGl_u TuWdCert_u TuWd_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TWDC.
Definition REGS0 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp0.
Definition KNOW0 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp0.
Lemma regs0 : CC.cp_regs Cut_cwd_csrc_u.cp0 = REGS0. Proof. vmc_refl. Qed.
Lemma know0 : CC.cp_know Cut_cwd_csrc_u.cp0 = KNOW0. Proof. vmc_refl. Qed.
Definition REGS3 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp3.
Definition KNOW3 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp3.
Lemma regs3 : CC.cp_regs Cut_cwd_csrc_u.cp3 = REGS3. Proof. vmc_refl. Qed.
Lemma know3 : CC.cp_know Cut_cwd_csrc_u.cp3 = KNOW3. Proof. vmc_refl. Qed.
Definition REGS6 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp6.
Definition KNOW6 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp6.
Lemma regs6 : CC.cp_regs Cut_cwd_csrc_u.cp6 = REGS6. Proof. vmc_refl. Qed.
Lemma know6 : CC.cp_know Cut_cwd_csrc_u.cp6 = KNOW6. Proof. vmc_refl. Qed.
Definition REGS7 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp7.
Definition KNOW7 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp7.
Lemma regs7 : CC.cp_regs Cut_cwd_csrc_u.cp7 = REGS7. Proof. vmc_refl. Qed.
Lemma know7 : CC.cp_know Cut_cwd_csrc_u.cp7 = KNOW7. Proof. vmc_refl. Qed.
Definition REGS8 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp8.
Definition KNOW8 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp8.
Lemma regs8 : CC.cp_regs Cut_cwd_csrc_u.cp8 = REGS8. Proof. vmc_refl. Qed.
Lemma know8 : CC.cp_know Cut_cwd_csrc_u.cp8 = KNOW8. Proof. vmc_refl. Qed.
Definition REGS9 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp9.
Definition KNOW9 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp9.
Lemma regs9 : CC.cp_regs Cut_cwd_csrc_u.cp9 = REGS9. Proof. vmc_refl. Qed.
Lemma know9 : CC.cp_know Cut_cwd_csrc_u.cp9 = KNOW9. Proof. vmc_refl. Qed.
Definition REGS12 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp12.
Definition KNOW12 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp12.
Lemma regs12 : CC.cp_regs Cut_cwd_csrc_u.cp12 = REGS12. Proof. vmc_refl. Qed.
Lemma know12 : CC.cp_know Cut_cwd_csrc_u.cp12 = KNOW12. Proof. vmc_refl. Qed.
Definition REGS13 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp13.
Definition KNOW13 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp13.
Lemma regs13 : CC.cp_regs Cut_cwd_csrc_u.cp13 = REGS13. Proof. vmc_refl. Qed.
Lemma know13 : CC.cp_know Cut_cwd_csrc_u.cp13 = KNOW13. Proof. vmc_refl. Qed.
Definition REGS49 : list expr := Eval vm_compute in CC.cp_regs Cut_cwd_csrc_u.cp49.
Definition KNOW49 : list kentry := Eval vm_compute in CC.cp_know Cut_cwd_csrc_u.cp49.
Lemma regs49 : CC.cp_regs Cut_cwd_csrc_u.cp49 = REGS49. Proof. vmc_refl. Qed.
Lemma know49 : CC.cp_know Cut_cwd_csrc_u.cp49 = KNOW49. Proof. vmc_refl. Qed.

Lemma dpc_val : forall len K, 1 <= len -> WdHead_u.dpc len K =
  (if (K <? 0)%Z then (if (0 <? len + K)%Z then (if (len + K <=? 17)%Z then 0x44628 else 0x44764) else (if (len + K <=? -4)%Z then 0x44764 else 0x446b0))
   else (if (len + K <=? 17)%Z then 0x4457c else 0x44764)).
Proof. reflexivity. Qed.
Ltac dpc_tac len Kx := rewrite dpc_val by lia;
  destruct (Z.ltb_spec Kx 0); destruct (Z.ltb_spec 0 (len + Kx)); destruct (Z.leb_spec (len + Kx) 17); destruct (Z.leb_spec (len + Kx) (-4)); try lia; reflexivity.
Lemma dpc_C1 : forall len Kx, 1 <= len -> 0 <= Kx /\ len + Kx <= 17 -> WdHead_u.dpc len Kx = 0x4457c. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C2 : forall len Kx, 1 <= len -> Kx < 0 /\ 0 < len + Kx <= 17 -> WdHead_u.dpc len Kx = 0x44628. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C3z0 : forall len Kx, 1 <= len -> len + Kx = 0 -> WdHead_u.dpc len Kx = 0x446b0. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C3z1 : forall len Kx, 1 <= len -> len + Kx = -1 -> WdHead_u.dpc len Kx = 0x446b0. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C3z2 : forall len Kx, 1 <= len -> len + Kx = -2 -> WdHead_u.dpc len Kx = 0x446b0. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C3z3 : forall len Kx, 1 <= len -> len + Kx = -3 -> WdHead_u.dpc len Kx = 0x446b0. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C45p : forall len Kx, 1 <= len -> 17 < len + Kx -> WdHead_u.dpc len Kx = 0x44764. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.
Lemma dpc_C45n : forall len Kx, 1 <= len -> len + Kx <= -4 -> WdHead_u.dpc len Kx = 0x44764. Proof. intros len Kx H1 H2. dpc_tac len Kx. Qed.

Lemma lin_val : forall E e v, lden E (lin_of e) = v -> edenot E e = Z_to_bv 64 v.
Proof.
  intros E e v H. apply bv_eq. pose proof (lin_of_sound E e) as [q Hq]. unfold uE in Hq. rewrite H in Hq.
  pose proof (TWC.uE_range E e) as Hu. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Hq, Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.
Lemma getr_mkR_nth : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (n : nat),
  (0 < n < 32)%nat -> getr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 (Z.of_nat n)) =
  nth n [Z_to_bv 64 0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] (Z_to_bv 64 0).
Proof. intros. do 32 (destruct n as [|n]; [first [lia | reflexivity]|]). lia. Qed.

Ltac reg_tac RG := lazymatch goal with
  | |- _ = edenot _ (EVar _) => cbn [edenot ev TWD.EW]; rewrite <- RG; reflexivity
  | |- _ = edenot _ _ => rewrite <- RG, getr_mkR_nth by lia; cbn [nth];
      first [reflexivity | (erewrite lin_val by (lin_eval; rw_atoms; reflexivity); f_equal; unfold WdHead_u.SPB; lia)]
  end.
Ltac regs_tac RG REGS := apply TWD.regs_ok_of; intros n Hn;
  let Hn' := fresh "Hn'" in
  assert (Hn' : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16
               \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31)%nat) by lia;
  repeat destruct Hn' as [->|Hn']; try subst n; cbn [nth REGS]; reg_tac RG.

Ltac kval RG := first [reflexivity | (cbn [edenot ev TWD.EW]; rewrite <- RG; reflexivity) | assumption | (symmetry; assumption)].
Ltac kwd FR d RG := lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord {| a_base := EVar 2; a_off := ?off |} 8 ?v) =>
    let k := eval vm_compute in (Z.to_nat (off - d)) in
    eapply (TWB.kw8_of_cell E M _ _ k); [exact FR | reflexivity | unfold estart, WdHead_u.SPB; cbn [a_base a_off edenot]; rw_atoms; lia | unfold WdHead_u.SPB; lia | unfold WdHead_u.SPB; lia | kval RG]
  | |- kentry_ok _ ?E ?M (KWord {| a_base := EVar 2; a_off := ?off |} 4 ?v) =>
    let k := eval vm_compute in (Z.to_nat (off - d)) in
    eapply (TWB.kw4_of_cell E M _ _ k); [exact FR | reflexivity | unfold estart, WdHead_u.SPB; cbn [a_base a_off edenot]; rw_atoms; lia | unfold WdHead_u.SPB; lia | unfold WdHead_u.SPB; lia | kval RG]
  end.

Ltac k_tac FR d RG oo zb B0 A8 A16 := lazymatch goal with
  | |- kentry_ok _ _ _ (KRange _ _ _) => e_range
  | |- kentry_ok _ _ _ (KAlign (EVar 8) _) => e_align A8
  | |- kentry_ok _ _ _ (KAlign (EVar 2) _) => e_align A16
  | |- kentry_ok _ _ _ (KDisj _ _ _ _) => e_disj
  | |- kentry_ok _ _ _ (KUnk _ _) => e_unk
  | |- kentry_ok _ _ _ (KWr _ _) => e_wr
  | |- kentry_ok _ _ _ (KWord {| a_base := EVar 8; a_off := 0 |} 1 _) =>
      eapply GK.kword8_intro with (A := oo) (z := zb); [ev_start | lia | lia | erewrite lin_val by (lin_eval; rw_atoms; reflexivity); f_equal; lia | lia | exact B0]
  | |- kentry_ok _ _ _ (KWord {| a_base := EVar 2; a_off := _ |} _ _) => kwd FR d RG
  end.

Section C.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps PML.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PML.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom PML.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
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

Lemma case_C : forall ms1 ms1', wpC (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                                   (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M ms1 -> ms_eqv ms1 ms1' ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros ms1 ms1' HC EQV. unfold wpC in HC.
  destruct HC as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & len & Kx & n0 & fs0w & j2 & dig & j3 & bs & -> &
                  Hlen & HKx & FRM & FR & BU & BL & B0n & Hn0 & ST & MU & WM & MI).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). clear Hf0 Hp0 Hd0 Hstr Himg Hcr Ha0 Ha1.
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  assert (RG : forall n, getr (mkR (Z_to_bv 64 0x45148) (Z_to_bv 64 (WdHead_u.SPB sp - 80)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 len)
                  (Z_to_bv 64 (WdHead_u.SPB sp + 4)) (Z_to_bv 64 (len + Kx)) (Z_to_bv 64 Kx) (Z_to_bv 64 (-4)) (Z_to_bv 64 17) (Z_to_bv 64 o) a6' a7'
                  (Z_to_bv 64 (WdHead_u.SPB sp + 4)) (getr R 19) (Z_to_bv 64 (len + Kx)) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') n = getr R' n) by (intros n; apply getr_eqv; exact REQ).
  assert (DST : L5.defined m' (sp - 9600) (WdHead_u.SPB sp - 80 - (sp - 9600))) by (apply TWB.stk_defined; [exact ST | lia | unfold WdHead_u.SPB; lia]).
  assert (DFR : L5.defined m' (WdHead_u.SPB sp - 80) 480) by (exact (TWB.rw_defined _ _ _ FR ltac:(unfold WdHead_u.SPB; lia))).
  assert (DOB : L5.defined m' o 24) by (pose proof (TWB.u8arr_defined _ _ _ BU ltac:(lia)) as X; rewrite BL in X; exact X).
  assert (DALL : L5.defined m' (sp - 9600) 9600).
  { intros j Hj. destruct (Z_lt_dec j 9120).
    - apply DST. unfold WdHead_u.SPB. lia.
    - replace (sp - 9600 + j) with (WdHead_u.SPB sp - 80 + (j - 9120)) by (unfold WdHead_u.SPB; lia). apply DFR. lia. }
  assert (B0 : L5.u8_at RSEGS m' o (2 * n0)).
  { pose proof (TWB.u8_of_u8arr m' o bs 0 _ BU B0n) as X. rewrite Z.add_0_r in X. destruct Hn0 as [-> | ->]; exact X. }
  assert (A8 : o mod 8 = 0) by exact O3. assert (A16 : (sp - 400) mod 16 = 0) by (rewrite Zminus_mod, S1; reflexivity).
  assert (Hn0' : 0 <= n0 <= 1) by lia. clear Hn0 O3 S1 B0n BL S5 Hdo.
  assert (HFR : forall x : word, ~ TWG.inreg sp o (bv_unsigned x) -> m' x = M x).
  { intros x Hx. apply MU. unfold WdHead_u.WH_W, TWG.inreg in *. cbn [outside]. lia. }
  clear EQV Ems REQ.
  assert (CS : (0 <= Kx /\ len + Kx <= 17) \/ (Kx < 0 /\ 0 < len + Kx <= 17) \/ (len + Kx = 0) \/ (len + Kx = -1) \/ (len + Kx = -2) \/ (len + Kx = -3) \/ (17 < len + Kx) \/ (len + Kx <= -4)) by lia.
  destruct CS as [C|[C|[C|[C|[C|[C|[C|C]]]]]]].
  -
    rewrite (dpc_C1 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x4457c) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp0) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (Kx) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 0 Cut_cwd_csrc_u.cp0 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs0, know0.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = Kx) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS0.
      * unfold know_ok, KNOW0. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C2 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x44628) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp3) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (- Kx) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 3 Cut_cwd_csrc_u.cp3 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs3, know3.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = - Kx) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS3.
      * unfold know_ok, KNOW3. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C3z0 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x446b0) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp6) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (0) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 6 Cut_cwd_csrc_u.cp6 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs6, know6.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = 0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS6.
      * unfold know_ok, KNOW6. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C3z1 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x446b0) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp7) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (0) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 7 Cut_cwd_csrc_u.cp7 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs7, know7.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = 0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS7.
      * unfold know_ok, KNOW7. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C3z2 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x446b0) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp8) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (0) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 8 Cut_cwd_csrc_u.cp8 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs8, know8.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = 0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS8.
      * unfold know_ok, KNOW8. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C3z3 len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x446b0) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp9) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (0) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 9 Cut_cwd_csrc_u.cp9 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs9, know9.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = 0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS9.
      * unfold know_ok, KNOW9. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C45p len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x44764) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp12) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (len + Kx) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 12 Cut_cwd_csrc_u.cp12 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs12, know12.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = len + Kx) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS12.
      * unfold know_ok, KNOW12. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
  -
    rewrite (dpc_C45n len Kx) by lia.
    change (mkCfg (MS R' F' (Z_to_bv 64 0x44764) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp13) m' model).
    set (gh := fun n : nat => match n with 36%nat => fs0w | 37%nat => Z_to_bv 64 len | 38%nat => Z_to_bv 64 (- (len + Kx)) | 39%nat => Z_to_bv 64 n0 | _ => Z_to_bv 64 0 end).
    apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 13 Cut_cwd_csrc_u.cp13 (mkFP F' fc') gh R' m').
    + vm_compute. reflexivity.
    + reflexivity.
    + unfold CC.At. rewrite regs13, know13.
      assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
      assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
      assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
      assert (U37 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 37) = len) by (cbn; apply L5.unsigned_lit; lia).
      assert (U38 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 38) = - (len + Kx)) by (cbn; apply L5.unsigned_lit; lia).
      assert (U39 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 39) = n0) by (cbn; apply L5.unsigned_lit; lia).
      split.
      * regs_tac RG REGS13.
      * unfold know_ok, KNOW13. repeat (apply Forall_cons); [.. | apply Forall_nil].
        all: k_tac FR (-80) RG o (2 * n0) B0 A8 A16.
    + exact FRM.
    + exact HFR.
    + exact DALL.
    + exact DOB.
Qed.

Lemma case_A2 : forall ms1 ms1', wpA2 (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                                     (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) sp wd o (TWD.dp dp0) M ms1 -> ms_eqv ms1 ms1' ->
  srealizes PML.RSEGS SCFG (mkCfg ms1' model) K.
Proof.
  intros ms1 ms1' HA EQV. unfold wpA2 in HA.
  destruct HA as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & fs0b & fs0w & kw & lw & jf & txt & j2 & dig & j3 & bs & -> &
                  FRM & FR & BU & ES & ST & MU & WM & MI).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof PRE as ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hwd1 & Hwd2 & Hf0 & Hp0 & Hd0 & Hstr & Hdo & Hobj & Himg & Hcr).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). replace (PMFC.WD_SCR PML.STRTOD_SCR_V) with 9600 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). clear Hf0 Hp0 Hd0 Hstr Himg Hcr Ha0 Ha1.
  assert (DPR : 0 <= TWD.dp dp0 < 256) by (unfold TWD.dp; apply Z.mod_pos_bound; lia).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  assert (RG : forall n, getr (mkR (Z_to_bv 64 0x45178) (Z_to_bv 64 (WdHead_u.SPB sp - 160)) (getr R 3) (getr R 4) t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (TWD.dp dp0))
                  (Z_to_bv 64 (TWD.dp dp0)) (Z_to_bv 64 1) a2' a3' a4' a5' a6' a7'
                  (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  t3' t4' t5' t6') n = getr R' n) by (intros n; apply getr_eqv; exact REQ).
  assert (DST : L5.defined m' (sp - 9600) (WdHead_u.SPB sp - 160 - (sp - 9600))) by (apply TWB.stk_defined; [exact ST | lia | unfold WdHead_u.SPB; lia]).
  assert (DFR : L5.defined m' (WdHead_u.SPB sp - 160) 560) by (exact (TWB.rw_defined _ _ _ FR ltac:(unfold WdHead_u.SPB; lia))).
  assert (DOB : L5.defined m' o 24) by (destruct ES as [BL _]; pose proof (TWB.u8arr_defined _ _ _ BU ltac:(lia)) as X; rewrite BL in X; exact X).
  assert (DALL : L5.defined m' (sp - 9600) 9600).
  { intros j Hj. destruct (Z_lt_dec j 9040).
    - apply DST. unfold WdHead_u.SPB. lia.
    - replace (sp - 9600 + j) with (WdHead_u.SPB sp - 160 + (j - 9040)) by (unfold WdHead_u.SPB; lia). apply DFR. lia. }
  assert (B0 : L5.u8_at RSEGS m' o 0).
  { destruct ES as [_ [E0 _]]. pose proof (TWB.u8_of_u8arr m' o bs 0 _ BU E0) as X. rewrite Z.add_0_r in X. exact X. }
  assert (A8 : o mod 8 = 0) by exact O3. assert (A16 : (sp - 400) mod 16 = 0) by (rewrite Zminus_mod, S1; reflexivity).
  assert (HFR : forall x : word, ~ TWG.inreg sp o (bv_unsigned x) -> m' x = M x).
  { intros x Hx. apply MU. unfold WdHead_u.WH_W, TWG.inreg in *. cbn [outside]. lia. }
  clear EQV Ems REQ O3 S1 S5 Hdo ES.
  change (mkCfg (MS R' F' (Z_to_bv 64 0x451a8) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc Cut_cwd_csrc_u.cp49) m' model).
  set (gh := fun n : nat => match n with 36%nat => fs0w | 43%nat => fs0b | _ => Z_to_bv 64 0 end).
  apply (TWD.finish L HI HIok LAY FPM LB cr wd o dp0 sp r R M model K HH Hmo HK PRE Hcont 49 Cut_cwd_csrc_u.cp49 (mkFP F' fc') gh R' m').
  - vm_compute. reflexivity.
  - reflexivity.
  - unfold CC.At. rewrite regs49, know49.
    assert (U2 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 2) = sp - 400) by (cbn; apply L5.unsigned_lit; lia).
    assert (U8 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 8) = o) by (cbn; apply L5.unsigned_lit; lia).
    assert (U9 : bv_unsigned (ev (TWD.EW wd o dp0 sp r R R' gh) 9) = TWD.dp dp0) by (cbn; apply L5.unsigned_lit; lia).
    split.
    + regs_tac RG REGS49.
    + unfold know_ok, KNOW49. repeat (apply Forall_cons); [.. | apply Forall_nil].
      all: k_tac FR (-160) RG o 0 B0 A8 A16.
  - exact FRM.
  - exact HFR.
  - exact DALL.
  - exact DOB.
Qed.
End C.
End TWDC.
