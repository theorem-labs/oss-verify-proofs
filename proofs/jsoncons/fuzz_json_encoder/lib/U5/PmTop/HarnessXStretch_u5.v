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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_harness_xsrc_u5 Cut_harness_br_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HSX.
Module G := Cut_harness_xsrc_u5.
Module GB := Cut_harness_br_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
(* [comment removed for export] *)
Definition KS8 : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition FR : Z := 1376.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition spok (sp0 : Z) : Prop := 2 ^ 40 <= sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.

(* [comment removed for export] *)
Lemma s_entry : forall (fx : FPState) R M model K sp0 ra,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp0 -> getr R 1%bv = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> spok sp0 -> L5.defined M (sp0 - 1376) 1376 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a62c -> getr R' 10%bv = Z_to_bv 64 (sp0 - 40) ->
      getr R' 11%bv = getr R 10%bv -> getr R' 12%bv = getr R 11%bv -> TK.keepsR KS8 R R' ->
      L5.u64_at RSEGS M' (sp0 - 8) ra -> L5.u64_at RSEGS M' (sp0 - 16) (bv_unsigned (getr R 8%bv)) ->
      TK.samem (fun a => ~ (sp0 - 1376 <= a < sp0)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_STRINIT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K.
Proof.
  intros fx R M model K sp0 ra Hh Hl Hfp H2 H1 Hra [Hsp Hal] Hdef Hcont.
  set (E := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (unfold E; rewrite (CL5.ev_reg R _ _ 2%bv), H2; apply u64_of_Z; lia).
  change PML.PC_LIB with (CC.cp_pc G.cp0).
  apply (TK.stretch_cps FPM G.cp0 fx E R M model K (G.plans 0%nat _ eq_refl) Hh Hl Hfp).
  - exact (regs_ok_id R _ _).
  - unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    destruct k as [|k]; [|destruct k; discriminate Hnth]. injection Hnth as <-.
    assert (Hag32 : env_agree 32 E E') by exact Hag.
    assert (U2' : bv_unsigned (ev E' 2) = sp0) by (rewrite <- (proj1 Hag32 2%nat) by lia; exact U2).
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg).
    + tk_lin HLF (1%bv : reg).
    + tk_lin HLF (10%bv : reg).
    + tk_reg HLF (11%bv : reg). rewrite <- (proj1 Hag32 10%nat) by lia. exact (CL5.ev_reg R _ _ 10%bv).
    + tk_reg HLF (12%bv : reg). rewrite <- (proj1 Hag32 11%nat) by lia. exact (CL5.ev_reg R _ _ 11%bv).
    + intros r Hr. exact (TK.keeps_id_sound _ _ R _ _ E' R' M M' KS8 r HLF eq_refl Hag32 Hr).
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-8)) 8 (EVar 1))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 1%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 1%bv), H1. apply u64_of_Z. exact Hra.
    + eapply (CL5.kword64_elim RSEGS E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-16)) 8 (EVar 8))); cbn; tauto | ev_start |].
      cbn [edenot]. rewrite <- (proj1 Hag32 8%nat) by lia. unfold E. rewrite (CL5.ev_reg R _ _ 8%bv). reflexivity.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp0]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Ltac hv_open FPM cp plans gh sp0 R M fx model K Hh Hl Hfp H2 :=
  let E := fresh "E" in set (E := TK.hvE sp0 R gh);
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply TK.regs_ok_hv with (off := -1376) (pins := []); [vm_compute; reflexivity | lia | lia | exact H2 | intros q z []] | | ].
Ltac hv_leaf k Hnth Hag E' :=
  (destruct k as [|k]; [|destruct k; discriminate Hnth]); injection Hnth as <-;
  assert (Hag64 : env_agree 64 _ E') by (eapply CC.env_agree_le; [exact Hag | vm_compute; lia]);
  assert (U2' : bv_unsigned (ev E' 2) = _) by (rewrite <- (proj1 Hag64 2%nat) by lia; eassumption).
Ltac hv_open_p FPM cp plans gh pn sp0 R M fx model K Hh Hl Hfp H2 Hpin :=
  let E := fresh "E" in set (E := TK.hvE sp0 R gh);
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (TK.regs_ok_hv _ (-1376) pn); [vm_compute; reflexivity | lia | lia | exact H2 | intros q z [X|[]]; injection X as <- <-; exact Hpin] | | ].
Ltac hv_keeps HLF Hag64 sp0 R E' R' M M' qs := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; exact (TK.keeps_hv_sound _ _ sp0 R _ E' R' M M' qs r HLF eq_refl Hag64 Hr).
Ltac hv_cell64 HLF off v := eapply (CL5.kword64_elim RSEGS); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) off) 8 v)); cbn; tauto | ev_start | cbn [edenot]; rewrite ?u64_of_Z by lia; try reflexivity].
(* [comment removed for export] *)
Ltac hv_cell64_lin HLF off e v := eapply (CL5.kword64_elim RSEGS); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) off) 8 e)); cbn; tauto | ev_start
  | apply (CL5.u_lin _ e v); [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia]].

(* [comment removed for export] *)
Lemma s_r_strinit : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a63c -> getr R' 10%bv = Z_to_bv 64 (sp0 - 312) ->
      getr R' 11%bv = Z_to_bv 64 (sp0 - 40) -> getr R' 12%bv = Z_to_bv 64 8 -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_ISS_CTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a62c M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a62c with (CC.cp_pc G.cp1).
  hv_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg). + tk_lin HLF (12%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.

(* [comment removed for export] *)
Lemma s_r_iss : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  L5.defined M (sp0 - 336) 24 -> L5.defined M (sp0 - 1344) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a660 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 744) ->
      getr R' 11%bv = Z_to_bv 64 (sp0 - 1344) -> getr R' 12%bv = Z_to_bv 64 (sp0 - 1360) -> TK.keepsR KS8 R R' ->
      L5.u64_at RSEGS M' (sp0 - 336) 0 -> L5.u64_at RSEGS M' (sp0 - 328) 0 -> L5.u64_at RSEGS M' (sp0 - 320) 0 -> L5.u64_at RSEGS M' (sp0 - 1344) (sp0 - 336) ->
      TK.samem (fun a => ~ (sp0 - 336 <= a < sp0 - 312) /\ ~ (sp0 - 1344 <= a < sp0 - 1336)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMES.PC_ENC_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a63c M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] D1 D2 Hcont.
  change 0x3a63c with (CC.cp_pc G.cp2).
  hv_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg). + tk_lin HLF (12%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
    + hv_cell64 HLF (-336) (ELit 0). + hv_cell64 HLF (-328) (ELit 0). + hv_cell64 HLF (-320) (ELit 0).
    + hv_cell64_lin HLF (-1344) (EAlu ALU_ADD (EVar 2) (ELit (-336))) (sp0 - 336).
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F G.cp2]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Lemma s_r_encctor : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a674 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 1344) ->
      getr R' 11%bv = Z_to_bv 64 (sp0 - 312) -> getr R' 12%bv = Z_to_bv 64 (sp0 - 744) -> getr R' 13%bv = Z_to_bv 64 (sp0 - 1360) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READER_CTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a660 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a660 with (CC.cp_pc G.cp3).
  hv_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg). + tk_lin HLF (12%bv : reg). + tk_lin HLF (13%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.

(* [comment removed for export] *)
Lemma s_r_rctor : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  L5.defined M (sp0 - 1360) 4 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a67c -> TK.keepsR KS8 R R' ->
      L5.u32_at RSEGS M' (sp0 - 1360) 0 -> TK.samem (fun a => ~ (sp0 - 1360 <= a < sp0 - 1356)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SYSTEM_CATEGORY M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a674 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hdef Hcont.
  change 0x3a674 with (CC.cp_pc G.cp4).
  hv_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
    + eapply (TK.kword32_elim E' M'); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA (EVar 2) (-1360)) 4 (ELit 0))); cbn; tauto | ev_start | cbn [edenot]; apply u64_of_Z; lia].
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp4]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Lemma s_r_syscat : forall (fx : FPState) R M model K sp0 v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  getr R 10%bv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> L5.defined M (sp0 - 1352) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a68c -> getr R' 10%bv = Z_to_bv 64 (sp0 - 1344) -> getr R' 11%bv = Z_to_bv 64 (sp0 - 1360) ->
      TK.keepsR KS8 R R' -> L5.u64_at RSEGS M' (sp0 - 1352) v -> TK.samem (fun a => ~ (sp0 - 1352 <= a < sp0 - 1344)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a67c M model) K.
Proof.
  intros fx R M model K sp0 v Hh Hl Hfp H2 [Hsp Hal] H10 Hv Hdef Hcont.
  change 0x3a67c with (CC.cp_pc G.cp5).
  hv_open FPM G.cp5 (G.plans 5%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
    + hv_cell64 HLF (-1352) (EVar 42). rewrite <- (proj1 Hag64 42%nat) by lia. change (ev E 42) with (ev (TK.hvE sp0 R (fun _ : nat => Z_to_bv 64 0)) (32 + ridx (10%bv : reg))). rewrite TK.hvE_reg, H10. apply u64_of_Z. exact Hv.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp5]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Lemma s_r_read : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a694 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 1024) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSER_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a68c M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a68c with (CC.cp_pc G.cp6).
  hv_open FPM G.cp6 (G.plans 6%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp6. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_r_pdtor : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a69c -> getr R' 10%bv = Z_to_bv 64 (sp0 - 1344) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SOURCE_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a694 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a694 with (CC.cp_pc G.cp7).
  hv_open FPM G.cp7 (G.plans 7%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp7. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_r_sdtor : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a6a4 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 744) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PMES.PC_ENC_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a69c M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a69c with (CC.cp_pc G.cp8).
  hv_open FPM G.cp8 (G.plans 8%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp8. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_r_locdtor : forall (fx : FPState) R M model K sp0 vtt,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  getr R 8%bv = Z_to_bv 64 vtt -> 0 <= vtt < 2 ^ 63 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a734 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 312) -> getr R' 11%bv = Z_to_bv 64 (vtt + 8) ->
      TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_ISTREAM_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a728 M model) K.
Proof.
  intros fx R M model K sp0 vtt Hh Hl Hfp H2 [Hsp Hal] H8 Hvtt Hcont.
  change 0x3a728 with (CC.cp_pc G.cp12).
  hv_open FPM G.cp12 (G.plans 12%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp12. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (U40 : bv_unsigned (ev E' 40) = vtt) by (rewrite <- (proj1 Hag64 40%nat) by lia; change (ev E 40) with (ev (TK.hvE sp0 R (fun _ : nat => Z_to_bv 64 0)) (32 + ridx (8%bv : reg))); rewrite TK.hvE_reg, H8; apply u64_of_Z; lia).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (11%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_r_istrdtor : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a73c -> getr R' 10%bv = Z_to_bv 64 (sp0 - 192) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a734 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] Hcont.
  change 0x3a734 with (CC.cp_pc G.cp13).
  hv_open FPM G.cp13 (G.plans 13%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp13. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.

Definition gh1 (a : Z) : nat -> word := fun k => Z_to_bv 64 (nth k [a] 0).
Definition gh2 (a b : Z) : nat -> word := fun k => Z_to_bv 64 (nth k [a; b] 0).
Definition VTT_ISS : Z := 0xc7e00.         (* [comment removed for export] *)
Definition VT_STREAMBUF16 : Z := 0xc7c58.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma s_r_encdtor : forall (fx : FPState) R M model K sp0 b,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  L5.u8_at RSEGS M (sp0 - 336) b -> 0 <= b <= 255 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> bv_unsigned (getr R' 10%bv) = Z.land b 1 -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a6ac M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6a4 M model) K.
Proof.
  intros fx R M model K sp0 b Hh Hl Hfp H2 [Hsp Hal] Hb Hbr Hcont.
  change 0x3a6a4 with (CC.cp_pc G.cp9).
  hv_open FPM G.cp9 (G.plans 9%nat _ eq_refl) (gh1 b) sp0 R M fx model K Hh Hl Hfp H2.
  - assert (U64 : bv_unsigned (ev E 64) = b) by (change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    unfold know_ok, G.cp9. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply TK.kword8_intro with (A := sp0 - 336) (z := b); [ev_start | lia | lia | reflexivity | lia | exact Hb].
    + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (U64' : bv_unsigned (ev E' 64) = b) by (rewrite <- (proj1 Hag 64%nat) by (vm_compute; lia); change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg).
    + tk_reg HLF (10%bv : reg). apply TK.and1_val. exact U64'.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_r_iosbdtor : forall (fx : FPState) R M model K sp0 b,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  L5.u8_at RSEGS M (sp0 - 40) b -> 0 <= b <= 255 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> bv_unsigned (getr R' 10%bv) = Z.land b 1 -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a744 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a73c M model) K.
Proof.
  intros fx R M model K sp0 b Hh Hl Hfp H2 [Hsp Hal] Hb Hbr Hcont.
  change 0x3a73c with (CC.cp_pc G.cp14).
  hv_open FPM G.cp14 (G.plans 14%nat _ eq_refl) (gh1 b) sp0 R M fx model K Hh Hl Hfp H2.
  - assert (U64 : bv_unsigned (ev E 64) = b) by (change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    unfold know_ok, G.cp14. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply TK.kword8_intro with (A := sp0 - 40) (z := b); [ev_start | lia | lia | reflexivity | lia | exact Hb].
    + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (U64' : bv_unsigned (ev E' 64) = b) by (rewrite <- (proj1 Hag 64%nat) by (vm_compute; lia); change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg).
    + tk_reg HLF (10%bv : reg). apply TK.and1_val. exact U64'.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.

(* [comment removed for export] *)
Lemma s_r_opdel0 : forall (fx : FPState) R M model K sp0 b,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  PML.img_ro M -> L5.defined M (sp0 - 312) 8 -> L5.defined M (sp0 - 296) 8 -> L5.defined M (sp0 - 192) 8 -> L5.u8_at RSEGS M (sp0 - 232) b -> 0 <= b <= 255 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 8%bv = Z_to_bv 64 VTT_ISS -> bv_unsigned (getr R' 11%bv) = Z.land b 1 -> TK.keepsR TK.KS R R' ->
      L5.u64_at RSEGS M' (sp0 - 312) PML.VT_ISS -> L5.u64_at RSEGS M' (sp0 - 296) PML.VT_STRINGBUF -> L5.u64_at RSEGS M' (sp0 - 192) PML.VT_ISS_IOS ->
      TK.samem (fun a => ~ (sp0 - 312 <= a < sp0 - 304) /\ ~ (sp0 - 296 <= a < sp0 - 288) /\ ~ (sp0 - 192 <= a < sp0 - 184)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a6fc M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6c0 M model) K.
Proof.
  intros fx R M model K sp0 b Hh Hl Hfp H2 [Hsp Hal] RO D1 D2 D3 Hb Hbr Hcont.
  change 0x3a6c0 with (CC.cp_pc G.cp10).
  hv_open FPM G.cp10 (G.plans 10%nat _ eq_refl) (gh1 b) sp0 R M fx model K Hh Hl Hfp H2.
  - assert (U64 : bv_unsigned (ev E 64) = b) by (change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    unfold know_ok, G.cp10. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr.
    + eapply TK.kword8_intro with (A := sp0 - 232) (z := b); [ev_start | lia | lia | reflexivity | lia | exact Hb].
    + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    assert (U64' : bv_unsigned (ev E' 64) = b) by (rewrite <- (proj1 Hag 64%nat) by (vm_compute; lia); change (ev E 64) with (Z_to_bv 64 b); apply u64_of_Z; lia).
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + unfold VTT_ISS. tk_lin HLF (8%bv : reg).
    + tk_reg HLF (11%bv : reg). apply TK.and1_val. exact U64'.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' TK.KS.
    + hv_cell64 HLF (-312) (ELit 818632). + hv_cell64 HLF (-296) (ELit 818392). + hv_cell64 HLF (-192) (ELit 818672).
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp10]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Lemma s_r_opdel1 : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  PML.img_ro M -> L5.defined M (sp0 - 296) 8 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a728 -> getr R' 10%bv = Z_to_bv 64 (sp0 - 288) -> TK.keepsR KS8 R R' ->
      L5.u64_at RSEGS M' (sp0 - 296) VT_STREAMBUF16 -> TK.samem (fun a => ~ (sp0 - 296 <= a < sp0 - 288)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a710 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] RO Hdef Hcont.
  change 0x3a710 with (CC.cp_pc G.cp11).
  hv_open FPM G.cp11 (G.plans 11%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp11. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + tk_kimg RO. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'.
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
    + hv_cell64 HLF (-296) (ELit 818264).
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F G.cp11]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Lemma ret_at : CL.is_ret_at RSEGS 0x3a768.
Proof. CL.solve_is_ret. Qed.
Lemma s_r_opdel2 : forall (fx : FPState) R M model K sp0 ra s0v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  L5.u64_at RSEGS M (sp0 - 8) ra -> L5.u64_at RSEGS M (sp0 - 16) s0v -> L5.ra_ok ra -> 0 <= s0v < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 sp0 -> getr R' 10%bv = Z_to_bv 64 0 -> getr R' 8%bv = Z_to_bv 64 s0v -> TK.keepsR TK.KS R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' ra M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a758 M model) K.
Proof.
  intros fx R M model K sp0 ra s0v Hh Hl Hfp H2 [Hsp Hal] Hra Hs0 [Hrar Hrae] Hs0r Hcont.
  change 0x3a758 with (CC.cp_pc G.cp15).
  hv_open FPM G.cp15 (G.plans 15%nat _ eq_refl) (gh2 ra s0v) sp0 R M fx model K Hh Hl Hfp H2.
  - unfold know_ok, G.cp15. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply CL5.kword64_intro with (A := sp0 - 8) (z := ra); [ev_start | lia | lia | reflexivity | exact Hra].
    + eapply CL5.kword64_intro with (A := sp0 - 16) (z := s0v); [ev_start | lia | lia | reflexivity | exact Hs0].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    assert (R1 : getr R' 1%bv = Z_to_bv 64 ra) by (tk_reg HLF (1%bv : reg); rewrite <- (proj1 Hag 64%nat) by (vm_compute; lia); reflexivity).
    unfold PML.cfg. apply (CL.ret_cps RSEGS fx' R' _ M model K ret_at Hh Hl).
    + rewrite R1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hrae.
    + rewrite R1. apply (Hcont fx' R' Hfp').
      * tk_lin HLF (2%bv : reg). * tk_lin HLF (10%bv : reg).
      * tk_reg HLF (8%bv : reg). rewrite <- (proj1 Hag 65%nat) by (vm_compute; lia). reflexivity.
      * hv_keeps HLF Hag64 sp0 R E' R' M M' TK.KS.
Qed.

(* [comment removed for export] *)
Lemma s_b0_long : forall (fx : FPState) R M model K sp0 w0 p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  getr R 10%bv = Z_to_bv 64 1 -> L5.u64_at RSEGS M (sp0 - 336) w0 -> L5.u64_at RSEGS M (sp0 - 320) p -> 0 <= w0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a6c0 -> getr R' 10%bv = Z_to_bv 64 p -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6ac M model) K.
Proof.
  intros fx R M model K sp0 w0 p Hh Hl Hfp H2 [Hsp Hal] H10 Hw Hp Hwr Hpr Hcont.
  change 0x3a6ac with (CC.cp_pc GB.cp0).
  hv_open_p FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (gh2 w0 p) [(10%nat, 1)] sp0 R M fx model K Hh Hl Hfp H2 H10.
  - unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply CL5.kword64_intro with (A := sp0 - 336) (z := w0); [ev_start | lia | lia | reflexivity | exact Hw].
    + eapply CL5.kword64_intro with (A := sp0 - 320) (z := p); [ev_start | lia | lia | reflexivity | exact Hp].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg).
    + tk_reg HLF (10%bv : reg). rewrite <- (proj1 Hag 65%nat) by (vm_compute; lia). reflexivity.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_b0_short : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 -> getr R 10%bv = Z_to_bv 64 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a6c0 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6ac M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] H10 Hcont.
  change 0x3a6ac with (CC.cp_pc GB.cp1).
  hv_open_p FPM GB.cp1 (GB.plans 1%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) [(10%nat, 0)] sp0 R M fx model K Hh Hl Hfp H2 H10.
  - unfold know_ok, GB.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_b1_long : forall (fx : FPState) R M model K sp0 w0 p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  getr R 11%bv = Z_to_bv 64 1 -> L5.u64_at RSEGS M (sp0 - 232) w0 -> L5.u64_at RSEGS M (sp0 - 216) p -> 0 <= w0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a710 -> getr R' 10%bv = Z_to_bv 64 p -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6fc M model) K.
Proof.
  intros fx R M model K sp0 w0 p Hh Hl Hfp H2 [Hsp Hal] H11 Hw Hp Hwr Hpr Hcont.
  change 0x3a6fc with (CC.cp_pc GB.cp2).
  hv_open_p FPM GB.cp2 (GB.plans 2%nat _ eq_refl) (gh2 w0 p) [(11%nat, 1)] sp0 R M fx model K Hh Hl Hfp H2 H11.
  - unfold know_ok, GB.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply CL5.kword64_intro with (A := sp0 - 232) (z := w0); [ev_start | lia | lia | reflexivity | exact Hw].
    + eapply CL5.kword64_intro with (A := sp0 - 216) (z := p); [ev_start | lia | lia | reflexivity | exact Hp].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg).
    + tk_reg HLF (10%bv : reg). rewrite <- (proj1 Hag 65%nat) by (vm_compute; lia). reflexivity.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_b1_short : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 -> getr R 11%bv = Z_to_bv 64 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a710 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a6fc M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] H11 Hcont.
  change 0x3a6fc with (CC.cp_pc GB.cp3).
  hv_open_p FPM GB.cp3 (GB.plans 3%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) [(11%nat, 0)] sp0 R M fx model K Hh Hl Hfp H2 H11.
  - unfold know_ok, GB.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_b2_long : forall (fx : FPState) R M model K sp0 w0 p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 ->
  getr R 10%bv = Z_to_bv 64 1 -> L5.u64_at RSEGS M (sp0 - 40) w0 -> L5.u64_at RSEGS M (sp0 - 24) p -> 0 <= w0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' ->
      getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> getr R' 1%bv = Z_to_bv 64 0x3a758 -> getr R' 10%bv = Z_to_bv 64 p -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a744 M model) K.
Proof.
  intros fx R M model K sp0 w0 p Hh Hl Hfp H2 [Hsp Hal] H10 Hw Hp Hwr Hpr Hcont.
  change 0x3a744 with (CC.cp_pc GB.cp4).
  hv_open_p FPM GB.cp4 (GB.plans 4%nat _ eq_refl) (gh2 w0 p) [(10%nat, 1)] sp0 R M fx model K Hh Hl Hfp H2 H10.
  - unfold know_ok, GB.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + eapply CL5.kword64_intro with (A := sp0 - 40) (z := w0); [ev_start | lia | lia | reflexivity | exact Hw].
    + eapply CL5.kword64_intro with (A := sp0 - 24) (z := p); [ev_start | lia | lia | reflexivity | exact Hp].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_lin HLF (1%bv : reg).
    + tk_reg HLF (10%bv : reg). rewrite <- (proj1 Hag 65%nat) by (vm_compute; lia). reflexivity.
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
Lemma s_b2_short : forall (fx : FPState) R M model K sp0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp0 - 1376) -> spok sp0 -> getr R 10%bv = Z_to_bv 64 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp0 - 1376) -> TK.keepsR KS8 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' 0x3a758 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x3a744 M model) K.
Proof.
  intros fx R M model K sp0 Hh Hl Hfp H2 [Hsp Hal] H10 Hcont.
  change 0x3a744 with (CC.cp_pc GB.cp5).
  hv_open_p FPM GB.cp5 (GB.plans 5%nat _ eq_refl) (fun _ : nat => Z_to_bv 64 0) [(10%nat, 0)] sp0 R M fx model K Hh Hl Hfp H2 H10.
  - unfold know_ok, GB.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil]. + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. hv_leaf k Hnth Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg).
    + hv_keeps HLF Hag64 sp0 R E' R' M M' KS8.
Qed.
End S.
End HSX.
