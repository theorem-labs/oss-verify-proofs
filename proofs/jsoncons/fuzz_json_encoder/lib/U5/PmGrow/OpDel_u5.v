(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_opdel_plain_xsrc_u5 Cut_opdel_sized_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module OD.
Module P := Cut_opdel_plain_xsrc_u5.  Module S := Cut_opdel_sized_xsrc_u5.
Definition FREE : Z := PML.PC_FREE.
Definition KEPT : list nat := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.       (* [comment removed for export] *)
Definition leaf_good (c : CC.cutpoint) : bool :=
  match CC.cp_PSS c with [ps] => (Z.eqb (SR.ps_pc ps) FREE && CL.ps_keeps ps KEPT)%bool | _ => false end.
Lemma goodP : (leaf_good P.cp0 && match CC.cp_F P.cp0 with [] => true | _ => false end)%bool = true. Proof. vm_compute. reflexivity. Qed.
Lemma goodS : (leaf_good S.cp0 && match CC.cp_F S.cp0 with [] => true | _ => false end)%bool = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stub : forall (c : CC.cutpoint), CC.plan_sound GK.RSEGS c -> CC.cp_regs c = sr_id -> (CC.cp_nx c = 32)%nat -> CC.cp_know c = [] ->
  (leaf_good c && match CC.cp_F c with [] => true | _ => false end)%bool = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte),
  exists (fx' : FPState) R', msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 FREE) M (seg_rom GK.RSEGS))
    /\ (forall x : reg, In (ridx x) KEPT -> getr R' x = getr R x).
Proof.
  intros c HP Hregs Hnx Hkn Hgood fx R M. apply andb_prop in Hgood as [Hg HF]. unfold leaf_good in Hg.
  destruct (HP fx (EnvR R) R M ltac:(rewrite Hregs; apply EnvR_regs_ok) ltac:(rewrite Hkn; apply Forall_nil)) as (fx' & E' & R' & M' & k & ps & Hps & Hag & Hms & HLF).
  destruct (CC.cp_PSS c) as [|ps0 [|]] eqn:HPSS; try discriminate Hg. destruct k as [|[|]]; cbn [nth_error] in Hps; try discriminate Hps. injection Hps as <-.
  apply andb_prop in Hg as [Hpc' Hk]. apply Z.eqb_eq in Hpc'.
  assert (HM : M' = M).
  { apply functional_extensionality. intros a. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). destruct (CC.cp_F c); [constructor | discriminate HF]. }
  subst M'. rewrite Hpc' in Hms. exists fx', R'. split; [exact Hms|].
  intros x Hx. assert (Hx32 : (ridx x < CC.cp_nx c)%nat) by (rewrite Hnx; unfold KEPT in Hx; cbn [In] in Hx; intuition lia).
  rewrite (CL.ps_keeps_sound GK.RSEGS c ps0 (EnvR R) E' R' M M KEPT (CC.cp_nx c) x HLF Hk Hag Hx Hx32). apply CL.EnvR_reg.
Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) callee_saved_idx -> In (ridx r) KEPT.
Proof.
  intros r H. unfold ridx. unfold callee_saved_idx in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma opdel_ok_at : forall (c : CC.cutpoint), CC.plan_sound GK.RSEGS c -> CC.cp_regs c = sr_id -> (CC.cp_nx c = 32)%nat -> CC.cp_know c = [] ->
  (leaf_good c && match CC.cp_F c with [] => true | _ => false end)%bool = true -> PMS.opdel_spec_at L HI (CC.cp_pc c).
Proof.
  intros c HPL Hregs Hnx Hkn Hgood. unfold PMS.opdel_spec_at, PML.cps_heap.
  intros LB cr A n sp r fx R M model K HH (Mh & Ml & Mm) HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & HIN) KONT.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMS.OPDEL_SCR, PML.HEAP_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (stub c HPL Hregs Hnx Hkn Hgood fx R M) as (fx1 & R1 & MS1 & K1).
  assert (Hfp1 : PML.fp_ok fx1) by exact (FPM fx fx1 R _ M R1 _ M MS1 Hfp).
  assert (G1 : getr R1 1%bv = Z_to_bv 64 r) by (rewrite (K1 1%bv ltac:(cbn; tauto)); exact Hra).
  assert (G2 : getr R1 2%bv = Z_to_bv 64 sp) by (rewrite (K1 2%bv ltac:(cbn; tauto)); exact Hsp).
  assert (G4 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (K1 4%bv ltac:(cbn; tauto)); exact Htp).
  assert (G10 : getr R1 10%bv = Z_to_bv 64 A) by (rewrite (K1 10%bv ltac:(cbn; tauto)); exact Ha0).
  unfold PML.cfg. eapply (L5.cps_of_msteps GK.RSEGS); [exact Mh | exact Ml | exact MS1 |].
  pose proof (hio_free L SCFG HI HIok) as HF. unfold free_spec in HF. rewrite LS, (PmLayout.ly_free L LAY) in HF.
  eapply (HF fx1 R1 M model LB cr A n K); clear HF.
  - exact HH.
  - exact Mh. - exact Ml. - exact Mm.
  - exact HIN.
  - exact G10.
  - rewrite (PmLayout.ly_tp L LAY). exact G4.
  - rewrite G1. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite G2, u64_of_Z by lia. unfold stack_ok. rewrite LSTK, LS.
    split; [exact S1|]. split; [lia|]. split; [lia|]. split; [lia|].
    assert (W1 : L5.writable GK.RSEGS M (sp - 8224) 8224) by (apply (L5C.writable_of_defined GK.RSEGS M _ _ S5); lia).
    intros d m Hd Hm. apply W1; lia.
  - exact HK0.
  - intros R2 M2 model2 RP [[PRES SDEF] _] MBV HH2. rewrite G1. rewrite G2, u64_of_Z in PRES, SDEF by lia. rewrite LSTK in PRES, SDEF.
    apply (KONT fx1 R2 M2 model2 (lb_remove A LB) cr (lb_remove A LB) [] Hfp1).
    + repeat split; reflexivity.
    + intros x Hx. rewrite (RP x Hx). apply K1. exact (kept_in x Hx).
    + apply L5C.hpres_intro.
      * intros a (Ha & CA & NE & _). exact (PRES a Ha CA NE).
      * intros i Hi. apply SDEF. lia.
      * intros a Ha CA NE D0. rewrite (PRES a Ha CA NE). exact D0.
    + exact MBV.
    + exact HH2.
Qed.

Theorem opdel_ok : PMS.opdel_spec L HI.
Proof. exact (opdel_ok_at P.cp0 (P.plans 0%nat P.cp0 eq_refl) eq_refl eq_refl eq_refl goodP). Qed.
Theorem opdel_sized_ok : PMS.opdel_sized_spec L HI.
Proof. exact (opdel_ok_at S.cp0 (S.plans 0%nat S.cp0 eq_refl) eq_refl eq_refl eq_refl goodS). Qed.
End WithHeap.
End OD.
