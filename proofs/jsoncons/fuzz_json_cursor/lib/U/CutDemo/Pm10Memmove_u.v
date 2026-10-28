(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Sums_u Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_memmove_preA_csrc_u Cut_memmove_preB_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module MA := Cut_memmove_preA_csrc_u.  Module MB := Cut_memmove_preB_csrc_u.
Definition MEMMOVE : Z := 0xb7c98.
Definition KEPT : list nat := [1; 2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition leaf_good (c : CC.cutpoint) : bool :=
  match CC.cp_PSS c with [ps] => (Z.eqb (SR.ps_pc ps) 0xb7894 && CL.ps_keeps ps KEPT)%bool | _ => false end.
Lemma goodA : (leaf_good MA.cp0 && match CC.cp_F MA.cp0 with [] => true | _ => false end)%bool = true. Proof. vmc_refl. Qed.
Lemma goodB : (leaf_good MB.cp0 && match CC.cp_F MB.cp0 with [] => true | _ => false end)%bool = true. Proof. vmc_refl. Qed.

Ltac lin_eval := unfold lden; repeat (match goal with |- context [lin_of ?e] => let l := fresh "l" in set (l := lin_of e); vm_compute in l; subst l end);
                 cbn [fst snd tden]; unfold uE; cbn [edenot].
Ltac rw_atoms := repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end.

Lemma prologue : forall (c : CC.cutpoint), CC.plan_sound RSEGS c -> CC.cp_pc c = MEMMOVE -> CC.cp_regs c = sr_id -> (CC.cp_nx c = 32)%nat ->
  (leaf_good c && match CC.cp_F c with [] => true | _ => false end)%bool = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte), know_ok RSEGS (EnvR R) M (CC.cp_know c) ->
  exists (fx' : FPState) R', msteps RSEGS (@mkst fx R (Z_to_bv 64 MEMMOVE) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb7894) M (seg_rom RSEGS))
    /\ (forall x : reg, In (ridx x) KEPT -> getr R' x = getr R x).
Proof.
  intros c HP Hpc Hregs Hnx Hgood fx R M HK. apply andb_prop in Hgood as [Hg HF]. unfold leaf_good in Hg.
  destruct (HP fx (EnvR R) R M ltac:(rewrite Hregs; apply EnvR_regs_ok) HK) as (fx' & E' & R' & M' & k & ps & Hps & Hag & Hms & HLF).
  destruct (CC.cp_PSS c) as [|ps0 [|]] eqn:HPSS; try discriminate Hg. destruct k as [|[|]]; cbn [nth_error] in Hps; try discriminate Hps. injection Hps as <-.
  apply andb_prop in Hg as [Hpc' Hk]. apply Z.eqb_eq in Hpc'.
  assert (HM : M' = M).
  { apply functional_extensionality. intros a. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). destruct (CC.cp_F c); [constructor | discriminate HF]. }
  subst M'. rewrite Hpc, Hpc' in Hms. exists fx', R'. split; [exact Hms|].
  intros x Hx. assert (Hx32 : (ridx x < CC.cp_nx c)%nat) by (rewrite Hnx; unfold KEPT in Hx; cbn [In] in Hx; intuition lia).
  rewrite (CL.ps_keeps_sound RSEGS c ps0 (EnvR R) E' R' M M KEPT (CC.cp_nx c) x HLF Hk Hag Hx Hx32). apply CL.EnvR_reg.
Qed.

Section Inst.
Context {SCFG_P : ScfgP}.
Theorem memmove_copy1 : forall L : heap_layout, hl_segs L = RSEGS -> CH2.copy1_spec L MEMMOVE.
Proof.
  intros L LS fx mem0 dst src n bs regs ret Hn Hd62 Hs62 Hlen Hrd Hst Hdisj Hs64 Hd64 Hret G1 G10 G11 G12. rewrite LS in *.
  assert (U10 : bv_unsigned (ev (EnvR regs) 10) = bv_unsigned dst) by (rewrite <- G10; f_equal; exact (CL.EnvR_reg regs 10%bv)).
  assert (U11 : bv_unsigned (ev (EnvR regs) 11) = bv_unsigned src) by (rewrite <- G11; f_equal; exact (CL.EnvR_reg regs 11%bv)).
  assert (U12 : bv_unsigned (ev (EnvR regs) 12) = n) by (rewrite (CL.EnvR_reg regs 12%bv : ev (EnvR regs) 12 = _), G12; apply u64_of_Z; lia).
  pose proof (u64_range dst) as Ud. pose proof (u64_range src) as Us. unfold two64 in *.
  assert (RUN : exists (fx' : FPState) R', msteps RSEGS (@mkst fx regs (Z_to_bv 64 MEMMOVE) mem0 (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb7894) mem0 (seg_rom RSEGS))
                  /\ (forall x : reg, In (ridx x) KEPT -> getr R' x = getr regs x)).
  { destruct Hdisj as [HA|HB].
    - apply (prologue MA.cp0 (MA.plans 0%nat MA.cp0 eq_refl) eq_refl eq_refl eq_refl goodA fx regs mem0).
      unfold know_ok, MA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil];
        (eapply CL5.krange_intro; [lin_eval; rw_atoms; reflexivity | lia | lia]).
    - apply (prologue MB.cp0 (MB.plans 0%nat MB.cp0 eq_refl) eq_refl eq_refl eq_refl goodB fx regs mem0).
      unfold know_ok, MB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil];
        (eapply CL5.krange_intro; [lin_eval; rw_atoms; reflexivity | lia | lia]). }
  destruct RUN as (fx' & R' & Hms & Hkeep).
  assert (K1 : getr R' 1%bv = ret) by (rewrite (Hkeep 1%bv ltac:(cbn; tauto)); exact G1).
  assert (K10 : getr R' 10%bv = dst) by (rewrite (Hkeep 10%bv ltac:(cbn; tauto)); exact G10).
  assert (K11 : getr R' 11%bv = src) by (rewrite (Hkeep 11%bv ltac:(cbn; tauto)); exact G11).
  assert (K12 : getr R' 12%bv = Z_to_bv 64 n) by (rewrite (Hkeep 12%bv ltac:(cbn; tauto)); exact G12).
  destruct (src0_copy_spec_memcpy fx' mem0 dst src n bs R' ret ltac:(lia) Hlen Hrd Hst Hdisj Hs64 Hd64 Hret K1 K10 K11 K12) as (R2 & Hms2 & Hk2 & Ha0).
  exists fx', R2. split; [exact (msteps_trans _ _ _ _ Hms Hms2)|]. split; [|exact Ha0].
  intros r Hr0 Hnc. rewrite (Hk2 r Hr0 Hnc). apply Hkeep.
  pose proof (CH2.reg_partition r Hr0 Hnc) as Hin. unfold callee_saved_idx in Hin. unfold ridx, KEPT. cbn [In] in Hin |- *.
  repeat (destruct Hin as [Hin|Hin]; [rewrite <- Hin; cbn; tauto|]). destruct Hin.
Qed.
End Inst.

