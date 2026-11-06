(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.openssl.punycode.lib.Cls Require Import ClsSyscallFacts ClsMustExitCfg.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof. reflexivity. Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
  intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz.
  intros H. apply (f_equal bv_unsigned) in H. cbv in H. discriminate H.
Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc mem rom x8 r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc, epend.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCfg.
Variable b : SpuriousCfg.
Variable segs : list Segment.

Local Notation "'ME' code c" := (must_exit_at_cfg b segs code c)
  (at level 10, code at level 9, c at level 9, only parsing).

(* [comment removed for export] *)
Lemma me_msteps : forall code ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ME code (mkCfg ms' model) ->
  ME code (mkCfg ms model).
Proof.
  intros code ms ms' model Hh Hlazy Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros Hme; [exact Hme|].
  eapply me_cfg_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hme].
Qed.

(* [comment removed for export] *)
Lemma me_sys : forall code regs pc mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  ME code (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
  ME code (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros code regs pc mem rom model w Hh Hlazy HF HE Hme.
  eapply me_cfg_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hme].
Qed.

(* [comment removed for export] *)
Lemma me_exit_at : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  ME (Z_to_bv 64 code) (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  eapply me_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (me_cfg_exit_lit b segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) code);
    [exact Hh | reflexivity | | rewrite ms_gpr_epend0; exact H10 | exact Hc].
  destruct H17 as [H|H]; rewrite H; [right|left]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma me_set_tid : forall code regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     ME code (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
  ME code (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros code regs pc mem rom model w HF HE Hh Hlazy H17 Htid Hk.
  eapply me_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (me_cfg_set_tid b segs code (epend regs pc mem rom (getr regs 17)) model (getr regs 17));
    [exact Hh | reflexivity | rewrite H17; reflexivity | exact Htid |].
  intros t Ht. rewrite adv_eff_ret_epend. apply Hk. exact Ht.
Qed.

End WithCfg.
