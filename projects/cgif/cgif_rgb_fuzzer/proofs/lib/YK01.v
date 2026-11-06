(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK16 YK0o YK11 YK0i YK0j YK14 YK1c YK0v YK02 YK0q
YK15 YK0y YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK00.
Unset Lia Cache. Unset Nia Cache.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Import ListNotations.
Open Scope bv_scope.
Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
(x8 : word) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma step_ecall_epend : forall segs regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step segs (mkst regs pc mem rom)
= MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.




Lemma adv_set_epend : forall regs pc mem rom x8 v,
advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
= mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.


Lemma rz_sys : forall segs regs pc mem rom model w T,
m_halted model = None ->
m_vm_lazy model = [] ->
fetch_word segs pc = Some w -> is_ecall w = true ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

