(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPX. Context {fx : PropExec.FPState}.

Lemma step_fence : forall segs regs pc mem rom w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_fencei : forall segs regs pc mem rom w a b c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w a b c Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4; reflexivity.
Qed.

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2 ^ 32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

End FPX.

Ltac stepfence F D :=
  chain_step; [reflexivity | eapply step_fence; [exact F | reflexivity | exact D] | step_simpl].

Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

Ltac addr_lit lit :=
  match goal with |- rdn _ _ ?ad _ = _ =>
    replace ad with lit by (gres; rwH; imm_norm; apply bv_eq; vm_compute; reflexivity) end.
Ltac mlb F D lit HYP :=
  chain_step; [reflexivity | eapply step_lb; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlbu F D lit HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlw F D lit HYP :=
  chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | apply bytes_le_to_Z_4; first [lia | rewrite u_Z2bv by lia; lia | vm_compute; first [reflexivity | lia] ] ] | step_simpl; vnorm].
Ltac mld F D lit HYP :=
  chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | exact (bytes_le_to_Z_8 _) ] | step_simpl; vnorm].
