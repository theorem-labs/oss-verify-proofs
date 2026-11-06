(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec StepTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma step_fence : forall segs regs pc mem rom w fm pr su rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pr su rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w fm pr su rd rs1 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4. reflexivity.
Qed.

Lemma step_fencei : forall segs regs pc mem rom w rd rs1 imm,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac stepf F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Fence _ _ _ _ _, _) => exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (FenceI _ _ _, _) => exact (step_fencei _ _ _ _ _ _ _ _ _ F eq_refl D)
    end
  | step_simpl ].
