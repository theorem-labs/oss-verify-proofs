(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort HaltsKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractS1 S1Spec S1MainInst BaseSpecNk.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition CODES02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma spec_exits_02 : forall argv fs0, t_exits_in CODES02 (spec argv fs0).
Proof.
  assert (E2 : In (exit_code 2) CODES02) by (right; left; reflexivity).
  assert (E0 : In (exit_code 0) CODES02) by (left; reflexivity).
  assert (DIE : forall msg fs, t_exits_in CODES02 (t_die msg fs)).
  { intros msg fs. unfold t_die. apply t_exits_in_emit; [apply evs_exits_in_writes | apply t_exits_in_exit; exact E2]. }
  intros argv fs0. unfold spec.
  destruct argv as [|a [|path [|z l]]]; try apply DIE.
  destruct (4096 <=? length path)%nat; [apply DIE|].
  destruct (list_byte_eqb path []); [apply DIE|].
  destruct (list_byte_eqb path dot_path); [apply t_exits_in_alt2; apply DIE|].
  destruct (fs_lookup fs0 path) as [data|]; [|apply DIE].
  apply t_exits_in_alt2; [apply DIE|].
  unfold t_opened, t_body.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try apply DIE.
  all: apply t_exits_in_emit; [apply evs_exits_in_writes | apply t_exits_in_exit; exact E0].
Qed.

Theorem halts_bp_plain_drv :
  lib_contract_S1 ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source CODES02
    (mkImage Plain.M.loaded_segments
             Plain.M.init_pc
             Plain.M.phdrs).
Proof.
  intros LIB1.
  apply (srealizes_halts_scfg_budgets forced_only_cfg); [apply cfg_le_forced_only_CFG|].
  intros sp brk mbase rnd inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit).
  destruct Hvalid as (Hva & Hve & _).
  exists (spec (in_argv inp) (in_fs inp)). split; [| split].
  - exact (s1_main_inst sp brk mbase rnd inp LIB1 Hsp Hbrk Hva Hve Hfit).
  - apply spec_nokill.
  - apply spec_exits_02.
Qed.

