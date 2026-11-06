(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.Spec4KF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition P_root : Prop := root_obligation_core PIMG source_alloc_limit spec_of.
Definition U_root : Prop := root_obligation_core UIMG target_alloc_limit spec_of.
Definition A_root : Prop := root_obligation_core AIMG target_alloc_limit spec_of.
Definition B_root : Prop := root_obligation_core BIMG target_alloc_limit spec_of.



(* [comment removed for export] *)
Lemma valid_entry_unfold : forall segs pc ph sp brk0 mb rnd inp,
  valid_input_core inp ->
  valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp
  <-> (valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mb /\ entry_stack_fits sp (in_argv inp) (in_envp inp)).
Proof. intros segs pc ph sp brk0 mb rnd inp Hc. apply valid_entry_sv48. exact (valid_input_core_va_size _ Hc). Qed.

(* [comment removed for export] *)

Theorem ubsan_base_of : P_root -> U_root ->
  strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros HP HU. exact (rrealizes_universal_ef_budgets_abort _ _ PIMG UIMG spec_of HP HU spec_of_kill_free). Qed.



