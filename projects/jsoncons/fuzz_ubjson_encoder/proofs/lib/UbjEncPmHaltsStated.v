(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the read-only-backing form of the system-call steps; the run over the run's segments; the channel-reader premise of writev; the BMode context; imports. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec KillFree HaltsKit HeapIface LibIface LibIfaceE L5Defs
     UbjEncShapes FrmInit Es0DrvLibL Es0DrvG Es0DrvMain Es0HeapBridgeHe Eu0DrvLibL Eu0DrvG Eu0DrvMain Eu0HeapBridgeHe
     PeCSink PeCTopS PeCTopU PeCSExitCells PeCUExitCells UbjEncPmStated.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Import HeIface HeInst0 HeInst1 HeV16.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require SRomStable.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ES := Plain.M.
Module EU := Ubsan.M.

(* [comment removed for export] *)
Definition LayUh (sp : word) : lib_layout := PECTU.TopLay (HeInst1.L1 (bv_unsigned sp)) tbS.
Definition DLLUh := PECTU.drv_lib_layout_top tbS (proj1 tbS_range).
Definition BudgetUh := PECTU.budget_top tbS tbS_range.

Section HaltsStated.
#[local] Existing Instance PropExec.fx0.
Variables PE PEu : list byte -> Prop.   (* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis LIBSh : forall sp, valid_sp sp ->
  @lib_iface_ok_x (LayS sp) cfg0 bm_on_inst (@HeV16.HIV0 bm_on_inst (bv_unsigned sp) ShippedBudgets.lim_source) (LStS sp) (fun _ => True) PE.
(* [comment removed for export] *)
Hypothesis LIBUh : forall sp, valid_sp sp ->
  @lib_iface_ok_x (LayUh sp) cfg0 bm_on_inst (@HeV16.HIV1 bm_on_inst (bv_unsigned sp) ShippedBudgets.lim_source) (LStU sp) (fun _ => True) PEu.

Section ModeOn.
#[local] Existing Instance bm_on_inst | 0.

Lemma SRC_on : Es0DrvMain.src_realizes_stmt2 cfg0 ShippedBudgets.lim_source.
Proof.
  exact (src0_realizes_spec_heap (bmK := bm_on_inst) cfg0 eq_refl eq_refl ShippedBudgets.lim_source LayS LStS DLLS
           (fun _ => True) PE LIBSh LSXS BudgetS (or_introl eq_refl) (fun _ => I)).
Qed.
Lemma TGT_on : Eu0DrvMain.tgt_realizes_stmt2 cfg0 ShippedBudgets.lim_source.
Proof.
  exact (ub0_realizes_spec_heap (bmK := bm_on_inst) cfg0 eq_refl eq_refl ShippedBudgets.lim_source LayUh LStU DLLUh
           (fun _ => True) PEu LIBUh LSXU BudgetUh (or_introl eq_refl) (fun _ => I)).
Qed.

(* [comment removed for export] *)
Theorem ue_halts_plain_stated :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 (mkImage ES.loaded_segments ES.init_pc ES.phdrs).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hsw.
  (* LPS 727298f3: [valid_entry]'s fifth conjunct is the launch; the input facts are read through the
     model's named accessors, never by position *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb [_ Hlau]]]].
  pose proof (valid_input_argv _ Hvalid) as Hargv. pose proof (valid_input_envp _ Hvalid) as Henvp.
  pose proof (valid_input_fs _ Hvalid) as Hfs. pose proof (valid_input_creds _ Hvalid) as Hcreds.
  pose proof (valid_input_launch _ Hvalid) as Hvl. pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  pose proof (top_of_guarded (bmK := bm_on_inst) _ cfg0 _ _ _ _ _ _ _ inp _
                (SRomStable.frm_safe_run_segments _ inp sp mb frm_safe_Ms0)
                (SRC_on sp brk mb rnd inp Hsp Hbrk Hmb Hvl Hlau Hargv Henvp Hfs Hcreds Hrd)) as SRC.
  eapply (srealizes_init_must_exit (bmK := bm_on_inst) eq_refl cfg0).
  - exact SRC.
  - apply exit_codes_in_spec.
  - apply kill_free_spec.
  - exact Hsw.
Qed.

(* [comment removed for export] *)
Theorem ue_halts_ubsan_stated :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 (mkImage EU.loaded_segments EU.init_pc EU.phdrs).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hsw.
  (* LPS 727298f3: [valid_entry]'s fifth conjunct is the launch; the input facts are read through the
     model's named accessors, never by position *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb [_ Hlau]]]].
  pose proof (valid_input_argv _ Hvalid) as Hargv. pose proof (valid_input_envp _ Hvalid) as Henvp.
  pose proof (valid_input_fs _ Hvalid) as Hfs. pose proof (valid_input_creds _ Hvalid) as Hcreds.
  pose proof (valid_input_launch _ Hvalid) as Hvl. pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  pose proof (top_of_guarded (bmK := bm_on_inst) _ cfg0 _ _ _ _ _ _ _ inp _
                (SRomStable.frm_safe_run_segments _ inp sp mb frm_safe_Mu0)
                (TGT_on sp brk mb rnd inp Hsp Hbrk Hmb Hvl Hlau Hargv Henvp Hfs Hcreds Hrd)) as SRC.
  eapply (srealizes_init_must_exit (bmK := bm_on_inst) eq_refl cfg0).
  - exact SRC.
  - apply exit_codes_in_spec.
  - apply kill_free_spec.
  - exact Hsw.
Qed.
End ModeOn.
End HaltsStated.
