(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog ModelInv ProgDetIface ProgDet ProgNoEnomem.   (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_example_large_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition impl_P_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) en inp ->
    valid_input inp ->
    impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
         (ms0 psegs SrcP.M.init_pc SrcP.M.phdrs en inp).

Definition impl_U_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs) en inp ->
    valid_input inp ->
    impl usegs (at_node usegs) (the_prog usegs ustage inp en) (epost the_post)
         (ms0 usegs TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs en inp).

Definition noenomem_P_stmt : Prop := prog_no_enomem_stmt psegs pstage SrcP.M.init_pc SrcP.M.phdrs source_alloc_limit.
Definition noenomem_U_stmt : Prop := prog_no_enomem_stmt usegs ustage TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs target_alloc_limit.

Lemma base_obligations_of_parts :
  impl_P_stmt -> impl_U_stmt -> noenomem_P_stmt -> noenomem_U_stmt -> base_obligations.
Proof.
  intros HP HU LP LU. constructor.
  - intros en inp He Hi. split; [exact (HP en inp He Hi)|].
    exact (prog_model_ok_P (CE__:=run_ceiling en) en inp He (valid_input_either_of_valid_input _ Hi) (run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hi) He)).
  - intros en inp He Hi. split; [exact (HU en inp He Hi)|].
    exact (prog_model_ok_U (CE__:=run_ceiling en) en inp He (valid_input_either_of_valid_input _ Hi) (run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hi) He)).
  - intros enP enU inp HeP HeU Hi. exact (trees_equiv_of_no_enomem LP LU enP enU inp HeP HeU (valid_input_either_of_valid_input _ Hi)).
Qed.

(* forced-only port: the obligations give the equivalence over the filtered run. *)
Theorem base_ubsan_of_parts :
  impl_P_stmt -> impl_U_stmt -> noenomem_P_stmt -> noenomem_U_stmt ->
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage TgtO_example_large_fuzzer_ubsan.M.loaded_segments TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  intros HP HU LP LU. apply base_ubsan_from_obligations. exact (base_obligations_of_parts HP HU LP LU).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem base_ubsan_of_impls :
  impl_P_stmt -> impl_U_stmt ->
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage TgtO_example_large_fuzzer_ubsan.M.loaded_segments TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs).
Proof. intros HP HU. exact (base_ubsan_of_parts HP HU prog_no_enomem_P prog_no_enomem_U). Qed.

