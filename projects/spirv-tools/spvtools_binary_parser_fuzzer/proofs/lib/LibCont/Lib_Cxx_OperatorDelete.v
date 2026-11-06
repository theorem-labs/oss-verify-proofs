(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6db30_6db3c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6db30 : bv 32 := 0x4306406f.
Lemma F_6db30 : fetch_word Plain.M.loaded_segments (0x6db70 : word) = Some W_6db30.
Proof. vm_refl. Qed.
Lemma D_6db30 : decode_any W_6db30 = Some (Jal 0 410672, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db34 : bv 32 := 0xffdff06f.
Lemma F_6db34 : fetch_word Plain.M.loaded_segments (0x6db74 : word) = Some W_6db34.
Proof. vm_refl. Qed.
Lemma D_6db34 : decode_any W_6db34 = Some (Jal 0 2097148, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db38 : bv 32 := 0xff9ff06f.

End S1_code_6db30_6db3c.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg
  SRealizes RefMemcpyLib LibIface S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete.S1_code_6db30_6db3c.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Section OpDelete.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.

  Definition DEL0 : Z := 0x6db70.
  Definition DEL1 : Z := 0x6db74.
  Definition DEL2 : Z := 0x6db78.

  Theorem op_delete0_spec : op_delete_stmt SEGS Ly.L MI DEL0 (MALLOC_STACK MI).
  Proof using AC MI.
    intros fx A R M model p n sp ret K AI MS ROC CR Ha0 Hp Hsp Hroom Hwin CONT.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    - unfold DEL0. norm_pc. stepj F_6db30 D_6db30. apply mst_refl.
    - lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc1 _ _) _) _ =>
        replace pc1 with (Z_to_bv 64 (ly_free Ly.L)) by (apply bv_eq; reflexivity) end.
      exact (mi_free MI fx A R M model p n sp ret K AI MS ROC CR Ha0 Hp Hsp Hroom Hwin CONT).
  Qed.

  Theorem op_delete1_spec : op_delete_stmt SEGS Ly.L MI DEL1 (MALLOC_STACK MI).
  Proof using AC MI.
    intros fx A R M model p n sp ret K AI MS ROC CR Ha0 Hp Hsp Hroom Hwin CONT.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    - unfold DEL1. norm_pc. stepj F_6db34 D_6db34. stepj F_6db30 D_6db30. apply mst_refl.
    - lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc1 _ _) _) _ =>
        replace pc1 with (Z_to_bv 64 (ly_free Ly.L)) by (apply bv_eq; reflexivity) end.
      exact (mi_free MI fx A R M model p n sp ret K AI MS ROC CR Ha0 Hp Hsp Hroom Hwin CONT).
  Qed.

  Theorem operator_delete_spec : delete_rule_stmt SEGS Ly.L MI (MALLOC_STACK MI).
  Proof using AC MI. exact op_delete0_spec. Qed.

End OpDelete.
