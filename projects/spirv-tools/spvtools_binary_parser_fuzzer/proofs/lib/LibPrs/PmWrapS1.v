(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitDiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmDispatchS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_RidS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrLibS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_66400_66404.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_66400 : bv 32 := 0x00008067.
Lemma F_66400 : fetch_word Plain.M.loaded_segments (0x66440 : word) = Some W_66400.
Proof. vm_refl. Qed.
Lemma D_66400 : decode_any W_66400 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_66400_66404.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_TylS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_MaskS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_SpecS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_EnumS1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts3 S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmBody2S1 PmZw PmOLoopS1 PmStep4S1 PmStep5S1 PmExitDiagS1 PmOHeadS1 PmExitS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrDiagS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1.PmHdrS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmDispatchS1 PmArm_RidS1 PmArm_StrLibS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b20_69b24. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b5c_69b60. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapS1.S1_code_66400_66404. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmSetNumS1 PmArm_TylS1 PmArm_StrS1 PmBodyS1 PmArm_MaskS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_IdS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_SpecS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_ExtS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_LitS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyS1.PmArm_TyScDfS1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_EnumS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Local Ltac fexact := first [ match goal with |- ?g => match goal with H : ?T |- _ => constr_eq T g; exact H end end | eassumption ].
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).
  #[local] Notation pm_X1 := (PmOLoopS1.pm_X1 CL).
  #[local] Notation pm_opnd_pb := (PmOLoopS1.pm_opnd_pb CL).
  #[local] Notation pm_copy_loop := (PmOLoopS1.pm_copy_loop CL).
  #[local] Notation pm_push_tail := (PmOLoopS1.pm_push_tail CL).
  #[local] Notation pm_v3_pb := (PmStep4S1.pm_v3_pb CL).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_find_m1 := (PmStep4S1.pm_find_m1 CL).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  #[local] Notation pm_B2 := (PmBody2S1.pm_B2 CL).
  #[local] Notation pm_B1 := (PmBody1S1.pm_B1 CL).
  #[local] Notation pm_h5 := (PmStep5S1.pm_h5 CL).
  #[local] Notation pm_D7 := (PmExitDiagS1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagS1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagS1.pm_D9 CL).
  #[local] Notation pm_oloop := (PmOHeadS1.pm_oloop CL).
  #[local] Notation pm_xexit := (PmExitS1.pm_xexit CL).
  #[local] Notation pm_main := (PmLoopS1.pm_main CL).
  #[local] Notation pm_loop := (PmLoopS1.pm_loop CL).
  #[local] Notation pmx_room_ms := (PmArm_StrLibS1.pmx_room_ms CL).
  #[local] Notation pm_makestring := (PmArm_StrLibS1.pm_makestring CL).
  #[local] Notation pm_del_tr := (PmArm_StrLibS1.pm_del_tr CL).
  #[local] Notation pm_import := (PmArm_StrLibS1.pm_import CL).
  #[local] Notation pm_put_string := (PmArm_StrLibS1.pm_put_string CL).
  #[local] Notation pm_emplace_m3 := (PmArm_StrLibS1.pm_emplace_m3 CL).
  #[local] Notation ls_pdiag0x := (PmArm_StrLibS1.ls_pdiag0x CL).
  #[local] Notation ls_put_cstrx := (PmArm_StrLibS1.ls_put_cstrx CL).
  #[local] Notation ls_sdtor := (PmArm_StrLibS1.ls_sdtor CL).
  #[local] Notation ls_etail := (PmArm_StrLibS1.ls_etail CL).
  #[local] Notation ls_exh := (PmArm_StrLibS1.ls_exh CL).
  #[local] Notation ls_toolong := (PmArm_StrLibS1.ls_toolong CL).
  #[local] Notation ls_badimport := (PmArm_StrLibS1.ls_badimport CL).
  #[local] Notation pm_ctor_at := (PmSetNumS1.pm_ctor_at CL).
  #[local] Notation pm_put_cstr_at := (PmSetNumS1.pm_put_cstr_at CL).
  #[local] Notation pm_put_num_at := (PmSetNumS1.pm_put_num_at CL).
  #[local] Notation pm_put_u32_at := (PmSetNumS1.pm_put_u32_at CL).
  #[local] Notation pm_dtor_at := (PmSetNumS1.pm_dtor_at CL).
  #[local] Notation pm_nt_find := (PmSetNumS1.pm_nt_find CL).
  #[local] Notation sn_tail := (PmSetNumS1.sn_tail CL).
  #[local] Notation sn_diag := (PmSetNumS1.sn_diag CL).
  #[local] Notation pm_set_numeric := (PmSetNumS1.pm_set_numeric CL).

  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).

  Ltac fixregs3 := fixregs2;
    try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity).

  Definition PO_STK : Z := 17072.
  Definition PO_FRAME : Z := 672.

  Record ww : Type := WW {
    v_sp0 : Z; v_ret : Z; v_ctx : Z; v_env : Z; v_words : Z; v_n : Z;
    v_R0 : bvmap 5 word; v_A0 : AS MI; v_M0 : mem; v_model0 : Model; v_s : LibIface.SX ST }.
  Definition v_sp (w : ww) : Z := v_sp0 w - PO_FRAME.

  Definition PO_SLOTS (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 24%bv; getr R 23%bv; getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Record WS (w : ww) (X : list (Z * Z)) (A : AS MI) (M : mem) (model : Model) : Prop := MKWS {
    s_ai   : ainv MI A M model;
    s_ms   : mstd model;
    s_fs   : m_fs model = m_fs (v_model0 w);
    s_fds  : m_fds model = m_fds (v_model0 w);
    s_sx   : sx_inv ST (v_s w) M;
    s_sxh  : sx_handler_set ST (v_s w);
    s_roc  : ro_clear Ly.L M;
    s_eff  : eff MI (v_A0 w) A (v_M0 w) M (v_sp0 w - PO_STK, v_sp0 w) (junk SEGS Ly.L MI (v_A0 w));
    s_own_sx : forall a, owned MI A a -> ~ sx_region ST a;
    s_err_sx : forall a, errno_win Ly.L a -> ~ sx_region ST a;
    s_win_sx : forall a, zwin (v_sp0 w - PO_STK) (v_sp0 w) a -> ~ sx_region ST a;
    s_caps : caps MI A = caps MI (v_A0 w) /\ bigcap MI A = bigcap MI (v_A0 w);
    s_geo  : v_sp0 w mod 16 = 0 /\ alloc_ceiling + PO_STK <= v_sp0 w /\ v_sp0 w < 2 ^ 47;
    s_wdef : mdef M (v_sp0 w - PO_STK) (PO_STK - PO_FRAME);
    s_fdef : mdef M (v_sp0 w - PO_FRAME) (PO_FRAME - 80);
    s_sdef : mdef M (v_sp0 w - 80) 80;
    s_slots : forall k, 1 <= k <= 10 ->
        rdn SEGS M (Z_to_bv 64 (v_sp0 w - 8 * k)) 8 = Some (word_to_le_bytes 8 (nth (Z.to_nat (10 - k)) (PO_SLOTS (v_R0 w) (v_ret w)) (Z_to_bv 64 0)));
    s_live : Permutation (live MI A) (live MI (v_A0 w) ++ X)
  }.

  Lemma ws_stores : forall w X A M M' model (W : Z -> Prop),
    WS w X A M model -> stores_in W M M' -> (forall a, W a -> v_sp w <= a < v_sp0 w - 80) -> WS w X A M' model.
  Proof using AC MI ST.
    intros w X A M M' model W S SI HW. pose proof ac_bounds_lit as Hcv. destruct S as [AI MS FS FDS SX SXH ROC EF OSX ESX WSX CAPS GEO WD FD SD SL PL].
    destruct GEO as (G16 & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    assert (HWhi : forall a, W a -> alloc_ceiling <= a /\ ~ in_ranges (ly_img Ly.L) a).
    { intros a Ha. pose proof (HW a Ha). split; [lia|]. intros Hi. pose proof (ly_img_low _ Hi). lia. }
    constructor; try assumption.
    - eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact SI | intros a Ha; eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | exact (proj1 (HWhi a Ha))]].
    - eapply (stores_in_sx SEGS Ly.L ST); [exact SX | exact SI |]. intros a Ha. split; [apply WSX; pose proof (HW a Ha); unfold zwin; lia | intros Hr; exact (proj2 (HWhi a Ha) (ly_relro_img _ Hr))].
    - eapply (ro_clear_frame Ly.L); [exact ROC | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
      intros a (Hi & _ & _) Hw. exact (proj2 (HWhi a Hw) Hi).
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF | apply (eff_store MI A M M' _ (fun _ => False)); [| exact (proj2 SI)] |] |].
      + intros a HF HWn. apply (proj1 SI). intros Hw. apply HWn. pose proof (HW _ Hw) as HH. unfold W_of. cbn. pose proof (u64_range a). unfold PO_STK, v_sp, PO_FRAME in *. lia.
      + intros a Ha. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | unfold W_of, PO_STK in Ha; cbn in Ha; lia].
      + intros a [Ha|[]]. exact Ha.
    - split; [exact G16 | unfold PO_STK in *; lia].
    - eapply stores_in_mdef; [exact SI | exact WD].
    - eapply stores_in_mdef; [exact SI | exact FD].
    - eapply stores_in_mdef; [exact SI | exact SD].
    - intros k Hk. rewrite <- (SL k Hk). apply (rdn_agree_win SEGS M M' (v_sp0 w - 8 * k) 8); [lia | cbn; lia |].
      eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in Ha. cbn in Ha. split; [lia|]. intros Hw. pose proof (HW a Hw). unfold v_sp, PO_FRAME in *. lia.
  Qed.

  Lemma ws_through : forall w X X' A M model A' M' model' (S : Z) (Gf : Z -> Prop),
    WS w X A M model ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model -> sx_inv ST (v_s w) M' ->
    eff MI A A' M M' (v_sp w - S, v_sp w) Gf -> 0 <= S <= PO_STK - PO_FRAME ->
    (forall a, Gf a -> junk SEGS Ly.L MI (v_A0 w) a \/ (v_sp w <= a < v_sp0 w - 80 /\ M' (Z_to_bv 64 a) <> None)) ->
    Permutation (live MI A') (live MI (v_A0 w) ++ X') ->
    WS w X' A' M' model'.
  Proof using AC MI ST.
    intros w X X' A M model A' M' model' S Gf WSX AI' MS' FS' FDS' SX' EF HS HG PL'.
    pose proof ac_bounds_lit as Hcv. destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX CAPS GEO WD FD SD SL PL].
    destruct GEO as (G16 & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img Ly.L) x) by (intros x Hx Hi; pose proof (ly_img_low _ Hi); lia).
    assert (HGimg : forall a, Gf a -> ~ in_ranges (ly_img Ly.L) a).
    { intros a Ha. destruct (HG a Ha) as [(J1 & J2 & J3)|[Hr _]]; [exact J2 | apply HI; lia]. }
    assert (EF1 : eff MI A A' M M' (v_sp0 w - 17072, v_sp0 w) (junk SEGS Ly.L MI (v_A0 w))).
    { eapply (eff_drop SEGS Ly.L MI ly_img_low ly_rw_img A A' M M' model' _ _ (fun a => v_sp0 w - 672 <= a < v_sp0 w - 80 /\ M' (Z_to_bv 64 a) <> None)); [| exact AI' | |].
      - eapply eff_weaken; [eapply eff_widen; [exact EF | cbn; lia | cbn; lia] |]. intros a Ha. exact (HG a Ha).
      - intros a [Ha _]. unfold W_of. cbn. lia.
      - intros a [_ Hd] _. exact Hd. }
    constructor; try assumption. all: unfold v_sp, PO_STK, PO_FRAME in *.
    - rewrite FS'. exact FS. - rewrite FDS'. exact FDS.
    - eapply (ro_clear_via_eff SEGS Ly.L MI ly_img_low ly_errno_rw); [exact ROC | exact AI | exact EF | exact HGimg | cbn; lia].
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF0 | exact EF1 |] |].
      + intros a Ha. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | unfold W_of in Ha; cbn in Ha; lia].
      + intros a [Ha|Ha]; exact Ha.
    - intros a Ho'. destruct (ef_own _ _ _ _ _ _ _ _ _ EF a Ho') as [Ho|[[Hni _]|Hg]].
      + exact (OSX a Ho).
      + intros Hs. exact (Hni (ly_rw_img _ (sx_region_rw ST _ Hs))).
      + intros Hs. exact (HGimg a Hg (ly_rw_img _ (sx_region_rw ST _ Hs))).
    - rewrite (ef_caps _ _ _ _ _ _ _ _ _ EF), (ef_bigcap _ _ _ _ _ _ _ _ _ EF). exact CAPS.
    - split; [exact G16 | lia].
    - eapply (mdef_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_rw); [exact EF | left; lia | lia | lia | | | exact WD].
      + intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + intros i Hi Hg. destruct (HG _ Hg) as [(J1 & _)|[Hr _]]; lia.
    - intros i Hi. destruct (ef_def _ _ _ _ _ _ _ _ _ EF (v_sp0 w - 672 + i) ltac:(lia) (FD i Hi)) as [H|[H|[H|H]]].
      + exact H.
      + exfalso. revert H. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + destruct (HG _ H) as [(J1 & _)|[_ Hd]]; [exfalso; lia | exact Hd].
      + exfalso. pose proof (ly_img_low _ (ly_errno_img _ H)). lia.
    - eapply (mdef_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_rw); [exact EF | left; lia | lia | lia | | | exact SD].
      + intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + intros i Hi Hg. destruct (HG _ Hg) as [(J1 & _)|[Hr _]]; lia.
    - intros k Hk. rewrite <- (SL k Hk). apply (rdn_agree_win SEGS M M' (v_sp0 w - 8 * k) 8); [lia | cbn; lia |].
      eapply (agree_via_eff SEGS Ly.L MI); [exact EF|]. intros a Ha. unfold zwin in Ha. cbn in Ha.
      split; [lia|]. split; [eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia]|]. split; [eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia]|].
      split; [pose proof (SD (a - (v_sp0 w - 80)) ltac:(lia)) as D; replace (v_sp0 w - 80 + (a - (v_sp0 w - 80))) with a in D by lia; exact D|].
      split; [intros Hg; destruct (HG _ Hg) as [(J1 & _)|[Hr _]]; lia|].
      split; [unfold W_of; cbn; lia | intros He; exact (HI a ltac:(lia) (ly_errno_img a He))].
  Qed.

  Definition wregs (w : ww) (R : bvmap 5 word) (ret : Z) : Prop :=
    getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ 0 <= ret < 2 ^ 64 /\
    getr R 2%bv = Z_to_bv 64 (v_sp w) /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L).

  Lemma ws_callB : forall w X A M model R (ret S : Z),
    WS w X A M model -> wregs w R ret -> 0 <= S <= PO_STK - PO_FRAME -> callB MI ST A (v_s w) R M model (v_sp w) ret S.
  Proof using AC MI ST.
    intros w X A M model R ret S WSX (C1 & C2 & C3 & C4 & C5 & C6) HS. pose proof ac_bounds_lit as Hcv.
    destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    constructor.
    - exact AI. - exact MS. - apply (img_ro_clear_of Ly.L); [exact ROC |]. intros a Ha. eapply sx_relro; [exact SX | exact Ha]. - exact SX. - exact SXH.
    - constructor; try assumption; [replace (v_sp0 w - 672) with (v_sp0 w + (-42) * 16) by lia; rewrite Z_mod_plus_full; exact G16 | lia].
    - lia.
    - unfold stack_room. replace (v_sp0 w - 672 - S) with ((v_sp0 w - 17072) + (17072 - 672 - S)) by lia.
      apply (mdef_store_ok_off SEGS M _ (17072 - 672)); [exact WD | lia | lia | lia | rewrite Z2Nat.id by lia; lia].
    - intros a Ha. split.
      + eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | unfold zwin in Ha; lia].
      + apply WSX'. unfold zwin in *. lia.
    - exact OSX. - exact ESX.
  Qed.

  Lemma nodup_fst_drop_middle : forall (L B Y : list (Z * Z)), NoDup (map fst (L ++ B ++ Y)) -> NoDup (map fst (L ++ Y)).
  Proof using.
    intros L B Y N. rewrite !map_app in N. rewrite map_app.
    apply (proj1 (list_relations.list.NoDup_app _ _)) in N. destruct N as (NL & HX & NBY).
    apply (proj1 (list_relations.list.NoDup_app _ _)) in NBY. destruct NBY as (NB & HBY & NY).
    apply (proj2 (list_relations.list.NoDup_app _ _)). split; [exact NL|]. split; [| exact NY].
    intros x Hx Hy. apply (HX x Hx). apply (proj2 (list_basics.list.elem_of_app _ _ _)). right. exact Hy.
  Qed.

  Lemma perm_del_middle : forall (lv lv' L B Y : list (Z * Z)),
    NoDup (map fst lv) -> NoDup (map fst lv') -> Permutation lv (L ++ B ++ Y) ->
    (forall x, In x lv' <-> In x lv /\ ~ In (fst x) (map fst B)) ->
    Permutation lv' (L ++ Y).
  Proof using.
    intros lv lv' L B Y N N' P HM. pose proof (perm_nodup_fst _ _ P N) as NLBY.
    apply live_equiv_perm; [exact N' | exact (nodup_fst_drop_middle L B Y NLBY) |].
    intros q k. rewrite (HM (q, k)). cbn [fst].
    assert (HP : In (q, k) lv <-> In (q, k) (L ++ B ++ Y)) by (split; intros H; [apply (Permutation_in _ P H) | apply (Permutation_in _ (Permutation_sym P) H)]).
    rewrite HP, !in_app_iff.
    rewrite !map_app in NLBY. apply (proj1 (list_relations.list.NoDup_app _ _)) in NLBY. destruct NLBY as (NL & HX & NBY).
    apply (proj1 (list_relations.list.NoDup_app _ _)) in NBY. destruct NBY as (NB & HBY & NY).
    split.
    - intros [[HL|[HB|HY]] Hn]; [left; exact HL | exfalso; apply Hn; apply in_map_iff; exists (q, k); auto | right; exact HY].
    - intros [HL|HY].
      + split; [left; exact HL|]. intros HB. apply (HX q); [apply list_elem_of_In; apply in_map_iff; exists (q, k); auto | apply (proj2 (list_basics.list.elem_of_app _ _ _)); left; apply list_elem_of_In; exact HB].
      + split; [right; right; exact HY|]. intros HB. apply (HBY q); [apply list_elem_of_In; exact HB | apply list_elem_of_In; apply in_map_iff; exists (q, k); auto].
  Qed.

  Lemma ws_X_junk : forall w X A M model q k a, WS w X A M model -> In (q, k) X -> q <= a < q + k -> junk SEGS Ly.L MI (v_A0 w) a.
  Proof using AC MI ST.
    intros w X A M model q k a S Hq Ha. destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL].
    assert (HqA : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym PL)); apply in_app_iff; right; exact Hq).
    destruct (ai_live_block MI A M model q k AI HqA) as (_ & _ & Hq0 & Hqc & Hpay). destruct (Hpay a Ha) as (_ & Hni & _).
    split; [lia|]. split; [exact Hni|]. intros q' k' Hq' Ha'.
    assert (Hq'A : In (q', k') (live MI A)) by (apply (Permutation_in (q', k') (Permutation_sym PL)); apply in_app_iff; left; exact Hq').
    pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A M model AI)) as ND.
    assert (Hne : q' <> q) by (eapply (nodup_app_ne _ _ q' q ND); apply in_map_iff; [exists (q', k') | exists (q, k)]; auto).
    destruct (ai_live_disjoint MI A M model q' k' q k AI Hq'A HqA Hne); lia.
  Qed.

  #[local] Notation cnt l c := (count_class_f (size_class MI) (BIG MI) l c).

  Lemma ws_room : forall w X A M model n, WS w X A M model -> pm_budget SEGS Ly.L MI (v_A0 w) (v_n w) ->
    Zlength X <= 8 -> 0 <= n < BIG MI -> roomL MI A (live MI A) n.
  Proof using AC MI ST.
    intros w X A M model n S BUD HX Hn. destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' [Hcaps Hbig] GEO WD FD SD SL PL].
    destruct BUD as (Bcaps & Bbig & Bnmax & Bn & BS & BN & BB). pose proof (ai_size_class_range MI n Hn) as Hcls.
    split; [intros _ | intros Hb; lia]. rewrite Hcaps, Bcaps. rewrite !(count_class_f_perm _ _ _ _ _ PL), !cnt_app.
    pose proof (cnt_le_len SEGS Ly.L MI X (size_class MI n)). pose proof (cnt_le_len SEGS Ly.L MI X (size_class MI n + 1)).
    unfold PM_SMALL_SLACK, PM_NODES, CAP_SMALL, CAP_NODE in *.
    split.
    - destruct (Z.ltb_spec (size_class MI n) 4).
      + rewrite lib_caps_node by lia. pose proof (BN (size_class MI n) ltac:(lia)). unfold CAP_NODE in *. nia.
      + rewrite lib_caps_small by lia. pose proof (BS (size_class MI n) ltac:(lia)). unfold CAP_SMALL in *. lia.
    - destruct (Z.ltb_spec (size_class MI n + 1) 4).
      + rewrite lib_caps_node by lia. pose proof (BN (size_class MI n + 1) ltac:(lia)). unfold CAP_NODE in *. nia.
      + rewrite lib_caps_small by lia. pose proof (BS (size_class MI n + 1) ltac:(lia)). unfold CAP_SMALL in *. lia.
  Qed.

  Lemma ws_X_nodup : forall w X A M model, WS w X A M model -> NoDup (map fst X).
  Proof using AC MI ST.
    intros w X A M model S. destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL].
    pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A M model AI)) as ND. rewrite map_app in ND.
    apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & _ & ND). exact ND.
  Qed.
  Lemma ws_X_live : forall w X A M model b, WS w X A M model -> In b X -> In b (live MI A).
  Proof using AC MI ST.
    intros w X A M model b S Hb. destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL].
    apply (Permutation_in b (Permutation_sym PL)). apply in_app_iff. right. exact Hb.
  Qed.

  Lemma nodup_split6 : forall (a b c d e f : Z), NoDup [a; b; c; d; e; f] -> NoDup [a; b; c] /\ NoDup [d; e; f].
  Proof using.
    intros a b c d e f H. change [a; b; c; d; e; f] with ([a; b; c] ++ [d; e; f]) in H.
    apply (proj1 (list_relations.list.NoDup_app _ _)) in H. destruct H as (H1 & _ & H2). split; assumption.
  Qed.

  Lemma ws_heap_keep : forall w X A M model A' M' model' (W : Z * Z) (Gf : Z -> Prop) (Xk : list (Z * Z)),
    WS w X A M model -> ainv MI A' M' model' -> eff MI A A' M M' W Gf ->
    (forall b, In b Xk -> In b X) -> (forall b, In b Xk -> In b (live MI A')) ->
    (forall q k a, In (q, k) Xk -> q <= a < q + k -> ~ Gf a) -> alloc_ceiling <= fst W ->
    CRep.agree_on (fun a => exists q k, In (q, k) Xk /\ q <= a < q + k) M M'.
  Proof using AC MI ST.
    intros w X A M model A' M' model' W Gf Xk S AI' EF HX HL HG HW. pose proof ac_bounds_lit as Hcv.
    destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL].
    eapply (agree_via_eff SEGS Ly.L MI); [exact EF|]. intros a (q & k & Hq & Ha).
    assert (HqA : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym PL)); apply in_app_iff; right; exact (HX _ Hq)).
    destruct (ai_live_block MI A M model q k AI HqA) as (_ & _ & Hq0 & Hqc & Hpay). destruct (Hpay a Ha) as (Ho & Hni & Hd).
    destruct (ai_live_block MI A' M' model' q k AI' (HL _ Hq)) as (_ & _ & _ & _ & Hpay'). destruct (Hpay' a Ha) as (Ho' & _ & _).
    split; [lia|]. split; [exact Ho|]. split; [exact Ho'|]. split; [exact Hd|]. split; [exact (HG q k a Hq Ha)|].
    split; [unfold W_of; destruct W as [lo hi]; cbn in *; lia | intros He; exact (Hni (ly_errno_img a He))].
  Qed.

  Lemma ws_new : forall w X A M model (fx : FPState) R (n ret : Z) K,
    WS w X A M model -> wregs w R ret -> getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 500 ->
    room_for MI A n -> 500 <= NMAX MI ->
    (forall A' R' M' model' (p : Z),
        WS w (X ++ [(p, n)]) A' M' model' -> kept R R' -> getr R' 10%bv = Z_to_bv 64 p ->
        0 < p -> p + n <= alloc_ceiling -> p mod 16 = 0 -> mdef M' p n -> ~ In p (map fst (live MI A)) ->
        CRep.agree_on (fun a => v_sp w <= a < v_sp0 w) M M' ->
        CRep.agree_on (fun a => exists q k, In (q, k) X /\ q <= a < q + k) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (ly_new Ly.L) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w X A M model fx R n ret K WSX WR Ha0 Hn ROOM HNM CONT. pose proof ac_bounds_lit as Hcv.
    pose proof (ws_callB w X A M model R ret (NEW_STACK SEGS Ly.L MI) WSX WR) as CB.
    pose proof WSX as WS0. destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi).
    pose proof (cl_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS. unfold NEW_STACK in CB.
    specialize (CB ltac:(unfold PO_STK, PO_FRAME; lia)). destruct CB as [_ _ IRC _ _ CR CCEIL CROOM CWIN _ _].
    eapply ((cl_new _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (v_s w) R M model n (v_sp w) ret K AI MS IRC SX SXH CR Ha0 ltac:(lia) CCEIL CROOM CWIN OSX ESX).
    - unfold new_size. rewrite Z.max_l by lia. exact ROOM.
    - intros A' R' M' model' p AI' MS' FS' FDS' SX' KEPT Hp Hp0 LADD CAPS' BIG' OWN' FR' DEF'.
      unfold new_size in *. rewrite Z.max_l in LADD, FR' by lia. destruct LADD as [HL' Hfresh].
      assert (HIn : In (p, n) (live MI A')) by (rewrite HL'; left; reflexivity).
      destruct (ai_live_block MI A' M' model' p n AI' HIn) as (_ & Hpal & _ & Hpc & Hpay).
      assert (EF : eff MI A A' M M' (v_sp w - NEW_STACK SEGS Ly.L MI, v_sp w) (fun a => p <= a < p + n)).
      { eapply (eff_of_new MI A A' M M' model' _ _ p n); try fexact.
        - intros a Ha. exact Ha.
        - intros a Ha. exact Ha. }
      assert (WS1 : WS w (X ++ [(p, n)]) A' M' model').
      { eapply (ws_through w X _ A M model A' M' model' (NEW_STACK SEGS Ly.L MI)); [exact WS0 | exact AI' | exact MS' | exact FS' | exact FDS' | exact SX' | exact EF | unfold NEW_STACK, PO_STK, PO_FRAME; lia | |].
        - intros a Ha. cbn beta in Ha. left. destruct (Hpay a Ha) as (_ & Hni & _). split; [lia|]. split; [exact Hni|].
          intros q k Hqk Hqa. assert (HqA : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym PL)); apply in_app_iff; left; exact Hqk).
          assert (Hne : p <> q) by (intros ->; apply Hfresh; apply in_map_iff; exists (q, k); auto).
          destruct (ai_live_disjoint MI A' M' model' p n q k AI' HIn ltac:(rewrite HL'; right; exact HqA) Hne); lia.
        - rewrite HL'. rewrite PL. rewrite app_assoc. apply Permutation_cons_append. }
      eapply (CONT A' R' M' model' p WS1 KEPT Hp Hp0 Hpc Hpal); [intros i Hi; exact (proj2 (proj2 (Hpay (p + i) ltac:(lia)))) | exact Hfresh | |].
      2: { eapply (ws_heap_keep w _ A M model A' M' model' _ _ X WS0 AI' EF); [intros b Hb; exact Hb | intros b Hb; eapply (ws_X_live w _ A' M' model' b WS1); apply in_app_iff; left; exact Hb | | cbn [fst]; unfold v_sp, NEW_STACK, PO_STK, PO_FRAME in *; lia].
           intros q k a Hq Hqa Hf. cbn beta in Hf.
           assert (HqA : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym PL)); apply in_app_iff; right; exact Hq).
           assert (Hne : p <> q) by (intros ->; apply Hfresh; apply in_map_iff; exists (q, k); auto).
           destruct (ai_live_disjoint MI A' M' model' p n q k AI' HIn ltac:(rewrite HL'; right; exact HqA) Hne); lia. }
      intros a Ha. cbn beta in Ha. unfold v_sp, PO_FRAME, PO_STK in *. apply FR'. rewrite u64_of_Z by lia. unfold v_sp, PO_FRAME, NEW_STACK, zwin in *. intros [Ho|[Hb|[Hw|He]]].
      + revert Ho. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia].
      + lia. + lia.
      + pose proof (ly_img_low _ (ly_errno_img _ He)). lia.
  Qed.

  Definition state_dtor_stmt' : Prop :=
    forall (fx : FPState) (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model) (sp ret st : Z) (c : stateC) (K : TSet),
      callB MI ST A s R M model sp ret (STATE_DTOR_STACK (MALLOC_STACK MI)) ->
      getr R 10%bv = Z_to_bv 64 st ->
      state_rep MI A M st c -> above_sp MI A sp st 240 ->
      (forall A' R' M' model',
          retB MI ST A' s R R' M' model model' ->
          lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c)) (live MI A') ->
          eff MI A A' M M' (sp - STATE_DTOR_STACK (MALLOC_STACK MI), sp) (state_foot st c) ->
          mdef M' st 240 ->
          srealizes SEGS (cfg fx R' ret M' model') K) ->
      srealizes SEGS (cfg fx R (hc_state_dtor HConstsS1.hc) M model) K.

  Record po_callees : Prop := PO_CALLEES {
    po_mva  : state_mva_stmt SEGS Ly.L MI ST HConstsS1.hc (MALLOC_STACK MI);
    po_dtor : state_dtor_stmt'
  }.
  Variable PO : po_callees.

  Lemma state_foot_cases : forall st c a, state_foot st c a -> (st <= a < st + 240) \/ exists q k, In (q, k) (state_blocks c) /\ q <= a < q + k.
  Proof using. intros st c a [H|([q k] & Hb & Ha)]; [left; exact H | right; exists q, k; split; [exact Hb | exact Ha]]. Qed.

  Lemma ws_mva : forall w Y A M model (fx : FPState) R (ret st1 st2 : Z) (c1 c2 : stateC) K,
    WS w (state_blocks c1 ++ state_blocks c2 ++ Y) A M model -> wregs w R ret ->
    getr R 10%bv = Z_to_bv 64 st1 -> getr R 11%bv = Z_to_bv 64 st2 ->
    state_rep MI A M st1 c1 -> state_rep MI A M st2 c2 ->
    v_sp w <= st1 -> st1 + 240 <= v_sp0 w - 80 -> v_sp w <= st2 -> st2 + 240 <= v_sp0 w - 80 -> apart st1 240 st2 240 ->
    (forall (fx' : FPState) A' R' M' model',
        WS w (state_blocks c2 ++ Y) A' M' model' -> @fp_csr fx' = @fp_csr fx -> kept R R' -> getr R' 10%bv = Z_to_bv 64 st1 ->
        state_rep MI A' M' st1 (state_moved c1 c2) -> state_rep MI A' M' st2 (state_emptied c2) ->
        CRep.agree_on (fun a => v_sp w <= a < v_sp0 w /\ ~ (st1 <= a < st1 + 240) /\ ~ (st2 <= a < st2 + 240)) M M' ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (hc_state_mva HConstsS1.hc) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    intros w Y A M model fx R ret st1 st2 c1 c2 K WSX WR Ha0 Ha1 SR1 SR2 H1 H1' H2 H2' HAP CONT. pose proof ac_bounds_lit as Hcv.
    pose proof (cl_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (ws_callB w _ A M model R ret (STATE_MVA_STACK (MALLOC_STACK MI)) WSX WR ltac:(unfold STATE_MVA_STACK, PO_STK, PO_FRAME; lia)) as CB.
    pose proof WSX as WS0. destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A M model AI)) as ND.
    eapply ((po_mva PO) fx A (v_s w) R M model (v_sp0 w - 672) ret st1 st2 c1 c2 K CB Ha0 Ha1 SR1 SR2).
    - split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - exact HAP.
    - intros b Hb1 Hb2. rewrite !map_app in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & _ & ND).
      apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & HX & _).
      apply (HX b); apply list_elem_of_In; [exact Hb1 | apply in_app_iff; left; exact Hb2].
    - intros fx' A' R' M' model' RB Hcsr Ha0' SR1' SR2' LA EF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      assert (WS1 : WS w (state_blocks c2 ++ Y) A' M' model').
      { eapply (ws_through w _ _ A M model A' M' model' (STATE_MVA_STACK (MALLOC_STACK MI))); [exact WS0 | exact AI' | exact MS' | exact FS' | exact FDS' | exact SX' | exact EF | unfold STATE_MVA_STACK, PO_STK, PO_FRAME; lia | |].
        - intros a [Hf|Hf]; apply state_foot_cases in Hf; destruct Hf as [Ho|(q & k & Hb & Ha)].
          + right. split; [unfold v_sp, PO_FRAME; lia | pose proof (sr_def _ _ _ _ _ _ _ SR1') as D; unfold defined in D; pose proof (D (a - st1) ltac:(lia)) as D'; replace (st1 + (a - st1)) with a in D' by lia; exact D'].
          + left. eapply (ws_X_junk w _ A M model q k a WS0); [rewrite !in_app_iff; left; exact Hb | exact Ha].
          + right. split; [unfold v_sp, PO_FRAME; lia | pose proof (sr_def _ _ _ _ _ _ _ SR2') as D; unfold defined in D; pose proof (D (a - st2) ltac:(lia)) as D'; replace (st2 + (a - st2)) with a in D' by lia; exact D'].
          + left. eapply (ws_X_junk w _ A M model q k a WS0); [rewrite !in_app_iff; right; left; exact Hb | exact Ha].
        - eapply (perm_del_middle (live MI A) (live MI A') (live MI (v_A0 w)) (state_blocks c1) (state_blocks c2 ++ Y));
            [exact (ai_live_nodup MI A M model AI) | exact (ai_live_nodup MI A' M' model' AI') | exact PL |].
          intros [q k]. cbn [fst]. apply (lapply_dels_iff (map fst (state_blocks c1))). rewrite map_map. exact LA. }
      eapply (CONT fx' A' R' M' model' WS1 Hcsr KEPT Ha0' SR1' SR2').
      intros a (Ha & Hn1 & Hn2). cbn beta in *. apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
      unfold W_of, STATE_MVA_STACK. cbn [fst snd]. intros [Ho|[Ho'|[Hnm|[[Hf|Hf]|[Hw|He]]]]].
      + revert Ho. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + revert Ho'. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia].
      + destruct Hnm as (_ & _ & Hn). destruct (Z.lt_ge_cases a (v_sp0 w - 80)).
        * pose proof (FD (a - (v_sp0 w - 672)) ltac:(lia)) as D. replace (v_sp0 w - 672 + (a - (v_sp0 w - 672))) with a in D by lia. exact (D Hn).
        * pose proof (SD (a - (v_sp0 w - 80)) ltac:(lia)) as D. replace (v_sp0 w - 80 + (a - (v_sp0 w - 80))) with a in D by lia. exact (D Hn).
      + apply state_foot_cases in Hf. destruct Hf as [Hob|(q & k & Hb & Hqa)]; [lia|]. pose proof (proj1 (ws_X_junk w _ A M model q k a WS0 ltac:(rewrite !in_app_iff; left; exact Hb) Hqa)). lia.
      + apply state_foot_cases in Hf. destruct Hf as [Hob|(q & k & Hb & Hqa)]; [lia|]. pose proof (proj1 (ws_X_junk w _ A M model q k a WS0 ltac:(rewrite !in_app_iff; right; left; exact Hb) Hqa)). lia.
      + lia.
      + pose proof (ly_img_low _ (ly_errno_img _ He)). lia.
  Qed.

  Lemma ws_dtor : forall w Y A M model (fx : FPState) R (ret st : Z) (c : stateC) K,
    WS w (state_blocks c ++ Y) A M model -> wregs w R ret -> getr R 10%bv = Z_to_bv 64 st ->
    state_rep MI A M st c -> v_sp w <= st -> st + 240 <= v_sp0 w - 80 ->
    (forall A' R' M' model',
        WS w Y A' M' model' -> kept R R' ->
        CRep.agree_on (fun a => v_sp w <= a < v_sp0 w /\ ~ (st <= a < st + 240)) M M' ->
        CRep.agree_on (fun a => exists q k, In (q, k) Y /\ q <= a < q + k) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (hc_state_dtor HConstsS1.hc) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    intros w Y A M model fx R ret st c K WSX WR Ha0 SR H1 H1' CONT. pose proof ac_bounds_lit as Hcv.
    pose proof (cl_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (ws_callB w _ A M model R ret (STATE_DTOR_STACK (MALLOC_STACK MI)) WSX WR ltac:(unfold STATE_DTOR_STACK, PO_STK, PO_FRAME; lia)) as CB.
    pose proof WSX as WS0. destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    eapply ((po_dtor PO) fx A (v_s w) R M model (v_sp0 w - 672) ret st c K CB Ha0 SR).
    - split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - intros A' R' M' model' RB LA EF Hdef.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      assert (WS1 : WS w Y A' M' model').
      { eapply (ws_through w _ _ A M model A' M' model' (STATE_DTOR_STACK (MALLOC_STACK MI))); [exact WS0 | exact AI' | exact MS' | exact FS' | exact FDS' | exact SX' | exact EF | unfold STATE_DTOR_STACK, PO_STK, PO_FRAME; lia | |].
        - intros a Hf; apply state_foot_cases in Hf; destruct Hf as [Ho|(q & k & Hb & Ha)].
          + right. split; [unfold v_sp, PO_FRAME; lia | pose proof (Hdef (a - st) ltac:(lia)) as D'; replace (st + (a - st)) with a in D' by lia; exact D'].
          + left. eapply (ws_X_junk w _ A M model q k a WS0); [rewrite !in_app_iff; left; exact Hb | exact Ha].
        - eapply (perm_del_middle (live MI A) (live MI A') (live MI (v_A0 w)) (state_blocks c) Y);
            [exact (ai_live_nodup MI A M model AI) | exact (ai_live_nodup MI A' M' model' AI') | exact PL |].
          intros [q k]. cbn [fst]. apply (lapply_dels_iff (map fst (state_blocks c))). rewrite map_map. exact LA. }
      eapply (CONT A' R' M' model' WS1 KEPT).
      2: { pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A M model AI)) as NDx.
           eapply (ws_heap_keep w _ A M model A' M' model' _ _ Y WS0 AI' EF); [intros b Hb; apply in_app_iff; right; exact Hb | intros b Hb; eapply (ws_X_live w Y A' M' model' b WS1 Hb) | | cbn [fst]; unfold STATE_DTOR_STACK; lia].
           intros q k a Hq Hqa Hf. apply state_foot_cases in Hf. destruct Hf as [Hob|(q' & k' & Hb' & Ha')].
           - destruct (ai_live_block MI A M model q k AI (ws_X_live w _ A M model _ WS0 ltac:(apply in_app_iff; right; exact Hq))) as (_ & _ & _ & Hqc & _). lia.
           - refine (live_payload_disjoint SEGS Ly.L MI A M model q' k' q k a AI (ws_X_live w _ A M model _ WS0 ltac:(apply in_app_iff; left; exact Hb')) (ws_X_live w _ A M model _ WS0 ltac:(apply in_app_iff; right; exact Hq)) _ Ha' Hqa).
             rewrite map_app in NDx. apply (nodup_app_ne (live MI (v_A0 w)) (state_blocks c ++ Y) q' q) in NDx || idtac.
             intros ->. rewrite !map_app in NDx. apply (proj1 (list_relations.list.NoDup_app _ _)) in NDx. destruct NDx as (_ & _ & NDx).
             apply (proj1 (list_relations.list.NoDup_app _ _)) in NDx. destruct NDx as (_ & HX & _).
             apply (HX q); apply list_elem_of_In; apply in_map_iff; [exists (q, k') | exists (q, k)]; auto. }
      intros a (Ha & Hn1). cbn beta in *. apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
      unfold W_of, STATE_DTOR_STACK. cbn [fst snd]. intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
      + revert Ho. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + revert Ho'. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia].
      + destruct Hnm as (_ & _ & Hn). destruct (Z.lt_ge_cases a (v_sp0 w - 80)).
        * pose proof (FD (a - (v_sp0 w - 672)) ltac:(lia)) as D. replace (v_sp0 w - 672 + (a - (v_sp0 w - 672))) with a in D by lia. exact (D Hn).
        * pose proof (SD (a - (v_sp0 w - 80)) ltac:(lia)) as D. replace (v_sp0 w - 80 + (a - (v_sp0 w - 80))) with a in D by lia. exact (D Hn).
      + apply state_foot_cases in Hf. destruct Hf as [Hob|(q & k & Hb & Hqa)]; [lia|]. pose proof (proj1 (ws_X_junk w _ A M model q k a WS0 ltac:(rewrite !in_app_iff; left; exact Hb) Hqa)). lia.
      + lia.
      + pose proof (ly_img_low _ (ly_errno_img _ He)). lia.
  Qed.

  Lemma ws_pm : forall w A M model (fx : FPState) R (ret : Z) (c0 : parserC) K,
    WS w (state_blocks (pc_state c0)) A M model -> wregs w R ret -> frm_zero (@fp_csr fx) -> getr R 10%bv = Z_to_bv 64 (v_sp w) ->
    parser_rep SEGS Ly.L MI A M (v_sp w) c0 -> pc_cons c0 = v_sp w + 304 ->
    fresh_state (pc_state c0) (v_words w) (v_n w) ->
    (v_words w <> 0 -> words_ok (live MI (v_A0 w)) (v_sp0 w) M (v_words w) (v_n w)) ->
    (forall a, zwin (v_words w) (v_words w + 4 * v_n w) a -> ~ zwin (v_sp0 w - PO_STK) (v_sp0 w) a) ->
    pm_budget SEGS Ly.L MI (v_A0 w) (v_n w) ->
    (forall (fx' : FPState) A' R' M' model' (c' : parserC) (r : Z),
        WS w (state_blocks (pc_state c')) A' M' model' -> frm_zero (@fp_csr fx') -> kept R R' -> getr R' 10%bv = Z_to_bv 64 r ->
        parser_rep SEGS Ly.L MI A' M' (v_sp w) c' -> pc_cons c' = pc_cons c0 ->
        st_words (pc_state c') = v_words w -> st_nwords (pc_state c') = v_n w ->
        (forall cls, cnt (state_blocks (pc_state c')) cls <= (if cls <? 4 then PM_NODES (v_n w) else 0) + 10) ->
        CRep.agree_on (fun a => v_sp w + PARSER_SIZE <= a < v_sp0 w) M M' ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (kc_parse_module kcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model fx R ret c0 K WSX WR FZ Ha0 PR Hcons FR WOK WWIN BUD CONT. pose proof ac_bounds_lit as Hcv.
    pose proof (ws_callB w _ A M model R ret 16384 WSX WR ltac:(unfold PO_STK, PO_FRAME; lia)) as CB.
    pose proof WSX as WS0. destruct WSX as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi).
    pose proof FR as FR'. destruct FR' as (Fw & Fn & _).
    pose proof (PmBodyS1.parse_module_S1 CL fx A (v_s w) R M model (v_sp w) ret (v_sp w) c0 (live MI (v_A0 w)) K) as PM.
    cbn zeta in PM. cbn [kc_pm_stack kc_parse_module kcS1] in PM |- *. rewrite Fw, Fn in PM.
    unfold v_sp, PO_STK, PO_FRAME, PARSER_SIZE in *.
    eapply (PM CB ROC FZ Ha0 PR); clear PM.
    - split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - rewrite Hcons. split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - rewrite Hcons. replace (v_sp0 w - 672 + 304) with (v_sp0 w + (-23) * 16) by lia. rewrite Z_mod_plus_full. exact G16.
    - exact FR.
    - intros Hw. destruct (WOK Hw) as (W1 & W2 & W3 & W4 & W5 & W6). split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
      destruct W6 as [W6|W6]; [left; lia | right; exact W6].
    - intros Hwn a Ha. split; [pose proof (WWIN a Ha); unfold zwin in *; lia|].
      unfold parser_foot, PARSER_SIZE. intros [Hobj|Hsf]; [pose proof (WWIN a Ha); unfold zwin in *; lia|].
      apply state_foot_cases in Hsf. destruct Hsf as [Hobj|(q & k & Hb & Hqa)].
      { pose proof (WWIN a Ha) as WW. unfold zwin in Ha, WW, Hobj. unfold ST_OFF in Hobj. lia. }
      pose proof (ws_X_junk w _ A M model q k a WS0 Hb Hqa) as (J1 & J2 & J3).
      destruct (WOK Hwn) as (W1 & W2 & W3 & W4 & W5 & W6). destruct W6 as [W6|(q' & k' & Hq' & Hlo & Hhi)]; [unfold zwin in Ha; lia|].
      exact (J3 q' k' Hq' ltac:(unfold zwin in Ha; lia)).
    - exact PL.
    - destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7). destruct CAPS as [HC HB]. unfold pm_budgetL. rewrite HC, HB. repeat (split; [assumption|]). exact B7.
    - intros fx' A' R' M' model' c' r RB FZ' Hr PR' Hcons' Hw' Hn' PL' SZ CNT' VST' EF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof (perm_nodup_fst _ _ PL' (ai_live_nodup MI A' M' model' AI')) as ND'.
      assert (JC' : forall q k a, In (q, k) (state_blocks (pc_state c')) -> q <= a < q + k -> junk SEGS Ly.L MI (v_A0 w) a).
      { intros q k a Hq Ha. assert (HqA : In (q, k) (live MI A')) by (apply (Permutation_in (q, k) (Permutation_sym PL')); apply in_app_iff; right; exact Hq).
        destruct (ai_live_block MI A' M' model' q k AI' HqA) as (_ & _ & Hq0 & Hqc & Hpay). destruct (Hpay a Ha) as (_ & Hni & _).
        split; [lia|]. split; [exact Hni|]. intros q' k' Hq' Ha'.
        assert (Hq'A : In (q', k') (live MI A')) by (apply (Permutation_in (q', k') (Permutation_sym PL')); apply in_app_iff; left; exact Hq').
        assert (Hne : q' <> q) by (eapply (nodup_app_ne _ _ q' q ND'); apply in_map_iff; [exists (q', k') | exists (q, k)]; auto).
        destruct (ai_live_disjoint MI A' M' model' q' k' q k AI' Hq'A HqA Hne); lia. }
      assert (OBJ : forall a, v_sp0 w - 672 <= a < v_sp0 w - 672 + 288 -> M' (Z_to_bv 64 a) <> None).
      { intros a Ha. destruct (Z.lt_ge_cases a (v_sp0 w - 672 + 48)).
        - pose proof (pr_def _ _ _ _ _ _ _ PR' (a - (v_sp0 w - 672)) ltac:(unfold ST_OFF; lia)) as D. replace (v_sp0 w - 672 + (a - (v_sp0 w - 672))) with a in D by lia. exact D.
        - pose proof (sr_def _ _ _ _ _ _ _ (pr_state _ _ _ _ _ _ _ PR')) as D. unfold defined, ST_OFF in D.
          pose proof (D (a - (v_sp0 w - 672 + 48)) ltac:(lia)) as D'. replace (v_sp0 w - 672 + 48 + (a - (v_sp0 w - 672 + 48))) with a in D' by lia. exact D'. }
      assert (WS1 : WS w (state_blocks (pc_state c')) A' M' model').
      { eapply (ws_through w _ _ A M model A' M' model' 16384); [exact WS0 | exact AI' | exact MS' | exact FS' | exact FDS' | exact SX' | exact EF | unfold PO_STK, PO_FRAME; lia | | exact PL'].
        intros a HG0. unfold pm_foot, parser_foot, PARSER_SIZE, ST_OFF in HG0. destruct HG0 as [Hf|[Hf|Hj]].
        - destruct Hf as [Hobj|Hsf]; [right; unfold v_sp, PO_FRAME; split; [lia | apply OBJ; lia]|].
          apply state_foot_cases in Hsf. destruct Hsf as [Hobj|(q & k & Hb & Hqa)]; [right; unfold v_sp, PO_FRAME, ST_OFF in *; split; [lia | apply OBJ; lia]|].
          left. exact (ws_X_junk w _ A M model q k a WS0 Hb Hqa).
        - destruct Hf as [Hobj|Hsf]; [right; unfold v_sp, PO_FRAME; split; [lia | apply OBJ; lia]|].
          apply state_foot_cases in Hsf. destruct Hsf as [Hobj|(q & k & Hb & Hqa)]; [right; unfold v_sp, PO_FRAME, ST_OFF in *; split; [lia | apply OBJ; lia]|].
          left. exact (JC' q k a Hb Hqa).
        - left. destruct Hj as (J1 & J2 & J3). split; [exact J1|]. split; [exact J2|]. intros q k Hq. apply J3.
          apply (Permutation_in (q, k) (Permutation_sym PL)). apply in_app_iff. left. exact Hq. }
      eapply (CONT fx' A' R' M' model' c' r WS1 FZ' KEPT Hr PR' Hcons' Hw' Hn' CNT').
      intros a Ha. cbn beta in *. apply (ef_frame _ _ _ _ _ _ _ _ _ EF). rewrite u64_of_Z by lia.
      unfold W_of. cbn [fst snd]. intros [Ho|[Ho'|[Hnm|[Hf|[Hw|He]]]]].
      + revert Ho. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      + revert Ho'. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia].
      + destruct Hnm as (_ & _ & Hn). destruct (Z.lt_ge_cases a (v_sp0 w - 80)).
        * pose proof (FD (a - (v_sp0 w - 672)) ltac:(lia)) as D. replace (v_sp0 w - 672 + (a - (v_sp0 w - 672))) with a in D by lia. exact (D Hn).
        * pose proof (SD (a - (v_sp0 w - 80)) ltac:(lia)) as D. replace (v_sp0 w - 80 + (a - (v_sp0 w - 80))) with a in D by lia. exact (D Hn).
      + unfold pm_foot, parser_foot, PARSER_SIZE, ST_OFF in Hf. destruct Hf as [[Hobj|Hsf]|[[Hobj|Hsf]|Hj]]; [lia | | lia | |].
        * apply state_foot_cases in Hsf. destruct Hsf as [Hobj|(q & k & Hb & Hqa)]; [unfold ST_OFF in Hobj; lia|]. pose proof (proj1 (ws_X_junk w _ A M model q k a WS0 Hb Hqa)). lia.
        * apply state_foot_cases in Hsf. destruct Hsf as [Hobj|(q & k & Hb & Hqa)]; [unfold ST_OFF in Hobj; lia|]. pose proof (proj1 (JC' q k a Hb Hqa)). lia.
        * pose proof (proj1 Hj). lia.
      + lia.
      + pose proof (ly_img_low _ (ly_errno_img _ He)). lia.
  Qed.

  Ltac in_regs := apply PmStepS1.in_reg_list; reflexivity.
  Definition WSTOPS : list Z := [0xe5ddc; 0x664c8; 0x666fc; 0x66818].
  Ltac fixregsN :=
    try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 5)) with (5%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 6)) with (6%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 7)) with (7%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 14)) with (14%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 15)) with (15%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 16)) with (16%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 17)) with (17%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 19)) with (19%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 28)) with (28%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 29)) with (29%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 30)) with (30%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 31)) with (31%bv : reg) in * by (apply bv_eq; reflexivity).

  Definition pinit (b : Z) (M : mem) : Prop :=
    cellw SEGS M (b + 8) 8 (b + 304) /\ cellw SEGS M (b + 16) 8 0 /\ cellw SEGS M (b + 24) 8 0 /\ cellw SEGS M (b + 32) 8 0 /\ cellw SEGS M (b + 40) 1 0 /\
    cellw SEGS M (b + 48) 8 0 /\ cellw SEGS M (b + 56) 8 0 /\ cellw SEGS M (b + 64) 8 0 /\ cellw SEGS M (b + 72) 8 0 /\ cellw SEGS M (b + 80) 8 0 /\
    cellw SEGS M (b + 88) 4 0 /\ cellw SEGS M (b + 92) 2 0 /\
    cellw SEGS M (b + 96) 8 0 /\ cellw SEGS M (b + 104) 8 0 /\ cellw SEGS M (b + 112) 8 0 /\ cellw SEGS M (b + 120) 8 0 /\ cellw SEGS M (b + 128) 4 0x3f800000 /\
    cellw SEGS M (b + 136) 8 0 /\ cellw SEGS M (b + 144) 8 0 /\ cellw SEGS M (b + 152) 8 0 /\ cellw SEGS M (b + 160) 8 0 /\ cellw SEGS M (b + 168) 4 0x3f800000 /\
    cellw SEGS M (b + 176) 8 0 /\ cellw SEGS M (b + 184) 8 0 /\ cellw SEGS M (b + 192) 8 0 /\ cellw SEGS M (b + 200) 8 0 /\ cellw SEGS M (b + 208) 4 0x3f800000 /\
    cellw SEGS M (b + 336) 8 0.
  Lemma pinit_agree : forall b M M', pinit b M -> 0 <= b -> b + 344 < 2 ^ 64 ->
    CRep.agree_on (fun a => b <= a < b + 216 \/ b + 336 <= a < b + 344) M M' -> pinit b M'.
  Proof using.
    intros b M M' P Hb Hhi AG. unfold pinit in *.
    repeat match goal with |- _ /\ _ => split end; repeat match type of P with _ /\ _ => let H := fresh "C" in destruct P as [H P] end;
      (eapply (PmBody1S1.cellw_frame M M'); [fexact | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition vtrip (b o p sz : Z) (M : mem) : Prop := cell8 SEGS M (b + o) p /\ cell8 SEGS M (b + o + 8) p /\ cell8 SEGS M (b + o + 16) (p + sz).
  Lemma vtrip_agree : forall b o p sz M M', vtrip b o p sz M -> 0 <= b + o -> b + o + 24 < 2 ^ 64 ->
    CRep.agree_on (fun a => b + o <= a < b + o + 24) M M' -> vtrip b o p sz M'.
  Proof using.
    intros b o p sz M M' (C1 & C2 & C3) Hlo Hhi AG. unfold vtrip, cell8 in *.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (PmBody1S1.cellw_frame M M'); [fexact | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition tinit (b words n : Z) (M : mem) : Prop :=
    cellw SEGS M (b + 352) 8 words /\ cellw SEGS M (b + 360) 8 n /\ cellw SEGS M (b + 368) 8 0 /\ cellw SEGS M (b + 376) 8 0 /\ cellw SEGS M (b + 384) 8 0 /\
    cellw SEGS M (b + 392) 4 0 /\ cellw SEGS M (b + 396) 2 0 /\
    cellw SEGS M (b + 400) 8 0 /\ cellw SEGS M (b + 408) 8 0 /\ cellw SEGS M (b + 416) 8 0 /\ cellw SEGS M (b + 424) 8 0 /\ cellw SEGS M (b + 432) 4 0x3f800000 /\
    cellw SEGS M (b + 440) 8 0 /\ cellw SEGS M (b + 448) 8 0 /\ cellw SEGS M (b + 456) 8 0 /\ cellw SEGS M (b + 464) 8 0 /\ cellw SEGS M (b + 472) 4 0x3f800000 /\
    cellw SEGS M (b + 480) 8 0 /\ cellw SEGS M (b + 488) 8 0 /\ cellw SEGS M (b + 496) 8 0 /\ cellw SEGS M (b + 504) 8 0 /\ cellw SEGS M (b + 512) 4 0x3f800000.
  Lemma tinit_agree : forall b words n M M', tinit b words n M -> 0 <= b -> b + 600 < 2 ^ 64 ->
    CRep.agree_on (fun a => b + 352 <= a < b + 520) M M' -> tinit b words n M'.
  Proof using.
    intros b words n M M' P Hb Hhi AG. unfold tinit in *.
    repeat match goal with |- _ /\ _ => split end; repeat match type of P with _ /\ _ => let H := fresh "C" in destruct P as [H P] end;
      (eapply (PmBody1S1.cellw_frame M M'); [fexact | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition mkfresh (words n q1 q2 q3 : Z) : stateC :=
    {| st_words := words; st_nwords := n; st_diag := 0; st_widx := 0; st_icount := 0; st_endian := 0; st_flags := 0;
       st_m1 := (0, 0, []); st_m2 := (0, 0, []); st_m3 := (0, 0, []);
       st_v1 := (q1, q1, q1 + 500); st_v2 := (q2, q2, q2 + 100); st_v3 := (q3, q3, q3 + 100) |}.

  Lemma vec_blocks_nz : forall q e c, q <> 0 -> vec_blocks (q, e, c) = [(q, c - q)].
  Proof using. intros q e c Hq. unfold vec_blocks. cbn [HStmts.t3a HStmts.t3c fst snd]. destruct (Z.eqb_spec q 0); [lia | reflexivity]. Qed.

  Lemma mkfresh_blocks : forall words n q1 q2 q3, q1 <> 0 -> q2 <> 0 -> q3 <> 0 ->
    state_blocks (mkfresh words n q1 q2 q3) = [(q1, 500); (q2, 100); (q3, 100)].
  Proof using.
    intros words n q1 q2 q3 H1 H2 H3. unfold state_blocks, mkfresh. cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b HStmts.t3c fst snd].
    rewrite !vec_blocks_nz by assumption. cbn. repeat (f_equal; try lia).
  Qed.

  Lemma st_rep_fresh : forall A M model (b d words n q1 q2 q3 : Z),
    ainv MI A M model ->
    cellw SEGS M (b + d) 8 words -> cellw SEGS M (b + (d + 8)) 8 n -> cellw SEGS M (b + (d + 16)) 8 0 -> cellw SEGS M (b + (d + 24)) 8 0 -> cellw SEGS M (b + (d + 32)) 8 0 ->
    cellw SEGS M (b + (d + 40)) 4 0 -> cellw SEGS M (b + (d + 44)) 2 0 ->
    cellw SEGS M (b + (d + 48)) 8 0 -> cellw SEGS M (b + (d + 56)) 8 0 -> cellw SEGS M (b + (d + 64)) 8 0 -> cellw SEGS M (b + (d + 72)) 8 0 -> cellw SEGS M (b + (d + 80)) 4 0x3f800000 ->
    cellw SEGS M (b + (d + 88)) 8 0 -> cellw SEGS M (b + (d + 96)) 8 0 -> cellw SEGS M (b + (d + 104)) 8 0 -> cellw SEGS M (b + (d + 112)) 8 0 -> cellw SEGS M (b + (d + 120)) 4 0x3f800000 ->
    cellw SEGS M (b + (d + 128)) 8 0 -> cellw SEGS M (b + (d + 136)) 8 0 -> cellw SEGS M (b + (d + 144)) 8 0 -> cellw SEGS M (b + (d + 152)) 8 0 -> cellw SEGS M (b + (d + 160)) 4 0x3f800000 ->
    vtrip b (d + 168) q1 500 M -> vtrip b (d + 192) q2 100 M -> vtrip b (d + 216) q3 100 M ->
    mdef M (b + d) 240 -> (b + d) mod 8 = 0 -> 0 < b + d -> b + d + 240 <= 2 ^ 47 ->
    In (q1, 500) (live MI A) -> In (q2, 100) (live MI A) -> In (q3, 100) (live MI A) -> NoDup [q1; q2; q3] ->
    state_rep MI A M (b + d) (mkfresh words n q1 q2 q3).
  Proof using AC MI.
    intros A M model b d words n q1 q2 q3 AI C0 C8 C16 C24 C32 C40 C44 C48 C56 C64 C72 C80 C88 C96 C104 C112 C120 C128 C136 C144 C152 C160 (V1a & V1b & V1c) (V2a & V2b & V2c) (V3a & V3b & V3c) HD Hal Hlo Hhi I1 I2 I3 ND.
    destruct (ai_live_block MI A M model q1 500 AI I1) as (_ & _ & Q1 & _). destruct (ai_live_block MI A M model q2 100 AI I2) as (_ & _ & Q2 & _). destruct (ai_live_block MI A M model q3 100 AI I3) as (_ & _ & Q3 & _).
    assert (DEF : forall o k, 0 <= o -> o + k <= 240 -> defined M (b + d + o) k).
    { intros o k Ho Hk i Hi. pose proof (HD (o + i) ltac:(lia)) as D. replace (b + d + (o + i)) with (b + d + o + i) in D by lia. exact D. }
    assert (RW : forall k, b + (d + k) = b + d + k) by (intros; lia).
    rewrite !RW in *.
    constructor; cbn [mkfresh st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b HStmts.t3c fst snd].
    - rewrite Z.add_0_r || idtac. replace (b + d) with (b + d + 0) by lia. exact C0 || (rewrite Z.add_0_r; exact C0).
    - exact C8. - exact C16. - exact C24. - exact C32. - exact C40. - exact C44.
    - apply (umapx_empty SEGS Ly.L MI 24 Z (nval24 SEGS)); unfold cell8, cell4; try assumption.
      + replace (b + d + 48 + 8) with (b + d + 56) by lia. exact C56.
      + replace (b + d + 48 + 16) with (b + d + 64) by lia. exact C64.
      + replace (b + d + 48 + 24) with (b + d + 72) by lia. exact C72.
      + replace (b + d + 48 + 32) with (b + d + 80) by lia. exact C80.
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - apply (umapx_empty SEGS Ly.L MI 32 (Z * Z * Z) (nval32 SEGS)); unfold cell8, cell4; try assumption.
      + replace (b + d + 88 + 8) with (b + d + 96) by lia. exact C96.
      + replace (b + d + 88 + 16) with (b + d + 104) by lia. exact C104.
      + replace (b + d + 88 + 24) with (b + d + 112) by lia. exact C112.
      + replace (b + d + 88 + 32) with (b + d + 120) by lia. exact C120.
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - apply (umapx_empty SEGS Ly.L MI 24 Z (nval24 SEGS)); unfold cell8, cell4; try assumption.
      + replace (b + d + 128 + 8) with (b + d + 136) by lia. exact C136.
      + replace (b + d + 128 + 16) with (b + d + 144) by lia. exact C144.
      + replace (b + d + 128 + 24) with (b + d + 152) by lia. exact C152.
      + replace (b + d + 128 + 32) with (b + d + 160) by lia. exact C160.
      + apply DEF; lia.
      + rewrite <- Zplus_mod_idemp_l, Hal. reflexivity.
      + lia. + lia.
    - constructor; [exact V1a | replace (b + d + 168 + 8) with (b + d + 168 + 8) by lia; exact V1b | exact V1c | right; split; [lia | split; [replace (q1 + 500 - q1) with 500 by lia; exact I1 | lia]]].
    - constructor; [exact V2a | exact V2b | exact V2c | right; split; [lia | split; [replace (q2 + 100 - q2) with 100 by lia; exact I2 | lia]]].
    - constructor; [exact V3a | exact V3b | exact V3c | right; split; [lia | split; [replace (q3 + 100 - q3) with 100 by lia; exact I3 | lia]]].
    - replace (b + d) with (b + d + 0) by lia. apply DEF; lia.
    - exact Hal.
    - rewrite (mkfresh_blocks words n q1 q2 q3) by lia. cbn [map fst]. exact ND.
  Qed.

  Lemma state_rep_keep : forall (A A' : AS MI) M M' st c,
    state_rep MI A M st c -> 0 < st -> st + 240 <= 2 ^ 47 ->
    (forall a, state_foot st c a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall b, In b (state_blocks c) -> In b (live MI A')) ->
    state_rep MI A' M' st c.
  Proof using AC MI.
    intros A A' M M' st c SR Hlo Hhi HM HL.
    destruct SR as [W0 W1 W2 W3 W4 W5 W6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd].
    assert (AGO : forall o k, 0 <= o -> o + k <= 240 -> agree_on M M' (st + o) k).
    { intros o k Ho Hk i Hi. apply HM. left. lia. }
    assert (CW : forall o (wd : N) v, cellw SEGS M (st + o) wd v -> 0 <= o -> o + Z.of_N wd <= 240 -> cellw SEGS M' (st + o) wd v).
    { intros o wd v C Ho Hk. eapply cellw_agree; [exact C | apply AGO; lia | lia | lia]. }
    assert (INB : forall (b : Z * Z) (sel : list (Z * Z)), In b sel -> (forall x, In x sel -> In x (state_blocks c)) -> In b (live MI A')).
    { intros b sel Hb Hs. apply HL. apply Hs. exact Hb. }
    assert (UF : forall NS (V : Type) (o bl bc : Z) (ents : list (Z * (Z * V))) a,
              (forall x, In x (umap_blocks NS bl bc ents) -> In x (state_blocks c)) -> 0 <= o -> o + 40 <= 240 ->
              umap_foot NS (st + o) bl bc ents a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros NS V o bl bc ents a Hs Ho Hk Hf. apply HM. destruct (umap_foot_cases NS (st + o) bl bc ents a Hf) as [H|(b & Hb & Hab)]; [left; lia | right].
      exists b. split; [apply Hs; exact Hb | exact Hab]. }
    unfold state_blocks in *.
    constructor.
    - replace st with (st + 0) by lia. apply CW; [rewrite Z.add_0_r; exact W0 | lia | cbn; lia].
    - apply CW; [exact W1 | lia | cbn; lia]. - apply CW; [exact W2 | lia | cbn; lia]. - apply CW; [exact W3 | lia | cbn; lia].
    - apply CW; [exact W4 | lia | cbn; lia]. - apply CW; [exact W5 | lia | cbn; lia]. - apply CW; [exact W6 | lia | cbn; lia].
    - eapply (umapx_agree SEGS Ly.L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact Sm1 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
    - eapply (umapx_agree SEGS Ly.L MI 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia)); [exact Sm2 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
    - eapply (umapx_agree SEGS Ly.L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact Sm3 | intros a Hf; refine (UF _ _ _ _ _ _ _ _ _ _ Hf); [intros x Hx; rewrite !in_app_iff; tauto | lia | lia] | intros p n Hp _; apply HL; rewrite !in_app_iff; tauto].
    - destruct Sv1 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 168 + 8) with (st + 176) by lia; apply CW; [replace (st + 176) with (st + 168 + 8) by lia; exact E | lia | cbn; lia]
        | replace (st + 168 + 16) with (st + 184) by lia; apply CW; [replace (st + 184) with (st + 168 + 16) by lia; exact C | lia | cbn; lia] |].
      destruct BLK as [L|(Hb & Hin & Hbe)]; [left; exact L | right]. split; [exact Hb|]. split; [| exact Hbe].
      apply HL. rewrite !in_app_iff. right; right; right; left. unfold vec_blocks. cbn [HStmts.t3a HStmts.t3c fst snd]. destruct (Z.eqb_spec (HStmts.t3a (st_v1 c)) 0); [lia | left; reflexivity].
    - destruct Sv2 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 192 + 8) with (st + 200) by lia; apply CW; [replace (st + 200) with (st + 192 + 8) by lia; exact E | lia | cbn; lia]
        | replace (st + 192 + 16) with (st + 208) by lia; apply CW; [replace (st + 208) with (st + 192 + 16) by lia; exact C | lia | cbn; lia] |].
      destruct BLK as [L|(Hb & Hin & Hbe)]; [left; exact L | right]. split; [exact Hb|]. split; [| exact Hbe].
      apply HL. rewrite !in_app_iff. right; right; right; right; left. unfold vec_blocks. cbn [HStmts.t3a HStmts.t3c fst snd]. destruct (Z.eqb_spec (HStmts.t3a (st_v2 c)) 0); [lia | left; reflexivity].
    - destruct Sv3 as [B E C BLK]. constructor; [apply CW; [exact B | lia | cbn; lia] | replace (st + 216 + 8) with (st + 224) by lia; apply CW; [replace (st + 224) with (st + 216 + 8) by lia; exact E | lia | cbn; lia]
        | replace (st + 216 + 16) with (st + 232) by lia; apply CW; [replace (st + 232) with (st + 216 + 16) by lia; exact C | lia | cbn; lia] |].
      destruct BLK as [L|(Hb & Hin & Hbe)]; [left; exact L | right]. split; [exact Hb|]. split; [| exact Hbe].
      apply HL. rewrite !in_app_iff. right; right; right; right; right. unfold vec_blocks. cbn [HStmts.t3a HStmts.t3c fst snd]. destruct (Z.eqb_spec (HStmts.t3a (st_v3 c)) 0); [lia | left; reflexivity].
    - eapply defined_agree; [exact Sdef | replace st with (st + 0) by lia; apply AGO; lia].
    - exact Sal.
    - exact Snd.
  Qed.

  Lemma state_blocks_emptied : forall c, state_blocks (state_emptied c) = [].
  Proof using. intros c. reflexivity. Qed.
  Lemma state_moved_mkfresh : forall c words n q1 q2 q3, state_moved c (mkfresh words n q1 q2 q3) = mkfresh words n q1 q2 q3.
  Proof using. intros. reflexivity. Qed.
  Lemma fresh_mkfresh : forall words n q1 q2 q3, q1 <> 0 -> q2 <> 0 -> q3 <> 0 -> fresh_state (mkfresh words n q1 q2 q3) words n.
  Proof using. intros. unfold fresh_state, mkfresh. cbn [st_words st_nwords st_widx st_icount st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b HStmts.t3c fst snd]. repeat (split; [first [reflexivity | assumption] |]). reflexivity. Qed.

  Definition phdr (b : Z) (M : mem) : Prop :=
    cellw SEGS M (b + 8) 8 (b + 304) /\ cellw SEGS M (b + 16) 8 0 /\ cellw SEGS M (b + 24) 8 0 /\ cellw SEGS M (b + 32) 8 0 /\ cellw SEGS M (b + 40) 1 0 /\
    cellw SEGS M (b + 336) 8 0.
  Lemma phdr_of_pinit : forall b M, pinit b M -> phdr b M.
  Proof using. intros b M P. unfold pinit in P. unfold phdr. repeat match type of P with _ /\ _ => let H := fresh "C" in destruct P as [H P] end. repeat (split; [assumption|]). exact P. Qed.
  Lemma phdr_agree : forall b M M', phdr b M -> 0 <= b -> b + 344 < 2 ^ 64 ->
    CRep.agree_on (fun a => b <= a < b + 48 \/ b + 336 <= a < b + 344) M M' -> phdr b M'.
  Proof using.
    intros b M M' P Hb Hhi AG. unfold phdr in *.
    repeat match goal with |- _ /\ _ => split end; repeat match type of P with _ /\ _ => let H := fresh "C" in destruct P as [H P] end;
      (eapply (PmBody1S1.cellw_frame M M'); [fexact | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Lemma ws_words_ok : forall w X A M model, WS w X A M model -> ainv MI (v_A0 w) (v_M0 w) (v_model0 w) ->
    (forall a, zwin (v_words w) (v_words w + 4 * v_n w) a -> ~ zwin (v_sp0 w - PO_STK) (v_sp0 w) a) ->
    words_ok (live MI (v_A0 w)) (v_sp0 w) (v_M0 w) (v_words w) (v_n w) ->
    words_ok (live MI (v_A0 w)) (v_sp0 w) M (v_words w) (v_n w).
  Proof using AC MI ST.
    intros w X A M model S AI0 WWIN (W1 & W2 & W3 & W4 & W5 & W6). pose proof ac_bounds_lit as Hcv.
    destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' CAPS GEO WD FD SD SL PL]. destruct GEO as (G16 & Gceil & Ghi).
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [| exact W6].
    intros i Hi. pose proof (W5 i Hi) as D.
    assert (E : M (Z_to_bv 64 (v_words w + i)) = v_M0 w (Z_to_bv 64 (v_words w + i))); [| rewrite E; exact D].
    apply (ef_frame _ _ _ _ _ _ _ _ _ EF0). rewrite u64_of_Z by lia. unfold W_of, PO_STK in *. cbn [fst snd].
    assert (CASES : forall A1 M1 model1, ainv MI A1 M1 model1 -> (forall b, In b (live MI (v_A0 w)) -> In b (live MI A1)) ->
              ~ owned MI A1 (v_words w + i) /\ (in_ranges (ly_img Ly.L) (v_words w + i) -> False)).
    { intros A1 M1 model1 AI1 HL. destruct W6 as [Hs|(q & k & Hq & Hlo & Hhi')].
      - split; [eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI1 | lia] | intros Hi'; pose proof (ly_img_low _ Hi'); lia].
      - destruct (ai_live_block MI A1 M1 model1 q k AI1 (HL _ Hq)) as (_ & _ & _ & _ & Hpay). destruct (Hpay (v_words w + i) ltac:(lia)) as (Ho & Hni & _). split; [exact Ho | exact Hni]. }
    destruct (CASES _ _ _ AI0 ltac:(intros b Hb; exact Hb)) as [O0 I0].
    destruct (CASES _ _ _ AI ltac:(intros b Hb; apply (Permutation_in b (Permutation_sym PL)); apply in_app_iff; left; exact Hb)) as [O1 _].
    intros [Ho|[Ho'|[Hnm|[Hj|[Hw|He]]]]].
    - exact (O0 Ho). - exact (O1 Ho').
    - destruct Hnm as (_ & _ & Hn). exact (D Hn).
    - destruct Hj as (J1 & J2 & J3). destruct W6 as [Hs|(q & k & Hq & Hlo & Hhi')]; [lia | exact (J3 q k Hq ltac:(lia))].
    - exact (WWIN (v_words w + i) ltac:(unfold zwin; lia) ltac:(unfold zwin; lia)).
    - exact (I0 (ly_errno_img _ He)).
  Qed.

  Lemma ws_slots10 : forall w X A M model, WS w X A M model ->
    let sp := v_sp0 w in let R0 := v_R0 w in
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (v_ret w))) /\
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R0 8%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 (getr R0 9%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (getr R0 18%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 (getr R0 19%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 (getr R0 20%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 (getr R0 21%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 (getr R0 22%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 (getr R0 23%bv)) /\
    rdn SEGS M (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 (getr R0 24%bv)).
  Proof using AC MI ST.
    intros w X A M model S. cbn zeta. pose proof (s_slots _ _ _ _ _ S) as SL.
    pose proof (SL 1 ltac:(lia)) as T1. pose proof (SL 2 ltac:(lia)) as T2. pose proof (SL 3 ltac:(lia)) as T3. pose proof (SL 4 ltac:(lia)) as T4. pose proof (SL 5 ltac:(lia)) as T5.
    pose proof (SL 6 ltac:(lia)) as T6. pose proof (SL 7 ltac:(lia)) as T7. pose proof (SL 8 ltac:(lia)) as T8. pose proof (SL 9 ltac:(lia)) as T9. pose proof (SL 10 ltac:(lia)) as T10.
    unfold PO_SLOTS in *. cbn [Z.to_nat Z.sub nth Pos.to_nat Z.mul Pos.mul Z.pos_sub Pos.iter_op Nat.add Nat.mul] in T1, T2, T3, T4, T5, T6, T7, T8, T9, T10.
    replace (v_sp0 w - 8 * 1) with (v_sp0 w - 8) in T1 by lia. replace (v_sp0 w - 8 * 2) with (v_sp0 w - 16) in T2 by lia.
    replace (v_sp0 w - 8 * 3) with (v_sp0 w - 24) in T3 by lia. replace (v_sp0 w - 8 * 4) with (v_sp0 w - 32) in T4 by lia.
    replace (v_sp0 w - 8 * 5) with (v_sp0 w - 40) in T5 by lia. replace (v_sp0 w - 8 * 6) with (v_sp0 w - 48) in T6 by lia.
    replace (v_sp0 w - 8 * 7) with (v_sp0 w - 56) in T7 by lia. replace (v_sp0 w - 8 * 8) with (v_sp0 w - 64) in T8 by lia.
    replace (v_sp0 w - 8 * 9) with (v_sp0 w - 72) in T9 by lia. replace (v_sp0 w - 8 * 10) with (v_sp0 w - 80) in T10 by lia.
    repeat (split; [assumption|]). assumption.
  Qed.

  Ltac sc_rdw H := eapply (PmCoreS1.sc_read_w _ _ _ _ _ _ H); [evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia] | evs; reflexivity].

  Definition POPOST (w : ww) (K : TSet) : Prop :=
    forall (fx' : FPState) A' R' M' model' (r : Z),
        retB MI ST A' (v_s w) (v_R0 w) R' M' (v_model0 w) model' -> frm_zero (@fp_csr fx') -> getr R' 10%bv = Z_to_bv 64 r ->
        Permutation (live MI A') (live MI (v_A0 w)) ->
        eff MI (v_A0 w) A' (v_M0 w) M' (v_sp0 w - PO_STK, v_sp0 w) (junk SEGS Ly.L MI (v_A0 w)) ->
        srealizes SEGS (cfg fx' R' (v_ret w) M' model') K.

  Definition POW (w : ww) : Prop :=
    ret_ok (Z_to_bv 64 (v_ret w)) /\ 0 <= v_ret w < 2 ^ 64 /\
    getr (v_R0 w) 1%bv = Z_to_bv 64 (v_ret w) /\ getr (v_R0 w) 2%bv = Z_to_bv 64 (v_sp0 w) /\
    getr (v_R0 w) 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr (v_R0 w) 4%bv = Z_to_bv 64 (ly_tp Ly.L).

  Lemma po_epi : forall (w : ww) K (fx : FPState) A M model R (r : Z),
    let sp := v_sp0 w in let b := v_sp0 w - 672 in
    POPOST w K -> POW w -> frm_zero (@fp_csr fx) ->
    WS w [] A M model -> cellw SEGS M (b + 336) 8 0 ->
    getr R 2%bv = Z_to_bv 64 b -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (b + 304) -> getr R 18%bv = Z_to_bv 64 r ->
    getr R 25%bv = getr (v_R0 w) 25%bv -> getr R 26%bv = getr (v_R0 w) 26%bv -> getr R 27%bv = getr (v_R0 w) 27%bv ->
    srealizes SEGS (cfg fx R 0x663e8 M model) K.
  Proof using AC MI ST.
    intros w K fx A M model R r. cbn zeta.
    intros POST (Hret & Hretr & R0ra & R0sp & R0gp & R0tp) FZ WS0 C336 H2 Qgp Qtp G8 G18 E25 E26 E27.
    pose proof ac_bounds_lit as Hcv. pose proof (s_geo _ _ _ _ _ WS0) as (_ & Gceil & Ghi). unfold PO_STK in *.
    pose proof (ws_slots10 _ _ _ _ _ WS0) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
    pose (E := Eseed R [Z_to_bv 64 (v_sp0 w - 672); Z_to_bv 64 (v_ret w); getr (v_R0 w) 8%bv; getr (v_R0 w) 9%bv; getr (v_R0 w) 18%bv;
                        getr (v_R0 w) 19%bv; getr (v_R0 w) 20%bv; getr (v_R0 w) 21%bv; getr (v_R0 w) 22%bv; getr (v_R0 w) 23%bv; getr (v_R0 w) 24%bv]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 304))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; try assumption. rewrite w_add by lia. exact G8. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWord (SA (EVar 32) 336) (N.to_nat 8) (ELit 0)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kword_var; [exact C336 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    pose proof (s_ms _ _ _ _ _ WS0) as MS.
    xruns HR HK 100%nat WSTOPS (SCR [false] [EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42] []) 60%N.
    { split_scs; try sc_auto1.
      all: first [sc_rdw T1 | sc_rdw T2 | sc_rdw T3 | sc_rdw T4 | sc_rdw T5 | sc_rdw T6 | sc_rdw T7 | sc_rdw T8 | sc_rdw T9 | sc_rdw T10]. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (10%bv) G10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 25; 26; 27]%bv HRn eq_refl) as GS. fixregsN.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    { norm_pc. stepjr F_66400 D_66400 (Z_to_bv 64 (v_ret w)) ltac:(gres; rewrite G1; reflexivity). apply mst_refl. }
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 (v_ret w)) by (symmetry; exact Hret) end.
    eapply (POST fx A R1 M model r).
    - constructor.
      + exact (s_ai _ _ _ _ _ WS0). + exact MS. + exact (s_fs _ _ _ _ _ WS0). + exact (s_fds _ _ _ _ _ WS0). + exact (s_sx _ _ _ _ _ WS0).
      + intros rr Hrr. unfold callee_saved in Hrr.
        destruct (bv_eq_dec _ rr 1%bv) as [->|N1]; [rewrite G1; symmetry; exact R0ra|].
        destruct (bv_eq_dec _ rr 2%bv) as [->|N2]; [rewrite G2, w_add by lia; rewrite R0sp; f_equal; lia|].
        destruct (bv_eq_dec _ rr 3%bv) as [->|N3]; [rewrite (GS 3%bv) by (clear; in_regs); rewrite Qgp; symmetry; exact R0gp|].
        destruct (bv_eq_dec _ rr 4%bv) as [->|N4]; [rewrite (GS 4%bv) by (clear; in_regs); rewrite Qtp; symmetry; exact R0tp|].
        destruct (bv_eq_dec _ rr 25%bv) as [->|N25]; [rewrite (GS 25%bv) by (clear; in_regs); exact E25|].
        destruct (bv_eq_dec _ rr 26%bv) as [->|N26]; [rewrite (GS 26%bv) by (clear; in_regs); exact E26|].
        destruct (bv_eq_dec _ rr 27%bv) as [->|N27]; [rewrite (GS 27%bv) by (clear; in_regs); exact E27|].
        repeat (destruct Hrr as [<-|Hrr]; [first [contradiction | rewrite (reg_val _ _ _ _ HRn); evs; reflexivity] |]). destruct Hrr.
    - exact FZ.
    - rewrite G10. first [exact G18 | rewrite (GS 18%bv) by (clear; in_regs); exact G18].
    - rewrite (s_live _ _ _ _ _ WS0). rewrite app_nil_r. reflexivity.
    - exact (s_eff _ _ _ _ _ WS0).
  Qed.

  Lemma if_true_Z : forall (x y : Z), (if true then x else y) = x. Proof using. reflexivity. Qed.
  Lemma if_false_Z : forall (x y : Z), (if false then x else y) = y. Proof using. reflexivity. Qed.

  Lemma ws_room2 : forall w SB extra A M model m, WS w (SB ++ extra) A M model -> pm_budget SEGS Ly.L MI (v_A0 w) (v_n w) ->
    (forall cls, cnt SB cls <= (if cls <? 4 then PM_NODES (v_n w) else 0) + 10) -> Zlength extra <= 3 -> 0 <= m < BIG MI ->
    roomL MI A (live MI A) m.
  Proof using AC MI ST.
    intros w SB extra A M model m S BUD HC HX Hm. destruct S as [AI MS FS FDS SX SXH ROC EF0 OSX ESX WSX' [Hcaps Hbig] GEO WD FD SD SL PL].
    destruct BUD as (Bcaps & Bbig & Bnmax & Bn & BS & BN & BB). pose proof (ai_size_class_range MI m Hm) as Hcls.
    split; [intros _ | intros Hb; lia]. rewrite Hcaps, Bcaps. rewrite !(count_class_f_perm _ _ _ _ _ PL), !cnt_app.
    pose proof (cnt_le_len SEGS Ly.L MI extra (size_class MI m)). pose proof (cnt_le_len SEGS Ly.L MI extra (size_class MI m + 1)).
    unfold PM_SMALL_SLACK, CAP_SMALL, CAP_NODE in *.
    split.
    - destruct (Z.ltb_spec (size_class MI m) 4) as [Hl|Hl].
      + rewrite lib_caps_node by lia. pose proof (BN (size_class MI m) ltac:(lia)). pose proof (HC (size_class MI m)) as T.
        rewrite (proj2 (Z.ltb_lt _ _) Hl) in T; try rewrite if_true_Z in T. unfold CAP_NODE in *. lia.
      + rewrite lib_caps_small by lia. pose proof (BS (size_class MI m) ltac:(lia)). pose proof (HC (size_class MI m)) as T.
        rewrite (proj2 (Z.ltb_ge _ _) Hl) in T; try rewrite if_false_Z in T. unfold CAP_SMALL in *. lia.
    - destruct (Z.ltb_spec (size_class MI m + 1) 4) as [Hl|Hl].
      + rewrite lib_caps_node by lia. pose proof (BN (size_class MI m + 1) ltac:(lia)). pose proof (HC (size_class MI m + 1)) as T.
        rewrite (proj2 (Z.ltb_lt _ _) Hl) in T; try rewrite if_true_Z in T. unfold CAP_NODE in *. lia.
      + rewrite lib_caps_small by lia. pose proof (BS (size_class MI m + 1) ltac:(lia)). pose proof (HC (size_class MI m + 1)) as T.
        rewrite (proj2 (Z.ltb_ge _ _) Hl) in T; try rewrite if_false_Z in T. unfold CAP_SMALL in *. lia.
  Qed.

  Lemma state_rep_stores : forall w X A M M' model st c (W : Z -> Prop) lo hi,
    WS w (state_blocks c ++ X) A M model -> state_rep MI A M st c -> stores_in W M M' -> (forall a, W a -> lo <= a < hi) ->
    v_sp w <= lo -> (st + 240 <= lo \/ hi <= st) -> 0 < st -> st + 240 <= 2 ^ 47 -> state_rep MI A M' st c.
  Proof using AC MI ST.
    intros w X A M M' model st c W lo hi S SR STI HW Hlo Hst Hst0 Hst1. pose proof ac_bounds_lit as Hcv.
    pose proof (s_geo _ _ _ _ _ S) as (_ & Gceil & Ghi). unfold v_sp, PO_STK, PO_FRAME in *.
    eapply (state_rep_keep A A M M' st c SR); [lia | lia | | intros b Hb; eapply (ws_X_live w _ A M model b S); apply in_app_iff; left; exact Hb].
    intros a Hf. apply state_foot_cases in Hf.
    assert (Ra : 0 <= a < 2 ^ 64 /\ ~ W a).
    { destruct Hf as [Ho|(q & k & Hb & Ha)].
      - split; [lia|]. intros HWa. pose proof (HW _ HWa). lia.
      - destruct (ai_live_block MI A M model q k (s_ai _ _ _ _ _ S) (ws_X_live w _ A M model _ S ltac:(apply in_app_iff; left; exact Hb))) as (_ & _ & Hq0 & Hqc & _).
        split; [lia|]. intros HWa. pose proof (HW _ HWa). lia. }
    destruct Ra as [Ra Rn]. pose proof (proj1 STI (Z_to_bv 64 a)) as E. rewrite u64_of_Z in E by lia. exact (E Rn).
  Qed.

  Lemma state_rep_via : forall w X' (Xh : list (Z * Z)) A A' M M' model' st c (P : Z -> Prop),
    state_rep MI A M st c -> WS w X' A' M' model' -> (forall b, In b (state_blocks c) -> In b X') ->
    CRep.agree_on P M M' -> (forall a, st <= a < st + 240 -> P a) ->
    CRep.agree_on (fun a => exists q k, In (q, k) Xh /\ q <= a < q + k) M M' -> (forall b, In b (state_blocks c) -> In b Xh) ->
    0 < st -> st + 240 <= 2 ^ 47 -> state_rep MI A' M' st c.
  Proof using AC MI ST.
    intros w X' Xh A A' M M' model' st c P SR S' HX' AG HP AH HXh Hst0 Hst1.
    eapply (state_rep_keep A A' M M' st c SR); [lia | lia | | intros b Hb; eapply (ws_X_live w _ A' M' model' b S'); apply HX'; exact Hb].
    intros a Hf. apply state_foot_cases in Hf. destruct Hf as [Ho|(q & k & Hb & Ha)].
    - apply AG. apply HP. exact Ho.
    - apply AH. exists q, k. split; [apply HXh; exact Hb | exact Ha].
  Qed.

  Lemma parser_rep_mk : forall w X A M model c, let b := v_sp w in
    WS w X A M model -> phdr b M -> state_rep MI A M (b + 48) c ->
    parser_rep SEGS Ly.L MI A M b {| pc_cons := b + 304; pc_user := 0; pc_state := c |}.
  Proof using AC MI ST.
    intros w X A M model c. cbn zeta. intros S PH SR. pose proof ac_bounds_lit as Hcv.
    pose proof (s_geo _ _ _ _ _ S) as (G16 & Gceil & Ghi). pose proof (s_fdef _ _ _ _ _ S) as FD. unfold v_sp, PO_STK, PO_FRAME in *.
    destruct PH as (C8 & C16 & C24 & C32 & C40 & C336).
    constructor; cbn [pc_cons pc_user pc_state]; unfold ST_OFF, PARSER_SIZE.
    - exact (proj2 C8). - exact (proj2 C16). - exact (proj2 C24). - exact (proj2 C32). - exact (proj2 C40).
    - exact SR.
    - eapply mdef_sub; [exact FD | lia | lia].
    - replace (v_sp0 w - 672) with (v_sp0 w + (-42) * 16) by lia. rewrite Z_mod_plus_full. exact G16.
    - lia.
    - replace (v_sp0 w - 672 + 304 + 32) with (v_sp0 w - 672 + 336) by lia. exact (proj2 C336).
    - eapply mdef_sub; [exact FD | lia | lia].
    - unfold apart. lia.
  Qed.

  Ltac carryG GS G Q := lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (GS r) in Q by (clear; in_regs) end.

  Lemma po_tail2 : forall (w : ww) K (fx : FPState) A9 M9 model9 R9 (c : stateC) (r : Z),
    let sp := v_sp0 w in let b := v_sp0 w - 672 in
    POPOST w K -> POW w -> pm_budget SEGS Ly.L MI (v_A0 w) (v_n w) -> 500 <= NMAX MI -> frm_zero (@fp_csr fx) ->
    WS w (state_blocks c) A9 M9 model9 -> state_rep MI A9 M9 (b + 48) c -> cellw SEGS M9 (b + 336) 8 0 ->
    (forall cls, cnt (state_blocks c) cls <= (if cls <? 4 then PM_NODES (v_n w) else 0) + 10) ->
    getr R9 2%bv = Z_to_bv 64 b -> getr R9 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R9 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R9 8%bv = Z_to_bv 64 (b + 304) -> getr R9 9%bv = Z_to_bv 64 (b + 48) -> getr R9 10%bv = Z_to_bv 64 r -> getr R9 24%bv = Z_to_bv 64 0x3f800000 ->
    getr R9 25%bv = getr (v_R0 w) 25%bv -> getr R9 26%bv = getr (v_R0 w) 26%bv -> getr R9 27%bv = getr (v_R0 w) 27%bv ->
    srealizes SEGS (cfg fx R9 0x66328 M9 model9) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    intros w K fx A9 M9 model9 R9 c r. cbn zeta.
    intros POST PW BUD HNM FZ WS9 SRP9 C9 CNT H2_9 Qgp9 Qtp9 G8_9 G9_9 G10_9 G24_9 E25_9 E26_9 E27_9.
    pose proof ac_bounds_lit as Hcv. pose proof (s_geo _ _ _ _ _ WS9) as (Hsp16 & Gceil & Ghi). pose proof (proj2 (proj2 (cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL))) as HBIG. unfold PO_STK in *.
    assert (Esp : v_sp w = v_sp0 w - 672) by reflexivity.
    set (sp := v_sp0 w) in *.

    pose (E9 := Eseed R9 [Z_to_bv 64 (sp - 672); Z_to_bv 64 r]).
    assert (HR9 : regs_ok E9 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (24%bv, ELit 1065353216)]) R9).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK9 : know_ok SEGS E9 M9 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS9) as FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS9) as MS9.
    xruns HR9 HK9 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9'.
    rreg HRn (1%bv) G1_9. rreg HRn (2%bv) H2_9'. rreg HRn (10%bv) G10_9'. rreg HRn (18%bv) G18_9'. rreg HRn (24%bv) G24_9'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 25; 26; 27]%bv HRn eq_refl) as GS9'.
    clear HRn HR9 HK9. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M9' := mm) in * end.
    assert (ST9 : stores_in (zwin (sp - 672 + 352) (sp - 672 + 516)) M9 M9') by (unfold M9'; stin).
    assert (WS9' : WS w (state_blocks c) A9 M9' model9) by (eapply (ws_stores w _ A9 M9 M9' model9 _ WS9 ST9); rewrite Esp; unfold zwin; intros; lia).
    assert (TI9' : tinit (sp - 672) 0 0 M9').
    { unfold tinit. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M9'; rdback]). }
    assert (AG9s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 352) (sp - 672 + 516) a) M9 M9') by (eapply stores_in_agree; [exact ST9 | intros b' Hb'; unfold zwin in *; lia]).
    assert (SRP9' : state_rep MI A9 M9' (sp - 672 + 48) c).
    { rewrite <- (app_nil_r (state_blocks c)) in WS9. eapply (state_rep_stores w [] A9 M9 M9' model9 _ c _ (sp - 672 + 352) (sp - 672 + 516) WS9 SRP9 ST9); [unfold zwin; intros; lia | rewrite Esp; lia | lia | lia | lia]. }
    assert (C9' : cellw SEGS M9' (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M9 M9'); [exact C9 | lia | cbn; lia | eapply agree_on_weaken; [exact AG9s | unfold zwin; cbn; intros; lia]]).
    pose proof (s_ms _ _ _ _ _ WS9') as MS9'. clearbody M9'. clear ST9 AG9s C9 SRP9 WS9 MS9.
    rewrite <- (app_nil_r (state_blocks c)) in WS9'.
    eapply (ws_new w _ A9 M9' model9 fx R9' 500 0x6638c K WS9');
      [ split; [exact G1_9 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_9' | split; [rewrite (GS9' 3%bv) by (clear; in_regs); exact Qgp9 | rewrite (GS9' 4%bv) by (clear; in_regs); exact Qtp9]]]]]
      | exact G10_9' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS9') | lia | eapply (ws_room2 w _ _ A9 M9' model9 500 WS9' BUD CNT); [rewrite Zlength_nil; lia | lia]]
      | exact HNM |].
    intros A10 R10 M10 model10 q1 WS10 KEPT10 G10_10 Hq1a Hq1c Hq1al Hq1d Hq1f AG10 AH10. rewrite <- app_assoc in WS10. cbn [app] in WS10.
    assert (Qgp10 : getr R10 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT10 3%bv) by (clear; in_regs); rewrite (GS9' 3%bv) by (clear; in_regs); exact Qgp9).
    assert (Qtp10 : getr R10 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT10 4%bv) by (clear; in_regs); rewrite (GS9' 4%bv) by (clear; in_regs); exact Qtp9).
    keptQ KEPT10 H2_9' H2_10.
    carryG GS9' G8_9 G8_9'. keptQ KEPT10 G8_9' G8_10. carryG GS9' G9_9 G9_9'. keptQ KEPT10 G9_9' G9_10. keptQ KEPT10 G18_9' G18_10.
    keptQ KEPT10 G24_9' G24_10.
    carryG GS9' E25_9 E25_9'. keptQ KEPT10 E25_9' E25_10. carryG GS9' E26_9 E26_9'. keptQ KEPT10 E26_9' E26_10. carryG GS9' E27_9 E27_9'. keptQ KEPT10 E27_9' E27_10.
    assert (TI10 : tinit (sp - 672) 0 0 M10) by (eapply (tinit_agree _ _ _ M9' M10 TI9'); [lia | lia | eapply agree_on_weaken; [exact AG10 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (C10 : cellw SEGS M10 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M9' M10); [exact C9' | lia | cbn; lia | eapply agree_on_weaken; [exact AG10 | rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (SRP10 : state_rep MI A10 M10 (sp - 672 + 48) c).
    { eapply (state_rep_via w _ _ A9 A10 M9' M10 model10 _ c _ SRP9' WS10); [intros b' Hb'; apply in_app_iff; left; exact Hb' | exact AG10 | rewrite Esp; cbn beta; intros; lia | exact AH10 | intros b' Hb'; apply in_app_iff; left; exact Hb' | lia | lia]. }
    clear AG10 AH10 TI9' C9' SRP9' MS9' G8_9' G9_9' G24_9' E25_9' E26_9' E27_9'.

    pose (E10 := Eseed R10 [Z_to_bv 64 (sp - 672); Z_to_bv 64 q1]).
    assert (HR10 : regs_ok E10 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R10).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK10 : know_ok SEGS E10 M10 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS10) as FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS10) as MS10.
    xruns HR10 HK10 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10'.
    rreg HRn (1%bv) G1_10. rreg HRn (2%bv) H2_10'. rreg HRn (10%bv) G10_10'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS10'.
    clear HRn HR10 HK10. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M10' := mm) in * end.
    assert (ST10 : stores_in (zwin (sp - 672 + 520) (sp - 672 + 544)) M10 M10') by (unfold M10'; stin).
    assert (WS10' : WS w (state_blocks c ++ [(q1, 500)]) A10 M10' model10) by (eapply (ws_stores w _ A10 M10 M10' model10 _ WS10 ST10); rewrite Esp; unfold zwin; intros; lia).
    assert (V10 : cell8 SEGS M10' (sp - 672 + 520) q1 /\ cell8 SEGS M10' (sp - 672 + 528) q1 /\ cell8 SEGS M10' (sp - 672 + 536) (q1 + 500)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M10'; rdback]). }
    assert (AG10s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 520) (sp - 672 + 544) a) M10 M10') by (eapply stores_in_agree; [exact ST10 | intros b' Hb'; unfold zwin in *; lia]).
    assert (TI10' : tinit (sp - 672) 0 0 M10') by (eapply (tinit_agree _ _ _ M10 M10' TI10); [lia | lia | eapply agree_on_weaken; [exact AG10s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (C10' : cellw SEGS M10' (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M10 M10'); [exact C10 | lia | cbn; lia | eapply agree_on_weaken; [exact AG10s | unfold zwin; cbn; intros; lia]]).
    assert (SRP10' : state_rep MI A10 M10' (sp - 672 + 48) c).
    { eapply (state_rep_stores w _ A10 M10 M10' model10 _ c _ (sp - 672 + 520) (sp - 672 + 544) WS10 SRP10 ST10); [unfold zwin; intros; lia | rewrite Esp; lia | lia | lia | lia]. }
    assert (VT10 : vtrip (sp - 672) 520 q1 500 M10') by (unfold vtrip; replace (sp - 672 + 520 + 8) with (sp - 672 + 528) by lia; replace (sp - 672 + 520 + 16) with (sp - 672 + 536) by lia; exact V10).
    pose proof (s_ms _ _ _ _ _ WS10') as MS10'. clearbody M10'. clear ST10 TI10 C10 SRP10 V10 MS10 WS10.
    eapply (ws_new w _ A10 M10' model10 fx R10' 100 0x663a4 K WS10');
      [ split; [exact G1_10 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_10' | split; [rewrite (GS10' 3%bv) by (clear; in_regs); exact Qgp10 | rewrite (GS10' 4%bv) by (clear; in_regs); exact Qtp10]]]]]
      | exact G10_10' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS10') | lia | eapply (ws_room2 w _ _ A10 M10' model10 100 WS10' BUD CNT); [unfold Zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]]
      | exact HNM |].
    intros A11 R11 M11 model11 q2 WS11 KEPT11 G10_11 Hq2a Hq2c Hq2al Hq2d Hq2f AG11 AH11. rewrite <- app_assoc in WS11. cbn [app] in WS11.
    assert (Qgp11 : getr R11 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT11 3%bv) by (clear; in_regs); rewrite (GS10' 3%bv) by (clear; in_regs); exact Qgp10).
    assert (Qtp11 : getr R11 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT11 4%bv) by (clear; in_regs); rewrite (GS10' 4%bv) by (clear; in_regs); exact Qtp10).
    keptQ KEPT11 H2_10' H2_11.
    carryG GS10' G8_10 G8_10'. keptQ KEPT11 G8_10' G8_11. carryG GS10' G9_10 G9_10'. keptQ KEPT11 G9_10' G9_11. carryG GS10' G18_10 G18_10'. keptQ KEPT11 G18_10' G18_11. carryG GS10' G24_10 G24_10'. keptQ KEPT11 G24_10' G24_11. carryG GS10' E25_10 E25_10'. keptQ KEPT11 E25_10' E25_11. carryG GS10' E26_10 E26_10'. keptQ KEPT11 E26_10' E26_11. carryG GS10' E27_10 E27_10'. keptQ KEPT11 E27_10' E27_11.
    clear G8_10' G9_10' G18_10' G24_10' E25_10' E26_10' E27_10'.
    assert (TI11 : tinit (sp - 672) 0 0 M11) by (eapply (tinit_agree _ _ _ M10' M11 TI10'); [lia | lia | eapply agree_on_weaken; [exact AG11 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (C11 : cellw SEGS M11 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M10' M11); [exact C10' | lia | cbn; lia | eapply agree_on_weaken; [exact AG11 | rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (SRP11 : state_rep MI A11 M11 (sp - 672 + 48) c).
    { eapply (state_rep_via w _ _ A10 A11 M10' M11 model11 _ c _ SRP10' WS11); [intros b' Hb'; apply in_app_iff; left; exact Hb' | exact AG11 | rewrite Esp; cbn beta; intros; lia | exact AH11 | intros b' Hb'; apply in_app_iff; left; exact Hb' | lia | lia]. }
    assert (W1_11 : vtrip (sp - 672) 520 q1 500 M11) by (eapply (vtrip_agree _ _ _ _ M10' M11 VT10); [lia | lia | eapply agree_on_weaken; [exact AG11 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    clear AG10s AG11 AH11 TI10' C10' SRP10' VT10 MS10'.

    pose (E11 := Eseed R11 [Z_to_bv 64 (sp - 672); Z_to_bv 64 q2]).
    assert (HR11 : regs_ok E11 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R11).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK11 : know_ok SEGS E11 M11 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS11) as FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS11) as MS11.
    xruns HR11 HK11 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R11'.
    rreg HRn (1%bv) G1_11. rreg HRn (2%bv) H2_11'. rreg HRn (10%bv) G10_11'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS11'.
    clear HRn HR11 HK11. fixregsN. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M11' := mm) in * end.
    assert (ST11 : stores_in (zwin (sp - 672 + 544) (sp - 672 + 568)) M11 M11') by (unfold M11'; stin).
    assert (WS11' : WS w (state_blocks c ++ [(q1, 500); (q2, 100)]) A11 M11' model11) by (eapply (ws_stores w _ A11 M11 M11' model11 _ WS11 ST11); rewrite Esp; unfold zwin; intros; lia).
    assert (V11 : cell8 SEGS M11' (sp - 672 + 544) q2 /\ cell8 SEGS M11' (sp - 672 + 552) q2 /\ cell8 SEGS M11' (sp - 672 + 560) (q2 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M11'; rdback]). }
    assert (AG11s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 544) (sp - 672 + 568) a) M11 M11') by (eapply stores_in_agree; [exact ST11 | intros b' Hb'; unfold zwin in *; lia]).
    assert (TI11' : tinit (sp - 672) 0 0 M11') by (eapply (tinit_agree _ _ _ M11 M11' TI11); [lia | lia | eapply agree_on_weaken; [exact AG11s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (C11' : cellw SEGS M11' (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M11 M11'); [exact C11 | lia | cbn; lia | eapply agree_on_weaken; [exact AG11s | unfold zwin; cbn; intros; lia]]).
    assert (SRP11' : state_rep MI A11 M11' (sp - 672 + 48) c).
    { eapply (state_rep_stores w _ A11 M11 M11' model11 _ c _ (sp - 672 + 544) (sp - 672 + 568) WS11 SRP11 ST11); [unfold zwin; intros; lia | rewrite Esp; lia | lia | lia | lia]. }
    assert (W1_11' : vtrip (sp - 672) 520 q1 500 M11') by (eapply (vtrip_agree _ _ _ _ M11 M11' W1_11); [lia | lia | eapply agree_on_weaken; [exact AG11s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT11 : vtrip (sp - 672) 544 q2 100 M11') by (unfold vtrip; replace (sp - 672 + 544 + 8) with (sp - 672 + 552) by lia; replace (sp - 672 + 544 + 16) with (sp - 672 + 560) by lia; exact V11).
    pose proof (s_ms _ _ _ _ _ WS11') as MS11'. clearbody M11'. clear ST11 TI11 C11 SRP11 V11 MS11 WS11 W1_11.
    eapply (ws_new w _ A11 M11' model11 fx R11' 100 0x663bc K WS11');
      [ split; [exact G1_11 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_11' | split; [rewrite (GS11' 3%bv) by (clear; in_regs); exact Qgp11 | rewrite (GS11' 4%bv) by (clear; in_regs); exact Qtp11]]]]]
      | exact G10_11' | lia
      | eapply (roomL_room_for SEGS Ly.L MI); [exact (s_ai _ _ _ _ _ WS11') | lia | eapply (ws_room2 w _ _ A11 M11' model11 100 WS11' BUD CNT); [unfold Zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia]]
      | exact HNM |].
    intros A12 R12 M12 model12 q3 WS12 KEPT12 G10_12 Hq3a Hq3c Hq3al Hq3d Hq3f AG12 AH12. rewrite <- app_assoc in WS12. cbn [app] in WS12.
    assert (Qgp12 : getr R12 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT12 3%bv) by (clear; in_regs); rewrite (GS11' 3%bv) by (clear; in_regs); exact Qgp11).
    assert (Qtp12 : getr R12 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT12 4%bv) by (clear; in_regs); rewrite (GS11' 4%bv) by (clear; in_regs); exact Qtp11).
    keptQ KEPT12 H2_11' H2_12.
    carryG GS11' G8_11 G8_11'. keptQ KEPT12 G8_11' G8_12. carryG GS11' G9_11 G9_11'. keptQ KEPT12 G9_11' G9_12. carryG GS11' G18_11 G18_11'. keptQ KEPT12 G18_11' G18_12. carryG GS11' G24_11 G24_11'. keptQ KEPT12 G24_11' G24_12. carryG GS11' E25_11 E25_11'. keptQ KEPT12 E25_11' E25_12. carryG GS11' E26_11 E26_11'. keptQ KEPT12 E26_11' E26_12. carryG GS11' E27_11 E27_11'. keptQ KEPT12 E27_11' E27_12.
    clear G8_11' G9_11' G18_11' G24_11' E25_11' E26_11' E27_11'.
    assert (TI12 : tinit (sp - 672) 0 0 M12) by (eapply (tinit_agree _ _ _ M11' M12 TI11'); [lia | lia | eapply agree_on_weaken; [exact AG12 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (C12 : cellw SEGS M12 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M11' M12); [exact C11' | lia | cbn; lia | eapply agree_on_weaken; [exact AG12 | rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (SRP12 : state_rep MI A12 M12 (sp - 672 + 48) c).
    { eapply (state_rep_via w _ _ A11 A12 M11' M12 model12 _ c _ SRP11' WS12); [intros b' Hb'; apply in_app_iff; left; exact Hb' | exact AG12 | rewrite Esp; cbn beta; intros; lia | exact AH12 | intros b' Hb'; apply in_app_iff; left; exact Hb' | lia | lia]. }
    assert (W1_12 : vtrip (sp - 672) 520 q1 500 M12) by (eapply (vtrip_agree _ _ _ _ M11' M12 W1_11'); [lia | lia | eapply agree_on_weaken; [exact AG12 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    assert (W2_12 : vtrip (sp - 672) 544 q2 100 M12) by (eapply (vtrip_agree _ _ _ _ M11' M12 VT11); [lia | lia | eapply agree_on_weaken; [exact AG12 | cbn beta; rewrite Esp; unfold zwin; cbn; intros; lia]]).
    clear AG11s AG12 AH12 TI11' C11' SRP11' VT11 MS11' W1_11'.

    pose (E12 := Eseed R12 [Z_to_bv 64 (sp - 672); Z_to_bv 64 q3]).
    assert (HR12 : regs_ok E12 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 48))]) R12).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; try assumption. rewrite w_add by lia. exact G9_12. }
    assert (HK12 : know_ok SEGS E12 M12 [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) 0) (ELit 592)]).
    { pose proof (s_fdef _ _ _ _ _ WS12) as FD. unfold PO_FRAME in FD.
      repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact FD | lia | lia] | lia | lia | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS12) as MS12.
    xruns HR12 HK12 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R12'.
    rreg HRn (1%bv) G1_12. rreg HRn (2%bv) H2_12'. rreg HRn (10%bv) G10_12'. rreg HRn (11%bv) G11_12'. rreg HRn (9%bv) G9_12'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS12'.
    clear HRn HR12 HK12. fixregsN. rewrite ?w_add in G10_12', G11_12', G9_12' |- * by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M12' := mm) in * end.
    assert (ST12 : stores_in (zwin (sp - 672 + 568) (sp - 672 + 592)) M12 M12') by (unfold M12'; stin).
    assert (WS12' : WS w (state_blocks c ++ [(q1, 500); (q2, 100); (q3, 100)]) A12 M12' model12) by (eapply (ws_stores w _ A12 M12 M12' model12 _ WS12 ST12); rewrite Esp; unfold zwin; intros; lia).
    assert (V12 : cell8 SEGS M12' (sp - 672 + 568) q3 /\ cell8 SEGS M12' (sp - 672 + 576) q3 /\ cell8 SEGS M12' (sp - 672 + 584) (q3 + 100)).
    { unfold cell8. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | unfold M12'; rdback]). }
    assert (AG12s : CRep.agree_on (fun a => sp - 672 <= a < sp /\ ~ zwin (sp - 672 + 568) (sp - 672 + 592) a) M12 M12') by (eapply stores_in_agree; [exact ST12 | intros b' Hb'; unfold zwin in *; lia]).
    assert (TI12' : tinit (sp - 672) 0 0 M12') by (eapply (tinit_agree _ _ _ M12 M12' TI12); [lia | lia | eapply agree_on_weaken; [exact AG12s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (C12' : cellw SEGS M12' (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M12 M12'); [exact C12 | lia | cbn; lia | eapply agree_on_weaken; [exact AG12s | unfold zwin; cbn; intros; lia]]).
    assert (SRP12' : state_rep MI A12 M12' (sp - 672 + 48) c).
    { eapply (state_rep_stores w _ A12 M12 M12' model12 _ c _ (sp - 672 + 568) (sp - 672 + 592) WS12 SRP12 ST12); [unfold zwin; intros; lia | rewrite Esp; lia | lia | lia | lia]. }
    assert (W1_12' : vtrip (sp - 672) 520 q1 500 M12') by (eapply (vtrip_agree _ _ _ _ M12 M12' W1_12); [lia | lia | eapply agree_on_weaken; [exact AG12s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (W2_12' : vtrip (sp - 672) 544 q2 100 M12') by (eapply (vtrip_agree _ _ _ _ M12 M12' W2_12); [lia | lia | eapply agree_on_weaken; [exact AG12s | cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (VT12 : vtrip (sp - 672) 568 q3 100 M12') by (unfold vtrip; replace (sp - 672 + 568 + 8) with (sp - 672 + 576) by lia; replace (sp - 672 + 568 + 16) with (sp - 672 + 584) by lia; exact V12).
    pose proof (s_ms _ _ _ _ _ WS12') as MS12'. clearbody M12'. clear ST12 AG12s TI12 C12 SRP12 V12 MS12 WS12 W1_12 W2_12.

    pose proof (ws_X_nodup w _ A12 M12' model12 WS12') as NDX. rewrite map_app in NDX. apply (proj1 (list_relations.list.NoDup_app _ _)) in NDX. destruct NDX as (_ & _ & NDX). cbn [map fst] in NDX.
    pose proof TI12' as TIc. unfold tinit in TIc.
    destruct TIc as (U352 & U360 & U368 & U376 & U384 & U392 & U396 & U400 & U408 & U416 & U424 & U432 & U440 & U448 & U456 & U464 & U472 & U480 & U488 & U496 & U504 & U512).
    pose proof (s_fdef _ _ _ _ _ WS12') as FD12. unfold PO_FRAME in FD12.
    assert (SR2 : state_rep MI A12 M12' (sp - 672 + 352) (mkfresh 0 0 q1 q2 q3)).
    { eapply (st_rep_fresh A12 M12' model12 (sp - 672) 352 0 0 q1 q2 q3 (s_ai _ _ _ _ _ WS12')); try fexact.
      - eapply mdef_sub; [exact FD12 | lia | lia].
      - apply PmSetNumS1.mod16_mod8. replace (sp - 672 + 352) with (sp + (-20) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - lia. - lia.
      - eapply (ws_X_live w _ A12 M12' model12 _ WS12'). rewrite in_app_iff. right. cbn. tauto.
      - eapply (ws_X_live w _ A12 M12' model12 _ WS12'). rewrite in_app_iff. right. cbn. tauto.
      - eapply (ws_X_live w _ A12 M12' model12 _ WS12'). rewrite in_app_iff. right. cbn. tauto. }
    clear U352 U360 U368 U376 U384 U392 U396 U400 U408 U416 U424 U432 U440 U448 U456 U464 U472 U480 U488 U496 U504 U512 TI12' W1_12' W2_12' VT12 FD12 NDX.
    assert (WS12x : WS w (state_blocks c ++ state_blocks (mkfresh 0 0 q1 q2 q3) ++ []) A12 M12' model12).
    { rewrite mkfresh_blocks by lia. rewrite app_nil_r. exact WS12'. }
    eapply (ws_mva w [] A12 M12' model12 fx R12' 0x663d8 (sp - 672 + 48) (sp - 672 + 352) c (mkfresh 0 0 q1 q2 q3) K WS12x);
      [ split; [exact G1_12 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_12' | split; [rewrite (GS12' 3%bv) by (clear; in_regs); exact Qgp12 | rewrite (GS12' 4%bv) by (clear; in_regs); exact Qtp12]]]]]
      | exact G10_12' | exact G11_12' | exact SRP12' | exact SR2 | rewrite Esp; lia | lia | rewrite Esp; lia | lia | unfold apart; lia |].
    intros fx13 A13 R13 M13 model13 WS13 Hcsr KEPT13 Ha0_13 SR1' SR2' AG13. cbn [app] in WS13. rewrite state_moved_mkfresh in SR1'.
    assert (FZ13 : frm_zero (@fp_csr fx13)) by (rewrite Hcsr; exact FZ).
    assert (Qgp13 : getr R13 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT13 3%bv) by (clear; in_regs); rewrite (GS12' 3%bv) by (clear; in_regs); exact Qgp12).
    assert (Qtp13 : getr R13 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT13 4%bv) by (clear; in_regs); rewrite (GS12' 4%bv) by (clear; in_regs); exact Qtp12).
    keptQ KEPT13 H2_12' H2_13.
    carryG GS12' G8_12 G8_12'. keptQ KEPT13 G8_12' G8_13. keptQ KEPT13 G9_12' G9_13. carryG GS12' G18_12 G18_12'. keptQ KEPT13 G18_12' G18_13. carryG GS12' G24_12 G24_12'. keptQ KEPT13 G24_12' G24_13. carryG GS12' E25_12 E25_12'. keptQ KEPT13 E25_12' E25_13. carryG GS12' E26_12 E26_12'. keptQ KEPT13 E26_12' E26_13. carryG GS12' E27_12 E27_12'. keptQ KEPT13 E27_12' E27_13.
    clear G8_12' G9_12' G18_12' G24_12' E25_12' E26_12' E27_12'.
    assert (C13 : cellw SEGS M13 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M12' M13); [exact C12' | lia | cbn; lia | eapply agree_on_weaken; [exact AG13 | rewrite Esp; unfold zwin; cbn; intros; lia]]).
    clear AG13 C12' SRP12' SR2 WS12x WS12' MS12'.

    pose (E13 := Eseed R13 [Z_to_bv 64 (sp - 672)]).
    assert (HR13 : regs_ok E13 (srs sr_id [(2%bv, EVar 32)]) R13).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK13 : know_ok SEGS E13 M13 [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS13) as MS13.
    xruns HR13 HK13 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R13'.
    rreg HRn (1%bv) G1_13. rreg HRn (2%bv) H2_13'. rreg HRn (10%bv) G10_13'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS13'.
    clear HRn HR13 HK13. fixregsN. rewrite w_add in G10_13' by lia.
    assert (WS13x : WS w (state_blocks (state_emptied (mkfresh 0 0 q1 q2 q3)) ++ (state_blocks (mkfresh 0 0 q1 q2 q3) ++ [])) A13 M13 model13).
    { rewrite state_blocks_emptied. exact WS13. }
    eapply (ws_dtor w _ A13 M13 model13 fx13 R13' 0x663e0 (sp - 672 + 352) (state_emptied (mkfresh 0 0 q1 q2 q3)) K WS13x);
      [ split; [exact G1_13 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_13' | split; [rewrite (GS13' 3%bv) by (clear; in_regs); exact Qgp13 | rewrite (GS13' 4%bv) by (clear; in_regs); exact Qtp13]]]]]
      | exact G10_13' | exact SR2' | rewrite Esp; lia | lia |].
    intros A14 R14 M14 model14 WS14 KEPT14 AG14 AH14.
    assert (Qgp14 : getr R14 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT14 3%bv) by (clear; in_regs); rewrite (GS13' 3%bv) by (clear; in_regs); exact Qgp13).
    assert (Qtp14 : getr R14 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT14 4%bv) by (clear; in_regs); rewrite (GS13' 4%bv) by (clear; in_regs); exact Qtp13).
    keptQ KEPT14 H2_13' H2_14.
    carryG GS13' G8_13 G8_13'. keptQ KEPT14 G8_13' G8_14. carryG GS13' G9_13 G9_13'. keptQ KEPT14 G9_13' G9_14. carryG GS13' G18_13 G18_13'. keptQ KEPT14 G18_13' G18_14. carryG GS13' G24_13 G24_13'. keptQ KEPT14 G24_13' G24_14. carryG GS13' E25_13 E25_13'. keptQ KEPT14 E25_13' E25_14. carryG GS13' E26_13 E26_13'. keptQ KEPT14 E26_13' E26_14. carryG GS13' E27_13 E27_13'. keptQ KEPT14 E27_13' E27_14.
    clear G8_13' G9_13' G18_13' G24_13' E25_13' E26_13' E27_13'.
    assert (C14 : cellw SEGS M14 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M13 M14); [exact C13 | lia | cbn; lia | eapply agree_on_weaken; [exact AG14 | rewrite Esp; cbn beta; unfold zwin; cbn; intros; lia]]).
    assert (SR1_14 : state_rep MI A14 M14 (sp - 672 + 48) (mkfresh 0 0 q1 q2 q3)).
    { eapply (state_rep_via w _ _ A13 A14 M13 M14 model14 _ (mkfresh 0 0 q1 q2 q3) _ SR1' WS14); [intros b' Hb'; apply in_app_iff; left; exact Hb' | exact AG14 | rewrite Esp; cbn beta; intros; lia | exact AH14 | intros b' Hb'; apply in_app_iff; left; exact Hb' | lia | lia]. }
    clear AG14 AH14 C13 SR1' SR2' WS13x WS13 MS13.

    pose (E14 := Eseed R14 [Z_to_bv 64 (sp - 672)]).
    assert (HR14 : regs_ok E14 (srs sr_id [(2%bv, EVar 32); (9%bv, EAlu ALU_ADD (EVar 32) (ELit 48))]) R14).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; try assumption. rewrite w_add by lia. exact G9_14. }
    assert (HK14 : know_ok SEGS E14 M14 [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS14) as MS14.
    xruns HR14 HK14 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R14'.
    rreg HRn (1%bv) G1_14. rreg HRn (2%bv) H2_14'. rreg HRn (10%bv) G10_14'. rreg HRn (9%bv) G9_14'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS14'.
    clear HRn HR14 HK14. fixregsN. rewrite w_add in G10_14' by lia. rewrite w_add in G9_14' by lia.
    eapply (ws_dtor w [] A14 M14 model14 fx13 R14' 0x663e8 (sp - 672 + 48) (mkfresh 0 0 q1 q2 q3) K WS14);
      [ split; [exact G1_14 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_14' | split; [rewrite (GS14' 3%bv) by (clear; in_regs); exact Qgp14 | rewrite (GS14' 4%bv) by (clear; in_regs); exact Qtp14]]]]]
      | exact G10_14' | exact SR1_14 | rewrite Esp; lia | lia |].
    intros A15 R15 M15 model15 WS15 KEPT15 AG15 AH15.
    assert (Qgp15 : getr R15 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT15 3%bv) by (clear; in_regs); rewrite (GS14' 3%bv) by (clear; in_regs); exact Qgp14).
    assert (Qtp15 : getr R15 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT15 4%bv) by (clear; in_regs); rewrite (GS14' 4%bv) by (clear; in_regs); exact Qtp14).
    keptQ KEPT15 H2_14' H2_15.
    carryG GS14' G8_14 G8_14'. keptQ KEPT15 G8_14' G8_15. keptQ KEPT15 G9_14' G9_15. carryG GS14' G18_14 G18_14'. keptQ KEPT15 G18_14' G18_15. carryG GS14' G24_14 G24_14'. keptQ KEPT15 G24_14' G24_15. carryG GS14' E25_14 E25_14'. keptQ KEPT15 E25_14' E25_15. carryG GS14' E26_14 E26_14'. keptQ KEPT15 E26_14' E26_15. carryG GS14' E27_14 E27_14'. keptQ KEPT15 E27_14' E27_15.
    clear G8_14' G9_14' G18_14' G24_14' E25_14' E26_14' E27_14'.
    assert (C15 : cellw SEGS M15 (sp - 672 + 336) 8 0) by (eapply (PmBody1S1.cellw_frame M14 M15); [exact C14 | lia | cbn; lia | eapply agree_on_weaken; [exact AG15 | rewrite Esp; cbn beta; unfold zwin; cbn; intros; lia]]).

    eapply (po_epi w K fx13 A15 M15 model15 R15 r POST PW FZ13 WS15 C15 H2_15 Qgp15 Qtp15 G8_15 G18_15 E25_15 E26_15 E27_15).
  Qed.

  Lemma po_tail : forall (w : ww) K (fx : FPState) A8 M8 model8 R8 (p3 p4 p5 p6 p7 p8 : Z),
    let sp := v_sp0 w in let b := v_sp0 w - 672 in let words := v_words w in let n := v_n w in
    POPOST w K -> POW w -> pm_budget SEGS Ly.L MI (v_A0 w) n -> 500 <= NMAX MI ->
    ainv MI (v_A0 w) (v_M0 w) (v_model0 w) ->
    (words <> 0 -> words_ok (live MI (v_A0 w)) sp (v_M0 w) words n) ->
    (forall a, zwin words (words + 4 * n) a -> ~ zwin (sp - PO_STK) sp a) ->
    frm_zero (@fp_csr fx) ->
    WS w [(p3, 500); (p4, 100); (p5, 100); (p6, 500); (p7, 100); (p8, 100)] A8 M8 model8 ->
    state_rep MI A8 M8 (b + 48) (mkfresh 0 0 p3 p4 p5) -> state_rep MI A8 M8 (b + 352) (mkfresh words n p6 p7 p8) ->
    phdr b M8 -> 0 < p3 -> 0 < p4 -> 0 < p5 -> 0 < p6 -> 0 < p7 -> 0 < p8 ->
    getr R8 1%bv = Z_to_bv 64 0x66318 -> getr R8 2%bv = Z_to_bv 64 b -> getr R8 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R8 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R8 10%bv = Z_to_bv 64 (b + 48) -> getr R8 11%bv = Z_to_bv 64 (b + 352) -> getr R8 8%bv = Z_to_bv 64 (b + 304) -> getr R8 9%bv = Z_to_bv 64 (b + 48) ->
    getr R8 24%bv = Z_to_bv 64 0x3f800000 ->
    getr R8 25%bv = getr (v_R0 w) 25%bv -> getr R8 26%bv = getr (v_R0 w) 26%bv -> getr R8 27%bv = getr (v_R0 w) 27%bv ->
    srealizes SEGS (cfg fx R8 (hc_state_mva HConstsS1.hc) M8 model8) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL PO.
    intros w K fx A8 M8 model8 R8 p3 p4 p5 p6 p7 p8. cbn zeta.
    intros POST PW BUD HNM AI0 WOK WWIN FZ WS8 SR1 SR2 PH8 Z3 Z4 Z5 Z6 Z7 Z8 G1_8 H2_8 Qgp8 Qtp8 G10_8 G11_8 G8_8 G9_8 G24_8 E25_8 E26_8 E27_8.
    pose proof ac_bounds_lit as Hcv. pose proof (s_geo _ _ _ _ _ WS8) as (Hsp16 & Gceil & Ghi). unfold PO_STK in *.
    assert (Esp : v_sp w = v_sp0 w - 672) by reflexivity.
    set (sp := v_sp0 w) in *. set (words := v_words w) in *. set (n := v_n w) in *.

    assert (WS8x : WS w (state_blocks (mkfresh 0 0 p3 p4 p5) ++ state_blocks (mkfresh words n p6 p7 p8) ++ []) A8 M8 model8).
    { rewrite !mkfresh_blocks by lia. cbn [app]. exact WS8. }
    eapply (ws_mva w [] A8 M8 model8 fx R8 0x66318 (sp - 672 + 48) (sp - 672 + 352) _ _ K WS8x);
      [ split; [exact G1_8 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_8 | split; [exact Qgp8 | exact Qtp8]]]]]
      | exact G10_8 | exact G11_8 | exact SR1 | exact SR2 | rewrite Esp; lia | lia | rewrite Esp; lia | lia | unfold apart; lia |].
    intros fx9 A9 R9 M9 model9 WS9 Hcsr KEPT9 Ha0_9 SR1' SR2' AG9. cbn [app] in WS9. rewrite state_moved_mkfresh in SR1'.
    assert (FZ9 : frm_zero (@fp_csr fx9)) by (rewrite Hcsr; exact FZ).
    keptQ KEPT9 Qgp8 Qgp9. keptQ KEPT9 Qtp8 Qtp9. keptQ KEPT9 H2_8 H2_9.
    keptQ KEPT9 G8_8 G8_9. keptQ KEPT9 G9_8 G9_9. keptQ KEPT9 G24_8 G24_9. keptQ KEPT9 E25_8 E25_9. keptQ KEPT9 E26_8 E26_9. keptQ KEPT9 E27_8 E27_9.
    assert (PH9 : phdr (sp - 672) M9) by (eapply (phdr_agree _ M8 M9 PH8); [lia | lia | eapply agree_on_weaken; [exact AG9 | rewrite Esp; cbn beta; intros; lia]]).
    clear AG9 WS8x WS8 SR1 SR2 PH8.

    pose (EA := Eseed R9 [Z_to_bv 64 (sp - 672)]).
    assert (HRA : regs_ok EA (srs sr_id [(2%bv, EVar 32)]) R9).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HKA : know_ok SEGS EA M9 [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS9) as MS9.
    xruns HRA HKA 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R9'.
    rreg HRn (1%bv) G1_9. rreg HRn (2%bv) H2_9'. rreg HRn (10%bv) G10_9'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS9'.
    clear HRn HRA HKA. fixregsN. rewrite w_add in G10_9' by lia.
    assert (WS9x : WS w (state_blocks (state_emptied (mkfresh words n p6 p7 p8)) ++ (state_blocks (mkfresh words n p6 p7 p8) ++ [])) A9 M9 model9).
    { rewrite state_blocks_emptied. exact WS9. }
    eapply (ws_dtor w _ A9 M9 model9 fx9 R9' 0x66320 (sp - 672 + 352) (state_emptied (mkfresh words n p6 p7 p8)) K WS9x);
      [ split; [exact G1_9 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_9' | split; [rewrite (GS9' 3%bv) by (clear; in_regs); exact Qgp9 | rewrite (GS9' 4%bv) by (clear; in_regs); exact Qtp9]]]]]
      | exact G10_9' | exact SR2' | rewrite Esp; lia | lia |].
    intros A10 R10 M10 model10 WS10 KEPT10 AG10 AH10.
    assert (Qgp10 : getr R10 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT10 3%bv) by (clear; in_regs); rewrite (GS9' 3%bv) by (clear; in_regs); exact Qgp9).
    assert (Qtp10 : getr R10 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT10 4%bv) by (clear; in_regs); rewrite (GS9' 4%bv) by (clear; in_regs); exact Qtp9).
    keptQ KEPT10 H2_9' H2_10.
    carryG GS9' G8_9 G8_9'. keptQ KEPT10 G8_9' G8_10. carryG GS9' G9_9 G9_9'. keptQ KEPT10 G9_9' G9_10. carryG GS9' G24_9 G24_9'. keptQ KEPT10 G24_9' G24_10. carryG GS9' E25_9 E25_9'. keptQ KEPT10 E25_9' E25_10. carryG GS9' E26_9 E26_9'. keptQ KEPT10 E26_9' E26_10. carryG GS9' E27_9 E27_9'. keptQ KEPT10 E27_9' E27_10.
    assert (PH10 : phdr (sp - 672) M10) by (eapply (phdr_agree _ M9 M10 PH9); [lia | lia | eapply agree_on_weaken; [exact AG10 | rewrite Esp; cbn beta; intros; lia]]).
    assert (SR1_10 : state_rep MI A10 M10 (sp - 672 + 48) (mkfresh words n p6 p7 p8)).
    { eapply (state_rep_via w _ _ A9 A10 M9 M10 model10 _ (mkfresh words n p6 p7 p8) _ SR1' WS10); [intros b' Hb'; apply in_app_iff; left; exact Hb' | exact AG10 | rewrite Esp; cbn beta; intros; lia | exact AH10 | intros b' Hb'; apply in_app_iff; left; exact Hb' | lia | lia]. }
    clear AG10 AH10 PH9 SR1' SR2' WS9x WS9 MS9 G8_9' G9_9' G24_9' E25_9' E26_9' E27_9'.
    rewrite app_nil_r in WS10.

    pose (EB := Eseed R10 [Z_to_bv 64 (sp - 672)]).
    assert (HRB : regs_ok EB (srs sr_id [(2%bv, EVar 32)]) R10).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HKB : know_ok SEGS EB M10 [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (s_ms _ _ _ _ _ WS10) as MS10.
    xruns HRB HKB 100%nat WSTOPS (SCR [] [] []) 60%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R10'.
    rreg HRn (1%bv) G1_10. rreg HRn (2%bv) H2_10'. rreg HRn (10%bv) G10_10'.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 24; 25; 26; 27]%bv HRn eq_refl) as GS10'.
    clear HRn HRB HKB. fixregsN.
    eapply (ws_pm w A10 M10 model10 fx9 R10' 0x66328 {| pc_cons := sp - 672 + 304; pc_user := 0; pc_state := mkfresh words n p6 p7 p8 |} K);
      [ cbn [pc_state]; exact WS10
      | split; [exact G1_10 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [rewrite Esp; exact H2_10' | split; [rewrite (GS10' 3%bv) by (clear; in_regs); exact Qgp10 | rewrite (GS10' 4%bv) by (clear; in_regs); exact Qtp10]]]]]
      | exact FZ9 | rewrite Esp; exact G10_10'
      | rewrite Esp; exact (parser_rep_mk w _ A10 M10 model10 (mkfresh words n p6 p7 p8) WS10 PH10 SR1_10)
      | cbn [pc_cons]; rewrite Esp; reflexivity
      | cbn [pc_state]; apply fresh_mkfresh; lia
      | intros Hw; exact (ws_words_ok w _ A10 M10 model10 WS10 AI0 WWIN (WOK Hw))
      | exact WWIN | exact BUD |].
    intros fx11 A11 R11 M11 model11 c' r WS11 FZ11 KEPT11 Hr PR11 Hcons11 Hw11 Hn11 CNT11 AG11. cbn [pc_cons] in Hcons11.
    assert (Qgp11 : getr R11 3%bv = Z_to_bv 64 (ly_gp Ly.L)) by (rewrite (KEPT11 3%bv) by (clear; in_regs); rewrite (GS10' 3%bv) by (clear; in_regs); exact Qgp10).
    assert (Qtp11 : getr R11 4%bv = Z_to_bv 64 (ly_tp Ly.L)) by (rewrite (KEPT11 4%bv) by (clear; in_regs); rewrite (GS10' 4%bv) by (clear; in_regs); exact Qtp10).
    keptQ KEPT11 H2_10' H2_11.
    carryG GS10' G8_10 G8_10'. keptQ KEPT11 G8_10' G8_11. carryG GS10' G9_10 G9_10'. keptQ KEPT11 G9_10' G9_11. carryG GS10' G24_10 G24_10'. keptQ KEPT11 G24_10' G24_11. carryG GS10' E25_10 E25_10'. keptQ KEPT11 E25_10' E25_11. carryG GS10' E26_10 E26_10'. keptQ KEPT11 E26_10' E26_11. carryG GS10' E27_10 E27_10'. keptQ KEPT11 E27_10' E27_11.
    assert (C11 : cellw SEGS M11 (sp - 672 + 336) 8 0).
    { split; [cbn; lia|]. pose proof (pr_consf _ _ _ _ _ _ _ PR11) as F. rewrite Hcons11 in F. unfold CRep.fld in F.
      replace (sp - 672 + 304 + 32) with (sp - 672 + 336) in F by lia. exact F. }
    pose proof (pr_state _ _ _ _ _ _ _ PR11) as SRc. rewrite Esp in SRc. unfold ST_OFF in SRc.
    eapply (po_tail2 w K fx11 A11 M11 model11 R11 (pc_state c') r POST PW BUD HNM FZ11 WS11 SRc C11 CNT11 H2_11 Qgp11 Qtp11 G8_11 G9_11 Hr G24_11 E25_11 E26_11 E27_11).
  Qed.
End PM.

Ltac fixregs2 := fixregs;
  try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).
Ltac fixregs3 := fixregs2;
  try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity).
Ltac in_regs := apply PmStepS1.in_reg_list; reflexivity.
Ltac fixregsN :=
  try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 5)) with (5%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 6)) with (6%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 7)) with (7%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 14)) with (14%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 15)) with (15%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 16)) with (16%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 17)) with (17%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 19)) with (19%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 20)) with (20%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 28)) with (28%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 29)) with (29%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 30)) with (30%bv : reg) in * by (apply bv_eq; reflexivity);
  try replace (Z_to_bv 5 (Z.of_N 31)) with (31%bv : reg) in * by (apply bv_eq; reflexivity).
Ltac sc_rdw H := eapply (PmCoreS1.sc_read_w _ _ _ _ _ _ H); [evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia] | evs; reflexivity].
Ltac carryG GS G Q := lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (GS r) in Q by (clear; in_regs) end.
