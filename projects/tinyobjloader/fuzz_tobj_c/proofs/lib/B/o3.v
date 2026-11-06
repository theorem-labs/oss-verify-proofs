(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push3 o1 nz DrvIfaceR.

(* [comment removed for export] *)
Module Lib_opt_push3_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push3"; "s_vr"; "E_2d"; "E_2v"; "E_vrL"; "Xk_op"; "pK"; "xf_vback"; "bd_op"; "pD"; "R_2d"; "R_2v"; "R_vrL"; "xf_vcall"; "T_fail2d0"; "T_fail2v0"; "T_failL0"; "T_grown2d0"; "T_grown2v0"; "T_grownL0"; "T_keep2d0"; "T_keep2v0"; "T_keepL0"; "vKg2d"; "vKg2v"; "vKgL"; "E_2d0"; "E_2v0"; "E_vrL0"; "FUEL_op"; "T_fail2d"; "T_fail2v"; "T_failL"; "T_grown2d"; "T_grown2v"; "T_grownL"; "T_keep2d"; "T_keep2v"; "T_keepL"; "cutpcs_all"; "cutsO"; "exitsO"; "vDg2d"; "vDg2v"; "vDgL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "tv_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.

Lemma ejcertO_ok : ltac2:(tb__ "0|0|
S0S3dS48S46S47S1eS28P64S29S2aA7S3eA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_vrL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1dSeA2S3aS1S5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1cSeA2S3aS1S4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1bSeA2S3aS1S3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS30S6A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS31S6A6S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS2fS6A6S14A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS30S6A6S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS31S6A6S10A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS2fS6A6S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS30S6A6S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS31S6A6SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS2fS6A6S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S17S8A2S3aS1S27A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S11S8A2S3aS1S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S14S8A2S3aS1S24A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S16S8A2S3aS1S26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S10S8A2S3aS1S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S13S8A2S3aS1S23A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S15S8A2S3aS1S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40SfS8A2S3aS1S1fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S12S8A2S3aS1S22A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma imp_keepL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS30S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keepL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS30S5A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_failL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS31S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS2fS5A4S35A2S41S2dS1aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS2fS5A4S32S34S37A2A2S9S1aA1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS30S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS30S4A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS31S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS2fS4A4S35A2S41S2cS19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS2fS4A4S32S34S37A2A2S9S19A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS30S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS30S3A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS31S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS2fS3A4S35A2S41S2bS18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS2fS3A4S32S34S37A2A2S9S18A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_opt_push3_eqs.

(* [comment removed for export] *)
Module Lib_opt_push3_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SPUle"; "SLit"; "ss_facts"; "sprop_eqb"; "ss_next"; "holds"; "sobj"; "SVar"; "rw"; "SMd"; "SAlu"; "SPBranch"; "sprop_below"; "DUnknown"; "SPNot"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "bool"; "true"; "cons"; "nil"; "app"; "Some"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "emeasA"; "PTrue"; "JA_pre"; "nd_below"; "JA"; "JLA"; "ND"; "nodeIA"; "ok_frameKA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bd_subst"; "bitem"; "bud_le"; "BXok_d"; "bd_wpos"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push3"; "pK"; "ndC"; "pC"; "VB"; "nd0"; "pCM"; "CM"; "pD"; "s_vr"; "vDEF"; "vVALS"; "bd_op"; "vVIDX"; "C_L"; "E_2d0"; "E_2v0"; "E_vrL0"; "Pre_op"; "X_back0"; "X_back1"; "inL_at"; "vALo"; "z0"; "O_deflt"; "O_vals"; "PD_op"; "PD_vrN"; "P_op0"; "P_op1"; "X_Lin0"; "X_Lin1"; "Xk_op"; "cutsO"; "dnzB"; "exitsO"; "nd0'"; "nd1"; "slot4_at"; "tv0"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "add"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_opt_push3_pf"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "B32"; "vC"; "vK"; "spm"; "vV"; "Pre_vr"; "nd0"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "tv_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_opt_push3_pf.Sum"; "Posts_op"; "baseOF"; "JLo"; "baseOz"; "base_factsO"; "is_siteobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "wsub_id_below"; "sv_subst"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "M_DIVU"; "ALU_ADD"; "BC_GEU"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb";
"tvz"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "PostsC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_opt_push3_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.
Local Open Scope lazy_bool_scope.

Definition P0_op (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S82VFF;S37Q40M0S14Vr;PcA2A2Z20A3S1S82VFF;S37G0S14Vr;P24A2A2Z30A3S1S82VFF;S37G0S14Vr;P21A2A2S6dZ4S48A2M1A3S82VFF;S37G0S14Vr;P22A2A2G1A3A2A2A2").

Lemma uval_divu_lit : ltac2:(tb__ "0|0|
SbSaS4S1S6fZ0R1A2S6fR1S6eZ2Z40A2A2A2S0S4S3bR4S15S9cR3SdR2A1A3A2S72S3bR4R3A2R2A2A3F_;Fc;Fa;Frho;").
Proof.
  intros rho a c Hc. unfold uval. cbn [eval]. unfold mul_div.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  destruct (Z.eqb_spec c 0) as [E|E]; [lia|]. rewrite bv_divu_unsigned. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma VB_val : ltac2:(tb__ "0|0|
SbSaS4S6cS3bR3R2A2S7aA2S1S6cZ0R2A2S6fR2Z40A2A2S0S4S3bR5S45R4R3A2A2S70S6dZ20S71S70S6eZ2Z2fA2Z1000A2S3bR5R4A2A2A2R3A2A3F_;F_;Fph;Fc;Frho;").
Proof.
  intros rho c ph Hc Hph. unfold VB, two47, RA.two47, Lib_scan_double.two47, B32 in *. pose proof (uval_range rho c) as Rc.
  assert (ES : uval rho (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c) = 2 ^ 47 + 4096 - uval rho c).
  { unfold uval in *. rewrite U_sub, U_lit. unfold M64v. rewrite (Z.mod_small (2 ^ 47 + 4096)) by lia. apply Z.mod_small. lia. }
  assert (EM : uval rho (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c)) = 32 * (2 ^ 47 + 4096 - uval rho c)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  rewrite uval_add_small by (rewrite EM, uval_lit by lia; lia). rewrite EM, uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb6SbS22S36Q40A1A1S8aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb0S2bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S4Sb1VCST;R1A2S1S6cZ0R2A2S6fR2SacA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S4Sb1VXGL;R1A2S1S6cZ0R2A2S6fR2SacA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S22S21S21S4S4A2S4A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JLo (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;VKc;S79VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Aa").
Definition Posts_op : list (axst * jpostA) := ltac2:(tb__ "0|1|
S25S21S5S74A2M0S20S5S74S5eS8fS66A1A4S25G0S20S5S74S5dS8fS65A1A4S26G0A1A3A3").
Lemma Posts_op_PD : ltac2:(tb__ "0|0|
S0S22S21S5S74A2A1S8dSa8VAInv;VCST;VXGL;VKc;S79S2eS5bVFB;VFF;VBX;AaA3").
Proof. reflexivity. Qed.

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VCST;VXGL;S73VKc;Vrho0;S79VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S21S5S2cA2Sa4Fn;") := ltac2:(tb__ "0|0|
S34VAInv;VCST;VXGL;S73VKc;Vrho0;S79VFB;VFF;A2VFB;VFF;VBX;S2eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S75S2bS73Vrho0;Vtp0;S8dA5").

Definition base_factsO : list sprop := ltac2:(tb__ "0|5|
S25S9ScS13PaA1M0SdS81A1M1A2S25S9ScS13P1eA1M2S7dZ80A1A2S25S9ScSdZ1000A1M3S4cA2S25S9ScS16S9dS4cSdS6dZ4S48A2A1M4A3G2A2S25S9ScS4cG1A2S25S9ScG3S4bA2S25S9ScS16S9dS4bG4A3G2A2S25S9ScS4bG1A2S25S9ScS4eSdS6eZ2Z1bA2A1A2S25S9ScG2G0A2S25S9ScSdZ7fff7f800000A1G2A2S25S9ScG2SdZ7fffff800000A1A2S26S9A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseOF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S6bS9S9S69S9SfR1A1VF;A3Lp;S91A3").
Record baseOz (rho : valuation) : Prop := BZO {
  bz_sp : aceil + 128 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_vals : 4096 <= uval rho vVALS /\ uval rho vVALS + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_def : 4096 <= uval rho vDEF /\ uval rho vDEF + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_vidx : uval rho vVIDX <= 2 ^ 27;

  bz_top : bv_unsigned (rw rho V_TOP) + 128 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
SbS4S1S6cZ0R1A2S6cR1S3bR2S13PaA1M0A2A2A2S0S4S3bR3S7dR2A1A2S71S3bR3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma baseOz_of : ltac2:(tb__ "0|0|
SbS22S9A1S88S9S11R2A1R1A3S0S23S8eR2A1S24A3S90R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseOF in HB.
  assert (G : forall p, In p base_factsO -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_factsO] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  unfold two47, RA.two47, Lib_scan_double.two47, CM in *. rewrite !uval_lit in F1, F3, F5, F6, F8, F9, F11, F12 by lia.
  pose proof (uval_range rho vVALS). pose proof (uval_range rho vDEF).
  rewrite uval_add_small in F4 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F4 by lia.
  rewrite uval_add_small in F7 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F7 by lia.
  rewrite uval_spm in F2 by lia.
  constructor; rewrite ?aceil_val; unfold CM; lia.
Qed.

Lemma P0o_now : ltac2:(tb__ "0|1|
SbSa1S73Vrho0;R1A3S79VFB;VFF;Vrho0;A3S1S82VFF;S3bR3S7eA2Z20A3S1S82VFF;S3bR3S57A2Z30A3S1S82VFF;S3bR3S4cA2S6dZ4S48A2M0A3S82VFF;S3bR3S4bA2G0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D). unfold uval, vV, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.vV, vALo, vVALS, vDEF. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 36%positive eq_refl), <- (proj1 Hav 33%positive eq_refl), <- (proj1 Hav 34%positive eq_refl).
  auto.
Qed.

Lemma tvz_kd : ltac2:(tb__ "0|1|
SbSaSaSa6R3S8cR2R1A2A2S6cS3bR4R2A2S7aA2S2S0S4S3bR5R3A2Z0M0A3A1S2S0S4S3bR6R5A2G0A3A1F_;F_;F_;Fk;Fd;Frho;").
Proof.
  intros rho d k HZ HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho 4 k ltac:(lia) ltac:(unfold uval; lia)) as E4. unfold uval, kb4 in E4. unfold kb4 in HZ. rewrite E4 in HZ. lia.
Qed.

Definition is_siteobj (o : sobj) : Prop := ltac2:(tb__ "0|0|
S3S1S0SaS1bVo;A1S13PaA1A3S1S0SaS1eVo;A1SdN80A1A3S1S0SaS1dVo;A1SdZ0A1A3S0S1fS1cVo;A1S19A3A2A2A2S3S0S12Vo;S5aA3S0S12Vo;S59A3A2A2").
Lemma HIN_site : ltac2:(tb__ "0|2|
S5S22S12A1SbS99S12S6aS12R1R4A3S92R2A1F_;Fo;S0SaS95S4aR5A1P11A2S42A3S0SaS95S4aR6A1PfA2S49A3S0SaS95S4aR7A1PcA2S7eA3S0SaS95S4aR8A1PeA2S57A3S0S23S69S9SfScS42SdS7aA1A2A1SeS6R9A1A1A3S24A3S0S23S8eSeS6RaA1A1A1S24A3S88S9S11R9A1SeS6RbA1A1A3S79VFB;VFF;Vrho0;A3Sa1S73Vrho0;RbA3Sa6RcS8cS49S42A2A2S1SaaVCST;Vrho0;VFB;VFF;RdS26S21SaSaA2A1M0S26S21S21SaS4A2SaA2A1M1ReA8S1SabVCST;VXGL;Vrho0;VFB;VFF;RdG0G1S61A9Sa0Sa7VFB;RdG0A3Sa9VFF;RdG1A3S94S93RdReRcA3S4aRfA1A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR H17 H15 H12 H14 HK HB HF HP0 Hav HZ. destruct (P0o_now rho Hav HP0) as (HV & HA & HS & HD).
  pose proof (baseOz_of rho _ HF HB) as [Bsp Bv Bd _ Btop]. rewrite aceil_val in *. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. destruct (HR o Ho) as [(H1 & H2 & H3 & H4)|[->| ->]].
    + left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst. apply range_lit' in Hr; [|lia|lia]. lia.
    + unfold O_vals in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HS | unfold CM in *; lia].
    + unfold O_deflt in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HD | unfold CM in *; lia].
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; rewrite uval_lit in Ha by (unfold CM; lia); left.
    + eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HS | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HD | lia].
  - unfold P0_vr. rewrite !rw_call'. rewrite H17, H15, H12, H14.
    split; [|split].
    + intros Hk. pose proof (holds_mem _ _ _ HF HK) as HKB. rewrite h_ule in HKB. unfold B32 in HKB. rewrite uval_lit in HKB by lia. exact (tvz_kd rho pD pK HZ HKB Hk).
    + destruct HV as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma slot4_holds : ltac2:(tb__ "0|1|
SbS22S9A1SaS88S9S11R3A1R2A3S0S23S69S9SfScS47R2A2A1R3A3S24A3S0S23S69S9SfScR3SdS7aA1M0A2A1R4A3S24A3S0S23S69S9SfScS44S42A2A1R5A3S24A3S0S23S69S9SfScS42G0A2A1R6A3S24A3S11R8S67R6A1A2F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H4. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4. rewrite h_ule in F1, F2, F3, F4.
  unfold B32 in F2, F4. rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. unfold pCM in F1. pose proof (uval_range rho pC) as RC. unfold CM in *.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  unfold slot4_at. apply (proj2 (h_ule _ _ _)).
  assert (E1 : uval rho (SMd M_MUL pC (SLit 4)) = uval rho pC * 4) by (rewrite uval_mul_comm; rewrite uval_mul_lit by lia; lia).
  assert (E2 : uval rho (kb4 k) = 4 * uval rho k) by (unfold kb4; rewrite uval_mul_lit by lia; lia).
  unfold CM. rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia). rewrite E1, E2, uval_lit by lia. lia.
Qed.

Lemma dnz_keep : ltac2:(tb__ "0|0|
SbS22S36Q40A1A1S22S8bA1S8aS22S3dA1S22S9A1VJAv;S33S8cS49S42A2S26S21S21SaS4A2SaA2A1R2A3R6R5R4R3A5S88S9S11R7A1R2A3S0S23S69S9SfScS47S42A2A1R3A3S24A3S0S23S69S9SfScS42SdS7aA1A2A1R4A3S24A3S0S23S69S9SfScS44S42A2A1R5A3S24A3S11RbS63A2F_;F_;F_;F_;F_;FF;Fbd;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md bd F HJ HF H1 H2 H3.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. rewrite h_ule in F1, F2, F3.
  unfold B32 in F2. rewrite uval_lit in F2 by lia. unfold pCM in F1. pose proof (uval_range rho pC) as RC. unfold CM in *.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (TNZ : tnz rho (pD, kb4 pK)).
  { destruct HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ') & _). unfold tnz. cbn [fst]. apply (tvz_kd rho pD pK HZ'); unfold B32; lia. }
  pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue ALA _ _ _ _ _ (pD, kb4 pK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
  apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, dnzB. cbn [fst snd]. do 3 right. left. reflexivity.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
SbOF_;S22S9A1S22S3dA1S0S23S40R1A1S24A3Sb5S73Vrho0;R4R3SdZ0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia. split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S4S22S36Q40A1A1S83F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S39S5SbS22S36Q40A1A1S83S88S9S11R3A1SeS6R4A1A1A3VTR;S38S2bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S83S83S83S86R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S39S39S5S5S96S22S12A1M0S22S21S5S74A2M1A1S22S21SaSaA2M2A1S83SbS22S36Q40A1A1M3G2S6aG2R1R5A3S6aG2R2S8RbA1A3F_;Fr;S0S2aG0A1S78RaR9R8A3S28G0R7A2A3S0S23S77RbRaR9R8S89G1S5S29S5S74A2R7A4A5S24A3SbG3VTR;S38S2bRfRdR2R1A5S75S2bS10S6RdA1A1R2R1RaA5A2Ftp1;Frho1;S22S8bA1M4S99S8aS3aS2bR9R8R10S20G4S9aR3S9bR2R1A2A4A5R13RaR9R4R2A4R13S94S93RbRfS87R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5S74G4S99S8aSbG3G4S99S8aS6aG1S20S5S74RaR9A4R14A3S3aS2bR12R11R19S20G4S9aR9S9bR8R7A2A4A5R1cR13R12RaR8A4Sa1S10S6R1aA1A1S94S93R14R18S87R9R13RaA3A3R19A2R8A3S3aS2bR9R8ReS20G4S9aR7S9bR6R5A2A4A5ReS94S93R16R1aS87RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sb3R17S87RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSa2R18S87RdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S38S2bS76R11S94S93R19R1dS87ReR18RfA3A3R1eA2R18RdRcA5Sb4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S38S2bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRES : ltac2:(tb__ "0|1|
S22S21S4S4A2M0A1S22S21G0S4A2A1S41SbS22S36Q40A1A1S3fZ3R3A2VTR;S38S2bS2fVAInv;VCST;VXGL;VKc;Sa0R6R5A2R6R5R4S2eS80AaS7fR3R2A5S75S2bS73R3R2Sa8VAInv;VCST;VXGL;VKc;Sa0S2eS5cR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S2cS21S4SaA2M0SbS22S36Q40A1A1M1S4G1S6aS21S21S5S2cA2M2G0A2S20G2G0S20S5S2cR7R6A4R5A4S62A3S1S6cZ0S2dS20G2G0S20S5S2cR8R7A4R6A4R5A2M3A2S6fG3R3A2A2VTR;S38S2bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S2cSbS22S36Q40A1A1M0S4G0S6aS21S5S74A2S20S5S74R6S8fR5A1A4S8dA3VTR;S38S2bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Tactic Notation "innth" integer(n) := cbn [In cutsO exitsO Posts_op PD_op]; do n right; left; reflexivity.

Lemma meas_VB : ltac2:(tb__ "0|2|
S5S2cS4SaS4SbS6cS3bR1R3A2S7aA2S1S6cZ0R3A2S6fR3Z40M0A2A2S0S4S2dS20S21S5S2cA2S21S4SaA2S20S5S2cR8R7A4S20S4SaR6S45R5R4A2A4A4R3A2S70S6dR6S6eZ2M1G0A2A2S70S6dZ20S71S70S6eG1Z2fA2Z1000A2S3bR3R5A2A2A2R4A2A2A3F_;F_;Frho;Fph;Fc;Frk;Fnd;FT;").
Proof. intros T nd rk c ph rho Hc Hph. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (VB c ph))) with (uval rho (VB c ph)). rewrite (VB_val rho c ph Hc Hph). unfold two47, RA.two47, Lib_scan_double.two47. reflexivity. Qed.

Lemma meas_lit : ltac2:(tb__ "0|1|
S5S2cS4S4SbS1S6cZ0R2A2S6fR2S6eZ2Z40A2M0A2A2S0S4S2dS20S21S5S2cA2S21S4SaA2S20S5S2cR6R5A4S20S4SaR4SdR3A1A4A4R2A2S70S6dR4G0A2R3A2A3F_;Frho;Fz;Frk;Fnd;FT;").
Proof. intros T nd rk z rho Hz. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (SLit z))) with (uval rho (SLit z)). rewrite uval_lit by lia. reflexivity. Qed.

Ltac meas0 := unfold z0; rewrite meas_lit by lia; lia.

Lemma X_E_L : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0G0VTR;S38S2bVJAv;S43A1S52R3R2A5VFAM;S2dS20S21S5S2cA2S21S4SaA2S20S5S2cS52S43A4S20S4SaZ32S45S44Z13A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_vrL rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vrL0 E_vrL tp w E_vrL_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vrL (s_vr E_vrL) R_vrL Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_vrL0, ndC, (50, VB pC 19)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_vrL R_vrL rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keepL0_eq, imp_keepL_tv, imp_keepL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_keepL)); [innth 2 | assert (ES : sv_subst s_keepL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_keepL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_keepL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keepL0 T_keepL tp' w T_keepL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keepLs TA_Ls s_keepL (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keepLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keepL ([slot4_at pK; dnzB] ++ ss_facts (ax_S T_keepL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. constructor; [apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity|]. constructor; [|constructor].
      exact (dnz_keep rho' tp' tr md _ _ HJ HF2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    +   rewrite T_failL0_eq, imp_failL_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_L ndF (45, z0) (rho_sub rho' s_failL)); [innth 3 | unfold z0; rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite meas_lit by lia; pose proof (uval_range rho pC); unfold B32 in *; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_failL0 T_failL tp' w T_failL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_failL TF_L s_failL (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grownL0_eq, imp_grownL_tv, imp_grownL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_grownL)); [innth 2 | assert (ES : sv_subst s_grownL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_grownL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_grownL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grownL0 T_grownL tp' w T_grownL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grownLs TA_Ls s_grownL (ND (tv_vec vDgL vKgL) [] (bd_op vKgL)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grownLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grownL ([slot4_at vKgL] ++ ss_facts (ax_S T_grownL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKgL HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2v : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0G0VTR;S38S2bVJAv;S43A1S51R3R2A5VFAM;S2dS20S21S5S2cA2S21S4SaA2S20S5S2cS51S43A4S20S4SaZ23S58A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2v rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2v0 E_2v tp w E_2v_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2v (s_vr E_2v) R_2v Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2v0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2v R_2v rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2v0_eq, imp_keep2v_tv, imp_keep2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2v0 T_keep2v tp' w T_keep2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2vs (TA_2s vVALS) s_keep2v (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2v ([slot4_at pK; dnzB] ++ ss_facts (ax_S T_keep2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. constructor; [apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity|]. constructor; [|constructor].
      exact (dnz_keep rho' tp' tr md _ _ HJ HF2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    +   rewrite T_fail2v0_eq, imp_fail2v_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2v)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2v0 T_fail2v tp' w T_fail2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2v TF_2 s_fail2v (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2v0_eq, imp_grown2v_tv, imp_grown2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2v0 T_grown2v tp' w T_grown2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2vs (TA_2s vVALS) s_grown2v (ND (tv_vec vDg2v vKg2v) [] (bd_op vKg2v)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2v ([slot4_at vKg2v] ++ ss_facts (ax_S T_grown2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2v HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2d : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0G0VTR;S38S2bVJAv;S43A1S50R3R2A5VFAM;S2dS20S21S5S2cA2S21S4SaA2S20S5S2cS50S43A4S20S4SaZ23S58A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2d rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2d0 E_2d tp w E_2d_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2d (s_vr E_2d) R_2d Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2d0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2d R_2d rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2d0_eq, imp_keep2d_tv, imp_keep2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2d0 T_keep2d tp' w T_keep2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2ds (TA_2s vDEF) s_keep2d (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2d ([slot4_at pK; dnzB] ++ ss_facts (ax_S T_keep2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. constructor; [apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity|]. constructor; [|constructor].
      exact (dnz_keep rho' tp' tr md _ _ HJ HF2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    +   rewrite T_fail2d0_eq, imp_fail2d_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2d)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2d0 T_fail2d tp' w T_fail2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2d TF_2 s_fail2d (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2d0_eq, imp_grown2d_tv, imp_grown2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2d0 T_grown2d tp' w T_grown2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2ds (TA_2s vDEF) s_grown2d (ND (tv_vec vDg2d vKg2d) [] (bd_op vKg2d)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2d ([slot4_at vKg2d] ++ ss_facts (ax_S T_grown2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2d HF2); vm_compute; reflexivity.
Qed.

Lemma X_Lin : ltac2:(tb__ "0|3|
S5S5S96SbS22S36Q40A1A1M0S4G0S0S5Sa3S25S9S56S7bA1S26S9A1A3M1R7A2R6A3S0S23S69S9SfS1aS17S9eS15S9cS7bSdS48A1A3S4eA3A1A1SeS6R8A1A1A3S24A3S0S23S69S9SfScS7bS7cA2A1SeS6R9A1A1A3S24A3S0S23S69S9SfScS7cSdS7aA1A2A1SeS6RaA1A1A3S24A3S0S23S8eSeS6RbA1A1A1S24A3S0S23S6bS9S18S10S6RcA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S23S7RcS4fRbA3S24A3S0S23S97RcS73A2S24A3S0S23Sb2S73S10S6ReA1A1A2S24A3S0S23S30S10S6RfA1A1S46A2S24A3S0S23Sa5RfS68S8cS49S42A2A3S24A3S0S23S3eSeS6R11A1A1S3cR10S4dS42A1A2S4dS7cA1A3S24A3S6cS6dZ33S6eZ2Z40A2A2ReA2VTR;S38S2bVJAv;S46A1R14R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HB Hfb He Hid Hnf Hnb Htv Hle Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_nbgeu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU vC (SLit CM)))) with (uval rho (SMd M_DIVU vC (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. rewrite h_ule in H2, H3. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  assert (HIN : holds rho (inL_at vC)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho vC) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s nd0 ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at vC] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (U_range (eval (rho_sub rho s) (VB pC 20))). unfold M64v in *. lia.
Qed.
Lemma X_X_Lin0 : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0S4G0S6cS6dZ33S6eZ2Z40A2A2R2A2VTR;S38S2bVJAv;S46A1S5fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin0 X_Lin0f s_Lin0); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.
Lemma X_X_Lin1 : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0S4G0S6cS6dZ33S6eZ2Z40A2A2R2A2VTR;S38S2bVJAv;S46A1S60R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin1 X_Lin1f s_Lin1); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.

Lemma X_back : ltac2:(tb__ "0|5|
S5S5S96SbS22S36Q40A1A1M0S4G0S0S5Sa3S25S9S56S47A1S26S9A1A3M1R7A2R6A3S0S23S69S9SfS17S9fS15S9cS47SdS48A1A3S4eA3A1SeS6R8A1A1A3S24A3S0S23S69S9SfScS47S42A2A1SeS6R9A1A1A3S24A3S0S23S69S9SfScS42SdS7aA1A2A1SeS6RaA1A1A3S24A3S0S23S69S9SfScS44S42A2A1SeS6RbA1A1A3S24A3S0S23S8eSeS6RcA1A1A1S24A3S0S23S6bS9S18S10S6RdA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S23S7RdS4fRcA3S24A3S0S23S97RdS73A2S24A3S0S23Sb2S73S10S6RfA1A1A2S24A3S0S23S30S10S6R10A1A1S43A2S24A3S0S23Sa5R10S8cS49S42A2M3G3A3S24A3S0S23S3eSeS6R12A1A1S3cR11S4dS42A1M4A2G4A3S24A3S0SaS98R12S44A2S47A3S6cS2dS20S21S5S2cA2S21S4SaA2S20S5S2cR15S43A4S20S4SaZ32S45S44Z0A2A4A4R12A2R10A2VTR;S38S2bVJAv;S43A1R16R13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HCK0 HB Hfb He Hid Hnf Hnb Htv Hle Hs Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_bltu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU pCM (SLit CM)))) with (uval rho (SMd M_DIVU pCM (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. pose proof (holds_mem _ _ _ HF HCK0) as H4.
  rewrite h_ule in H2, H3, H4. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  pose proof (uval_range rho pC) as RC.
  assert (ECM : uval rho pCM = uval rho pC + CM).
  { unfold pCM, CM in *. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
  assert (HIN : holds rho (inL_at pCM)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho pCM) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s ndC ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at pCM] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - rewrite (meas_VB X ndC 50 pC 0 rho) in Hb by (unfold B32 in *; lia).
    assert (EC : uval (rho_sub rho s) pC = uval rho pCM).
    { unfold uval. rewrite <- eval_subst, Hs. reflexivity. }
    rewrite (meas_VB C_L ndC 50 pC 20 (rho_sub rho s)) by (rewrite ?EC; unfold B32 in *; lia). rewrite EC, ECM. unfold CM in *. lia.
Qed.
Lemma X_X_back0 : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0G0VTR;S38S2bVJAv;S43A1S54R3R2A5VFAM;S2dS20S21S5S2cA2S21S4SaA2S20S5S2cS54S43A4S20S4SaZ32S45S44Z0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back0 X_back0f s_back0); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.
Lemma X_X_back1 : ltac2:(tb__ "0|1|
SbS22S36Q40A1A1M0G0VTR;S38S2bVJAv;S43A1S55R3R2A5VFAM;S2dS20S21S5S2cA2S21S4SaA2S20S5S2cS55S43A4S20S4SaZ32S45S44Z0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back1 X_back1f s_back1); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S2cS21S4SaA2M0SbS22S36Q40A1A1M1G1S6aS21S21S5S2cA2M2G0A2S20G2G0S20S5S2cR6R5A4R4A4S64A3VTR;S38S2bVJAv;R6A1R7R4R3A5VFAM;S2dS20G2G0S20S5S2cR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsO] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_Lin0. meas0.
  - apply X_X_Lin1. meas0.
  - apply X_E_L.
  - apply X_X_back0.
  - apply X_X_back1.
  - apply X_E_2v.
  - apply X_E_2d.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S35S2bVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SaeS2bSadVAInv;VCST;VXGL;A5").

Theorem opt_push3_sum : ltac2:(tb__ "0|0|
S22S36Q40A1A1S85S2bVok;S38S2bS2fVAInv;VCST;VXGL;VKc;S79VFB;VFF;A2VFB;VFF;VBX;S2eS46AaS53Vrho0;R1A5S75S2bS73Vrho0;R1S8dA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100
                (map edropA cutsO) (map edropA exitsO) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertO_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsO)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue ok (map edropA cutsO) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SafS2bSadVAInv;VCST;VXGL;A5").

Theorem opt_push3_sum_ex : ltac2:(tb__ "0|0|
S22S36Q40A1A1S84S2bS38S2bS2fVAInv;VCST;VXGL;VKc;S79VFB;VFF;A2VFB;VFF;VBX;S2eS46AaS53Vrho0;R1A5S75S2bS73Vrho0;R1S8dA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100 cutsO exitsO (Q tp0) ejcertO_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue) cutsO) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue cutsO T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_opt_push3_pf.

(* [comment removed for export] *)
Module Lib_b_warn_H.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "true"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "FUEL_bw"; "cutpcs_bw"; "X_bw"; "bw_facts"; "bw_objs"; "cuts_bw"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H"; "P_bwH"; "Posts_bwH"; "NXP_bwH"; "exits_bwH"; "vcuts_bwH"; "vexits_bwH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "valuation"; "FcsrFrm0"; "mkSS"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn.BWarnAddr"; "bw_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn.
Import BWarnAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Definition NXP_bwH : positive := 190%positive.
Definition P_bwH : axst := ltac2:(tb__ "0|0|
S1S1fS29S2fS2A1S30S1eScS20A1S13S2aA1S12S18SdA9S11A2").
Definition Posts_bwH : list leafA := ltac2:(tb__ "0|0|
S7S26S27S16S2eA2S8S26A1A3").
Definition exits_bwH : list axst := [P_bwH].

Lemma check_bwH : ltac2:(tb__ "0|0|
S15S9S5S0SfS10S2S14S19A6SbA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem b_warn_sumH : ltac2:(tb__ "0|0|
S2dOF_;S23S1dSaS28Q40A1A1S25S0R4R3A3S24S0S2R4A3S2cS0R6S22S0R5SeR4R3A5S21S0R5S2R4R3S17A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NPH Pre_bw rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_bw cutpcs_bw NPH cuts_bw exits_bwH (withGA (fun r => agree_below NPH rho r) J) ok
           (LQA segs J NPH rho tp Posts_bwH) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_bwH.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_bwH : list vnodeA := ltac2:(tb__ "0|0|
S7S3S4SeZ1eS1cZ0A1A3S8S3A1A3").
Definition vexits_bwH : list vnodeA := ltac2:(tb__ "0|0|
S7S3S4S16Z1S1cZ0A1A3S8S3A1A3").

Lemma echeck_bwH : ltac2:(tb__ "0|0|
S15S9S6S0SfS10S2S1aS1bA6SbA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem b_warn_sumH_ex : ltac2:(tb__ "0|0|
S23S1dSaS28Q40A1A1S24S0S2R3A3S2bS0S22S0R4SeR3R2A5S21S0R4S2R3R2S17A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NPH Pre_bw rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_bw with (vna_state (mkVNA Pre_bw 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_bw cutpcs_bw NPH vcuts_bwH vexits_bwH (withGA (fun r => agree_below NPH rho r) J)
           (LQA segs J NPH rho tp Posts_bwH) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_bwH.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NPH rho vcuts_bwH Posts_bwH (mkVNA P_bwH 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_b_warn_H.

(* [comment removed for export] *)
Module Lib_vec_reserve_rom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "bool"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "SMd"; "cell"; "SAlu"; "sobj"; "SPAlign"; "SVar"; "DUnknown"; "FcsrFrm0"; "SPBranch"; "mkObj"; "mkSS"; "valuation"; "SAluW"; "SExt"; "SLBytes"; "SMdW"; "SPNot"; "reg_sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom"; "vK"; "vW"; "kbytes"; "nd0"; "vDt"; "c8"; "vDn"; "vC"; "vE"; "vKn"; "ndG"; "vAl"; "vV"; "z0"; "kn15"; "vDp"; "X_vr"; "pR"; "vr_facts"; "B32"; "bdP"; "canon_objs"; "inj"; "ndN"; "spm"; "tv0"; "O_Fv"; "O_W"; "O_alv"; "O_vec"; "Pre_vr"; "T_c8ok0"; "T_r15ok0"; "T_rW1ok0"; "X15"; "X8"; "XW1"; "injR"; "pC"; "two47"; "B_EW"; "C_c15"; "C_cW1"; "C_r8"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "G_15"; "G_8"; "G_W1"; "KLG"; "N15"; "N8"; "NW1"; "PHI"; "P_fail"; "P_fail_S"; "P_grown_S"; "P_keep"; "P_keep_S"; "Pre_c"; "Pre_vr_S"; "T_c8n"; "T_c8ok"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "Vs"; "cutpcs_vr"; "grown_facts"; "injZ"; "kbytesN"; "knR"; "two48"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "AXUnbase"; "AXRebase"; "AXSplit"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "mulop"; "aluop"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "BC_LTU"; "M_DIV"; "M_DIVU"; "M_MULH"; "M_MULHSU"; "M_MULHU"; "M_REM"; "M_REMU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "bitem"; "ASv"; "BI"; "ALog"; "KU"; "ZK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "setregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.VRRAddr"; "vr_ret"; "calloc_pc"; "vr_entry"; "vr_nc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "AE_A"; "Pre_calloc"; "UStopLeOrPc"; "Wcan"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "opp"; "pow"; "@Corelib.Init.Logic"; "True"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.RR"; "Pre_rr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.RR.RRAddr"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_realloc_rom. End RR.
Module RRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_realloc_rom_pf. End RRP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module VRRAddr. Include Lib_vec_reserve.VRAddr. End VRRAddr.
Import VRRAddr.
Import RR.RRAddr.
Definition c8 := RR.c8. Definition spm := RR.spm. Definition vUD := RR.vUD. Definition two47 := RR.two47. Definition two40 := RR.two40.

Definition FUEL_vr : nat := 400%nat.
Definition two48 : Z := 2 ^ 48.
Definition B_EW : Z := 2863311530.
Definition B32 : Z := 4294967295.

Definition vV : sv := SVar 12. Definition vW : sv := SVar 13. Definition vAl : sv := SVar 14.
Definition vDt : sv := SVar 15. Definition vC : sv := SVar 16. Definition vK : sv := SVar 17. Definition vE : sv := SLit 16.
Definition vDp : sv := SVar 19.
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.
Definition kbytesN (k : sv) : sv := ltac2:(tb__ "0|4|
SaSaLk;Vk;S22ScSa4Z10R1A2A1Lz;S23S2aVk;A1M0Li;S7eSaSaG0Lb;La;M1Lop;M2G2S7dG1Lop;M3G3S8S24SaG0La;Lw;Lsgn;S23SaS22G0Lk0;Li;Ll;Xax8").

Definition O_Fv (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S13PaA1ScN40A1ScZ0A1Vcells;S14A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S17S40Z40A1S37ScZ0A1S3SfA1S14A5").
Definition O_vec (d c k e : sv) : sobj := ltac2:(tb__ "0|1|
S17S34ScZ0M0A1ScZ20A1S0SfS2dG0Vd;A2S0SfS2dZ8Vc;A2S0SfS2dZ10Vk;A2S0SfS2dZ18Ve;A2S3SfA1A3A3A3A3S14A5").
Definition O_alv : sobj := ltac2:(tb__ "0|2|
S17S33ScZ0M0A1M1ScZ30A1S0SfS2dG0ScSacA1A2S0SfS2dZ8ScSadA1A2S0SfS2dZ10G1A2S0SfS2dZ18ScSaeA1A2S0SfS2dZ20G1A2S0SfS2dZ28S74A2S3SfA1A3A3A3A3A3A3S14A5").

Definition vr_facts : list sprop := ltac2:(tb__ "0|c|
S0SbS12PaM0Z4M1A2S0SbSdS13G0A1M2ScS4fA1M3A2S0SbSdS13P1eA1M4S10S7bS40Z40A1M5S37A3A2S0SbSdG4S40Za0A1A2S0SbSdG4G5A2S0SbSdG4G2A2S0SbS16S7fScN1060A1S37A3S0SbS16S7fS37ScSa5Sa6Z2Z27A2A1A1A3S0SbS12PcZ3M6A2S0SbSdG2S34A2S0SbSdS10S7bS34ScZ20A1A3G3A2S0SbSdS34G3A2S0SbS12PeG6A2S0SbSdScZ1000A1M7S33A2S0SbSdS10S7bS33ScZ30A1A3G4A2S0SbSdS33G3A2S0SbS12PfG1A2S0SbSdS2cG4A2S0SbSdS10S7bS2cS2aS28A1M8A3G4A2S0SbSdS2cG3A2S0SbSdScZ1A1M9S30A2S0SbSdS30G7A2S0SbSdS29ScS73A1A2S0SbSdS2fS28A2S0SbSdS28ScS3bA1MaA2S0SbSdS2aS29A1ScS50A1A2S0SbSdG8GaA2S0SbSdS29S10S7bS2fG9A3A2S0SbSdScZ7fff7f800000A1MbG4A2S0SbSdG4ScZ7fffff800000A1A2S0SbSdGbG2A2S3SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_vr (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SaSaA2M0S1SaSaS34ScZ20A1A4S0G0S1SaSaS33ScZ30A1A4S0G0S1SaSaVd;S2aVk;A1A4S3G0A1A3A3A3").
Definition Pre_vr_S : sstate := ltac2:(tb__ "0|0|
S18S9bS98S95S15S6SaA1S5S11S0S11S42S3SfA1A1S0S11S43S0S11S45S2cS2fS28S30A4S0S11S44S3S11A1A3A3A3A3S92A3S3aS94S7A9").
Definition Pre_vr : axst := ltac2:(tb__ "0|0|
S91S66S38S2cS28A2A2").

Definition cutpcs_vr : list Z := ltac2:(tb__ "0|0|
S0S22S9cS0S22SabS0S22S9aS3S22A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_vr end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa9S20Vk;S93S57S6eVS;Vpc;A4S46A4").

Definition X15 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 0.
Definition XW1 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 1.
Definition X8 : axst := Eval vm_compute in leafA_at Pre_vr vr_nc 2.

Definition kn15 : sv := ltac2:(tb__ "0|0|
S10S7bS10S80S28ScZ1A1A3S28A3").
Definition inj (kn : sv) : list sprop := ltac2:(tb__ "0|3|
S0SbSdSeS7cScZ4A1M0S2aS28A1A3SeS7cScZ3A1S2aVkn;A1M1A3A2S0SbSdSeS7cG0G1A3S10S7bSeS7cScZ6A1S2aS29A1A3SeS7cScZ20A1S30A3A3A2S0SbSdG1ScS3bA1M2A2S0SbSdScZ1A1G1A2S0SbSdVkn;G2A2S3SbA1A3A3A3A3A3").
Definition injR (kn : sv) : list sprop := ltac2:(tb__ "0|0|
S0SbSdS28S2fA2S0SbS16S82S28Vkn;A3S3SbA1A3A3").
Definition injZ : list sprop := ltac2:(tb__ "0|0|
S0SbSdS2fScZ0A1A2S3SbA1A3").
Definition N15 : axst := ltac2:(tb__ "0|0|
S9dS5SbS4dS36A1S3eS36A1A3S4aA2").
Definition NW1 : axst := ltac2:(tb__ "0|0|
S9dS5SbS4dS29A1S3eS29A1A3S4cA2").
Definition N8 : axst := ltac2:(tb__ "0|0|
S9dS5SbS70S3eScZ8A1A1A3S4bA2").

Definition E_r15 : axst := Eval vm_compute in leafA_at N15 ra_entry 0.
Definition E_rW1 : axst := Eval vm_compute in leafA_at NW1 ra_entry 0.
Definition C_c15 : axst := Eval vm_compute in leafA_at N15 calloc_pc 0.
Definition C_cW1 : axst := Eval vm_compute in leafA_at NW1 calloc_pc 0.
Definition E_c8 : axst := Eval vm_compute in leafA_at N8 calloc_pc 0.
Definition C_r8 : axst := Eval vm_compute in leafA_at N8 ra_entry 0.

Definition tvf0 : list sprop := ltac2:(tb__ "0|0|
S27S1SaSaS2cS2aS28A1A4A1").

Definition xf_rcall : list axform := ltac2:(tb__ "0|2|
S0S75S7aU1M0ScN60M1A1A2S0S75S78G0G1A2S3S75A1A3A3").
Definition E_r15x : axst := Eval vm_compute in optA (apply_axforms E_r15 xf_rcall).
Definition E_rW1x : axst := Eval vm_compute in optA (apply_axforms E_rW1 xf_rcall).
Definition E_r15f : axst := ax_add_facts tvf0 E_r15x.
Definition E_rW1f : axst := ax_add_facts tvf0 E_rW1x.
Definition knR (E : axst) : sv := match reg_sv (ax_S E) 13 with SMd M_MUL _ k => k | x => x end.
Definition s_r (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S23SaA2M0S1S23SaP13S10S7bS37ScZ60A1A3A4S0G0S1S23SaPeS28A4S0G0S1S23SaP21S72VE;A1A4S9ePaS21VE;A1S21SaaA1A3A3A3A3").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition PD_rr : list pdescK := RRP.PDk_rr.
Definition R_r15 : list sobj := Eval vm_compute in optR (entails_frA E_r15f RR.Pre_rr (s_r E_r15f)).
Definition R_rW1 : list sobj := Eval vm_compute in optR (entails_frA E_rW1f RR.Pre_rr (s_r E_rW1f)).
Goal entails_frA E_r15f RR.Pre_rr (s_r E_r15f) = Some R_r15 /\ call_checkPA E_r15f RR.Pre_rr (s_r E_r15f) R_r15 (map (fun d => fst (fst d)) PD_rr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal entails_frA E_rW1f RR.Pre_rr (s_r E_rW1f) = Some R_rW1 /\ call_checkPA E_rW1f RR.Pre_rr (s_r E_rW1f) R_rW1 (map (fun d => fst (fst d)) PD_rr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_ccall : list axform := ltac2:(tb__ "0|2|
S0S75S7aU2M0ScZ10M1A1A2S0S75S78G0G1A2S3S75A1A3A3").
Definition E_c8' : axst := Eval vm_compute in optA (apply_axforms E_c8 xf_ccall).
Definition Pre_c : axst := ltac2:(tb__ "0|0|
Sa1Sa0Sa3U1A1Sa2A3").
Definition s_c (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S23SaA2M0S1S23SaP34S2cA4S0G0S1S23SaP35S2fA4S9ePaS21VE;A1S21S65A1A3A3A3").
Definition R_c8 : list sobj := Eval vm_compute in optR (entails_frA E_c8' Pre_c (s_c E_c8')).
Goal entails_frA E_c8' Pre_c (s_c E_c8') = Some R_c8 /\ call_checkPA E_c8' Pre_c (s_c E_c8') R_c8 [L_calloc_null AE_A (Wcan 1) UStopLeOrPc; L_calloc_ok AE_A (Wcan 1) UStopLeOrPc] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_r : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SaSaA2M0S1SaSaS34ScZ20A1A4S0G0S1SaSaS33ScZ30A1A4S3G0A1A3A3").
Definition T_r15f0 : axst := Eval vm_compute in T_afterA3 RR.Pre_rr E_r15f (s_r E_r15f) R_r15 RR.P_fail Xk_r.
Definition T_r15ok0 : axst := Eval vm_compute in T_afterA3 RR.Pre_rr E_r15f (s_r E_r15f) R_r15 RR.P_ok Xk_r.
Definition T_rW1f0 : axst := Eval vm_compute in T_afterA3 RR.Pre_rr E_rW1f (s_r E_rW1f) R_rW1 RR.P_fail Xk_r.
Definition T_rW1ok0 : axst := Eval vm_compute in T_afterA3 RR.Pre_rr E_rW1f (s_r E_rW1f) R_rW1 RR.P_ok Xk_r.
Definition xf_cbackN : list axform := ltac2:(tb__ "0|2|
S0S75S79U1M0A1S0S75S77S0S2U0S0S2U2S0S2U3S0S2U4M1S0S2G0S0S2U5S0S2U6S3S2A1A3A3A3A3A3A3A3A1S0S75S76G1A1S3S75A1A3A3A3").

Definition xf_cbackZ : list axform := ltac2:(tb__ "0|2|
S0S75S79U1M0A1S0S75S77S0S2U0S0S2U3S0S2U4M1S0S2U5S0S2G0S0S2U6S0S2U7S0S2U2S3S2A1A3A3A3A3A3A3A3A3A1S0S75S76G1A1S3S75A1A3A3A3").
Definition T_c8n00 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_null AE_A (Wcan 1) UStopLeOrPc).
Definition T_c8ok00 : axst := Eval vm_compute in T_afterA Pre_c E_c8' (s_c E_c8') R_c8 (L_calloc_ok AE_A (Wcan 1) UStopLeOrPc).
Definition T_c8n0 : axst := Eval vm_compute in optA (apply_axforms T_c8n00 xf_cbackN).
Definition T_c8ok0 : axst := Eval vm_compute in optA (apply_axforms T_c8ok00 xf_cbackZ).
Definition T_c8n : axst := T_c8n0.
Definition pC (T : axst) : sv := reg_sv (ax_S T) 10.

Definition T_c8okZ : axst := Eval vm_compute in drop_lastA T_c8ok0 (removelast (ss_objs (ax_S T_c8ok0))).
Definition T_c8ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pC T_c8ok0, SLit 128)) T_c8okZ.

Definition xf_rback : list axform := ltac2:(tb__ "0|2|
S0S75S78U1M0Z60A2S0S75S77S0S2G0S0S2U0M1S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S3S2A1A3A3A3A3A3A3A3A1S0S75S76G1A1S3S75A1A3A3A3").
Definition T_r15f : axst := Eval vm_compute in optA (apply_axforms T_r15f0 xf_rback).
Definition T_rW1f : axst := Eval vm_compute in optA (apply_axforms T_rW1f0 xf_rback).
Definition T_r15okB : axst := Eval vm_compute in optA (apply_axforms T_r15ok0 xf_rback).
Definition T_rW1okB : axst := Eval vm_compute in optA (apply_axforms T_rW1ok0 xf_rback).
Definition pR (T : axst) : sv := reg_sv (ax_S T) 10.
Definition T_r15ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_r15ok0, kbytes kn15)) T_r15okB.
Definition T_rW1ok : axst := Eval vm_compute in ax_add_facts (tv_factsA (pR T_rW1ok0, kbytes vW)) T_rW1okB.

Definition canon_objs (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S5S11S0S11S42S3SfA1A1S0S11S43S0S11S45Vd;S2fVk;S30A4S0S11S44S3S11A1A3A3A3A3S92A3").
Definition P_keep_S : sstate := ltac2:(tb__ "0|1|
S18S99S97S96S94A1S0S4S2SaA2M0S1S2SaUaScZ1A1A4S3G0A1A3A2S95S15S6SaA1S3dS2cS28A2S0SbSdS29S28A2S3aA3S9fS7A9").
Definition P_keep : axst := ltac2:(tb__ "0|0|
S91S64S38S2cS28A2A2").
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S18S99S97S96S94A1S0S4S2SaA2M0S1S2SaUaScZ0A1A4S3G0A1A3A2S95S15S6SaA1S3dS2cS28A2S3aS9fS7A9").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S91S61S38S2cS28A2A2").
Definition vDn : sv := SVar 140. Definition vKn : sv := SVar 141.
Definition grown_facts : list sprop := ltac2:(tb__ "0|4|
S0SbSdS29S31A2S0SbS12P8cZ4M0A2S0SbS1eS16S81S2eScZ0A1A3A1S0SbSdScZ1000A1S2eA2S0SbSdS2eS13P1eA1M1A2S0SbSdS10S7bS2eS2aS31A1M2A3G1A2S0SbSdS2eScS4fA1A2S0SbSdScSafA1S2eA2S0SbSdSeS7cScG0A1G2A3S10S7bSeS7cScZ6A1S2aS29A1A3SeS7cScZ20A1S30A3A3A2S0SbSdG2ScS3bA1M3A2S0SbSdScZ1A1G2A2S0SbSdS2fS31A2S0SbSdS31G3A2S3SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_grown_S : sstate := ltac2:(tb__ "0|1|
S18S99S97S96S94A1S0S4S2SaA2M0S1S2SaUaScZ1A1A4S3G0A1A3A2S95S15S6SaA1S3dS2eS31A2S5SbS6fS3aA3P8eS7A9").
Definition P_grown : axst := ltac2:(tb__ "0|0|
S91S62S38S2eS31A2A2").

Definition G_15 : axst := Eval vm_compute in leafA_at T_r15ok vr_ret 0.
Definition G_W1 : axst := Eval vm_compute in leafA_at T_rW1ok vr_ret 0.
Definition G_8 : axst := Eval vm_compute in leafA_at T_c8ok vr_ret 0.

Definition PHI (w k : sv) : bitem := ltac2:(tb__ "0|2|
S8dZ1Z0M0S0S4S22S8aA2M1S1S22S8aZ6S8cS2aVw;A1A1A4S0G1S1S22S8aN4S8cS2aVk;A1A1A4S0G1S1S22S8aZ20S8cS30A1A4S3G1A1A3A3A3G0A4").
Definition KLG (k : sv) : bitem := ltac2:(tb__ "0|1|
S8dZ0Sa4Z2S8fA2S0S4S22S8aA2M0S1S22S8aN1S8eVk;A1A4S3G0A1A3S90A4").
Definition bdP (w k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8bS5fVw;Vk;A2S0S8bS5bVk;A1S3S8bA1A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SaSaA2M0S1SaSaS2cS2aS28A1A4S3G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SaSaA2M0S1SaSaS2eS2aS31A1A4S3G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S26S41S3S4S4SaS22A2SaA2A1S3cS29S28A2A3").
Definition ndN (kn : sv) : ndesc := ltac2:(tb__ "0|0|
S26S41S3S4S4SaS22A2SaA2A1S3cS29Vkn;A2A3").
Definition ndG (p kn : sv) : ndesc := ltac2:(tb__ "0|1|
S26S0S4SaSaA2M0S1SaSaVp;S71Vkn;A1A4S3G0A1A3S3S4S4SaS22A2SaA2A1S3cS29Vkn;A2A3").

Definition z0 : sv := SLit 0.

Definition Vs : list (list positive) := ltac2:(tb__ "0|3|
S0S9S23A1M0S3S23A1M1S0G0S0S23P8dG1A3M2S0G0G2S0G0S0S23P70G1A3S3G0A1A3A3A3A3").
Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|2|
Sa8S9S23A1M0S4G0S19OF_;M1A2G0S1G0G1R1S19Sa7L_;A4LV;S6dA4").
Definition cutsE : list efnode := ltac2:(tb__ "0|8|
S0S4S4S4S20S25A2M0S2A2M1S4S22SaA2M2A2M3S1G1G2S1G0S2S1S20S25S46S2bA4U0M4A4S1S22SaZ64S35A4A4S0G3S1G1G2S1G0S2S1S20S25S5cS2bA4G4A4S1S22SaZ50S35A4M5A4S0G3S1G1G2S1G0S2S1S20S25S5eS2bA4G4A4G5A4S0G3S1G1G2S1G0S2S1S20S25S5dS2bA4G4A4G5A4S0G3S1G1G2S1G0S2S1S20S25S69S3fS36A1A4G4A4S1S22SaZ3cS35A4M6A4S0G3S1G1G2S1G0S2S1S20S25S6aS32S39S48A1S36A2A4U1A4G6A4S0G3S1G1G2S1G0S2S1S20S25S6bS3fS29A1A4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S6cS32S39S49A1S29A2A4U2A4G6A4S0G3S1G1G2S1G0S2S1S20S25S67S3fScZ8A1M7A1A4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S68S32S4eS47A1G7A2A4U3A4G6A4S3G3A1A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|8|
S0S4S4S4S20S25A2M0S2A2M1S4S22SaA2M2A2M3S1G1G2S1G0S2S1S20S25S4aS2bA4U0M4A4S1S22SaZ5aS35A4M5A4S0G3S1G1G2S1G0S2S1S20S25S4cS2bA4G4A4G5A4S0G3S1G1G2S1G0S2S1S20S25S4bS2bA4G4A4G5A4S0G3S1G1G2S1G0S2S1S20S25S55S2bA4G4A4S1S22SaZ46S35A4M6A4S0G3S1G1G2S1G0S2S1S20S25S56S2bA4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S51S2bA4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S52S2bA4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S54S2bA4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S53S2bA4G4A4G6A4S0G3S1G1G2S1G0S2S1S20S25S63S2bA4G4A4S1S22SaZ0S35A4M7A4S0G3S1G1G2S1G0S2S1S20S25S60S26S41S3S4S4SaS22A2SaA2A1S3S8bA1A3A4G4A4G7A4S0G3S1G1G2S1G0S2S1S20S25S58S32S39S48A1S36A2A4U1A4G7A4S0G3S1G1G2S1G0S2S1S20S25S5aS32S39S49A1S29A2A4U2A4G7A4S0G3S1G1G2S1G0S2S1S20S25S59S32S4eS47A1ScZ8A1A2A4U3A4G7A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition s_g15 : wsub := Eval vm_compute in infer_sub NF (ax_S G_15) (ax_S P_grown).
Definition s_gW1 : wsub := Eval vm_compute in infer_sub NF (ax_S G_W1) (ax_S P_grown).
Definition s_g8 : wsub := Eval vm_compute in infer_sub NF (ax_S G_8) (ax_S P_grown).
Goal entailsA G_15 P_grown s_g15 = true /\ entailsA G_W1 P_grown s_gW1 = true /\ entailsA G_8 P_grown s_g8 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_vec_reserve_rom.

(* [comment removed for export] *)
Module Start6bStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "Some"; "option"; "app"; "length"; "nat"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "@Corelib.Init.Decimal"; "D0"; "D8"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "sprop"; "SPUle"; "SVar"; "ss_objs"; "SPAlign"; "ss_next"; "ss_pc"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates"; "E18"; "MALLOC_ENTRY"; "SPIN17"; "S_s17ok"; "F17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "SPIN_MMAPORDIE"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates"; "E_s17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@Stdlib.ZArith.BinInt.Z"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition MALLOC_ENTRY : Z := 0xd278c.

Definition F17 : list sprop := ltac2:(tb__ "0|2|
S0S1bS1fP53M0ZcA2S0S1bS1cS18Z643000A1S1dG0A1M1A2S0S1bS1cG1S18S34Z7fffff800000Zb09000A2A1A2S1S1bA1A3A3A3").
Definition S_s17ok : axst := ltac2:(tb__ "0|2|
S30S31S27S32S11S2aA1M0S1dP53M1A1S6S1aS1eG0A1S0S1aS33G1Zb09000A2S1S1aA1A3A3P54A4A2A1").
Definition run17b__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS17S2cS2dS15S14S14S14S16A1A1A1A1A1A1S0SaS24S1SaA1A3S26S2A5").
Local Strategy expand [run17b__R].
Definition E18 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (leaf1 S_s17ok (ro1__))) run17b__R).
Lemma run17b : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17S2cS2dS15S14S14S14S16A1A1A1A1A1A1S0SaS24S1SaA1A3S26S2A5S4G0S0SeS10S23S2bA2S1SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17b__R <: run17b__R = Some [mkLeafA E18 RsCut]). Qed.
Definition run17_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS17U12cS0SaS28S1SaA1A3S29S2aA1S2A5").
Local Strategy expand [run17_fail__R].
Definition SPIN17 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E_s17) (ro2__))) run17_fail__R).
Lemma run17_fail : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17U12cS0SaS28S1SaA1A3S29S2aA1S2A5S4G0S0SeS10S25S2bA2S1SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17_fail__R <: run17_fail__R = Some [mkLeafA SPIN17 RsCut]). Qed.
Lemma spin17 : ltac2:(tb__ "0|1|
ScS5S3SeA1M0A1SfS17U2S0SaS28S1SaA1A3S25S2A5S4G0S0SeS10S25S2bA2S1SeA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E18_at : ltac2:(tb__ "0|2|
SdScSaS21S11S23A1M0A1S24A3SdScSbS20G0A1P54A3SdScS3S9S19S19A2M1A1S12S23A1S1G1A1A3SdScS19S13S23A1S18S2fA1A3SdScS8S7S1aS1eG0A1A2U1aA3ScS19S2eS19UaS22G0A1S18Z0A1A4S18Z28A1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6bStates.

(* [comment removed for export] *)
Module DrvR_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "option"; "nil"; "bool"; "Some"; "pair"; "list"; "prod"; "andb"; "false"; "app"; "None"; "length"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "cell"; "sstate"; "SPUle"; "ss_objs"; "DUnknown"; "mkObj"; "ss_next"; "ss_pc"; "swf"; "ss_facts"; "SPAlign"; "reg_sv"; "ss_regs"; "SPBranch"; "mkSS"; "sprop_eqb"; "FcsrFrm0"; "SAlu"; "mkCell"; "sv_eqb"; "SExt"; "SPEq"; "SPNot"; "odefault"; "SAluW"; "SLBytes"; "SMd"; "SMdW"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "tfact"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "sym_runA"; "leafA"; "ax_setS"; "la_state"; "entailsA"; "sobj_eqb"; "ax_X"; "axwf"; "mkLeafA"; "la_reason"; "mkAX"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states"; "CUTS_R"; "RS"; "ibS"; "pcs_of"; "vWant"; "X_R"; "T_after"; "O_rdsC"; "obind"; "vRes1"; "vResH"; "R1c"; "ob_shape0b"; "G_cut"; "R0c"; "hcZ"; "irds"; "PreC"; "two_cap"; "C_s0"; "RD0"; "RD1"; "nthA"; "objs_R"; "optS"; "E_rd0"; "E_rd1"; "E_s0"; "O_rdsL"; "R_s0"; "S0f"; "errV"; "hdr_cell"; "rd_w1"; "rd_w2"; "s_s0"; "vRes0"; "C_cp1"; "C_czh"; "C_czk"; "C_mc"; "C_rd0"; "C_rd1"; "FUEL_R"; "G_mok"; "Hc1"; "LV_R0"; "LV_R1"; "LV_S0"; "PreM"; "Q1"; "R_mG"; "cp_s1"; "cz_rsd"; "cz_splits"; "errL"; "errL_okb"; "hcD"; "objs37"; "rds_cellsL"; "s_mG"; "vN'"; "B1u"; "Bg"; "C_f"; "E_cl0"; "E_cl1"; "E_clZ"; "E_mcf"; "G_mnull"; "Hc0"; "HcZ"; "Lref"; "LtrR"; "PreCH"; "PreMC"; "R_cp1"; "R_czh"; "R_czk"; "R_f"; "R_mc"; "R_rd0"; "R_rd1"; "T_cp1"; "T_czh"; "T_czk"; "T_f"; "T_mc"; "T_rd0k"; "T_rd0k'"; "T_rd1k"; "T_rd1k'"; "T_s0h"; "T_s0h'"; "T_s0k"; "T_s0k'"; "bk_okb"; "bkpipe"; "bkz_okb"; "bkzpipe"; "cp_cv"; "errV_okb"; "lenG"; "mc_rtc"; "q_okb"; "qpipe"; "qz_okb"; "qzpipe"; "rd_rs"; "rd_rtc"; "rd_s1"; "s_cp1"; "s_czh"; "s_czk"; "s_f"; "s_mc"; "s_rd0"; "s_rd1"; "BZhu"; "BZku"; "E_m"; "E_mG"; "E_mZ"; "E_mZG"; "F1"; "F2"; "LV_C1"; "LV_Gnull"; "LV_Gok"; "LV_S0h"; "LV_S0k"; "LV_T0k"; "LV_T1k"; "LV_Zh"; "LV_Zk"; "LV_c0"; "LV_c1"; "LV_cZ"; "LV_f"; "LV_h0"; "LV_h1"; "LV_hZ"; "LV_mc"; "LV_oom"; "LV_ov1"; "LV_ref"; "LV_sh0"; "LV_sh1"; "LV_shZ"; "Lb1"; "LbZh"; "LbZk"; "Lc0k"; "Lcl0"; "Lcl1"; "Lcp1"; "Lg1"; "LgZh"; "Loom"; "Lov1"; "Lr1"; "Ls0h"; "Ls0k"; "Lsh0"; "Lsh1"; "LshZ"; "Ltr"; "PostsC"; "QZh"; "QZhf"; "QZk"; "QZkf"; "XF_bka"; "XF_bkb"; "XF_bkza"; "XF_bkzb"; "XF_q"; "XF_qz"; "ax_of"; "bk2"; "bkz2"; "cp_rsd"; "cp_rss"; "cp_splits"; "cp_w1"; "cp_w2"; "czh_h1"; "czh_h2"; "czh_h3"; "errL0"; "facts_R"; "facts_R1"; "facts_Rb"; "has_tpfact"; "ierrL"; "ierrV"; "inew"; "len1'"; "mc_b1"; "mc_w1"; "mc_w2"; "mch_rtc"; "q2"; "qz2"; "rd_cv"; "rd_rsZ"; "rd_site"; "rdsb"; "s_RDa"; "s_RDb"; "vJ7"; "E_f"; "E_mc"; "F_bk1"; "Lg"; "O_bufR"; "O_dstC";
"O_dstL"; "O_dstZ"; "O_errnoV"; "PostsCH"; "PostsM"; "PostsMC"; "RD_cut"; "R_cut"; "XF_f"; "X_G"; "clen_x"; "cp_b0"; "cp_b1"; "cp_b2"; "cp_okb"; "cp_site"; "cz_b1"; "cz_okb"; "cz_site"; "czh_okb"; "czh_site"; "errL0_okb"; "errV0"; "errV0_okb"; "facts_G"; "facts_RD"; "mc_cv"; "mc_kfacts"; "mc_site"; "objs38"; "q1"; "q3"; "q4"; "rd_siteZ"; "regs_G"; "regs_R"; "regs_RD"; "s_G"; "s_GZ"; "s_R0"; "s_T"; "s_bk1"; "s_bkG"; "s_bkZh"; "s_bkZk"; "selb"; "selbZ"; "self"; "selq"; "selqZ"; "setregA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "RsFuel"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vB"; "vCap"; "vLen"; "vTP"; "locate"; "DEEP"; "sp0"; "vTOPv"; "PreF"; "fregs_T"; "spM"; "vA1"; "ATOPHI"; "IMGHI"; "PostF"; "X_rds"; "vTID"; "O_errno"; "O_rds"; "S_T"; "arg1_facts"; "top_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "add"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "combine"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@Corelib.Lists.ListDef"; "map"; "skipn"; "seq"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read"; "Pre_rd"; "Posts_rd"; "P_rd"; "hc"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "X_R0"; "CAP0"; "R_head"; "objs_R0"; "S_R0"; "argsX_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "malloc_stub"; "free_stub"; "tr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "fw_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states.RAddr"; "rd_cut"; "close_entry"; "t_oom2"; "t_overrun"; "t_ref"; "t_short"; "t_rderr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.MCAddr"; "mc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.RDAddr"; "rd_entry"; "rd_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "aluop"; "mulop"; "ALU_SLL"; "ALU_SUB"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "FERR"; "exit_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "fp_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "P_icpt"; "O_real";
"O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "X_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvErrno"; "errC"; "errC_okb"; "errR_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr"; "O_real"; "O_rtc3"; "P_icpt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs"; "P_icpt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvErrno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module RAddr.
  Definition grow_head : Z := 0x8c5b8.
  Definition malloc_site : Z := 0x8c5c8.
  Definition memcpy_site : Z := 0x8c5a0.
  Definition memcpy_grow : Z := 0x8c5e4.
  Definition free_site : Z := 0x8c5ec.
  Definition read_prep : Z := 0x8c5f0.
  Definition rd_cut : Z := 0x8c600.
  Definition read_site : Z := 0x8c608.
  Definition read_ret : Z := 0x8c60c.
  Definition close_ret : Z := 0x8c620.
  Definition t_ref : Z := 0x8c76c.
  Definition t_oom2 : Z := 0x8c78c.
  Definition t_rderr : Z := 0x8c750.
  Definition t_short : Z := 0x8c6dc.
  Definition t_overrun : Z := 0x8c6f8.
  Definition close_entry : Z := 0xe0224.
End RAddr.
Import RAddr.

Definition CUTS_R : list Z := ltac2:(tb__ "0|0|
S0S4fS1a6S0S4fS1a7S0S4fS1b8S0S4fS1b9S0S4fS1b2S0S4fS1baS0S4fS1c4S0S4fS1c6S0S4fS1b0S0S4fS19bS0S4fS1b1S0S4fS1a8S0S4fS1b5S0S4fS1b3S0S4fS1b7S0S4fS1b6S0S4fS1b4S4S4fA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition runR (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S3S8S45A1M0A1G0Lx;S44S52Vfuel;S54VA;S2A5G0R1Ll;S4S45A1X3x2").
Definition nthA (d : axst) (l : list leafA) (i : nat) : axst := ltac2:(tb__ "0|0|
S47S18fS45Vi;Vl;S4cVd;S168A2A4A1").
Definition optS (d : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
S3S17A1S42Lx;Vx;S17S46Vd;R1A2LS';Vd;X3x2").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition ax_of (o : option axst) (d : axst) : axst := match o with Some a => a | None => d end.
Definition pcs_of (l : list leafA) : list (Z * stop_reason) := ltac2:(tb__ "0|0|
S18bS45S9S4fS165A2S45S7S4fS165S1dS43S47R1A1A1A1S4dR1A1A4LL;Vl;A4").

Definition O_errnoV : sobj := ltac2:(tb__ "0|0|
S1bS16dS12Na4A1S12Na0A1S4S16A1S1aA5").
Definition ob_shape0b (o : sobj) (b lo hi : sv) : bool := ltac2:(tb__ "0|2|
SaSaSaSaS29S35Vo;A1Vb;A2S29S39Vo;A1Vlo;A2A2S29S38Vo;A1Vhi;A2A2S8S16A1M0S5Lx;S36Vo;A1S2S16G0SbLl;Lc;X8x2A2S2dS5Lx;S37Vo;A1S2SbSbS50SbLl;M1G1S4fS11S8S9S4fS4fA2A1S8S3fA1SbLtmpl;Lflds;Lcnt;Lesz;X2dx6A2").

Definition ierrL (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S12Z0A1S12S1a2S1a5Za4A2A1A3").
Definition ierrV (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S16dS12Na4A1A3").

Definition errV0 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S116VE;A1S12fA3A2").
Definition errL0 (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S117VE;A1S17bA3A2").
Definition errV (E : axst) : axst := errV0 (errC E).
Definition errL (E : axst) : axst := errR (errL0 E).
Definition has_tpfact (E : axst) : bool := ltac2:(tb__ "0|0|
S188S14S25S2bS16dS12S1a5A1A2A1S1fS43VE;A1A1A3").
Definition errV0_okb (E : axst) : bool := ltac2:(tb__ "0|1|
SaSaS3S13A1S5Lx;S185S13S19S43VE;A1M0A1S116VE;A1A3S13S60R1S12Z0A1S12S1a2S1a5Za4A2A1S12S1a2S1a5Za0A2A1A4Lo;SbX3x2S189G0S43S143VE;A1A1A2A2S115VE;A1A2").
Definition errV_okb (E : axst) : bool := ltac2:(tb__ "0|0|
SaS1ccVE;A1S144S1cbVE;A1A1A2").
Definition errL0_okb (E : axst) : bool := ltac2:(tb__ "0|1|
SaSaS3S13A1S5Lx;S185S13S19S43VE;A1M0A1S117VE;A1A3S13S60R1S16dS12Na4A1S12Na0A1A4Lo;SbX3x2S189G0S43S111VE;A1A1A2A2S115VE;A1A2").
Definition errL_okb (E : axst) : bool := ltac2:(tb__ "0|0|
SaS142VE;A1S1cdS111VE;A1A1A2").

Definition RS : Z := RD_STAGE.
Definition rdsb : sv := add (SLit RS) (SLit 0).
Definition O_rdsC (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS123S12Z0A1Vn;Vcs;S1aA5").
Definition O_rdsR (n : sv) : sobj := ltac2:(tb__ "0|0|
S1bS12Z0A1S180S12S55A1Vn;A2S12S1a0S55Z10000A2A1S4S16A1S1aA5").
Definition O_rdsL (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|1|
S1bS12Z0A1S12S55A1M0S180G0Vn;A2Vcs;S1aA5").

Definition O_rdsP (n : sv) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS12S55A1S12Z0A1Vn;Vcs;S1aA5").
Definition irds (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S12Z0A1S12S55A1A3").
Definition irdsC (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S123S12Z0A1A3").

Definition O_bufR (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bS16aS12Z0A1S16bVcs;S1aA5").
Definition hdr_cell : cell := mkCell (SLit 0) 4 vH.
Definition objs_R (cs : list cell) : list sobj := Eval vm_compute in (firstn 9 objs_R0 ++ [O_bufR cs] ++ skipn 10 objs_R0).
Lemma objs_R_shape : ltac2:(tb__ "0|0|
S8S16A1S40S8S13A1S6bR1A1ScS13S18eS13U9S19cA3ScS13S0S13S12bR1A1S4S13A1A3S18cS13UaS19cA3A3A3A3Fcs;"). Proof. reflexivity. Qed.
Definition X_R : list (sv * sv) := ltac2:(tb__ "0|1|
ScS9S11S11A2M0S0G0S7S11S11S12Z14d80A1S12Z40A1A4S0G0S7S11S11S180S170S12S1a3S1a0S16fZ80A2A1A1A2S12S16fA1A4S0G0S7S11S11S16aS16bA4S0G0S179S4G0A1A3A3A3A3S1caA3").

Definition facts_Rb : list sprop := ltac2:(tb__ "0|6|
ScS14S0S14S20P1Z4M0A2S0S14S18S12Z7fff80000000A1S170A2S0S14S18S170S12S1a2S1a1Z2M1Z2fA2Ze0A2A1A2S0S14S2bS16dS12S1a5A1A2S0S14S20P18Z3M2A2S0S14S20P28M3G0A2S0S14S20G3G2A2S0S14S18S12Z1000A1S16aA2S0S14S18S180S16aS16bA2M4S12S176A1M5A2S0S14S18S16aG5A2S0S14S18S12S177A1S16aA2S0S14S18G4S171A2S0S14S18S16aS171A2S0S14S2cS23S1bdS16aS12Z0A1A3A1S0S14S18S12Z10000A1S16bA2S0S14S18S16bS12S1a1G1Z1aA2A1A2S0S14S20P29ZcA2S0S14S18S12Z1A1S17aA2S0S14S18S17aS12Z3fffffA1A2S4S14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS14S17fScS14S17eS19eA3A3A3").
Definition facts_R : list sprop := ltac2:(tb__ "0|0|
ScS14S0S14S18S180S16cS12Z1A1A2S16bA2S0S14S18S16cS16bA2S4S14A1A3A3S114A3").

Definition facts_R0f : list sprop := ltac2:(tb__ "0|0|
S0S14S18S16cS12Z3A1A2S112A3").
Definition facts_R1 : list sprop := ltac2:(tb__ "0|0|
S0S14S18S12Z4A1S16cA2S112A3").

Definition vJ7 : sv := SVar 66.
Definition regs_R : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S15P3cA1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S15P64A1S0S11S15P33A1S0S11S15P34A1S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16cS0S11S12Z3A1S0S11S16bS0S11S12S55A1S0S11S126S0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_cut (cs : list cell) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S4eS24S19bS150S173S26SdS11A1S6bVcs;A1VF;P65SbA9S59S12S53A1A3").
Definition R0c : axst := R_cut [] facts_R0f.
Definition R1c : axst := ltac2:(tb__ "0|0|
S134S0S16S74S4S16A1A3S113A2").

Lemma R_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS62A1S2A3S41S40S5S1eS43S62A1A1S2A3S41S40S5S4bS5fA1S2A3S40S5S1eS43S5fA1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S0f : axst := ltac2:(tb__ "0|0|
S19fS0S14S20P18Z3A2S4S14A1A3S19dA2").
Definition s_R0 : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P2aS12Z0A1A4S0G0S7S50S11P29S12S19aA1A4S0G0S7S50S11P64S15P32A1A4S0G0S7S50S11P42S16aA4S4G0A1A3A3A3A3").
Lemma ent_R0 : ltac2:(tb__ "0|0|
S40S5S48S72S62S154A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FUEL_R : nat := 200%nat.
Definition run_R0__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52S7fS54S62S2A5").
Local Strategy expand [run_R0__R].
Definition LV_R0 : list leafA := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) run_R0__R).
Definition run_R1__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52S7fS54S5fS2A5").
Local Strategy expand [run_R1__R].
Definition LV_R1 : list leafA := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) run_R1__R).
Lemma run_R0 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52S7fS54S62S2A5S6G0S82A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_R0__R <: run_R0__R = Some LV_R0). Qed.
Lemma run_R1 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52S7fS54S5fS2A5S6G0S83A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_R1__R <: run_R1__R = Some LV_R1). Qed.
Lemma LV_R_pcs : ltac2:(tb__ "0|4|
S41S40S8S9S4fS165A2M0A1M1S57S82A1S0G0S7S4fS165S1b1S166A4M2S0G0G2S4G0A1A3A3M3A3S40G1S57S83A1G3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vWant : sv := SVar 49.
Definition facts_RD (F : list sprop) : list sprop := ltac2:(tb__ "0|0|
ScS14S0S14S18S12Z1A1S58A2S0S14S18S58S12Z10000A1A2S0S14S18S180S16cS58A2S16bA2S4S14A1A3A3A3VF;A3").
Definition regs_RD : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S15P3cA1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S12Z10000A1S0S11S15P33A1S0S11S58S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16cS0S11S12Z3A1S0S11S16bS0S11S12S55A1S0S11S126S0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition RD_cut (cs : list cell) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S4eS24S1b1S151S173S26SdS11A1S6bVcs;A1S146VF;A1P65SbA9S59S12S53A1A3").
Definition RD0 : axst := RD_cut [] facts_R0f.
Definition RD1 : axst := ltac2:(tb__ "0|0|
S133S0S16S74S4S16A1A3S113A2").
Lemma RD_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS68A1S2A3S41S40S5S1eS43S68A1A1S2A3S41S40S5S4bS69A1S2A3S40S5S1eS43S69A1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_RDa : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P31S27S1c1S16bS16cA3A4S4G0A1A3").
Definition s_RDb : wsub := ltac2:(tb__ "0|1|
S0S9S50S11A2M0S7S50S11P31S12Z10000A1A4S4G0A1A3").
Lemma ent_RD : ltac2:(tb__ "0|2|
S41S40S5S48S6aS62S82U0M0A3S68S124A3S2A3S41S40S5S48S6aS62S82U1M1A3S68S125A3S2A3S41S40S5S48S6aS5fS83G0A3S69S124A3S2A3S40S5S48S6aS5fS83G1A3S69S125A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_RD__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S68S2A5").
Local Strategy expand [run_RD__R1].
Definition LV_RD0 : list leafA := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) run_RD__R1).
Definition run_RD__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S69S2A5").
Local Strategy expand [run_RD__R2].
Definition LV_RD1 : list leafA := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) run_RD__R2).
Definition E_rd0 : axst := Eval vm_compute in nthA RD0 LV_RD0 0.
Definition E_rd1 : axst := Eval vm_compute in nthA RD1 LV_RD1 0.
Lemma run_RD : ltac2:(tb__ "0|4|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54S68S2A5S6G0S0S45S4cS6dS166A2S4S45A1M3A3A2A3S40G1S44S52G2S54S69S2A5S6G0S0S45S4cS6eS166A2G3A3A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_RD__R1 <: run_RD__R1 = Some [mkLeafA E_rd0 RsCut]) (@eq_refl (option (list leafA)) run_RD__R2 <: run_RD__R2 = Some [mkLeafA E_rd1 RsCut])). Qed.
Lemma E_rd_pcs : ltac2:(tb__ "0|0|
S41S40S4fS1dS43S6dA1A1S1b9A3S40S4fS1dS43S6eA1A1S1b9A3A2"). Proof. split; reflexivity. Qed.

Definition rd_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S194S0S13S181S4S13A1A3A3").
Definition rd_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N8d0A1A3A2").
Definition rd_w2 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N920A1A3A2").
Definition rd_s1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1S64VE;A1S180S12S55A1S58A2A3A2").
Definition rd_rs (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S64VE;A1S5bS58S4S16A1A2A3A2").
Definition rd_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S46VE;S167S43VE;A1M0ScS13S19G0A1Sc1A3A2A2").
Definition rd_site (E : axst) : axst := ltac2:(tb__ "0|0|
S120Sc0Sc2S76S75S73VE;A1A1A1A1A1A1").
Definition C_rd0 : axst := Eval vm_compute in rd_site E_rd0.
Definition C_rd1 : axst := Eval vm_compute in rd_site E_rd1.
Lemma rd_pipe0 : ltac2:(tb__ "0|8|
S73S6dA1S42S75R1A1S42S76R1A1S42Sc2R1A1S42S41S40S5Sb9S6dA1S2A3S41S40S3S17A1M0S182S43R4A1U0M1S12N8d0A1A3S6S17S43R3A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R2A1M3A2A3S41S40G0S182G3S64R2A1S180S12S55A1S58A2A3S6S17S43R1A1M4A2A3S41S40S3S13A1S185S13S19G4A1S64R1A1M5A3S6S13S70S58S4S16A1M6A2A2A3S41S40S17S184G4G5S5bS58G6A2A3S43Sc0R1A1A1M7A3S41S40S5S189G4G7A2S2A3S40S42S122S6dA1S7dA3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma rd_pipe1 : ltac2:(tb__ "0|8|
S73S6eA1S42S75R1A1S42S76R1A1S42Sc2R1A1S42S41S40S5Sb9S6eA1S2A3S41S40S3S17A1M0S182S43R4A1U0M1S12N8d0A1A3S6S17S43R3A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R2A1M3A2A3S41S40G0S182G3S64R2A1S180S12S55A1S58A2A3S6S17S43R1A1M4A2A3S41S40S3S13A1S185S13S19G4A1S64R1A1M5A3S6S13S70S58S4S16A1M6A2A2A3S41S40S17S184G4G5S5bS58G6A2A3S43Sc0R1A1A1M7A3S41S40S5S189G4G7A2S2A3S40S42S122S6eA1S7eA3A2A2A2A2A2A2A2TA3;TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_rd (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS9S50S11A2M0S0G0S7S50S11PfS12S55A1A4S0G0S7S50S11P10S12Z10000A1A4S0G0S7S50S11P11S12Z0A1A4S0G0S7S50S11P13S58A4S4G0A1A3A3A3A3S1c5P1S43VC;A1S43S190A1A3A3").
Definition s_rd0 : wsub := Eval vm_compute in s_rd C_rd0.
Definition s_rd1 : wsub := Eval vm_compute in s_rd C_rd1.
Definition R_rd0 : list sobj := Eval vm_compute in optR (entails_frA C_rd0 Pre_rd s_rd0).
Definition R_rd1 : list sobj := Eval vm_compute in optR (entails_frA C_rd1 Pre_rd s_rd1).
Lemma fr_rd0 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7dS190Sc8A3S6G0Sa5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_rd1 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7eS190Sc9A3S6G0Sa6A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_rd0k : ltac2:(tb__ "0|0|
S40S5S196S7dS190Sc8Sa5S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_rd1k : ltac2:(tb__ "0|0|
S40S5S196S7eS190Sc9Sa6S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_after (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S19fS1fS43VCl;A1A1S198Vs;VPre;VL;VCl;VR;A5A2").

Definition T_rd0k' : axst := Eval vm_compute in T_after Pre_rd C_rd0 s_rd0 R_rd0 (P_rd [] 100).
Definition T_rd1k' : axst := Eval vm_compute in T_after Pre_rd C_rd1 s_rd1 R_rd1 (P_rd [] 100).
Definition T_rd0k : axst := Eval vm_compute in errL T_rd0k'.
Definition T_rd1k : axst := Eval vm_compute in errL T_rd1k'.
Lemma T_rd_eqs : ltac2:(tb__ "0|1|
S41S40S42S5aS190S7dSc8Sa5S192S4S16A1P64A2M0A5SadA3S41S40S42S5aS190S7eSc9Sa6G0A5SafA3S41S40S42S8bSadA1SacA3S41S40S42S8bSafA1SaeA3S41S40S5S8cSadA1S2A3S40S5S8cSafA1S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_T__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54SacS2A5").
Local Strategy expand [run_T__R1].
Definition LV_T0k : list leafA := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) run_T__R1).
Definition run_T__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54SaeS2A5").
Local Strategy expand [run_T__R2].
Definition LV_T1k : list leafA := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) run_T__R2).
Lemma run_T : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U3cM2S54SacS2A5S6G0Sd7A2A3S40G1S44S52G2S54SaeS2A5S6G0Sd8A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_T__R1 <: run_T__R1 = Some LV_T0k) (@eq_refl (option (list leafA)) run_T__R2 <: run_T__R2 = Some LV_T1k)). Qed.
Lemma LV_T_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd7A1S0G0S7S4fS165S1b8S166A4S0G0S7S4fS165S1b2S166A4S4G0A1A3A3M2A3S40G1S57Sd8A1G2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_S0__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S72S2A5").
Local Strategy expand [run_S0__R].
Definition LV_S0 : list leafA := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) run_S0__R).
Lemma run_S0 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U28S54S72S2A5S6G0S84A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S0__R <: run_S0__R = Some LV_S0). Qed.
Lemma LV_S0_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57S84A1S0G0S7S4fS165S1b1S166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_S0b__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S6aS72S84U0A3S2A5").
Local Strategy expand [run_S0b__R].
Definition E_s0 : axst := Eval vm_compute in ((fun ro8__ : option (list leafA) => nthA S0f ((match ro8__ with Some l => l | None => [] end)) 0) run_S0b__R).
Lemma run_S0b : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54S6aS72S84U0A3S2A5S6G0S0S45S4cS6fS166A2S4S45A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S0b__R <: run_S0b__R = Some [mkLeafA E_s0 RsCut]). Qed.
Lemma E_s0_pc : ltac2:(tb__ "0|0|
S40S4fS1dS43S6fA1A1S1b9A3"). Proof. reflexivity. Qed.

Definition rd_rsZ (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1S64VE;A1S5bS12S19aA1S4S16A1A2A3A2").
Definition rd_siteZ (E : axst) : axst := ltac2:(tb__ "0|0|
S120S121S76S75S73VE;A1A1A1A1A1").
Definition C_s0 : axst := Eval vm_compute in rd_siteZ E_s0.
Lemma s0_pipe : ltac2:(tb__ "0|6|
S73S6fA1S42S75R1A1S42S76R1A1S42S41S40S5Sb9S6fA1S2A3S41S40S3S17A1M0S182S43R3A1U0M1S12N8d0A1A3S6S17S43R2A1M2A2A3S41S40G0S182G2G1S12N920A1A3S6S17S43R1A1M3A2A3S41S40S3S13A1S185S13S19G3A1S64R1A1M4A3S6S13S17cA2A3S41S40S17S184G3G4S5bS12S19aA1S4S16A1A2A3S43S121R1A1A1M5A3S41S40S5S189G3G5A2S2A3S40S42S14eS6fA1S67A3A2A2A2A2A2A2TA2;TA1;TA0;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_s0 : wsub := Eval vm_compute in ([(15%positive, SLit RS); (16%positive, SLit CAP0); (17%positive, SLit 0); (19%positive, SLit CAP0)] ++ infer_sub 1 (ax_S C_s0) (ax_S Pre_rd)).
Definition R_s0 : list sobj := Eval vm_compute in optR (entails_frA C_s0 Pre_rd s_s0).
Lemma fr_s0 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S67S190S77A3S6G0S71A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_s0k : ltac2:(tb__ "0|0|
S40S5S196S67S190S77S71S18bS45S42S47S191S4S16A1P64A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_s0h : ltac2:(tb__ "0|0|
S40S5S196S67S190S77S71S18bS45S42S47S191S193P65A2A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_s0k' : axst := Eval vm_compute in T_after Pre_rd C_s0 s_s0 R_s0 (P_rd [] 100).
Definition T_s0h' : axst := Eval vm_compute in T_after Pre_rd C_s0 s_s0 R_s0 (P_rd hc 101).
Definition T_s0k : axst := Eval vm_compute in errL T_s0k'.
Definition T_s0h : axst := Eval vm_compute in errL T_s0h'.
Lemma T_s0_eqs : ltac2:(tb__ "0|0|
S41S40S42S5aS190S67S77S71S192S4S16A1P64A2A5Sb3A3S41S40S42S5aS190S67S77S71S192S193P65A2A5Sb1A3S41S40S42S8bSb3A1Sb2A3S41S40S42S8bSb1A1Sb0A3S41S40S5S8cSb3A1S2A3S40S5S8cSb1A1S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition run_S0T__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sb2S2A5").
Local Strategy expand [run_S0T__R1].
Definition LV_S0k : list leafA := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) run_S0T__R1).
Definition run_S0T__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sb0S2A5").
Local Strategy expand [run_S0T__R2].
Definition LV_S0h : list leafA := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) run_S0T__R2).
Lemma run_S0T : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U3cM2S54Sb2S2A5S6G0Sd6A2A3S40G1S44S52G2S54Sb0S2A5S6G0Sd5A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_S0T__R1 <: run_S0T__R1 = Some LV_S0k) (@eq_refl (option (list leafA)) run_S0T__R2 <: run_S0T__R2 = Some LV_S0h)). Qed.
Lemma LV_S0T_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd6A1S0G0S7S4fS165S1b8S166A4S0G0S7S4fS165S1b2S166A4S4G0A1A3A3M2A3S40G1S57Sd5A1G2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition selq : list nat := ltac2:(tb__ "0|2|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1U3S0S1UfS0S1U10M0S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U6S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1bS0S1U1cS4S1A1M1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU1dG0A2S0S1U2S0S1U2dS0S1U7S0S1U8S0S1U4S0S1U5G1A3A3A3A3A3A3A3A3").
Definition XF_q : list axform := ltac2:(tb__ "0|1|
S0S160S164S15dA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").
Definition q1 (E : axst) : axst := ltac2:(tb__ "0|0|
S106S161VE;S104A2VE;A2").

Definition q2 (w : sv) (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1U26S70Vw;S4S16A1A2A3A2").
Definition q3 (E : axst) : axst := ltac2:(tb__ "0|0|
S106S161VE;S0S160S162U26A1S4S160A1A3A2VE;A2").

Definition objs37 (A : axst) : list sobj := firstn 41 (ss_objs (ax_S A)).
Definition q4 (X : list (sv * sv)) (E : axst) : axst := ltac2:(tb__ "0|0|
S1bbS46VE;S167S43VE;A1S8eVE;A1A2A2VX;A2").
Definition qpipe (w : sv) (X : list (sv * sv)) (E : axst) : axst := ltac2:(tb__ "0|0|
S14dVX;S14cS11eVw;S14bVE;A1A2A1A2").
Definition q_okb (w : sv) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|5|
S3S42A1S5Lx;M0S161VE;S104A2S42S3S13A1S5Lx;S185S13S19S43R1A1A1M1U26M2A3S13SaSaS60R1S12S55A1S12Z0A1Vw;A4S189S43R2A1S43S11eVw;R2A2M3A1A2A2G0S161G3S0S160S162G2A1S4S160A1A3A2S42SaSaS186S9S13S13A2M4G4S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29G1A3Sc1A4A3S1bcSeS13G1A2U2bA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo;SbX3x2LA1;SbX3x2").

Definition Lcp1 : axst := Eval vm_compute in nthA R1c LV_T1k 0.
Definition Lcl1 : axst := Eval vm_compute in nthA R1c LV_T1k 1.
Definition Q1 : axst := Eval vm_compute in qpipe vWant X_R Lcp1.
Definition Hc1 : axst := Eval vm_compute in qpipe vWant X_R Lcl1.
Lemma q1_ok : ltac2:(tb__ "0|0|
S41S40S5SbcS58S59SefA3S2A3S41S40S42SbdS58S59SefA3S86A3S41S40S5SbcS58S59SeeA3S2A3S40S42SbdS58S59SeeA3S81A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Q1_objs : ltac2:(tb__ "0|2|
S41S40S8S13A1M0S19S43S86A1A1S6bS0S16S74S4S16A1A3A1M1A3S40G0S19S43S81A1A1G1A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition mc_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S1c9S0S13S181S0S13S1c8S4S13A1A3A3A3").
Definition ibS (St : sstate) (b lo : sv) : nat := ltac2:(tb__ "0|0|
S16eS19VSt;A1Vb;Vlo;A3").
Definition obind (x : option sstate) (f : sstate -> option sstate) : option sstate := ltac2:(tb__ "0|1|
S3S17A1M0G0Lx;Vx;S17Vf;R1A1LSt;SdS17A1X3x2").
Definition cp_w1 (St : sstate) : option sstate := split_obj_at St 0 (SLit (-2288)).
Definition cp_w2 (St : sstate) : option sstate := split_obj_at St 0 (SLit (-2368)).
Definition cp_b0 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z0A1A3S12Z4A1A3").
Definition cp_b1 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z4A1A3S16cA3").
Definition cp_b2 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS16cA3S180S16cVr;A2A3").
Definition cp_splits (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S5cS5cS5cS5cS10cVSt;A1S10dA2S138A2S139A2S13aVr;A1A2").
Definition O_dstC (r : sv) : sobj := ltac2:(tb__ "0|0|
S1bS180S16aS16cA2S12Z0A1Vr;S4S16A1S1aA5").
Definition O_dstL (r : sv) : sobj := ltac2:(tb__ "0|0|
S1bS16aS16cS180S16cVr;A2S4S16A1S1aA5").
Definition cp_rsd (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S16aS16cA3S12cVr;A1A3").
Definition cp_s1 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|1|
S182VSt;S56VSt;S12Z0A1S12S55A1M0A3S180G0Vr;A2A3").
Definition cp_rss (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S12Z0A1S12S55A1A3S5bVr;S4S16A1A2A3").
Definition cp_cv (St : sstate) : sstate := ltac2:(tb__ "0|0|
S167VSt;ScS13S19VSt;A1SbbA3A2").
Definition cp_site (r : sv) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S10bVr;S43VE;A1A2S17G0S88Vr;S109Vr;R1A2A2S17S6S42S46VE;Sb8S10aVr;R1A2A1A2A2LS7;SdS42A1M1X3x2LS5;G1X3x2").

Definition cp_okb (r : sv) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S10bVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS16cA3A3S13SaSaS60R1S16aS16cS180S16cVr;A2A4S189R2S109Vr;R2A2M3A2A2G0S88Vr;G3A2S17G1S185S13G2S56R1S12Z0A1M4S12S55A1M5A3A3S13SaS60R1G4G5S180G5Vr;A2A4S189R2S10aVr;R2A2A2A2Lo';SbX3x2LS7;SbX3x2A2Lo;SbX3x2LS5;SbX3x2").
Definition PreC : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.Pre_mc0.
Definition PostsC : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.Posts_mc.
Definition s_cp (r : sv) (C : axst) : wsub := ltac2:(tb__ "0|1|
ScS9S50S11A2M0S0G0S7S50S11PfS16aA4S0G0S7S50S11P10S16bA4S0G0S7S50S11P11S16cA4S0G0S7S50S11P13S12S55A1A4S0G0S7S50S11P34S12Z10000A1A4S0G0S7S50S11P35S12Z0A1A4S0G0S7S50S11P12Vr;A4S4G0A1A3A3A3A3A3A3A3S1c5P1S43VC;A1S43S65A1A3A3").

Definition vRes1 : sv := SVar 101.
Definition C_cp1 : axst := Eval vm_compute in ax_of (cp_site vRes1 Q1) Q1.
Lemma cp1_ok : ltac2:(tb__ "0|0|
S41S40S5S13bS5dS86A2S2A3S40S3S42A1S13cS5dS86A2S6S42S79A2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_cp1 : wsub := Eval vm_compute in s_cp vRes1 C_cp1.
Definition R_cp1 : list sobj := Eval vm_compute in optR (entails_frA C_cp1 PreC s_cp1).
Lemma fr_cp1 : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S79S65Sc3A3S6G0Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_cp1 : ltac2:(tb__ "0|0|
S40S5S196S79S65Sc3Sa0S18bS45S42S47SfbA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_cp1 : axst := Eval vm_compute in T_after PreC C_cp1 s_cp1 R_cp1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.P_icpt.
Lemma T_cp1_eq : ltac2:(tb__ "0|0|
S40S42S5aS65S79Sc3Sa0S1c7A5Sa7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_C1__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa7S2A5").
Local Strategy expand [run_C1__R].
Definition LV_C1 : list leafA := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) run_C1__R).
Lemma run_C1 : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa7S2A5S6G0Sd2A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_C1__R <: run_C1__R = Some LV_C1). Qed.
Lemma LV_C1_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Sd2A1S0G0S7S4fS165S1b5S166A4S0G0S7S4fS165S1a6S166A4S0G0S7S4fS165S19bS166A4S4G0A1A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition selb : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U2S0S1U14S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU15U1cA2S0S1U3S0S1U31S0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3A3").
Definition XF_bka : list axform := ltac2:(tb__ "0|1|
S0S160S164S15aA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition bk2 (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184S184VSt;UbS12dVr;A1A3U29S70Vr;S4S16A1A2A3").
Definition XF_bkb : list axform := ltac2:(tb__ "0|1|
S0S160S162U9A1M0S0S160G0S0S160G0S0S160S162U26A1S4S160A1A3A3A3A3").
Definition bkpipe (r : sv) (X : list (sv * sv)) (E : axst) : option axst := ltac2:(tb__ "0|4|
S3S42A1M0G0Lx;M1S161VE;S100A2S42G1S161S46R1S107Vr;S43R1A1M2A2A2S101A2S42S6S42S1bbS46R1S167G2S8eR1A1A2A2VX;A2A2LA3;SdS42A1M3X3x2LA1;G3X3x2").
Definition bk_okb (r : sv) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|8|
S3S42A1S5Lx;M0S161VE;S100A2S42S3S13A1S5Lx;M1S185S13S19S43R1A1A1M2UbA3S13G1S185S13S19S43R2A1A1U29M3A3S13SaSaSaS60R2S180S16aS16cA2S12Z0A1M4Vr;A4S60R1S12S55A1G4Vr;A4A2S189S43R3A1M5S107Vr;G5A2M6A2A2G0S161S46R3G6A2S101A2S42SaSaS186S9S13S13A2M7G7S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13G3G2A3SbbA4A3S1bcSeS13G2A2U2cA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo';SbX3x2Lo;SbX3x2LA1;SbX3x2").

Definition Lb1 : axst := Eval vm_compute in nthA R1c LV_C1 2.
Definition B1u : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lb1) Lb1.
Lemma bk1_ok : ltac2:(tb__ "0|0|
S41S40S5Sb4S5dS59Se9A3S2A3S40S3S42A1Sb5S5dS59Se9A3S6S42S92A2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma B1u_objs : ltac2:(tb__ "0|0|
S40S8S13A1S19S43S92A1A1S6bS0S16S74S4S16A1A3A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_bk1 : wsub := Eval vm_compute in infer_sub 1 (ax_S B1u) (ax_S R1c).
Definition len1' : sv := Eval vm_compute in wsub_get s_bk1 42%positive.
Definition F_bk1 : list sprop := ltac2:(tb__ "0|0|
S0S14S18S180S119S12Z1A1A2S16bA2S0S14S18S119S16bA2S4S14A1A3A3").
Lemma ent_bk1 : ltac2:(tb__ "0|0|
S40S5S48S19fS129S92A2S5fS156A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition PreM : axst := ltac2:(tb__ "0|0|
S1afS1aaS4S1acA1S1abA3").
Definition PostsM : list axst := ltac2:(tb__ "0|1|
S0S42S1adS1aaS4S1acA1M0S1abA3S0S42S1aeS1aaG0S1abA3S4S42A1A3A3").

Definition Lg1 : axst := Eval vm_compute in nthA R1c LV_C1 1.
Definition Lr1 : axst := Eval vm_compute in nthA R1c LV_C1 0.
Definition E_m : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lg1) Lg1.
Definition Lref : axst := Eval vm_compute in ax_of (bkpipe vRes1 X_R Lr1) Lr1.
Lemma bkg_ok : ltac2:(tb__ "0|1|
S41S40S5Sb4S5dS59Sf0A3S2A3S41S40S3S42A1M0Sb5S5dS59Sf0A3S6S42SccA2A3S41S40S5Sb4S5dS59Sf4A3S2A3S40G0Sb5S5dS59Sf4A3S6S42S9cA2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition two_cap : sv := SAlu ALU_SLL vCap (SLit 1).
Definition regs_G : list sv := ltac2:(tb__ "0|1|
S0S11S12Z0A1M0S0S11S12Z8c5ccA1S0S11S174S0S11S12Z10800A1S0S11S16dS0S11S15P3dA1S0S11S15P3eA1S0S11S15P3fA1S0S11S12Z2A1S0S11S16aS0S11S66S0S11S15P33A1S0S11S15P34A1S0S11S15P35A1S0S11S15P36A1S0S11S15P37A1S0S11S15P38A1S0S11S15P39A1S0S11S175S0S11S16bS0S11S12Z3A1S0S11S66S0S11S12S55A1S0S11S16aS0S11G0S0S11G0S0S11G0S0S11G0S0S11S15P3aA1S0S11S15P3bA1S0S11S15P40A1S0S11S15P41A1S4S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition facts_G : list sprop := ltac2:(tb__ "0|0|
S0S14S18S16bS12S1a1Z2Z19A2A1A2S114A3").
Definition G_cut : axst := ltac2:(tb__ "0|0|
S4eS24S1a6S14fS173S26SdS11A1S6bS0S16S74S4S16A1A3A1S145P65SbA9S59S12S53A1A3").
Lemma G_wf : ltac2:(tb__ "0|0|
S41S40S5S4bS61A1S2A3S40S5S1eS43S61A1A1S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition lenG : sv := add vRes1 vLen.
Definition E_mG : axst := Eval vm_compute in
  ax_setS E_m (mkSS (ss_pc (ax_S E_m)) (list_set (list_set (list_set (ss_regs (ax_S E_m)) 10 two_cap) 19 vCap) 21 two_cap)
                    (ss_fregs (ax_S E_m)) (ss_fcsr (ax_S E_m)) (ss_resv (ax_S E_m)) (ss_objs (ax_S E_m)) (ss_facts (ax_S E_m)) (ss_next (ax_S E_m)) (ss_lenient (ax_S E_m))).
Lemma E_mG_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SccA1M4S43ScdA1M5A2S6G3S7G1G2S0G0S7S11S11S27S1c0SbaS12Z1A1A3S66A4M6S0G0S7S11S11SbaS16bA4S0G0G6S4G0A1A3A3A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S40S5S188S14S25S23S1bdSbaS16bA3A1S1fG4A1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_G : wsub := Eval vm_compute in infer_sub 1 (ax_S E_mG) (ax_S G_cut).

Lemma ent_G : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S16bS12S1a1Z2Z19A2A1A2S4S14A1A3ScdA2S61S152A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition s_mG : wsub := Eval vm_compute in ((15%positive, SLit (- DEEP)) :: infer_sub 1 (ax_S G_cut) (ax_S PreM)).
Definition R_mG : list sobj := Eval vm_compute in optR (entails_frA G_cut PreM s_mG).
Lemma fr_mG : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S61S85S90A3S6G0S87A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mG : ltac2:(tb__ "0|0|
S40S5S197S61S85S90S87S131A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G_mnull : axst := Eval vm_compute in T_after PreM G_cut s_mG R_mG (L_malloc_null AE_A [] UStopLe).
Definition G_mok : axst := Eval vm_compute in T_after PreM G_cut s_mG R_mG (L_malloc_ok AE_A [] UStopLe).
Lemma G_m_eqs : ltac2:(tb__ "0|1|
S41S40S42S5aS85S61S90S87S1adS1aaS4S1acA1M0S1abA3A5S99A3S40S42S5aS85S61S90S87S1aeS1aaG0S1abA3A5S80A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vN' : positive := Eval vm_compute in match nth 10 (ss_regs (ax_S G_mok)) (SLit 0) with SVar v => v | _ => 1%positive end.
Lemma vN'_eq : ltac2:(tb__ "0|0|
S40S11S18fS11UaS22S43S80A1A1S12Z0A1A4S15S91A1A3"). Proof. reflexivity. Qed.
Definition run_G__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S99S2A5").
Local Strategy expand [run_G__R1].
Definition LV_Gnull : list leafA := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) run_G__R1).
Definition run_G__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S80S2A5").
Local Strategy expand [run_G__R2].
Definition LV_Gok : list leafA := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) run_G__R2).
Lemma run_G : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54S99S2A5S6G0Sd3A2A3S40G1S44S52G2S54S80S2A5S6G0Sd4A2A3A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_G__R1 <: run_G__R1 = Some LV_Gnull) (@eq_refl (option (list leafA)) run_G__R2 <: run_G__R2 = Some LV_Gok)). Qed.
Lemma LV_G_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57Sd3A1S0G0S7S4fS165S1b3S166A4S4G0A1M2A3A3S40G1S57Sd4A1S0G0S7S4fS165S1b8S166A4G2A3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_mc : axst := Eval vm_compute in nthA G_mok LV_Gok 0.

Definition mch_rtc : list sobj := ltac2:(tb__ "0|0|
S0S13S1cfS0S13S181S0S13S1ceS4S13A1A3A3A3").
Definition mc_kfacts : list sprop := ltac2:(tb__ "0|3|
S0S14S18S16bS66A2S0S14S18S180S16bS12Z1A1A2S66A2S0S14S18S15S91A1M0S12S176A1M1A2S0S14S18S180G0S66A2M2G1A2S0S14S18S12S177A1G0A2S0S14S18G2S171A2S0S14S18G0S171A2S4S14A1A3A3A3A3A3A3A3").
Definition E_mcf : axst := ax_add_facts mc_kfacts E_mc.
Definition mc_w1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N870A1A3A2").
Definition mc_w2 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1U0S12N8c0A1A3A2").
Definition inew (E : axst) : nat := ltac2:(tb__ "0|0|
S16eS19S43VE;A1A1S15S91A1S12Z0A1A3").
Definition mc_b1 (E : axst) : axst := ltac2:(tb__ "0|0|
S6cVE;S182S43VE;A1S118VE;A1S16bA3A2").
Definition mc_cv (E : axst) : axst := ltac2:(tb__ "0|1|
S46VE;S167S43VE;A1M0ScS13S19G0A1S11dA3A2A2").
Definition mc_site (E : axst) : axst := ltac2:(tb__ "0|0|
S147S11aS11cS11bVE;A1A1A1A1").
Definition C_mc : axst := Eval vm_compute in mc_site E_mcf.
Lemma mc_pipe : ltac2:(tb__ "0|5|
S11bS98A1S42S11cR1A1S42S11aR1A1S42S41S40S5S186S14S3aS1cS43S128A1M0A1A1ScS14S148S1fG0A1A3A3S2A3S41S40S3S17A1M1S182S43S98A1U0M2S12N870A1A3S6S17S43R3A1M3A2A3S41S40G1S182G3G2S12N8c0A1A3S6S17S43R2A1M4A2A3S41S40G1S182G4S118R2A1S16bA3S6S17S43R1A1A2A3S40S42S149S98A1S7cA3A2A2A2A2TA3;TA2;TA1;").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition PreMC : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr.Pre_mc0.
Definition PostsMC : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr.Posts_mc.
Definition s_mc : wsub := Eval vm_compute in
  ([(15%positive, SVar vN'); (16%positive, two_cap); (19%positive, vB); (52%positive, vCap); (18%positive, vCap); (54%positive, vH)]
   ++ infer_sub 1 (ax_S C_mc) (ax_S PreMC)).
Definition R_mc : list sobj := Eval vm_compute in optR (entails_frA C_mc PreMC s_mc).
Lemma fr_mc : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7cS9fSc7A3S6G0Sa4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_mc : ltac2:(tb__ "0|0|
S40S5S196S7cS9fSc7Sa4S18bS45S42S47S132A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T_mc : axst := Eval vm_compute in T_after PreMC C_mc s_mc R_mc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr.P_icpt.
Lemma T_mc_eq : ltac2:(tb__ "0|0|
S40S42S5aS9fS7cSc7Sa4S1d0A5SabA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_mc__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U1eS54SabS2A5").
Local Strategy expand [run_mc__R].
Definition LV_mc : list leafA := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) run_mc__R).
Lemma run_mc : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U1eS54SabS2A5S6G0Se2A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_mc__R <: run_mc__R = Some LV_mc). Qed.
Lemma LV_mc_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Se2A1S0G0S7S4fS165S1a7S166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_f : axst := Eval vm_compute in nthA T_mc LV_mc 0.

Definition self : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U2S0S1UaS0S1U3S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU13U1cA2S0S1U2fS0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3").
Definition XF_f : list axform := ltac2:(tb__ "0|2|
S0S160S164S15cA1S0S160S163U0M0A1S0S160S163U1A1S0S160S163U2A1S0S160S162G0A1M1S0S160G1S0S160S162U9A1S4S160A1A3A3A3A3A3A3A3").
Definition X_G : list (sv * sv) := ltac2:(tb__ "0|1|
ScS9S11S11A2M0S0G0S7S11S11S12Z14d80A1S12Z40A1A4S0G0S7S11S11S180S170S12S1a3S1a0S16fZ80A2A1A1A2S12S16fA1A4S0G0S7S11S11S15S91A1S66A4S0G0S179S4G0A1A3A3A3A3S1caA3").
Definition F1 : axst := Eval vm_compute in ax_of (apply_axforms E_f XF_f) E_f.
Lemma F1_eq : ltac2:(tb__ "0|0|
S40S3S42A1S161S127S135A2S6S42Sd0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F2 : axst := Eval vm_compute in ax_setX F1 X_G.

Definition objs38 (A : axst) : list sobj := firstn 42 (ss_objs (ax_S A)).
Lemma F2_objs : ltac2:(tb__ "0|0|
S41S40S8S13A1S19S43Sd1A1A1ScS13S14aSd1A1S11dA3A3S40S5S1a9S136S4aSd0A1A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_f : axst := Eval vm_compute in ax_setS F2 (set_objs (ax_S F2) (objs38 F2)).
Definition s_f : wsub := Eval vm_compute in ([(15%positive, SLit (- DEEP)); (12%positive, vB); (13%positive, vCap)] ++ infer_sub 1 (ax_S C_f) (ax_S PreF)).
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA C_f PreF s_f).
Lemma fr_f : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S94S172Sc6A3S6G0Sa3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_f : ltac2:(tb__ "0|0|
S40S5S197S94S172Sc6Sa3S0S42S178S4S42A1A3A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_f : axst := Eval vm_compute in T_after PreF C_f s_f R_f PostF.
Lemma T_f_eq : ltac2:(tb__ "0|0|
S40S42S5aS172S94Sc6Sa3S178A5SaaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U1eS54SaaS2A5").
Local Strategy expand [run_f__R].
Definition LV_f : list leafA := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) run_f__R).
Lemma run_f : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U1eS54SaaS2A5S6G0SdeA2A3"). Proof. exact (@eq_refl (option (list leafA)) run_f__R <: run_f__R = Some LV_f). Qed.
Lemma LV_f_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57SdeA1S0G0S7S4fS165S19bS166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lg : axst := Eval vm_compute in nthA T_f LV_f 0.
Definition Bg : axst := Eval vm_compute in ax_of (apply_axforms Lg [AXRebase 0]) Lg.
Lemma Bg_eq : ltac2:(tb__ "0|0|
S40S3S42A1S161S12aS0S160S163U0A1S4S160A1A3A2S6S42S93A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Bg_objs : ltac2:(tb__ "0|0|
S40S1SeS13S19S43S93A1A1A2U29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s_bkG : wsub := Eval vm_compute in
  ([(40%positive, SVar vN'); (41%positive, two_cap); (42%positive, vCap); (45%positive, SExt true 32 vH)] ++ infer_sub 1 (ax_S Bg) (ax_S R1c)).
Lemma ent_bkG : ltac2:(tb__ "0|0|
S40S5S48S93S5fS157A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Ls0k : axst := Eval vm_compute in nthA S0f LV_S0k 0.
Definition Lc0k : axst := Eval vm_compute in nthA S0f LV_S0k 1.
Definition Ls0h : axst := Eval vm_compute in nthA S0f LV_S0h 0.
Definition selqZ : list nat := ltac2:(tb__ "0|2|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1U3S0S1UfS0S1U10M0S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U6S0S1U16S0S1U17S0S1U18S0S1U19S0S1U1aS0S1U1bS0S1U1cS4S1A1M1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU1dG0A2S0S1U2S0S1U7S0S1U8S0S1U4S0S1U5G1A3A3A3A3A3A3A3").
Definition XF_qz : list axform := ltac2:(tb__ "0|1|
S0S160S164S15eA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition rds_cellsL (cs : list cell) : list cell := ltac2:(tb__ "0|1|
S18bS16S16S16S28S11S11Lx;S32R1A1S4fS12S1a0S55R1A2A1Lz;S50S180S12S55A1M0S15R1A1A2Li;S1beS11S11S180G0S27R3R2R1A3A2Lb;La;Lop;S1beS11S11S180G0S2eR3R2R1A3A2Lb;La;Lop;S1bfS11S11S180G0S30R3R2R1A3A2Lb;La;Lop;S1bfS11S11S180G0S31R3R2R1A3A2Lb;La;Lop;S5S51S11S180G0S2aR3R2R1A3A2La;Lw;Lsgn;S50S11S4fS180G0S2fR3R2R1A3A2Lk;Li;Ll;X11x8S34R1A1S33R1A1A3Lc;Vcs;A4").
Definition qz2 (cs : list cell) (E : axst) : axst := ltac2:(tb__ "0|0|
S46VE;S184S43VE;A1U26S1bS12Z0A1S12S55A1S12S1a0S55Z10000A2A1S8fVcs;A1S1aA5A3A2").
Definition qzpipe (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|1|
S3S42A1M0G0Lx;S161VE;S105A2S42S11fVcs;R1A2S42S6S42S1bbS46R1S167S43R1A1S8eR1A1A2A2S199A2A2TA2;LA1;SdS42A1X3x2").
Definition qz_okb (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|3|
S3S42A1S5Lx;S161VE;S105A2S42S3S13A1S5Lx;S185S13S19S43R1A1A1U26A3S13SaSaSaSaS49R1S1bS12S55A1S12Z0A1S12Z10000A1Vcs;S1aA5A2S189S43R2A1M0S43S11fVcs;R2A2A1A2A2S186S9S13S13A2M1G1S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29S19G0A1M2A3Sc1A4A3A2S1bcSeS13G2A2U2bA2A2S1a9S199S4aR2A1A2A2Lo;SbX3x2LA1;SbX3x2").
Definition hcZ : list cell := ltac2:(tb__ "0|0|
S0S16S28S12Z0A1Z4S15P64A1A3S4S16A1A3").
Definition QZk : axst := Eval vm_compute in ax_of (qzpipe [] Ls0k) Ls0k.
Definition QZh : axst := Eval vm_compute in ax_of (qzpipe hcZ Ls0h) Ls0h.
Definition HcZ : axst := Eval vm_compute in ax_of (qzpipe [] Lc0k) Lc0k.
Lemma qz_ok : ltac2:(tb__ "0|2|
S41S40S5SbeS4S16A1M0Sf6A2S2A3S41S40S3S42A1M1SbfG0Sf6A2S6S42SfeA2A3S41S40S5SbeS63Sf5A2S2A3S41S40G1SbfS63Sf5A2S6S42SfcA2A3S41S40S5SbeG0SecA2S2A3S40G1SbfG0SecA2S6S42S9bA2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cz_b1 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S16aS12Z0A1A3Vr;A3").
Definition cz_splits (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S5cS5cS10cVSt;A1S10dA2S13dVr;A1A2").
Definition O_dstZ (r : sv) : sobj := ltac2:(tb__ "0|1|
S1bS180S16aS12Z0A1M0A2G0Vr;S4S16A1S1aA5").
Definition cz_rsd (r : sv) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;S56VSt;S16aS12Z0A1A3S12eVr;A1A3").
Definition cz_site (r : sv) (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S8aVr;S43VE;A1A2S17G0S88Vr;S89Vr;R1A2A2S17S6S42S46VE;Sb8S184R1S56R1S12Z0A1S12S55A1A3S5bVr;Vcs;A2A3A1A2A2LS5;SdS42A1M1X3x2LS3;G1X3x2").
Definition cz_okb (r : sv) (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S8aVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS12Z0A1M3A3A3S13SaSaS60R1S16aG3Vr;A4S189R2S89Vr;R2A2M4A2A2G0S88Vr;G4A2S17G1S185S13G2S56R1G3S12S55A1M5A3A3S13SaS49R1S1bG3G5S180G5Vr;A2S8fVcs;A1S1aA5A2S189R2S184R2S56R2G3G5A3S5bVr;Vcs;A2A3A2A2Lo';SbX3x2LS5;SbX3x2A2Lo;SbX3x2LS3;SbX3x2").
Definition s_cz (r : sv) (C Pre : axst) : wsub := ltac2:(tb__ "0|2|
ScS9S50S11A2M0S0G0S7S50S11PfS16aA4S0G0S7S50S11P10S12S19aA1A4S0G0S7S50S11P11S12Z0A1M1A4S0G0S7S50S11P13S12S55A1A4S0G0S7S50S11P34S12Z10000A1A4S0G0S7S50S11P35G1A4S0G0S7S50S11P12Vr;A4S4G0A1A3A3A3A3A3A3A3S1c5P1S43VC;A1S43VPre;A1A3A3").

Definition vRes0 : sv := SVar 100.
Definition QZkf : axst := ltac2:(tb__ "0|0|
S19fS0S14S18S78S12Z3A1A2S4S14A1A3SfeA2").
Definition C_czk : axst := Eval vm_compute in ax_of (cz_site vRes0 [] QZkf) QZkf.
Lemma czk_ok : ltac2:(tb__ "0|1|
S41S40S5S13eS78S4S16A1M0SffA3S2A3S40S3S42A1S13fS78G0SffA3S6S42S7bA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_czk : wsub := Eval vm_compute in s_cz vRes0 C_czk PreC.
Definition R_czk : list sobj := Eval vm_compute in optR (entails_frA C_czk PreC s_czk).
Lemma fr_czk : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7bS65Sc5A3S6G0Sa2A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_czk : ltac2:(tb__ "0|0|
S40S5S196S7bS65Sc5Sa2S18bS45S42S47SfbA4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_czk : axst := Eval vm_compute in T_after PreC C_czk s_czk R_czk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.P_icpt.
Lemma T_czk_eq : ltac2:(tb__ "0|0|
S40S42S5aS65S7bSc5Sa2S1c7A5Sa9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_Zk__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa9S2A5").
Local Strategy expand [run_Zk__R].
Definition LV_Zk : list leafA := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) run_Zk__R).
Lemma run_Zk : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa9S2A5S6G0SdaA2A3"). Proof. exact (@eq_refl (option (list leafA)) run_Zk__R <: run_Zk__R = Some LV_Zk). Qed.
Lemma LV_Zk_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57SdaA1S0G0S7S4fS165S19bS166A4S4G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition vResH : sv := SVar 101.
Definition PreCH : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs.Pre_mc0.
Definition PostsCH : list leafA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs.Posts_mc.
Definition QZhf : axst := ltac2:(tb__ "0|0|
S19fS0S14S18S12Z4A1S5eA2S4S14A1A3SfcA2").
Definition czh_h1 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S12Z0A1S12S55A1A3S12S1a0S55Z4A2A1A3").
Definition czh_h2 (r : sv) (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S182VSt;S56VSt;S12Z0A1S12S1a0S55Z4A2A1A3S180S12S55A1Vr;A2A3").
Definition czh_h3 (St : sstate) : option sstate := ltac2:(tb__ "0|0|
S183VSt;S56VSt;S12Z0A1S12S55A1A3A2").
Definition czh_site (r : sv) (cs : list cell) (E : axst) : option axst := ltac2:(tb__ "0|2|
S3S17A1S3S42A1Lx;M0S8aVr;S43VE;A1A2S17G0S5cS5cS10eS89Vr;R1A2A1S10fVr;A1A2S110A2S17S6S42S46VE;Sb8S184R1S56R1S12Z0A1S12S55A1A3S5bVr;Vcs;A2A3A1A2A2LS6;SdS42A1M1X3x2LS3;G1X3x2").
Definition czh_okb (r : sv) (cs : list cell) (E : axst) : bool := ltac2:(tb__ "0|6|
S3S17A1S5Lx;M0S8aVr;S43VE;A1A2S17S3S13A1S5Lx;M1S185S13S19R1A1M2S56R1S16aS12Z0A1M3A3A3S13SaSaS60R1S16aG3Vr;A4S189R2S89Vr;R2A2M4A2A2G0S5cS5cS10eG4A1S10fVr;A1A2S110A2S17G1S185S13G2S56R1G3S12S55A1M5A3A3S13SaS49R1S1bG3G5S180G5Vr;A2S8fVcs;A1S1aA5A2S189R2S184R2S56R2G3G5A3S5bVr;Vcs;A2A3A2A2Lo';SbX3x2LS6;SbX3x2A2Lo;SbX3x2LS3;SbX3x2").
Definition C_czh : axst := Eval vm_compute in ax_of (czh_site vResH hcZ QZhf) QZhf.
Lemma czh_ok : ltac2:(tb__ "0|0|
S41S40S5S140S5eS63SfdA3S2A3S40S3S42A1S141S5eS63SfdA3S6S42S7aA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_czh : wsub := Eval vm_compute in ((54%positive, SVar 100) :: s_cz vResH C_czh PreCH).
Definition R_czh : list sobj := Eval vm_compute in optR (entails_frA C_czh PreCH s_czh).
Lemma fr_czh : ltac2:(tb__ "0|1|
S40S3S8S13A1M0A1S195S7aS9eSc4A3S6G0Sa1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_czh : ltac2:(tb__ "0|0|
S40S5S196S7aS9eSc4Sa1S18bS45S42S47S130A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_czh : axst := Eval vm_compute in T_after PreCH C_czh s_czh R_czh OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs.P_icpt.
Lemma T_czh_eq : ltac2:(tb__ "0|0|
S40S42S5aS9eS7aSc4Sa1S1d1A5Sa8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_Zh__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U3cS54Sa8S2A5").
Local Strategy expand [run_Zh__R].
Definition LV_Zh : list leafA := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) run_Zh__R).
Lemma run_Zh : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U3cS54Sa8S2A5S6G0Sd9A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_Zh__R <: run_Zh__R = Some LV_Zh). Qed.
Lemma LV_Zh_pcs : ltac2:(tb__ "0|1|
S40S8S9S4fS165A2M0A1S57Sd9A1S0G0S7S4fS165S1a6S166A4S0G0S7S4fS165S19bS166A4S4G0A1A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition selbZ : list nat := ltac2:(tb__ "0|1|
ScS1S0S1U9S0S1U1S0S1U0S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U2S0S1U12S4S1A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3ScS1S18dU13U1cA2S0S1U3S0S1U2fS0S1U7S0S1U8S0S1U4S0S1U5S0S1U6G0A3A3A3A3A3A3A3A3A3").
Definition XF_bkza : list axform := ltac2:(tb__ "0|1|
S0S160S164S15bA1S0S160S163U1A1S0S160S163U2A1S0S160S162U0A1M0S0S160G0S4S160A1A3A3A3A3A3").

Definition bkz2 (r : sv) (cd cs : list cell) (St : sstate) : sstate := ltac2:(tb__ "0|0|
S184VSt;U27S70Vr;S8fVcs;A1A2A3").
Definition XF_bkzb : list axform := ltac2:(tb__ "0|0|
S0S160S162U9A1S0S160S162U26A1S4S160A1A3A3").
Definition bkzpipe (r : sv) (cd cs : list cell) (X : list (sv * sv)) (E : axst) : option axst := ltac2:(tb__ "0|4|
S3S42A1M0G0Lx;M1S161VE;S102A2S42G1S161S46R1S108Vr;Vcd;Vcs;S43R1A1M2A4A2S103A2S42S6S42S1bbS46R1S167G2S8eR1A1A2A2VX;A2A2LA3;SdS42A1M3X3x2LA1;G3X3x2").
Definition bkz_okb (r : sv) (cd cs : list cell) (X : list (sv * sv)) (E : axst) : bool := ltac2:(tb__ "0|7|
S3S42A1S5Lx;M0S161VE;S102A2S42S3S13A1S5Lx;M1S185S13S19S43R1A1A1M2U9A3S13G1S185S13S19S43R2A1A1U27A3S13SaSaSaS49R2S1bS16aS12Z0A1M3Vr;Vcd;S1aA5A2S49R1S1bS12S55A1G3Vr;Vcs;S1aA5A2A2S189S43R3A1M4S108Vr;Vcd;Vcs;G4A4M5A2A2G0S161S46R3G5A2S103A2S42SaSaS186S9S13S13A2M6G6S49SfS13S13R1A3S10S13S13R1A3A2Lp;S187S13S13S18cS13U29G2A3SbbA4A3S1bcSeS13G2A2U2cA2A2S1a9VX;S4aR1A1A2A2LA3;SbX3x2A2Lo';SbX3x2Lo;SbX3x2LA1;SbX3x2").

Definition LbZk : axst := Eval vm_compute in nthA S0f LV_Zk 0.
Definition BZku : axst := Eval vm_compute in ax_of (bkzpipe vRes0 [] [] X_R0 LbZk) LbZk.
Lemma bkzk_ok : ltac2:(tb__ "0|1|
S41S40S5Sb6S78S4S16A1M0G0S199SebA5S2A3S40S3S42A1Sb7S78G0G0S199SebA5S6S42ScbA2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_bkZk : wsub := Eval vm_compute in ([(42%positive, vRes0); (41%positive, SLit CAP0)] ++ infer_sub 1 (ax_S BZku) (ax_S R0c)).
Lemma ent_bkZk : ltac2:(tb__ "0|0|
S40S5S48ScbS62S159A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition hcD : list cell := ltac2:(tb__ "0|0|
S0S16S28S12Z0A1Z4S2aS2Q20S15P64A1A3A3S4S16A1A3").
Definition LbZh : axst := Eval vm_compute in nthA S0f LV_Zh 1.
Definition LgZh : axst := Eval vm_compute in nthA S0f LV_Zh 0.
Definition BZhu : axst := Eval vm_compute in ax_of (bkzpipe vResH hcD hcZ X_R0 LbZh) LbZh.
Definition E_mZ : axst := Eval vm_compute in ax_of (bkzpipe vResH hcD hcZ X_R0 LgZh) LgZh.
Lemma bkzh_ok : ltac2:(tb__ "0|1|
S41S40S5Sb6S5eS8dS63S199SeaA5S2A3S41S40S3S42A1M0Sb7S5eS8dS63S199SeaA5S6S42ScaA2A3S41S40S5Sb6S5eS8dS63S199Sf1A5S2A3S40G0Sb7S5eS8dS63S199Sf1A5S6S42SceA2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_bkZh : wsub := Eval vm_compute in ([(42%positive, vResH); (41%positive, SLit CAP0); (45%positive, SExt true 32 (SVar 100))] ++ infer_sub 1 (ax_S BZhu) (ax_S R1c)).
Lemma ent_bkZh : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S180S5eS12Z1A1A2S12S19aA1A2S4S14A1A3ScaA2S5fS158A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mZG : axst := Eval vm_compute in
  ax_setS E_mZ (mkSS (ss_pc (ax_S E_mZ)) (list_set (ss_regs (ax_S E_mZ)) 19 (SLit CAP0))
                     (ss_fregs (ax_S E_mZ)) (ss_fcsr (ax_S E_mZ)) (ss_resv (ax_S E_mZ)) (ss_objs (ax_S E_mZ)) (ss_facts (ax_S E_mZ)) (ss_next (ax_S E_mZ)) (ss_lenient (ax_S E_mZ))).
Lemma E_mZG_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SceA1M4S43ScfA1M5A2S6G3S7G1G2S0G0S7S11S11S5eS12S19aA1M6A4S4G0A1A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S40S5S188S14S25S23S1bdS5eG6A3A1S1fG4A1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_GZ : wsub := Eval vm_compute in ([(41%positive, SLit CAP0); (45%positive, SExt true 32 (SVar 100))] ++ infer_sub 1 (ax_S E_mZG) (ax_S G_cut)).
Lemma ent_GZ : ltac2:(tb__ "0|0|
S40S5S48ScfS61S153A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lcl0 : axst := Eval vm_compute in nthA R0c LV_T0k 1.
Definition Hc0 : axst := Eval vm_compute in qpipe vWant X_R Lcl0.
Lemma q0_ok : ltac2:(tb__ "0|0|
S41S40S5SbcS58S59SedA3S2A3S40S42SbdS58S59SedA3S9aA3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_c__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S81S2A5").
Local Strategy expand [run_c__R1].
Definition LV_c1 : list leafA := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) run_c__R1).
Definition run_c__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S9aS2A5").
Local Strategy expand [run_c__R2].
Definition LV_c0 : list leafA := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) run_c__R2).
Definition run_c__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U28S54S9bS2A5").
Local Strategy expand [run_c__R3].
Definition LV_cZ : list leafA := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) run_c__R3).
Lemma run_c : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U28M2S54S81S2A5S6G0SdcA2A3S41S40G1S44S52G2S54S9aS2A5S6G0SdbA2A3S40G1S44S52G2S54S9bS2A5S6G0SddA2A3A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_c__R1 <: run_c__R1 = Some LV_c1) (conj (@eq_refl (option (list leafA)) run_c__R2 <: run_c__R2 = Some LV_c0) (@eq_refl (option (list leafA)) run_c__R3 <: run_c__R3 = Some LV_cZ))). Qed.
Lemma LV_c_pcs : ltac2:(tb__ "0|3|
S41S40S8S9S4fS165A2M0A1M1S57SdcA1S0G0S7S4fS165S1baS166A4S4G0A1A3M2A3S41S40G1S57SdbA1G2A3S40G1S57SddA1G2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_cl1 : axst := Eval vm_compute in nthA R1c LV_c1 0.
Definition E_cl0 : axst := Eval vm_compute in nthA R0c LV_c0 0.
Definition E_clZ : axst := Eval vm_compute in nthA S0f LV_cZ 0.
Lemma E_cl_regs : ltac2:(tb__ "0|7|
S41S40S9S11S11A2M0S7S11S11S21S43S96A1M1Z11M2A2S21G1ZaM3A2A4S7S11S11S12Z39A1S12Z3A1A4M4A3S41S40G0S7S11S11S21S43S95A1M5G2A2S21G5G3A2A4G4A3S40G0S7S11S11S21S43S97A1M6G2A2S21G6G3A2A4G4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run_h__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S96S12Z0A1A2S2A5").
Local Strategy expand [run_h__R1].
Definition LV_h1 : list leafA := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) run_h__R1).
Definition run_h__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S95S12Z0A1A2S2A5").
Local Strategy expand [run_h__R2].
Definition LV_h0 : list leafA := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) run_h__R2).
Definition run_h__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U78S54S1a4S97S12Z0A1A2S2A5").
Local Strategy expand [run_h__R3].
Definition LV_hZ : list leafA := Eval vm_compute in ((fun ro23__ : option (list leafA) => (match ro23__ with Some l => l | None => [] end)) run_h__R3).
Lemma run_h : ltac2:(tb__ "0|4|
S41S40S3S8S45A1M0A1M1S44S52U78M2S54S1a4S96S12Z0A1M3A2S2A5S6G0Se0A2A3S41S40G1S44S52G2S54S1a4S95G3A2S2A5S6G0SdfA2A3S40G1S44S52G2S54S1a4S97G3A2S2A5S6G0Se1A2A3A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_h__R1 <: run_h__R1 = Some LV_h1) (conj (@eq_refl (option (list leafA)) run_h__R2 <: run_h__R2 = Some LV_h0) (@eq_refl (option (list leafA)) run_h__R3 <: run_h__R3 = Some LV_hZ))). Qed.
Lemma LV_h_pcs : ltac2:(tb__ "0|5|
S41S40S8S9S4fS165A2M0A1M1S57Se0A1S0G0S7S4fS165S1b6S166A4M2S0G0S7S4fS165S1b4S166A4S0G0S7S4fS165S1a8S166A4S4G0A1M3A3A3A3A3S41S40G1S57SdfA1S0G0G2G3A3M4A3S40G1S57Se1A1G4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ltr : axst := Eval vm_compute in nthA R1c LV_h1 2.
Definition clen_x : sv := Eval vm_compute in nth 11 (ss_regs (ax_S Ltr)) (SLit 0).
Definition plen_x : sv := Eval vm_compute in nth 13 (ss_regs (ax_S Ltr)) (SLit 0).
Definition flg_x : sv := Eval vm_compute in nth 21 (ss_regs (ax_S Ltr)) (SLit 0).

Definition setregA (A : axst) (k : nat) (v : sv) : axst := ltac2:(tb__ "0|1|
S46VA;S24S1dS43VA;A1M0A1S169S11S22G0A1Vk;Vv;A4S3cG0A1S3bG0A1S3eG0A1S19G0A1S1fG0A1S1cG0A1S3dG0A1A9A2").
Definition LtrR : axst := Eval vm_compute in setregA Ltr 23 (SLit 0).
Lemma LtrR_diff : ltac2:(tb__ "0|7|
S41S40S3S9S8S9S11S11A2M0A1M1S8S14A1M2A2M3A1S18aS43SfaA1M4S43S9dA1M5A2S6G3S7G1G2S0G0S7S11S11S5dS12Z0A1M6A4S4G0A1A3S4S14A1A4A2A3S41S40S5S1eG5A1S2A3S41S40S50S1cG5A1S1cG4A1A3S41S40S5S188S14S25S2cS23S1c2S5dG6A3A1A1S1fG4A1A3S2A3S40S42S15fSfaU17G6A3S9dA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_T : wsub := Eval vm_compute in
  ([(43%positive, clen_x); (44%positive, plen_x); (46%positive, flg_x)] ++ infer_sub 1 (ax_S LtrR) (ax_S S_T)).

Lemma ent_T : ltac2:(tb__ "0|0|
S40S5S48S19fS0S14S18S137S12Z7fffA1A2S4S14A1A3S9dA2S17dS155A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Loom : axst := Eval vm_compute in nthA G_cut LV_Gnull 0.
Definition run_oom__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf2S2A5").
Local Strategy expand [run_oom__R].
Definition LV_oom : list leafA := Eval vm_compute in ((fun ro24__ : option (list leafA) => (match ro24__ with Some l => l | None => [] end)) run_oom__R).
Lemma run_oom : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54Sf2S2A5S6G0Se3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_oom__R <: run_oom__R = Some LV_oom). Qed.
Lemma LV_oom_pcs : ltac2:(tb__ "0|4|
S40S8S9S9S4fS165A2M0S8S11A1M1A2M2A1S18bS45G2S45S7G0G1S7S4fS165S1dS43S47R1A1A1M3A1S4dR1A1A4S18eS11U4S18cS11UaS22G3A1A3A3A4LL;Se3A4S0G2S7G0G1S7S4fS165S1b0S166A4S0S11S12Z14d9dA1S0S11S12Z13A1S0S11S12Z1A1S0S11S12S1c3A1S4S11A1A3A3A3A3A4S4G2A1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run_ref__R : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54S9cS2A5").
Local Strategy expand [run_ref__R].
Definition LV_ref : list leafA := Eval vm_compute in ((fun ro25__ : option (list leafA) => (match ro25__ with Some l => l | None => [] end)) run_ref__R).
Lemma run_ref : ltac2:(tb__ "0|1|
S40S3S8S45A1M0A1S44S52U14S54S9cS2A5S6G0Se5A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_ref__R <: run_ref__R = Some LV_ref). Qed.
Lemma LV_ref_pcs : ltac2:(tb__ "0|4|
S40S8S9S9S4fS165A2M0S8S11A1M1A2M2A1S18bS45G2S45S7G0G1S7S4fS165S1dS43S47R1A1A1M3A1S4dR1A1A4S18eS11U3S18cS11UaS22G3A1A3A3A4LL;Se5A4S0G2S7G0G1S7S4fS165S1c6S166A4S0S11S12S1c3A1S0S11S12Z1a787A1S0S11S12Z4000000A1S4S11A1A3A3A3A4S4G2A1A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Lsh1 : axst := Eval vm_compute in nthA R1c LV_h1 0.
Definition Lov1 : axst := Eval vm_compute in nthA R1c LV_h1 1.
Definition Lsh0 : axst := Eval vm_compute in nthA R0c LV_h0 0.
Definition LshZ : axst := Eval vm_compute in nthA S0f LV_hZ 0.
Definition run_sh__R1 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf8S2A5").
Local Strategy expand [run_sh__R1].
Definition LV_sh1 : list leafA := Eval vm_compute in ((fun ro26__ : option (list leafA) => (match ro26__ with Some l => l | None => [] end)) run_sh__R1).
Definition run_sh__R2 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf3S2A5").
Local Strategy expand [run_sh__R2].
Definition LV_ov1 : list leafA := Eval vm_compute in ((fun ro27__ : option (list leafA) => (match ro27__ with Some l => l | None => [] end)) run_sh__R2).
Definition run_sh__R3 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf7S2A5").
Local Strategy expand [run_sh__R3].
Definition LV_sh0 : list leafA := Eval vm_compute in ((fun ro28__ : option (list leafA) => (match ro28__ with Some l => l | None => [] end)) run_sh__R3).
Definition run_sh__R4 : option (list leafA) := ltac2:(tb__ "0|0|
S44S52U14S54Sf9S2A5").
Local Strategy expand [run_sh__R4].
Definition LV_shZ : list leafA := Eval vm_compute in ((fun ro29__ : option (list leafA) => (match ro29__ with Some l => l | None => [] end)) run_sh__R4).
Lemma run_sh : ltac2:(tb__ "0|3|
S41S40S3S8S45A1M0A1M1S44S52U14M2S54Sf8S2A5S6G0Se7A2A3S41S40G1S44S52G2S54Sf3S2A5S6G0Se4A2A3S41S40G1S44S52G2S54Sf7S2A5S6G0Se6A2A3S40G1S44S52G2S54Sf9S2A5S6G0Se8A2A3A2A2A2").
Proof. exact (conj (@eq_refl (option (list leafA)) run_sh__R1 <: run_sh__R1 = Some LV_sh1) (conj (@eq_refl (option (list leafA)) run_sh__R2 <: run_sh__R2 = Some LV_ov1) (conj (@eq_refl (option (list leafA)) run_sh__R3 <: run_sh__R3 = Some LV_sh0) (@eq_refl (option (list leafA)) run_sh__R4 <: run_sh__R4 = Some LV_shZ)))). Qed.
Lemma LV_sh_pcs : ltac2:(tb__ "0|5|
S40S8S9S4fS8S11A1M0A2M1A1S18bS45G1S45S7S4fG0S1dS43S47R1A1A1M2A1S18eS11U4S18cS11UaS22G2A1A3A3A4LL;ScS45Se7ScS45Se4ScS45Se6Se8A3A3A3A4S0G1S7S4fG0S1b0S0S11S12Z21447A1S0S11S12Z1fA1S0S11S12Z1A1S0S11S12S1c3A1S4S11A1A3A3A3M3A3A4M4S0G1S7S4fG0S1b0S0S11S12Z160cdA1G3A3A4S0G1G4S0G1G4S4G1A1A3A3A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

End DrvR_states.

