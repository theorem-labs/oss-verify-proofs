(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6 ea fn.

(* [comment removed for export] *)
Module Lib_vec_reserveN_eqs.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "SLit"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "nil"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "E_r15f"; "E_rW1f"; "E_c8"; "E_cW0"; "Pre_c"; "Xk_r"; "inj"; "kbytes"; "s_c"; "s_r"; "vW"; "xf_rback"; "E_r15x"; "E_rW1x"; "R_c8"; "R_cW0"; "R_r15"; "R_rW1"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW0"; "XW1"; "kn15"; "tvf0"; "xf_rcall"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW0"; "NW1"; "T_c8n0"; "T_c8ok"; "T_c8ok0"; "T_c8ok2"; "T_cW0n0"; "T_cW0ok"; "T_cW0ok0"; "T_cW0ok2"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.RA"; "Pre_ra"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "tv_factsA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_calloc_null"; "L_calloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S2SdS4bS53S54S32S43P64S44S45A7SeA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_r15x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S30S2fA2S8S0S1dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_rW1x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S31S2fA2S8S0S1eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_r15f_eq : ltac2:(tb__ "0|0|
S2S0SfS1dS9S4S2eS5S1S1dA1A1A3A2S11A3"). Proof. reflexivity. Qed.
Lemma E_rW1f_eq : ltac2:(tb__ "0|0|
S2S0SfS1eS9S4S2eS5S1S1eA1A1A3A2S12A3"). Proof. reflexivity. Qed.
Lemma T_r15f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S47S16A6S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S48S16A6S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S47S16A6S26A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S48S16A6S27A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S23S1cA2S8S0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S26S1cA2S8S0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S24S1cA2S8S0S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S27S1cA2S8S0S28A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S2dA1A4A1S25A2S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S1bA1A4A1S28A2S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S51S4eSbS50A1S4fA3A5S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S52S4eSbS50A1S4fA3A5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS51S4eSbS50A1S4fA3A5S37A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS52S4eSbS50A1S4fA3A5S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S1bA1A4A1S3eA2S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S7Z8A1A1A4A1S3aA2S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N15_eq : ltac2:(tb__ "0|0|
S2S0SfS29S9S4S17S2dA1S5S1S29A1A1A3A2S33A3"). Proof. reflexivity. Qed.
Lemma NW1_eq : ltac2:(tb__ "0|0|
S2S0SfS2cS9S4S17S1bA1S5S1S2cA1A1A3A2S36A3"). Proof. reflexivity. Qed.
Lemma NW0_eq : ltac2:(tb__ "0|0|
S2S0SfS2bS9S4S17S1bA1S5S1S2bA1A1A3A2S35A3"). Proof. reflexivity. Qed.
Lemma N8_eq : ltac2:(tb__ "0|0|
S2S0SfS2aS9S4S17S7Z8A1A1S5S1S2aA1A1A3A2S34A3"). Proof. reflexivity. Qed.
End Lib_vec_reserveN_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserveN_pf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "zlog15"; "KU"; "bitem"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bd_subst"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "sobj"; "SLit"; "sprop_eqb"; "ss_next"; "SVar"; "SPUle"; "holds"; "SPBranch"; "SPNot"; "mkObj"; "rw"; "DUnknown"; "ob_cells"; "sprop_below"; "eval"; "ss_objs"; "DZero"; "cell"; "obj_range"; "obj_wf"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "xr_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "nil"; "cons"; "app"; "Some"; "None"; "option"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "vK"; "kbytes"; "bdP"; "nd0"; "vN"; "s_r"; "vDt"; "vE"; "vW"; "cutsE"; "vAl"; "E_c8'"; "E_cW0'"; "O_data"; "Pre_c"; "Xk_r"; "inj"; "kn15"; "s_c"; "vV"; "O_W"; "O_vec"; "tv0"; "vC"; "B32"; "PD_ra"; "z0"; "E_r15f"; "E_rW1f"; "Pre_vr"; "R_c8"; "R_cW0"; "X15"; "X8"; "XW0"; "XW1"; "X_vr"; "ndG"; "ndN"; "spm"; "tvf0"; "B_EW"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "O_alv"; "P_fail"; "P_grown"; "P_keep"; "exitsE"; "tvP"; "two47"; "two48"; "vKn"; "xf_rback"; "xf_rcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "tv_factsA"; "JA_pre"; "ND"; "emeasA"; "ffinA"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf.Sum"; "baseF"; "basez"; "s_rbd"; "JL"; "Posts_vr"; "injF"; "injz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "import_subA"; "J_ofPA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.RA"; "Pre_ra"; "P0_ra"; "tv0"; "P_fail"; "P_ok"; "bd0"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "csz"; "payA"; "site_okA"; "T_afterA"; "call_checkTA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "ulink"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "FBx"; "T0"; "T_ok"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "robjs_okF"; "xrs_okF"; "FFx"; "PostsC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr.

Lemma uval_kn15 : ltac2:(tb__ "0|1|
S12S3eS3R1S46A2S5eA2S0S2fS3R2S57A2S41S3R2S46A2M0S44G0Z2A2A2A3F_;Frho;").
Proof.
  intros rho HK. unfold kn15. pose proof (uval_range rho vK).
  assert (E1 : uval rho (SAlu ALU_SRL vK (SLit 1)) = uval rho vK / 2).
  { unfold uval. rewrite U_srl_lit. change (2 ^ (1 mod 64)) with 2. reflexivity. }
  unfold B32 in HK. rewrite uval_add_small; rewrite E1; [lia|]. pose proof (Z.div_le_upper_bound (uval rho vK) 2). lia.
Qed.

Definition P0_vr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S2fS84Q40M0S1fVr;P11A2A2Z0M1A3A1S2S0S2fS84G0S1fVr;PfA2A2G1A3A1F_;S1S9eVFF;S84G0S1fVr;PcA2A2Z20A3S9eVFF;S84G0S1fVr;PeA2A2Z30A3A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
SceS12S33S83Q40A1A1Sd4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
ScbS45VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2fSf0VCST;R1A2S1S3eZ0R2A2S42R2SefA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2fSf0VXGL;R1A2S1S3eZ0R2A2S42R2SefA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S33S34S34S2fS2fA2S2fA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S93VAInv;VCST;VXGL;VKc;S96VFB;VFF;A2VFB;VFF;VBX;S8bVnd;Aa").
Definition Posts_vr : list (axst * jpostA) := ltac2:(tb__ "0|2|
S37S34S2aSa3A2M0S35S2aSa3S77S9aS49A1A4S37G0S35S2aSa3S75S9aS8eS5cS36S34S34S11S2fA2S11A2A1M1S36S6A1A3A1A4S37G0S35S2aSa3S76S9aS8eS79G1S48S4aS7cA2A3A1A4S36G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S92VAInv;VCST;VXGL;S7fVKc;Vrho0;S96VFB;VFF;A2VFB;VFF;VBX;S8bVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S34S2aS8aA2SddFn;") := ltac2:(tb__ "0|0|
S94VAInv;VCST;VXGL;S7fVKc;Vrho0;S96VFB;VFF;A2VFB;VFF;VBX;S8bAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sa4S45S7fVrho0;Vtp0;S9bA5").

Lemma range_data : ltac2:(tb__ "0|2|
S12S11S11S2fS42S3R4S47R2A1A2S40Z2Z3fA2A2S1S3eS3cS2fS2fS27R5S53R4S47R3A1A2A2M0A3R2A2S42R2S3dS2fS2fG0A3A2A2S1S3eS3R6R5A2M1R3A2S42R3S41G1S3R6S47R4A1A2A2A2A2F_;F_;Fa;Fk;Fd;Frho;").
Proof.
  intros rho d k a Hk Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_data in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho (kbytes k) Hk) in Hr. unfold uval in *. lia.
Qed.

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|6|
S1S0S31S85S13S17S1aS19P1eA1M0S6dZ40A1A2A1VF;A3S32A3S1S0S31S85S13S17S1aG0S19PaA1M1A2A1VF;A3S32A3S1S0S31S85S13S17S1aG1S16S7aA1A2A1VF;A3S32A3S1S0S31S85S13S17S1aS16Z1A1S4dA2A1VF;A3S32A3S1S0S31S85S13S17S1aS4dS16Z1000A1A2A1VF;A3S32A3S1S0S31S85S13S17S1aS4eS16S7bA1A2A1VF;A3S32A3S1S0S31S85S13S17S1aS46S16S5eA1M2A2A1VF;A3S32A3S1S0S31S85S13S17S1aS47S4eA1M3S16S6fA1M4A2A1VF;A3S32A3S1S0S31S85S13S17S1aS47S46A1G2A2A1VF;A3S32A3S1S0S31S85S13S17S1aG3S47S4aA1M5A2A1VF;A3S32A3S1S0S31S85S13S17S1aG5G4A2A1VF;A3S32A3S1S0S31S85S13S17S1aS16Z7fff7f800000A1G0A2A1VF;A3S32A3S0S31S85S13S17S1aG0S16Z7fffff800000A1A2A1VF;A3S32A3A2A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_e : 1 <= uval rho vE <= 4096;
  bz_w : uval rho vW <= 2 ^ 48;
  bz_k : uval rho vK <= B32;
  bz_ew : uval rho (kbytes vW) = uval rho vE * uval rho vW /\ uval rho (kbytes vW) <= B_EW;
  bz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK /\ uval rho (kbytes vK) <= B32;
  bz_n : uval rho (kbytes vW) <= uval rho (kbytes vN) <= B_EW;

  bz_top : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S12S2fS1S3eZ0R1A2S3eR1S3R2S19PaA1M0A2A2A2S0S2fS3R3S6dR2A1A2S43S3R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S12S33S13A1Sa9S13S1bR2A1R1A3S97R2A1S98R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B1') as H1'. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8.
  pose proof (holds_mem _ _ _ HF B9) as H9. pose proof (holds_mem _ _ _ HF B10) as H10.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2.
  zf H1. zf H1'. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf HT1. zf HT2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold aceil, two47, RA.two47, two48, B_EW, B32 in *.
  rewrite !uval_lit in H2, H3, H4, H5, H6, H7, H8, H10, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia.
  assert (EW : uval rho (kbytes vW) = uval rho vE * uval rho vW) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  constructor; unfold aceil, B_EW, B32; lia.
Qed.

Lemma robjs_r : ltac2:(tb__ "0|1|
S12S33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0A1S21S88S15S5aR1A3A1S20A5S37S15S5bS4cS5dS46S4dA4S36S15A1A3A3A3S98R3A1S0S2fSe2Vrho0;A1S84Q40S1fR4Sc8A2A2A3S9eVFF;S3R5S59A2Z20A3Se8VCST;Vrho0;VFB;VFF;R6S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1R5A8F_;F_;F_;F_;FR;Frho;").
Proof.
  intros rho R -> BZ ET HV o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
Qed.
Lemma xrs_r : ltac2:(tb__ "0|0|
S12S9eVFF;S3R1S59A2Z20A3S9eVFF;S3R2S50A2Z30A3Se9VCST;VXGL;Vrho0;VFB;VFF;R3S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1S55A9F_;F_;Frho;").
Proof.
  intros rho HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S12Sd8S7fVrho0;R1A3S96VFB;VFF;Vrho0;A3S1S2S0S2fS3R3S46A2Z0M0A3A1S2S0S2fS3R4S4cA2G0A3A1F_;S1S9eVFF;S3R3S59A2Z20A3S9eVFF;S3R3S50A2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C). unfold uval, vK, vDt, vV, vAl. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 14%positive eq_refl).
  auto.
Qed.

Lemma HIN_r : ltac2:(tb__ "0|3|
S2aS33S15A1M0S12ScdS0G0R3S37S15S1eS19PaA1S16N40A1S16Z0A1S21S88S15S5aR3A3A1S20A5S37S15S5bS4cS5dS46S4dA4S36S15A1A3A3A3S97S14S2bR5A1A1A1S0S11SabS4bR6A1PcA2S50A3Sa9S13S1bR5A1S14S2bR7A1A1A3S96VFB;VFF;Vrho0;A3Sd8S7fVrho0;R7A3S1Se8VCST;Vrho0;VFB;VFF;R8S36S34S11S11A2A1M1S36S34S34S11S2fA2S11A2A1M2R9A8S1Se9VCST;VXGL;Vrho0;VFB;VFF;R8G1G2S55A9Sb0Se1VFB;R8G1A3SeaVFF;R8G2A3SadSacR8R9R7A3S4bRaA1A2A3A2A2F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR HB Hs12 HF HP0 Hav. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF HB) as BZ. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [exact (robjs_r rho R HR BZ ET HV)|]. split; [exact (xrs_r rho HV HA)|].
  unfold RA.P0_ra. rewrite rw_call', Hs12. destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl.
  split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma robjs_c : ltac2:(tb__ "0|2|
S12SceS33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0M1A1S21S88S15S5aR1A3A1S20A5S37S15S5bS4cS5dS46S4dA4S37S15S74S37S15S53S4cS47S46A1A2S36S15A1A3A3A3A3A3S98R4A1Se3R5Sd0ScfR4A1A1A2S0S2fS3R6S46A2G1A3S90VFF;R6A2S9eVFF;S3R8S59A2Z20A3S9eVFF;S3R9S50A2Z30A3SbcVCST;R9S3aS2fA1RaR8A5F_;F_;F_;F_;F_;F_;F_;FR;FAi;Frho;").
Proof.
  intros rho Ai R -> BZ HTK HK0 HFF HV HA o a Ho Hr. cbn in Ho. apply T_ok_rw in HTK. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - unfold O_alv in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _ _]. apply range_data in Hr; [|rewrite EK, HK0; lia]. rewrite EK, HK0 in Hr. lia.
Qed.
Lemma xrs_c : ltac2:(tb__ "0|1|
S12SceS33S34S11S11A2A1M0S0G0R1S6aS4cS46A2A3S98R4A1S0S2fS3R5S46A2Z0A3S90VFF;R5A2S9eVFF;S3R7S59A2Z20A3S9eVFF;S3R8S50A2Z30A3SbdVCST;VXGL;R8S3aS2fA1R9R7A6F_;F_;F_;F_;F_;F_;FX;FAi;Frho;").
Proof.
  intros rho Ai X -> BZ HK0 HFF HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _ _]. rewrite EK, HK0 in Ha. lia.
Qed.

Lemma baseF_E_cW0' : ltac2:(tb__ "0|0|
S97S14S2bS52A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_c8' : ltac2:(tb__ "0|0|
S97S14S2bS51A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_r15f : ltac2:(tb__ "0|0|
S97S14S2bS61A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_rW1f : ltac2:(tb__ "0|0|
S97S14S2bS62A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X15 : ltac2:(tb__ "0|0|
S97S14S2bS66A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW1 : ltac2:(tb__ "0|0|
S97S14S2bS69A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW0 : ltac2:(tb__ "0|0|
S97S14S2bS68A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X8 : ltac2:(tb__ "0|0|
S97S14S2bS67A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma site_cW0 : ltac2:(tb__ "0|2|
S12Sb9VAInv;VCST;VXGL;S7fVrho0;S96VFB;VFF;A2VFB;VFF;S52S58S52A1M0S65R1S49S3aS2fA1SceScdS1S1S3eZ1S3R3Sb7G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SabG0PcA2A2S3R3SabG0PdA2A2A2G1A3Sc1S36Sc0A1SbeSadSacR3S65R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_cW0') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  factz HF (SPBranch BC_GEU vW (SLit 8)) HW8. rewrite uval_lit in HW8 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). change (wsub_get (s_c E_cW0') 12) with vW. change (wsub_get (s_c E_cW0') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. rewrite uval_mul_comm. fold (kbytes vW). rewrite EW. unfold B_EW in BEW.
  split; [nia|]. split; [lia | exact I].
Qed.
Lemma site_c8 : ltac2:(tb__ "0|2|
S12Sb9VAInv;VCST;VXGL;S7fVrho0;S96VFB;VFF;A2VFB;VFF;S51S58S51A1M0S64R1S49S3aS2fA1SceScdS1S1S3eZ1S3R3Sb7G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SabG0PcA2A2S3R3SabG0PdA2A2A2G1A3Sc1S36Sc0A1SbeSadSacR3S64R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_c8') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). change (wsub_get (s_c E_c8') 12) with (SLit 8). change (wsub_get (s_c E_c8') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. rewrite uval_mul_lit by lia. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact I].
Qed.

Definition s_rbd (kn : sv) : list bitem := ltac2:(tb__ "0|2|
S38S6S37S6ScZ1M0Z0M1S47Vkn;A1A3S37S6SbG1S3fZ2S5A2G0A3S36S6A1A3A3S48S4aVkn;A2A3").

Lemma sums_bdP : ltac2:(tb__ "0|1|
S12S11S11S1S0S2fS9S48R2R1A2M0R3A2S41S43S3fZ6S3R3S47R2A1A2A2S3fZ4S3R3S47R1A1A2A2A2S3fZ20S3R3S4dA2A2A2A3S0S2fS8G0R3A2S3fS3fZ2S5A2S43SeS4S3R3R1A2A1A2A2A3A2Fk;Fw;Frho;").
Proof. intros. unfold bdP, PHI, KLG. cbn [bsumV bsumK]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma sums_s_rbd : ltac2:(tb__ "0|2|
S12S11S1S0S2fS9S99R1A1M0R2A2S41S3R2S47R1A1A2S9S48S4aR1A2M1R2A2A2A3S0S2fS8G0R2A2S41S3fZ2S5A2S8G1R2A2A2A3A2Fkn;Frho;").
Proof. intros. unfold s_rbd, BIs, BIc. cbn [bsumV bsumK app]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma bd_nn_bdP : ltac2:(tb__ "0|1|
S12S11S11S3eS3fZ4S3R3S47R1A1A2A2S41S3fZ6S3R3S47R2A1A2A2S3fZ20M0S3R3S4dA2A2A2A2S3eS3R4R2A2S40Z2G0A2A2S7S48R4R3A2R5A2F_;F_;Fk;Fw;Frho;").
Proof.
  intros rho w k H1 H2. unfold bd_nn, bdP, PHI, KLG. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c]; [lia|].
  pose proof (zlog15_ZK _ H2). lia.
Qed.
Lemma bd_nn_s_rbd : ltac2:(tb__ "0|0|
S12S11S7S48S4aR1A2R2A2S7S99R2A1R3A2F_;Fkn;Frho;").
Proof.
  intros rho kn H. unfold s_rbd. apply bd_nn_app. split; [|exact H]. unfold bd_nn, BIs, BIc. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c].
  - pose proof (uval_range rho (kbytes kn)). lia.
  - lia.
Qed.

Record injz (rho : valuation) (kn : sv) : Prop := IJ {
  ij_b : 4 * uval rho (kbytes vK) <= 3 * uval rho (kbytes kn);
  ij_a : 4 * uval rho (kbytes kn) <= 6 * uval rho (kbytes vW) + 32 * uval rho vE;
  ij_c : 1 <= uval rho (kbytes kn) <= B32;
  ij_e : uval rho (kbytes kn) = uval rho vE * uval rho kn }.
Definition injF (kn : sv) (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S0S31S87S13S13S85S13S17R1A1VF;A3Lf;S56Vkn;A1A3S32A3").
Lemma injz_of : ltac2:(tb__ "0|0|
S12S11S33S13A1Sa9S13S1bR3A1R1A3S98R4A1S9cR4R3A2S3eS3R6R5A2S40Z2Z31A2A2S9dR7R6A2F_;F_;F_;F_;FF;Fkn;Frho;").
Proof.
  intros rho kn F HF BZ H Hkn. unfold injF, inj in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. unfold B_EW, B32 in *.
  pose proof (uval_range rho kn) as Rkn.
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite !uval_lit in F3, F4 by lia.
  rewrite !uval_mul_lit in F1 by (rewrite ?EKn; lia). rewrite uval_add_small in F2 by (rewrite !uval_mul_lit by lia; lia).
  rewrite !uval_mul_lit in F2 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma grow15 : ltac2:(tb__ "0|0|
S12S98R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S4eA2A2S42S3R4S4eA2S3R4S57A2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S57A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2 |- *.
  pose proof (uval_range rho vK). pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma growW1 : ltac2:(tb__ "0|0|
S12S98R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S4eA2A2S3eS3R4S57A2S3R4S4eA2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S4eA2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2.
  pose proof (uval_range rho vK).
  destruct (Z_lt_ge_dec (uval rho vK) 2).
  - assert (E1 : uval rho vK = 1) by lia. rewrite E1, zlog15_1. pose proof (zlog15_ge1 (uval rho vW) ltac:(lia)). lia.
  - pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). pose proof (zlog15_mono (uval rho vK + uval rho vK / 2) (uval rho vW) ltac:(lia)). lia.
Qed.
Lemma grow0 : ltac2:(tb__ "0|0|
S12S11S0S2fS3R2S46A2Z0A3S3eZ8S3R3R2A2A2S3eS41S4S3R4S46A2A1Z1A2S4S3R4R3A2A1A2F_;F_;Fkn;Frho;").
Proof. intros rho kn -> H. rewrite zlog15_0. pose proof (zlog15_ge1 (uval rho kn) ltac:(lia)). lia. Qed.

Lemma pay_r : ltac2:(tb__ "0|3|
S2aS11S97S14S2bR2A1A1A1S9cR2S14S2bR3A1A1A2S12Sa9S13S1bR1A1S14S2bR5A1A1M0A3S98R2A1S1S3eS3R3R6A2M1S40Z2Z31A2A2S3eS41S4S3R3S46A2A1Z1A2S4G1A1A2A2F_;F_;Frho;Sb8S7fVrho0;S96VFB;VFF;A2G0S16Z0M2A1G2S48S4aS46A2S99R4A1A8F_;F_;F_;Fkn;FE;").
Proof.
  intros E kn HB HI HG. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as [Hkn HL]. pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vN kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|apply bd_nn_s_rbd; exact NN]].
  - rewrite uval_lit by lia. destruct (sums_s_rbd rho kn) as [-> _]. destruct (sums_bdP rho vN kn) as [-> _]. destruct (sums_bdP rho vN vK) as [-> _]. lia.
  - destruct (sums_s_rbd rho kn) as [_ ->]. destruct (sums_bdP rho vN kn) as [_ ->]. destruct (sums_bdP rho vN vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_r15 : ltac2:(tb__ "0|1|
Sb8S7fVrho0;S96VFB;VFF;A2S14S2bS61A1A1S16Z0M0A1G0S48S4aS46A2S99S57A1A8").
Proof.
  apply pay_r; [exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (grow15 rho BZ HK0 HKW HWn)].
  destruct BZ as [Bsp Be Bw Bk _ _ _ _]. rewrite (uval_kn15 rho Bk). pose proof (uval_range rho vK). lia.
Qed.
Lemma pay_rW1 : ltac2:(tb__ "0|1|
Sb8S7fVrho0;S96VFB;VFF;A2S14S2bS62A1A1S16Z0M0A1G0S48S4aS46A2S99S4eA1A8").
Proof.
  apply pay_r; [exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (growW1 rho BZ HK0 HKW HWn)]. destruct BZ; lia.
Qed.

Lemma pay_c : ltac2:(tb__ "0|2|
S2aS11S11S97S14S2bR3A1A1A1S9cR3S14S2bR4A1A1A2S12Sa9S13S1bR1A1S14S2bR6A1A1M0A3S98R2A1S1S3eS3R3R7A2M1S40Z2Z31A2A2S1S0S2fS3R3S46A2Z0A3S1S3eZ8G1A2S0S2fS3R3R6A2S3R3S47R7A1A2A3A2A2A2F_;F_;Frho;Sb8S7fVrho0;S96VFB;VFF;A2G0R4S5S48S4aS46A2S48S4aR5A2A8F_;F_;F_;Fcst;Fkn;FE;").
Proof.
  intros E kn cst HB HI HG. split; [reflexivity|]. split; [unfold KU; lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as (Hkn & HK0 & H8 & ->). pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  pose proof (grow0 rho kn HK0 H8) as HL.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vN kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|exact NN]].
  - destruct (sums_bdP rho vN kn) as [-> _]. destruct (sums_bdP rho vN vK) as [-> _]. rewrite EK, HK0. lia.
  - destruct (sums_bdP rho vN kn) as [_ ->]. destruct (sums_bdP rho vN vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_cW0 : ltac2:(tb__ "0|0|
Sb8S7fVrho0;S96VFB;VFF;A2S14S2bS52A1A1Sb7S58S52A1A1S5S48S4aS46A2S48S4aS4eA2A8").
Proof.
  apply pay_c; [exact baseF_E_cW0' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia.
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). rewrite uval_mul_comm. fold (kbytes vW).
  destruct BZ; repeat split; lia.
Qed.
Lemma pay_c8 : ltac2:(tb__ "0|0|
Sb8S7fVrho0;S96VFB;VFF;A2S14S2bS51A1A1Sb7S58S51A1A1S5S48S4aS46A2S48S4aS16Z8A1A2A8").
Proof.
  apply pay_c; [exact baseF_E_c8' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). rewrite uval_mul_comm. fold (kbytes (SLit 8)).
  rewrite uval_lit by lia. destruct BZ; repeat split; lia.
Qed.

Lemma inj_holds : ltac2:(tb__ "0|4|
S12S11S98R2A1S3eS3R3R2A2S40Z2Z31A2A2S3eS3fZ4M0S3fS3R4S4dA2M1S3R4S46A2A2A2S3fZ3S3fG1S3R4R3A2A2A2A2S3eS3fG0S3fS3R5S4dA2M2S3R5R4A2A2A2S41S3fZ6S3fG2S3R5S4eA2A2A2S3fZ20G2A2A2A2S1S3eZ1S3fS3R6S4dA2S3R6R5A2A2M3A2S3eG3S5eA2A2Sa9S13S1bR7A1S56R6A1A3F_;F_;F_;F_;F_;Fkn;Frho;").
Proof.
  intros rho kn BZ Hkn H1 H2 H3. destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2] Btop]. unfold B_EW, B32 in *.
  assert (Hkn32 : uval rho kn <= 4294967295) by nia.
  pose proof (uval_range rho kn).
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  unfold inj, B32. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite !uval_mul_lit by (rewrite ?EK, ?EKn; lia). rewrite EK, EKn. lia.
  - rewrite uval_add_small by (rewrite !uval_mul_lit by (rewrite ?EW; lia); rewrite EW; lia).
    rewrite !uval_mul_lit by (rewrite ?EW, ?EKn; lia). rewrite EW, EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. exact Hkn32.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2fS33S83Q40A1A1S9fF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S81S2aS12S33S83Q40A1A1S9fSa9S13S1bR3A1S14S2bR4A1A1A3VTR;S80S45R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9fS9fS9fSa0R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S9fS9fSa0S2R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S81S81S2aS2aSaeS33S15A1M0S33S34S2aSa3A2M1A1S33S34S11S11A2M2A1S9fS12S33S83Q40A1A1M3G2S86G2R1R5A3S86G2R2S2cRbA1A3F_;Fr;S0S3bG0A1Sa6RaR9R8A3S39G0R7A2A3S0S31Sa5RbRaR9R8SaaG1S2aS3cS2aSa3A2R7A4A5S32A3S12G3VTR;S80S45RfRdR2R1A5Sa4S45S18S2bRdA1A1R2R1RaA5A2Ftp1;Frho1;S33Sd5A1M4ScdSd4S82S45R9R8R10S35G4Sd6R3Sd7R2R1A2A4A5R13RaR9R4R2A4R13SadSacRbRfSd1R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2aSa3G4ScdSd4S12G3G4ScdSd4S86G1S35S2aSa3RaR9A4R14A3S82S45R12R11R19S35G4Sd6R9Sd7R8R7A2A4A5R1cR13R12RaR8A4Sd8S18S2bR1aA1A1SadSacR14R18Sd1R9R13RaA3A3R19A2R8A3S82S45R9R8ReS35G4Sd6R7Sd7R6R5A2A4A5ReSadSacR16R1aSd1RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf3R17Sd1RcR16RdA3R1bR1cR1dR10R1eR19RbA9S12SdaR18Sd1RdR17ReA3R1cR1dS2bR1eA1S2bR1fA1S2bR11A1R1RcA9VTR;S80S45Sa8R11SadSacR19R1dSd1ReR18RfA3A3R1eA2R18RdRcA5Sf4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S80S45R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CCALLOC : ltac2:(tb__ "0|1|
SceS12S33S83Q40A1A1VTR;S80S45Sc2VAInv;S36Sc0A1M0SbeR3VKc;SccA6Sc6SbfG0SbeA3R2R1A5Sa4S45S7fR2R1Sc5SbfVAInv;VCST;VXGL;G0SbeR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CREALLOC : ltac2:(tb__ "0|1|
S33S34S2fS2fA2M0A1S33S34G0S2fA2A1S10S12S33S83Q40A1A1SdZ2R3A2VTR;S80S45S8dVAInv;VCST;VXGL;VKc;Sb0R6R5A2R6R5R4S8bSb5Sb1Sb4A2AaSafR3R2A5Sa4S45S7fR3R2SebVAInv;VCST;VXGL;VKc;Sb0S8bS5fR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S2aS8aS34S2fS11A2M0S12S33S83Q40A1A1M1S2fG1S86S34S34S2aS8aA2M2G0A2S35G2G0S35S2aS8aR7R6A4R5A4S4fA3S1S3eZ0S8fS35G2G0S35S2aS8aR8R7A4R6A4R5A2M3A2S42G3R3A2A2VTR;S80S45VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2aS8aS12S33S83Q40A1A1M0S2fG0S86S34S2aSa3A2S35S2aSa3R6S9aR5A1A4S9bA3VTR;S80S45VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_vr PD_ra]; do n right; left; reflexivity.

Lemma X_N : ltac2:(tb__ "0|4|
S2aS2aS11S2fS12S33S83Q40A1A1M0S2fG0S0S2aSdeR8S38S13S56R6A1S14S2bR8A1A1A3A2R7A3S86S34S34S2aS8aA2M1S34S2fS11A2M2A2S35G1G2S35S2aS8aR8S49A4S35S2fS11R6S60A4A4S4fA3S3eS3fS41R7Z1A2S40Z2Z40A2A2R4A2S3eZ0R8A2S0S31S87S13S22S18S2bRcA1M3A1A1S38S13S56RaA1S14G3A1A3A3S32A3S12Sa9S13S1bR1A1S14S2bReA1A1A3Sa9S13S1bR2A1S56RdA1A3F_;Frho;VTR;S80S45VJAv;S49A1ReRaR9A5VFAM;R8R7A2A2F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fr;Fkn;FNs;FXs;").
Proof.
  intros Xs Ns kn r rho tp b tp0 HN Hin Hb Hr Hbelow Hinj.
  eapply TR_pre; [|apply (REENTER Ns nd0 (r, z0)); [exact Hin | meas]].
  intros w Hw. rewrite <- HN. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |].
  intros tr md _ HF. apply Forall_app. split; [exact (Hinj _ HF) | exact HF].
Qed.

Lemma X_X15 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X15 N15 kn15 80 rho tp b tp0 N15_eq); [innth 1 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X15) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r kn15 BZ); rewrite ?(uval_kn15 r Bk); unfold B32; try nia.
Qed.
Lemma X_XW1 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S69R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW1 NW1 vW 80 rho tp b tp0 NW1_eq); [innth 2 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW1) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_XW0 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S68R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW0 NW0 vW 80 rho tp b tp0 NW0_eq); [innth 3 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW0) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2]]. unfold B_EW, B32 in *.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_X8 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S67R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X8 N8 (SLit 8) 80 rho tp b tp0 N8_eq); [innth 4 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X8) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPNot (SPBranch BC_GEU vW (SLit 8))) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] [BN1 BN2]]. unfold B_EW, B32 in *.
  pose proof (uval_range r vW).
  apply (inj_holds r (SLit 8) BZ); rewrite ?uval_lit by lia; unfold B32; try nia.
Qed.

Lemma C_calloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S83Q40A1A1S9fS0S31S85S13S17S1cSd3S46S16Z0A1M0A3A1S14S2bR4A1A1A3S32A3S0S31S85S13S17S1cSd2S4cG0A3A1S14S2bR5A1A1A3S32A3VTR;S80S45VJAv;S49A1R6R5R4A5R3A2F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  destruct (P0_now rho Hav HP0) as (HKD & _ & _).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1, F2 by lia. exact (HKD F1 F2).
Qed.
Lemma C_realloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S83Q40A1A1S9fS0S31S85S13S17S1dS1cSd3S46S16Z0A1M0A3A1A1S14S2bR4A1A1A3S32A3S0S31S85S13S17S1dS1cSd2S4cG0A3A1A1S14S2bR5A1A1A3S32A3S97S14S2bR6A1A1A1VTR;S80S45VJAv;S49A1R7R6R5A5R4A2F_;F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2 HB. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & (HN & _ & _) & _).
  pose proof (basez_of rho _ HF HB) as [_ _ _ _ _ [EK _]].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (tnz_of_fact rho vDt (kbytes vK) F2) as Hnz. zf F1.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1 by lia.
  cbn [nd_tv nd0] in HN. destruct (proj1 (Forall_forall _ _) HN (vDt, kbytes vK) ltac:(left; reflexivity) Hnz) as (Hpos & _).
  unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho (kbytes vK))) with (uval rho (kbytes vK)) in Hpos.
  rewrite EK, F1 in Hpos. lia.
Qed.

Lemma X_E_r : ltac2:(tb__ "0|10|
S2aS2aS2aS2aS2aS2aS2aS2aS33S15A1M0S11S30S12S33S83Q40A1A1M1S2fG1S0S3bS2aA1M2Se5RfS7eA2S39S2aReA2A3S0S2aSdeRfS38S13S6eS14S2bRfA1A1A3A2ReA3S0S31S85S13S17S1dS1cSd2S4cS16Z0M3A1M4A3A1A1S14S2bR10A1A1A3S32A3S0G0RaS37S15S1eS19PaA1S16N40A1G4S21S88S15S5aRaA3A1S20A5S37S15S5bS4cS5dS46S4dA4S36S15A1A3A3A3S97S14S2bR11A1A1A1S0S11SabS4bR12A1PcA2S50A3S0S31SeeS55S2cR13A1A2S32A3S0S3bG0A1Sa6R14SafS4bR14A1A3S39G0ReA2A3S0S31Sa5R15SafS4bR15A1RfSaaS34S2aS8aA2M5S2aS3cS2aS8aA2S5fA4A5S32A3S0S31SbbS7fS4bR16A1A2S32A3S0S31SdbS4bR17A1S7fA2S32A3S0S31Sf1S7fS18S2bR18A1A1A2S32A3S0S31S91S18S2bR19A1A1S8eS38S34S11S11A2M6S36G6A1M7S5cA3S36S34S34S11S2fA2S11A2A1S48S4aS46A2M8A3A2S32A3S0S31SaS18S2bR1aA1A1S48S4aR13A2A2S32A3S0S31Se4S4bR1bA1S5cSb1A3S32A3Sb8S7fVrho0;S96VFB;VFF;A2S14S2bR1cA1A1G4G3G8S38S6SfS4bR1cA1Sb4A2S48S4aR15A2A3A8S0S31S87SedSecSafS7fS4bR1dA1S18S2bR1dA1A1A4S5fA3S32A3S0S2aSe7SafR1eS4bR1eA1R18Sb2S55A6R1dA3S0G2Se5R1eS7dA2S39S2aR1dA2A3M9S0S2aSe7SafR20S4bR20A1R1aSb3S55A6R1dA3G9S0S2aSdcS8cS35S11S11S19R1aA1S47R1bA1A4A1R1eA2R1dA3S0S33G6A1MaSe0Sa7S4bR23A1SafSb3R23A4Sb6A2S37G6S35S11S11S19R1bA1S47R1cA1A4G7A3A3S0GaSe0Sa7S4bR24A1SafSb2R24A4Sb1A2S5cA3S0S31S85S13S17S1dS1cSd2S19R1dA1G4A3A1A1S14S2bR21A1A1A3S32A3S0S31S87S13S22S18S2bR22A1MbA1A1S38S13S8cS35S11S11S19R1eA1S47R1fA1A4A1S14GbA1A3A3S32A3S0S31S87S13S22S18S2bR28A1McA1A1S38S13S6eS14GcA1A3A3S32A3S86S34G5S34S2fS11A2MdA2MeS35G5GdS35S2aS8aR26S6cR21A1A4S35S2fS11Z3cS60A4MfA4S4fA3S86GeS35G5GdS35S2aS8aR24S6bS19R21A1R22A2A4GfA4S4fA3S3eS3fZ46S40Z2Z40A2A2R1fA2VTR;S80S45VJAv;S49A1R2dR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FpN;Fkn;FR;FTok;FTokB;FTok0;FTf;FTf0;FEf;FEx;FE;").
Proof.
  intros E Ex Ef Tf0 Tf Tok0 TokB Tok R kn pN rho tp b tp0 HEx HEf HD HR HB Hs12 HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass HPAY Hpd HTf0 HTf HTok0 HTokB HTok Htvok Htvf HpN Hbelow HbelowE HinF HinOK Hb.

  eapply TR_pre with (P := SPA segs (JAv nd0) Ef rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_rcall rho E Ex tp w HEx Hw) as Hw1.
    rewrite <- HEf. apply (SPA_refacts_JA segs); [exact Hw1 | exact HbelowE | ].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF HD). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX RA.P0_ra PTrue (fun _ H => H) (fun _ _ _ H => H) RA.Pre_ra (RA.ndR RA.tv0 RA.bd0) PD_ra NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CREALLOC eq_refl
           Ef (s_r Ef) R Xk_r rho tp [] tv0 [] (bdP vN vK) (bdP vN kn) ANone (FAM b tp0) HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl HPAY Hpd).
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD' HZ HFR HM HT HTK. apply (HIN_r Ef R rho ms HR HB Hs12 HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_ra In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am RA.ndR ND am_subst app].
    + rewrite HTf0, Htvf. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tf (ndN kn) (60, z0)); [exact HinF | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_rback rho' Tf0 Tf tp' w HTf Hw).
    + rewrite HTok0, Htvok. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tok (ndG (SVar pN) kn) (60, z0)); [exact HinOK | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_rback rho' Tok0 TokB tp' w HTokB Hw) as Hw1.
      rewrite <- HTok. unfold ax_add_facts.
      change (ax_setS TokB (add_facts (tv_factsA (SVar pN, kbytes kn)) (ax_S TokB))) with (ax_with_facts TokB (tv_factsA (SVar pN, kbytes kn) ++ ss_facts (ax_S TokB))).
      apply (SPA_refacts_JA segs); [exact Hw1 | exact Hbelow |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
      eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
      apply tnz_of_fact. exact (holds_mem _ _ _ HF2 HpN).
Qed.
Lemma X_E_r15 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_r15 E_r15x E_r15f T_r15f0 T_r15f T_r15ok0 T_r15okB T_r15ok R_r15 kn15 141%positive rho tp b tp0 E_r15x_eq E_r15f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_r15f.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - pose proof pay_r15 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes kn15); BIc 0 (2 * KU) 1] ++ bdP vN kn15) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_r15f0_eq.
  - exact T_r15f_eq.
  - exact T_r15ok0_eq.
  - exact T_r15okB_eq.
  - exact T_r15ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 5.
  - innth 6.
  - exact Hb.
Qed.
Lemma X_E_rW1 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S73R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_rW1 E_rW1x E_rW1f T_rW1f0 T_rW1f T_rW1ok0 T_rW1okB T_rW1ok R_rW1 vW 141%positive rho tp b tp0 E_rW1x_eq E_rW1f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_rW1f.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - pose proof pay_rW1 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes vW); BIc 0 (2 * KU) 1] ++ bdP vN vW) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_rW1f0_eq.
  - exact T_rW1f_eq.
  - exact T_rW1ok0_eq.
  - exact T_rW1okB_eq.
  - exact T_rW1ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 7.
  - innth 8.
  - exact Hb.
Qed.

Lemma X_E_c : ltac2:(tb__ "0|19|
S2aS2aS2aS2aS2aSaeS33S15A1M0S11S11S12S33S83Q40A1M1A1M2S2fG2S0SaeR8S58RdA1A3S0S3bG0A1Sa6ReS54R9A3S39G0R8A2A3S0S31Sa5RfS54RaR9S37S2aSc3SbfS36Sc0A1M3SbeA3M4S37S2aSc4SbfG3SbeA3M5S36S2aA1A3A3A5S32A3S0S31SbbS7fRbA2S32A3S0S31Sf1S7fS18S2bR11A1A1A2S32A3S0S31S91S18S2bR12A1A1S49A2S32A3S0S31SaS18S2bR13A1A1S48S4aRcA2A2S32A3S0S31S29S18S2bR14A1A1Sb7RfA1A2S32A3S0S11SabSa7R10S54G5R15A4Sc7A2S19Sd9S18S2bR15A1A1UaM6A2A1A3S0S11S19Sd9S18S2bR16A1A1G6A2A1S19P70A1M7A3Sb8S7fVrho0;S96VFB;VFF;A2M8S14S2bR17A1A1Sb7R12A1S5S48S4aS46A2S48S4aR10A2A8Sb9VAInv;VCST;VXGL;S7fVrho0;G8VFB;VFF;R18R13R12RfS49S3aS2fA1SceScdS1S1S3eZ1S3R11Sb7R15A1A2M9A2S42G9S40Z2MaZ27A2A2A2S1S0S2fS3fS3R11SabR15PcA2A2S3R11SabR15PdA2A2A2G9A3Sc1G3SbeSadSacR11R14R1A3R15A2A3A2A2Lms;LAi;AfS0S2aSbaS54R19R14R13G4A5R18A3S0S2aSbaS54R1aR15R14G5A5R18A3S12S0G1S23R1R14A2S23R1S47R15A1A2A3Fr;S0S11Sb7R17A1R14A3S0S3bS15A1MbS89S15S24S2bR1bA1A1U1McA3S39S15S1eG7S16Z0A1MdR15S36S26A1S25A5A2A3S0S33S34S11S11A2MeA1S2cR1cA1S38GeS6aS4cS46A2MfS37GeS35S11S11G7R16A4S36GeA1M10A3A3A3S0S2aSdfS2dR1dSf2S2bR1dA1GcS53G7S47R18A1M11A2A3A2S38GeGfS37GeS35S11S11G7G11A4G10A3A3A2R1cA3S0S31S28S18S2bR1eA1A1S53G7S47R19A1A2A2S32A3S0S31S87GeS2eS18S2bR1fA1M12A1A1S38GeGfS37GeS35S11S11G7S47R1aA1A4G10A3A3A3S32A3S0GbS89S15S24G12A1U7M13A3S39S15S53S4cS47S46A1A2A2A3S0S31S85S13S17S1dS1cSd3S46GdA3A1A1S14S2bR20A1A1A3S32A3S97S14S2bR21A1A1A1S0S2aSdcS8cS35S11S11G7S47R1eA1A4A1S2dR22Se6S2bR22A1G13A2A2A2R21A3S0S31S85S13S17S1dS1cSd2G7GdA3A1A1S14S2bR23A1A1A3S32A3S0S31S87S13S22S18S2bR24A1M14A1A1S38S13S8cS35S11S11G7S47R20A1A4A1S14G14A1A3A3S32A3S86S34S34S2aS8aA2M15S34S2fS11A2M16A2M17S35G15G16S35S2aS8aR27S6cR21A1A4S35S2fS11Z3cS60A4M18A4S4fA3S86G17S35G15G16S35S2aS8aR25S6bG7R22A2A4G18A4S4fA3S3eS3fZ46S40GaZ40A2A2R1fA2VTR;S80S45VJAv;S49A1R2bR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fcst;Fkn;FR;Fs;FTok;FTokA;FTok0;FTn;FE;").
Proof.
  intros E Tn Tok0 TokA Tok s R kn cst rho tp b tp0 Hs He Hchk Htp Hnf Hnb Hbr Hcsz Hres H112 HPAY HSITE
         HTn HTok0 Hev Hcst Hblk HX HTokA Hwf HXb Hold HK0 HB HTok Hp0 Hbelow HinN HinOK Hb.
  subst s. unfold Pre_c in *.
  apply (calloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E (s_c E) R rho tp nd0 (bdP vN kn) (FAM b tp0) CCALLOC He Hchk Htp Hnf Hnb Hbr Hcsz Hres HPAY (fun _ _ _ _ => I) HSITE).
  -   intros rho' tp'. rewrite HTn. cbn [nd_tv nd_fr nd0]. apply (REENTER Tn (ndN kn) (60, z0)); [exact HinN | meas].
  -   intros rho' tp'. rewrite HTok0, H112, Hcst. cbn [nd_tv nd_fr nd0].
    eapply TR_pre; [|apply (REENTER Tok (ndG (SVar 112) kn) (60, z0)); [exact HinOK | meas]].
    intros w Hw.

    apply (SPA_JA_tv_ext segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ((SVar 112, cst) :: tv0) ((SVar 112, kbytes kn) :: tv0)) in Hw.
    2: { intros _. split; [cbn [map]; unfold tvv; cbn [fst snd]; rewrite (Hev rho'); reflexivity|].
         intros [|k] t t' Ht Ht'; cbn [nth_error] in Ht, Ht'; [injection Ht as <-; injection Ht' as <-; unfold tnz; cbn [fst]; tauto|].
         rewrite Ht in Ht'. injection Ht' as <-. tauto. }
    apply (SPA_JA_drop_tv segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue _ [] (bdP vN kn) 1) in Hw.
    2: {
         intros HF0 t Ht. unfold tv0 in Ht. cbn [nth_error] in Ht. injection Ht as <-. right.
         assert (EF : ss_facts (ax_S TokA) = ss_facts (ax_S Tok0)) by (rewrite <- HTokA; reflexivity).
         pose proof HB as HB0. pose proof HK0 as HK00. rewrite EF in HB0, HK00.
         pose proof (basez_of rho' _ HF0 HB0) as [_ _ _ _ _ [EK _]].
         pose proof (holds_mem _ _ _ HF0 HK00) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
         rewrite uval_lit in F0 by lia. unfold tvv. cbn [snd]. change (bv_unsigned (eval rho' (kbytes vK))) with (uval rho' (kbytes vK)). rewrite EK, F0. lia. }
    cbn [remove_nth] in Hw.
    change (ND [(SVar 112, kbytes kn)] [] (bdP vN kn)) with (ndG (SVar 112) kn) in Hw.

    assert (Hw1 : SPA segs (JAv (ndG (SVar 112) kn)) TokA rho' tp' w).
    { rewrite <- HTokA. apply (SPA_x_requiv segs).
      - cbn [ax_X ax_setS]. rewrite HX. unfold X_vr. repeat constructor; cbn [fst snd]; try reflexivity. symmetry. apply Hev.
      - cbn [ax_S ax_setS]. unfold reshape_obj_at. cbn [ss_next set_objs]. exact HXb.
      - apply (SPA_reshape segs _ rho' Tok0 1 _ _ tp' w Hblk); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw].
        intros _. unfold obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi]. unfold soff. rewrite (Hev rho'). split; reflexivity. }
    assert (Hw3 : SPA segs (JAv (ndG (SVar 112) kn)) (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) rho' tp' w).
    { apply (SPA_drop_empty segs _ rho' TokA 7 _ tp' w Hold); [|exact Hw1].
      intros HF. pose proof (basez_of rho' _ HF HB) as [_ _ _ _ _ [EK _]].
      pose proof (holds_mem _ _ _ HF HK0) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
      rewrite uval_lit in F0 by lia.
      unfold obj_hi_of, obj_lo_of, O_data. cbn [ob_lo ob_hi]. rewrite soff_lit_small by lia.
      rewrite (soff_smallu rho' (kbytes vK)) by (rewrite EK, F0; lia). rewrite EK, F0. lia. }
    rewrite <- HTok. unfold ax_add_facts.
    change (ax_setS (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (add_facts (tv_factsA (SVar 112, kbytes kn)) (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7)))))
      with (ax_with_facts (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (tv_factsA (SVar 112, kbytes kn) ++ ss_facts (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7))))).
    apply (SPA_refacts_JA segs); [exact Hw3 | exact Hbelow |].
    intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF2 Hp0).
Qed.
Lemma X_E_cW0 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S71R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_cW0 T_cW0n0 T_cW0ok0 T_cW0okA T_cW0ok (s_c E_cW0) R_cW0 vW (SMd M_MUL vW vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_cW0.
  - exact (site_cW0 rho).
  - exact T_cW0n0_eq.
  - exact T_cW0ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_cW0ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 9.
  - innth 10.
  - exact Hb.
Qed.
Lemma X_E_c8 : ltac2:(tb__ "0|1|
S12S33S83Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S80S45VJAv;S49A1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_c8 T_c8n0 T_c8ok0 T_c8okA T_c8ok (s_c E_c8) R_c8 (SLit 8) (SMd M_MUL (SLit 8) vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_c8.
  - exact (site_c8 rho).
  - exact T_c8n0_eq.
  - exact T_c8ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_c8ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 11.
  - innth 12.
  - exact Hb.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2aS8aS34S2fS11A2M0S12S33S83Q40A1A1M1G1S86S34S34S2aS8aA2M2G0A2S35G2G0S35S2aS8aR6R5A4R4A4S78A3VTR;S80S45VJAv;R6A1R7R4R3A5VFAM;S8fS35G2G0S35S2aS8aR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X15. meas.
  - apply X_XW1. meas.
  - apply X_XW0. meas.
  - apply X_X8. meas.
  - apply X_E_r15. meas.
  - apply X_E_rW1. meas.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_E_cW0. meas.
  - apply X_E_c8. meas.
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S95S45VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc9S45SbfVAInv;VCST;VXGL;A5").

Theorem vec_reserveN_sum : ltac2:(tb__ "0|0|
S33S83Q40A1A1Sa2S45Vok;S80S45S8dVAInv;VCST;VXGL;VKc;S96VFB;VFF;A2VFB;VFF;VBX;S8bS49AaS63Vrho0;R1A5Sa4S45S7fVrho0;R1S9bA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
ScaS45SbfVAInv;VCST;VXGL;A5").

Theorem vec_reserveN_sum_ex : ltac2:(tb__ "0|0|
S33S83Q40A1A1Sa1S45S80S45S8dVAInv;VCST;VXGL;VKc;S96VFB;VFF;A2VFB;VFF;VBX;S8bS49AaS63Vrho0;R1A5Sa4S45S7fVrho0;R1S9bA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_reserveN_pf.

(* [comment removed for export] *)
Module Icpt_memcpy_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "rw"; "holds"; "eval"; "ss_next"; "ss_facts"; "SVar"; "sprop_below"; "SLit"; "agree_below"; "SPBranch"; "SPNot"; "SAlu"; "sobj"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "sub"; "modulo"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "FT"; "Posts_mc"; "Pre_mc0"; "cur"; "F_L"; "E_src"; "E_dst"; "base_mc"; "gs"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "gl"; "E_Ld_bk"; "F8of"; "lastd"; "lasts"; "ord1"; "ord2"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "vBd"; "vBs"; "vLd"; "vLs"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "opZ"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "shp"; "HSE"; "vN"; "g8"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "withGA"; "vna_state"; "SPfamA"; "SPfamEA"; "enodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "vmeasIA"; "to_enodeIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Posts_memcpyA"; "Pre_memcpyA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr MCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section CallExit.
Variable ok : assn.
Variable J : jpredA.
Variable n : positive.
Variable rho0 : valuation.
Variable tp : list word.
Let J' : jpredA := ltac2:(tb__ "0|0|
S79S1SaVn;Vrho0;R1A3Lr;VJ;A2").

Variables (E Pre : axst) (s : wsub) (R : list sobj) (Posts : list leafA) (F : list sprop).
Hypothesis Hst : ltac2:(tb__ "0|0|
S36S11Vn;VJ;A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S17S2eS27SeA1M0A1S80VE;VPre;Vs;A3S2dG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S17S28S7fVE;VPre;Vs;VR;S24S30S31S32VPosts;A4A5S29A3").
Hypothesis Hn : ltac2:(tb__ "0|0|
S81Vn;S5S2fVE;A1A1A2").
Hypothesis HF : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fVE;A1A1A3S23S0S3R2A1VF;A3F_;Fr;").
Hypothesis HFb : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fVE;A1A1A1VF;A3S29A3").
Hypothesis HFbT : ltac2:(tb__ "0|0|
S30S3fS30R1VPosts;A3S17S28S40S0S8S5S2fS7eVs;VPre;S32R2A1VE;VR;A5A1A1A1VF;A3S29A3F_;FL;").

Let Jp (rhoE : valuation) : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';VrhoE;R3R2R1A4A2Lmd;Ltr;Lt;L_;").
Let Jc : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';R4R3R2R1A4A2Lmd;Ltr;Lt;Lr;").

Lemma HstG : ltac2:(tb__ "0|0|
S36S11Vn;VJ';A3").
Proof. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. Qed.

Lemma stable_Jp : ltac2:(tb__ "0|0|
S1S36S11S5S2fVPre;A1A1VJp;R1A1A3FrhoE;").
Proof.
  intros rhoE r r' t tr md md' Hag Hme [-> HJ]. split; [reflexivity|].
  eapply HstG; [apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma okframe_Jp : ltac2:(tb__ "0|0|
S1S37S11Vok;VJ;A3S37S11Vok;VJp;R2A1A3F_;FrhoE;").
Proof.
  intros rhoE Hok r t tr ms md msv' [-> [_ HJ]]. eapply Hok; eauto.
Qed.

Lemma facts_transport : ltac2:(tb__ "0|1|
S1S1S23S0S3R2A1S6S2fVE;A1M0A1A3SaS5G0A1R3R2A3S23S0S3R3A1VF;A3F_;F_;Frho';FrhoE;").
Proof.
  intros rhoE rho' HFE Hag. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree (ss_next (ax_S E)) rhoE rho' p Hag (proj1 (forallb_forall _ _) HFb p Hp))).
  exact (proj1 (Forall_forall _ _) (HF rhoE HFE) p Hp).
Qed.

Lemma call_exitA : ltac2:(tb__ "0|1|
S27S31A1S76S37S11Vok;VJ;A3S74OF_;S35S1S27S15Q40A1A1S37S11R4R3A3S36S11S5S2fVPre;A1A1M0R4A3S75S11R6S33S11R5VPre;R4R3A5S34S11R5G0R4R3VPosts;A6A4F_;F_;Ftp1;Frho1;FJq;Fok';S30S3fS30R1VPosts;A3S3fS31S78VF;S7eVs;VPre;S32R2A1VE;VR;A5A2R6A3F_;FL;S1S75S11Vok;S33S11VJ';VE;R1Vtp;A5S74S18S7bS11VJ';R7Vtp;R1A5R6R1A1A2Lw;A4FrhoE;F_;F_;F_;FQ;Fcuts;").
Proof.
  intros cuts Q Hok Hsum Hcuts rhoE.
  apply triple_factsA. intros HFE.
  apply (call_soundA segs ok J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum ok (Jp rhoE) rho1 tp1 (okframe_Jp rhoE Hok) (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag.
    eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm [-> HJ2]]. left. exists (ax_add_facts F (import_postA s Pre (la_state L) E R)), rho'.
    split; [exact (Hcuts L HinL)|]. split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.

Lemma call_exitA_ex : ltac2:(tb__ "0|3|
S27S77A1S74OF_;S77S17S31S7aR1A1M0VE;A3S35S1S27S15Q40A1A1S36S11S5S2fVPre;A1A1M1R3A3S73S11S33S11R4VPre;R3R2A5S34S11R4G1R3R2VPosts;A6A3F_;Ftp1;Frho1;FJq;S30S3fS30R1VPosts;A3S19S77S77S16S3fS77R1R8A3S16S17S31G0S78VF;S7eVs;VPre;S32R3A1VE;VR;A5A2A3S1S1S16S1cZ0S84R3R1A2M2A2S1fG2S84R8R2A2A2A2Fr';Fr;A2A2LnT;A2F_;FL;S1S73S11S33S11VJ';VE;R1Vtp;A5S74S18S7cS11S24S77S7dS85VJ';A1R8A4Vtp;S84R6R2A2R1A5R7R1A1A2Lw;A3FrhoE;F_;F_;F_;FnE;FQ;Fvcuts;").
Proof.
  intros vcuts Q nE HnE Hsum Hcuts rhoE.
  apply etriple_factsA. intros HFE.
  apply (call_completeA segs J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum (Jp rhoE) rho1 tp1 (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag w [Hsm [-> HJ2]]. exists w. split; [apply wsteps_refl|]. left.
    destruct (Hcuts L HinL) as (nT & HinT & HT & Hm).
    exists (to_enodeIA J' nT), rho'. split; [apply in_map; exact HinT|].
    cbn [to_enodeIA ena_state ena_pred ena_meas fst snd]. rewrite HT. split; [| exact (Hm rhoE rho')].
    split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.
End CallExit.

Section OpZ.
Variable rho : valuation.

Definition opZ (ib il io : positive) : Prop := ltac2:(tb__ "0|3|
S14Q40M0S2Vrho;Vib;A2A2S25S14G0S2Vrho;Vil;A2A2S25S14G0S2Vrho;Vio;A2A2S25S14G0S2Vrho;P12A2A2S25S16S1cS1dR2R1A2R3A2S16S1cR3S1eZ2M1Z28A2A2S16S1cZ1000R4A2S16S1cS1dR4R3A2S21S1eG1Z2fA2Z8M2A2A2S17S25S22R4G2A2Z0A3A2A2A2A2TN;TO;TL;TB;").

Lemma opnd_Z : ltac2:(tb__ "0|0|
S26S26S26S23S0S3Vrho;A1S66S7R3A1S7R2A1S7R1A1R3A4A3S83R4R3R2A3F_;Fio;Fil;Fib;").
Proof.
  intros ib il io HF.
  pose proof (urange (rw rho ib)) as RB. pose proof (urange (rw rho il)) as RL. pose proof (urange (rw rho io)) as RO.
  pose proof (urange (rw rho 18)) as RN.
  have_fact A1 HF (SPUle (add (SVar io) vN) (SVar il)). have_fact A2 HF (SPUle (SVar il) (SLit (2 ^ 40))).
  have_fact A3 HF (SPUle (SLit 4096) (SVar ib)). have_fact A4 HF (SPUle (add (SVar ib) (SVar il)) (SLit (2 ^ 47 - 8))).
  have_fact A5 HF (SPAlign ib 3). have_fact A6 HF (SPUle (SVar io) (SVar il)). have_fact A7 HF (SPUle vN (SVar il)).
  have_fact A8 HF (SPUle (SVar ib) (SLit (2 ^ 47 - 8))).
  unfold vN, add in A1, A2, A3, A4, A6, A7, A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A8.
  cbn [eval] in A2, A3, A6, A7, A8.
  assert (B1 : 0 <= bv_unsigned (rw rho io) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar io) (SVar 18) (bv_unsigned (rw rho io)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1) in A1.
  cbn [eval] in A1.
  assert (B2 : 0 <= bv_unsigned (rw rho ib) + bv_unsigned (rw rho il) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold opZ. repeat split; lia.
Qed.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S23S0S3Vrho;A1S48A3S16S83PfP10P11A3S16S83P13P34P35A3S16S16S1cZ1S14Q40M0S2Vrho;P12A2A2M1A2S1cG1S1eZ2M2Z28A2A2A2S16S16S1cS1dS13Z1000A2S14G0S2Vrho;PaA2A2M3A2S1cG3S1eG2Z3fA2A2A2S17S25S22G3Z10A2Z0A3A2A2A2A2F_;").
Proof.
  intros HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 1) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z 15 16 17 HD)|]. split; [exact (opnd_Z 19 52 53 HS)|]. repeat split; lia.
Qed.
End OpZ.

Lemma rw_sub : ltac2:(tb__ "0|0|
S1S3cS26S17S15Q40A1S2S3bR3R2A2R1A2S4R3S3dR2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.

Section LoopZ.
Variables (ib il io : positive).
Let vB := SVar ib. Let vL := SVar il. Let vO := SVar io.
Let opd : sv := add vB vO.
Let lastx : sv := ltac2:(tb__ "0|0|
S6dS6dVopd;S70A2S9N1A1A2").
Hypothesis Hib : (ib < NF)%positive. Hypothesis Hil : (il < NF)%positive. Hypothesis Hio : (io < NF)%positive.

Section Vals.
Variable r : valuation.
Let B : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vib;A2A2"). Let L : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vil;A2A2"). Let O : ltac2:(tb__ "0|0|
S25") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vio;A2A2"). Let N := bv_unsigned (rw r 18).
Hypothesis HZ : ltac2:(tb__ "0|0|
S6bVr;Vib;Vil;Vio;A4").
Hypothesis HN : 1 <= N <= 2 ^ 40.

Lemma V_opd : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;Vopd;A2A2S1dVB;VO;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst opd vB vO. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_last : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;Vlastx;A2A2S21S1dS1dVB;VO;A2VN;A2Z1A2A3").
Proof using HZ HN.
  pose proof V_opd as Vo. unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst lastx. unfold add at 1. unfold add at 1.
  replace (B + O + N - 1) with ((B + O + N) + (-1)) by lia.
  apply (U_addc r (SAlu ALU_ADD opd vN) (-1) (B + O + N)); [ | subst B L O N; unfold HSE in HZ; lia | lia].
  apply U_add2; [exact Vo | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_BL : ltac2:(tb__ "0|0|
S17S25S14Q40S4Vr;S6dVvB;VvL;A2A2A2S1dVB;VL;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r il)).
  subst vB vL. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; lia].
Qed.
Lemma V_g8 : ltac2:(tb__ "0|1|
S26S1fS14Q40M0S2Vr;R1A2A2S1eZ2Z3dA2A2S17S25S14G0S4Vr;S71S7R2A1A1A2A2S20Z8S14G0S2Vr;R2A2A2A2A3F_;Fv;").
Proof. intros v Hv. apply U_g8. exact Hv. Qed.
Lemma V_shp : ltac2:(tb__ "0|1|
S26S1fS14Q40M0S2Vr;R1A2A2S1eZ2Z3eA2A2S17S25S14G0S4Vr;S6eS7R2A1A1A2A2S1dS14G0S2Vr;R2A2A2S12A2A3F_;Fv;").
Proof. intros v Hv. apply U_shp. exact Hv. Qed.

Lemma F_L_intro : ltac2:(tb__ "0|3|
S25S25S17S25S14Q40M0S2Vr;P8cA2A2R2A3S17S25S14G0S2Vr;P8dA2A2R2A3S1cVB;S20Z8M1R4A2A2S1cS1dS20G1R5A2G1A2S1dVB;VL;A2A2S1fR6R5A2S1fR6S1eZ2Z3dA2A2S1cS20G1R7A2S21S1dS1dVB;VO;A2VN;A2Z1A2M2A2S1cG2S1dS20G1R8A2Z7A2A2S23S0S3Vr;A1S45VvB;VvL;Vlastx;A3A3F_;F_;F_;F_;F_;F_;F_;F_;Fl;Fc;").
Proof using HZ HN.
  intros c l Ec El H1 H2 H3 H4 H5 H6. unfold opZ in HZ.
  pose proof (urange (rw r ib)). pose proof (urange (rw r il)). pose proof (urange (rw r io)).
  assert (Hc : bv_unsigned (rw r 140) < 2 ^ 61) by lia.
  assert (Eg8c : UU r (g8 cur) = 8 * c) by (unfold cur; rewrite (V_g8 140 Hc); lia).
  assert (Eg8l : UU r (g8 gl) = 8 * l) by (unfold gl; rewrite (V_g8 141 ltac:(lia)); lia).
  unfold F_L, F8of.
  constructor. { cbn [holds]. rewrite Eg8c. change (eval r vB) with (rw r ib). lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 cur) 8 (8 * c) Eg8c) by lia. fold (add vB vL). rewrite V_BL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r cur) with (rw r 140). lia. }
  constructor. { cbn [holds]. change (eval r cur) with (rw r 140). change (eval r gl) with (rw r 141). lia. }
  constructor. { cbn [holds]. rewrite Eg8l, V_last. lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 gl) 7 (8 * l) Eg8l) by lia. rewrite V_last. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r gl) with (rw r 141). lia. }
  constructor.
Qed.
End Vals.

Lemma in_facts_Z : ltac2:(tb__ "0|e|
S1S6bR1Vib;Vil;Vio;A4S16S1cZ1M0S14Q40M1S2R2P12M2A2A2M3A2S1cG3S1eZ2M4Z28A2A2A2S23S0S3R3A1S2cS0S50S49P8eM5Vopd;A3S2cS0S50S4eP8dM6Vlastx;A3S2aS0ScSbS89S6eS49A1S6eS4eA1A3A1S2bS0A1A3A3A3A3S14G1S2R4Vib;A2A2S25S14G1S2R5Vio;A2A2S25S14G1S2R6G2A2A2S25S14G1S2R7G5A2A2S25S14G1S2R8G6A2A2S25S16S16S1cS20Z8M7R2A2M8S1dR5R4A2M9A2S1cG9S1dG8Z7MaA2A2A2S16S1fR2S1eG4Z3dA2MbA2S16S16S1cS20G7R1A2McS21S1dG9R3A2G0A2MdA2S1cGdS1dGcGaA2A2A2S16S1fR1GbA2S1fR2R1A2A2A2A2A2Tl;Tg;TN;TO;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  have_fact A1 HF (SPUle (g8 gs) opd). have_fact A2 HF (SPUle opd (add (g8 gs) (SLit 7))). have_fact A3 HF (SPUle gs (SLit (2 ^ 61 - 1))).
  have_fact A4 HF (SPUle (g8 gl) lastx). have_fact A5 HF (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A6 HF (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A7 HF (SPNot (SPBranch BC_GEU (shp gs) (shp gl))).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A6 by lia.
  change (eval rho gs) with (rw rho 142) in A3. change (eval rho gl) with (rw rho 141) in A6.
  assert (Hg : bv_unsigned (rw rho 142) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 142 Hg) as Eg. pose proof (V_g8 rho 141 Hl) as El. unfold gs in A1, A2, A7. unfold gl in A4, A5, A7.
  rewrite Eg in A1. rewrite El in A4.
  pose proof (V_opd rho HZ HN) as Vo. pose proof (V_last rho HZ HN) as Vl.
  rewrite Vo in A1. rewrite Vo in A2. rewrite Vl in A4. rewrite Vl in A5.
  unfold add in A2, A5.
  pose proof (U_addc rho (g8 (SVar 142)) 7 _ Eg ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A5.

  cbn [holds branch_taken] in A7. unfold bv_ltu in A7.
  pose proof (V_shp rho 142 ltac:(lia)) as S1. pose proof (V_shp rho 141 ltac:(lia)) as S2.
  assert (Hgl : bv_unsigned (rw rho 142) < bv_unsigned (rw rho 141)).
  { destruct (Z.ltb_spec (UU rho (shp (SVar 142))) (UU rho (shp (SVar 141)))) as [Hlt|Hge];
      [rewrite S1, S2 in Hlt; lia | exfalso; apply A7; reflexivity]. }
  cbv zeta. repeat split; lia.
Qed.

Lemma bk_facts_Z : ltac2:(tb__ "0|8|
S1S6bR1Vib;Vil;Vio;A4S16S1cZ1M0S14Q40M1S2R2P12M2A2A2M3A2S1cG3S1eZ2M4Z28A2A2A2S23S0S3R3A1S2cS0S45VvB;VvL;Vlastx;A3S2aS0SbS8bS72S44G0A2S6eS4eA1A3S2bS0A1A3A3A3S14G1S2R4Vib;A2A2S25S14G1S2R5Vil;A2A2S25S14G1S2R6Vio;A2A2S25S14G1S2R7G2A2A2S25S14G1S2R8P8cA2A2S25S14G1S2R9P8dA2A2S25S16S1cR6S20Z8M5R2A2A2S16S1fR2R1A2S16S1fR1S1eG4Z3dA2A2S16S16S1cS20G5R1A2M6S21S1dS1dR6R4A2R3A2G0A2M7A2S1cG7S1dG6Z7A2A2A2S1bS17S25S1dR2G0A2R1A3A1A2A2A2A2Tl;Tc;TN;TO;TL;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  apply Forall_app in HF as [HL HB].
  have_fact A1 HL (SPUle vB (g8 cur)). have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). have_fact A4 HL (SPUlt cur gl).
  have_fact A5 HL (SPUle (g8 gl) lastx). have_fact A6 HL (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A7 HL (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A8 HB (SPBranch BC_NE (shpk cur 1) (shp gl)).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A7 by lia.
  change (eval rho cur) with (rw rho 140) in A3, A4. change (eval rho gl) with (rw rho 141) in A4, A7.
  change (eval rho vB) with (rw rho ib) in A1.
  assert (Hc : bv_unsigned (rw rho 140) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 140 Hc) as Ec. pose proof (V_g8 rho 141 Hl) as El. unfold cur in A1, A8. unfold gl in A5, A6, A8.
  rewrite Ec in A1. rewrite El in A5. pose proof (V_last rho HZ HN) as Vl. rewrite Vl in A5. rewrite Vl in A6.
  unfold add in A6. pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A6.

  cbn [holds branch_taken] in A8. unfold bv_eqb in A8. apply negb_true_iff in A8. apply Z.eqb_neq in A8.
  pose proof (V_shp rho 141 ltac:(lia)) as S2. rewrite S2 in A8.
  unfold shpk, add in A8.
  rewrite (U_addc rho (SVar 140) (SHB + 1) (bv_unsigned (rw rho 140)) eq_refl) in A8 by (unfold SHB; lia).
  cbv zeta. repeat split; try lia.
Qed.
End LoopZ.

Ltac split_mid HF HX HT :=
  cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Lemma FT_Z : ltac2:(tb__ "0|1|
S1S23S0S3R1A1S41A3S16S6bR2PfP10P11A4S16S6bR2P13P34P35A4S16S1cZ1S14Q40S2R2P12A2A2M0A2S1cG0S1eZ2Z28A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold FT in HF. apply Forall_app in HF as [_ HB].
  destruct (base_mc_Z rho HB) as (ZD & ZS & ZN & _). auto.
Qed.

Lemma opZ_sub : ltac2:(tb__ "0|1|
S1S3cS26S26S26S82R3S38A2M0G0G0S17S28S3eR7S38A2S29A3S6bR9R7R6R5A4S6bS3bRaR9A2R8R7R6A4F_;F_;F_;F_;F_;Fio;Fil;Fib;Fs;Frho;").
Proof.
  intros rho s ib il io Hb Hl Ho Hid HZ.
  assert (E : forall v, (v < NF)%positive -> rw (rho_sub rho s) v = rw rho v).
  { intros v Hv. rewrite rw_sub, (wsub_get_id s NF v Hid Hv). reflexivity. }
  unfold opZ in *. cbv zeta in *.
  rewrite (E ib Hb), (E il Hl), (E io Ho), (E 18%positive eq_refl). exact HZ.
Qed.

Section Glue.
Variable rho : valuation.

Lemma glue_Ls_in : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5fA1A1A3S23S0S3S3bVrho;S58A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_in).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 19)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 53)) as R53.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E19, ?E52, ?E53; unfold HSE in *; lia.
Qed.

Lemma glue_Ls_bk : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5eA1A1A3S23S0S3S3bVrho;S57A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_bk).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ls_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E19, ?E52, ?E53, ?E141; unfold HSE in *; try lia.
Qed.

Lemma glue_Ld_in : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS5dA1A1A3S23S0S3S3bVrho;S56A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_Ld_bk : ltac2:(tb__ "0|0|
S23S0S3Vrho;A1S6S2fS4fA1A1A3S23S0S3S3bVrho;S55A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_Ls_in : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S58A2S44A2S4Vrho;S49A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ls_bk : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S57A2S44A2S4Vrho;S6dS44S9Z1A1A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_in : ltac2:(tb__ "0|1|
S17S15Q40A1S4S3bVrho;S56A2S6dS44S9S1eZ2Z3eA2A1M0A2A2S4Vrho;S6dS49G0A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_bk : ltac2:(tb__ "0|2|
S23S0S3Vrho;A1S6S2fS4fA1A1A3S1cS14Q40M0S4Vrho;S6dS44S9S1dS1eZ2Z3eA2M1Z1A2A1A2A2A2S14G0S4S3bVrho;S55A2S6dS44S9G1A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT. apply Forall_app in HX as [HL _].
  have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia.
  change (eval rho cur) with (rw rho 140) in A3. pose proof (urange (rw rho 140)) as R140.
  assert (E1 : bv_unsigned (rw (rho_sub rho s_Ld_bk) 140) = bv_unsigned (rw rho 140) + 1).
  { rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur. apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  unfold add, cur.
  rewrite (U_addc rho (SVar 140) (2 ^ 62 + 1) (bv_unsigned (rw rho 140)) eq_refl) by lia.
  rewrite (U_addc (rho_sub rho s_Ld_bk) (SVar 140) (2 ^ 62) (bv_unsigned (rw rho 140) + 1) E1) by lia.
  lia.
Qed.
End Glue.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S46S31S1S23S0S3R1A1S6S2fS46A1A1A3S23S0S3R2A1S41A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fS47A1A1A3S23S0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1S23S0S3R1A1S6S2fS4bA1A1A3S23S0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S16S81S38S5S2fS46A1A1A2S16S81S38S5S2fS47A1A1A2S81S38S5S2fS4bA1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S27S0A1S1S23S0S3R1A1S6S2fS78R2S46A2A1A1A3S23S0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S27S0A1S1S23S0S3R1A1S6S2fS78R2S47A2A1A1A3S23S0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Definition clsZ (rho : valuation) (ib il : positive) : Prop := ltac2:(tb__ "0|2|
S18S1cS6fS14Q40M0S2Vrho;Vib;A2A2M1A2S1cS1dG1S14G0S2Vrho;Vil;A2A2A2S21S12Z8A2A2A2").
Lemma hi_fact_holds : ltac2:(tb__ "0|0|
S1S26S1cS6fS14Q40S2R2R1A2A2A2S23S0S3R3A1S2aS0S64S7R2A1A1S2bS0A1A3A3F_;Fib;Frho;").
Proof. intros rho ib H. constructor; [|constructor]. unfold hi_fact. cbn [holds]. rewrite (U_lit64 rho HSE) by (unfold HSE; lia). exact H. Qed.
Lemma lo_fact_holds : ltac2:(tb__ "0|1|
S1S26S26S1cS1dS14Q40M0S2R3R2A2A2S14G0S2R3R1A2A2A2S21S12Z8A2A2S23S0S3R4A1S2aS0S65S7R3A1S7R2A1A2S2bS0A1A3A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. pose proof (urange (rw rho ib)). pose proof (urange (rw rho il)). constructor; [|constructor]. unfold lo_fact, add. cbn [holds].
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl) by (unfold SHB in H; lia).
  rewrite (U_lit64 rho (SHB - 8)) by (unfold SHB; lia). exact H.
Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS69S86S32R2A1S46S62A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS67S86S32R2A1S47S60A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S30S3fS30R1S8cA3S17S28S40S0S8S5S2fS7eS68S8dS32R2A1S4bS61A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[<-|[]]]; [exact (proj1 (proj2 (proj2 FT_below_T))) | exact (proj2 (proj2 (proj2 FT_below_T)))]. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S37S11Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S31S3fS31R1S63A3S1S75S11Vok;S33S11S79S1SaS38R6R1A3Lr;VJ;A2R3R1R4A5S34S11VJ;S38R5R4S42A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[<-|[]]]; [in_nth 4 | in_nth 5].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_in CLs_0 (F_L vBs vLs lasts) s_Ls_in tp);
      [in_nth 6 | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_bk CLs_0 (F_L vBs vLs lasts) s_Ls_bk tp);
      [in_nth 6 | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_bk r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_in CLd_0 (F_L vBd vLd lastd) s_Ld_in tp);
      [in_nth 7 | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_bk CLd_0 (F_L vBd vLd lastd) s_Ld_bk tp);
      [in_nth 7 | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_bk r HF)].
Qed.

Theorem memcpy_icpt_sum1 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Lemma etriple_SPA_pure' : ltac2:(tb__ "0|2|
S35S31S1S27S15Q40A1A1M0S74OF_;S27S3aA1M1S39R7R5R4R2R1A4S73S11S33S11S1G0G1S39S16RcR4R3R2R1A4S16S17G1R2R7A3S17S39R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A3F_;Fmd;Ftr;S73S11S33S11R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H w [Hsm Hk]. destruct w as [tr [ms md]]. apply (H tr md Hk). split; [exact Hsm|]. cbn. auto.
Qed.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S77S3fS77R1S6aA3S1S73S11S33S11S79S1SaS38R6R1A3Lr;VJ;A2S7aR3A1R1R4A5S34S11VJ;S38R5R4S42A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_icpt 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[<-|[]]].
      * exists (mkVNA T3a 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
      * exists (mkVNA T3b 39 (SLit (2 ^ 63 + 8))). split; [in_nth 5|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_in 151 gs) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_in tp);
      [in_nth 6 | reflexivity | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_bk 151 (add cur (SLit 1))) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_bk tp);
      [in_nth 6 | reflexivity | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_in 101 (add gs (SLit (2 ^ 62)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_in tp);
      [in_nth 7 | reflexivity | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ld_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_bk 101 (add cur (SLit (2 ^ 62 + 1)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_bk tp);
      [in_nth 7 | reflexivity | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_bk r HF) | right; split; [cbn [vna_var]; exact (meas_Ld_bk r HF) | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem memcpy_icpt_sum1_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Lemma soff_var' : ltac2:(tb__ "0|1|
S1S26S1fS14Q40M0S2R2R1A2A2S1eZ2Z3fA2A2S17S25SfR3S7R2A1A2S14G0S2R3R2A2A2A3F_;Fi;Frho;").
Proof.
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (urange (rw rho i)). lia.
Qed.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S27S15Q40A1A1M0S74S18S33S11S1G0S27S3aA1S39S1aL_;L_;L_;L_;S43Vrho;R2R1A6S19S35S35S33S11R1S43Vrho;R3R2A6LJ;A2A2S1fVn;S1eZ2Z3fA2A2S18S1cS1dVa;Vn;A2Vb;A2S18S1cS1dVb;Vn;A2Va;A2S17S25Vn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|5|
S23S0S3Vrho;A1S48A3S16S17S25Va;S1dS14Q40M0S2Vrho;PfM1A2A2S14G0S2Vrho;P11M2A2A2A2A3S16S17S25Vb;S1dS14G0S2Vrho;P13M3A2A2S14G0S2Vrho;P35M4A2A2A2A3S16S6bVrho;G1P10G2A4S16S6bVrho;G3P34G4A4S16S1cZ1Vn;A2S1cVn;S1eZ2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [exact (V_opd 15 16 17 rho ZD ZN)|]. split; [exact (V_opd 19 52 53 rho ZS ZN)|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
S10S25S17S25S14Q40S4Vrho;R2A2A2R1A3S1cS1dR2Vn;A2S21S1eZ2Z40A2Z1A2A2S3Vrho;ScSbS8aSdS88R4S9ZffffffffffffffffA1A3S70A3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S23S0S3Vrho;A1M0S48A3S1cS1dVa;Vn;A2Vb;A2S23S0G0S2aS0S53S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S23S0S3Vrho;A1M0S48A3S1cS1dVb;Vn;A2Va;A2S23S0G0S2aS0S54S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S53S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S54S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S35S27S15Q40A1A1S74S33S11R3S43Vrho;R2R1A6S18S33S11R4S4cVrho;R3R2A6S33S11R4S4dVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem memcpy_icpt_sum : ltac2:(tb__ "0|2|
S74OF_;S35S1S27S15Q40A1A1M0S37S11R4R3A3S36S11S38R4A3S1G0S27S3aA1M1S39R9R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39RaR4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S75S11R8S33S11R7S43R6R5A5S34S11R7S38R6R5S42A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply memcpy_icpt_sum1 | apply memcpy_icpt_sum2]; assumption.
Qed.

Theorem memcpy_icpt_sum_ex : ltac2:(tb__ "0|2|
S35S1S27S15Q40A1A1M0S36S11S38R3A3S1G0S27S3aA1M1S39R8R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39R9R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S73S11S33S11R6S43R5R4A5S34S11R6S38R5R4S42A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply memcpy_icpt_sum1_ex | apply memcpy_icpt_sum2_ex]; assumption.
Qed.
End Icpt_memcpy_proof.

(* [comment removed for export] *)
Module Icpt_memchr_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "nat"; "bool"; "option"; "Some"; "list"; "false"; "app"; "pair"; "prod"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "SAlu"; "sv"; "ss_next"; "sobj"; "cell"; "mkObj"; "SPEq"; "ss_lenient"; "DImage"; "SPAlign"; "FcsrFrm0"; "SPBranch"; "mkSS"; "sprop_below"; "sstate"; "swf"; "DList"; "DUnknown"; "mkCell"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "mkLeafA"; "la_state"; "axwf"; "entailsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GEU"; "BC_LTU"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "vXB"; "vXL"; "CUTS_MCI"; "FUEL_MCI"; "sX"; "facts_mci"; "E_call"; "E_ripS"; "P_mci"; "Pre_mci"; "vXL8"; "vXO"; "N1"; "s_call"; "D_MCI"; "E_rip"; "G_B"; "G_S"; "R_B"; "R_S"; "R_call"; "R_rip"; "T_B"; "T_S"; "T_rip"; "T_ripF"; "s_rip"; "ENDA"; "T_imp"; "X_mci"; "mci_ret"; "objs_mci"; "sp_B"; "sp_S"; "GEU65"; "O_realmc"; "O_strS"; "O_win"; "XB"; "XS"; "big_facts"; "factsB"; "factsS"; "mci_entry"; "post_facts"; "rip8_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "two62"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsFuel"; "RsSymJump"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "opp"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "Pre_memchr0"; "P_ret"; "Posts_memchr0"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "HSE"; "O_rtc2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA.MCHAddr"; "memchr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition mci_entry : Z := 0x4e8f8.
Definition mci_ret : Z := 0x4e9d8.

Definition O_realmc : sobj := ltac2:(tb__ "0|0|
S16SeZ0A1SeZe99a8A1SeZe99b0A1S2S15A1S19A5").
Definition O_realsn : sobj := ltac2:(tb__ "0|0|
S16SeZ0A1SeZe9a98A1SeZe9aa0A1S2S15A1S19A5").
Definition O_cfsl : sobj := ltac2:(tb__ "0|1|
S16SeZ0A1SeZ183020A1M0SeZ183028A1S0S15S23G0Z8SeZ101010101010101A1A3S2S15A1A3S19A5").
Definition D_MCI : Z := 2208.
Definition O_win : sobj := ltac2:(tb__ "0|0|
S16S10PaA1SeS76S43A1A1SeZ0A1S2S15A1S22A5").
Definition vXB := SVar 18. Definition vXL := SVar 19. Definition vXO := SVar 20.
Definition sX : sv := SAlu ALU_ADD vXB vXO.
Definition O_strS : sobj := ltac2:(tb__ "0|0|
S16S39SeZ0A1S10P11A1S2S15A1S21P3A1A5").
Definition facts_mci : list sprop := ltac2:(tb__ "0|d|
S0SdS1cS32S10P10A1M0S10PeA1M1A3S0SdSfS11S30G0SeZ8A1M2A3S10P11A1M3A2S0SdSfG2G3A2S0SdSfG3SeS6cA1M4A2S0SdSfG1G4A2S0SdSfSeZ1A1M5S39A2S0SdSfS39G4A2S0SdS1aPaM6Z4A2S0SdSfSeS78S65Z1000A2A1S10G6A1M7A2S0SdSfG7SeS75Z2M8Z2fA2M9A1MaA2S0SdSfS11S30S40G3A3S36A2S0SdSfS40S36A2S0SdSfG3S36A2S0SdSfS36SeS75G8Z28A2A1A2S0SdSfSeS88A1S35A2S0SdSfS11S30S35S36A3MbGaA2S0SdSfS35SeS77G9Z40A2A1A2S0SdS1aP12Z6McA2S0SdS1aP13GcA2S0SdSfS11S30S39G5A3GbA2S0SdSfS11S30G0SeZ10A1A3G3A2S2SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_mci : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS12S12A2M0SaS12S12S35S36A4S0G0SaS12S12S11S30S10PaA1SeS76S43A1A1A3SeS43A1A4S2G0A1A3A3").
Definition objs_mci : list sobj := ltac2:(tb__ "0|0|
S9S14S0S14S5aS0S14S59S0S14S87S0S14S89S0S14S58S2S14A1A3A3A3A3A3S66A3").
Definition Pre_mci : axst := ltac2:(tb__ "0|1|
S64S1dS60S69S6bS0SbS3S12A2M0SaS3S12UaS39A4S0G0SaS3S12UbSeZ0A1A4S2G0A1A3A3A2S68S1bScS12A1S54S3aS67S8A9S52A2").
Definition CUTS_MCI : ltac2:(tb__ "0|0|
S7S34A1") := ltac2:(tb__ "0|0|
S0S34S8dS0S34S8bS0S34S53S2S34A1A3A3A3").
Definition FUEL_MCI : nat := 400%nat.
Definition lf0 (S : axst) (r : option (list leafA)) (i : nat) : axst := ltac2:(tb__ "0|1|
S5S7S28A1M0A1S2aLr;Vr;G0S2dS81S28Vi;R1S2cVS;S73A2A4A1Lls;VS;X5x2").

Definition run_call__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S3eS1A5").
Local Strategy expand [run_call__R].
Definition E_call : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre_mci (ro1__) 0) run_call__R).
Definition s_call : wsub := Eval vm_compute in infer_sub 10 (ax_S E_call) (ax_S Pre_memchr0).
Definition R_call : list sobj := Eval vm_compute in match entails_frA E_call Pre_memchr0 s_call with Some R => R | None => [] end.
Definition T_imp : axst := Eval vm_compute in import_postA s_call Pre_memchr0 P_ret E_call R_call.
Definition T_impF : axst := ax_add_facts facts_mci T_imp.

Definition ENDA : sv := ltac2:(tb__ "0|0|
S11S30S11S30S39S11S30S10P8cA1SeZ1A1A3A3SeN1A1A3").
Definition post_facts : list sprop := ltac2:(tb__ "0|0|
S0SdSfS35S50A2S0SdSfS11S30S50SeZ1A1A3S11S30S35S36A3A2S2SdA1A3A3").
Definition GEU65 : sprop := ltac2:(tb__ "0|0|
S1cS31SeZffffffffffffffbfA1S11S30S10P8cA1SeN40A1A3A3").
Definition factsS : list sprop := SPNot GEU65 :: post_facts.

Definition vXL8 : sv := SAlu ALU_ADD vXL (SLit (-8)).
Definition rip8_facts (n : sv) : list sprop := ltac2:(tb__ "0|3|
S0SdSfS11S30S40Vn;A3S3fA2S0SdSfS40S3fA2S0SdSfVn;S3fA2S0SdSfS3fSeS75Z2M0Z28A2A1A2S0SdSfS11S30S35S3fA3M1SeS77S75G0Z2fA2Z8A2A1M2A2S0SdSfS35G2A2S0SdSfS35G1A2S0SdSfG1S11S30S35S36A3A2S2SdA1A3A3A3A3A3A3A3A3").
Definition N1 : sv := SAlu ALU_ADD (SVar 140) (SLit 1).
Definition big_facts : list sprop := ltac2:(tb__ "0|0|
S9SdS0SdSfS11S30S40S41A3S36A2S0SdSfS41S36A2S0SdSfSeZ1A1S41A2S2SdA1A3A3A3S62S41A1A3").
Definition factsB : list sprop := ltac2:(tb__ "0|0|
S0SdS57S9SdS61S5dA3A3").
Definition T_S : axst := ax_add_facts factsS T_impF.
Definition T_B : axst := ax_add_facts factsB T_impF.

Definition run_S__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4cS1A5").
Local Strategy expand [run_S__R].
Definition R_S : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 T_S (ro2__) 0) run_S__R).

Definition run_B__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4bS1A5").
Local Strategy expand [run_B__R].
Definition E_rip : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T_B (ro3__) 0) run_B__R).
Definition E_ripS : axst := Eval vm_compute in match split_obj_at (ax_S E_rip) 1 (SLit (-2128)) with Some S' => ax_setS E_rip S' | None => E_rip end.
Definition s_rip : wsub := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E_ripS) (ax_S Pre_rip)).
Definition R_rip : list sobj := Eval vm_compute in match entails_frA E_ripS Pre_rip s_rip with Some R => R | None => [] end.
Definition T_rip : axst := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.P_ret E_ripS R_rip.
Definition T_ripF : axst := ltac2:(tb__ "0|0|
S8fS0SdS17S10P8cA1S10P10A1A2S3aA3S4dA2").
Definition run_B2__R : option (list leafA) := ltac2:(tb__ "0|0|
S2bS63S38S37S4eS1A5").
Local Strategy expand [run_B2__R].
Definition R_B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => lf0 T_ripF (ro4__) 0) run_B2__R).

Definition XS : list axform := ltac2:(tb__ "0|0|
S0S6dS6eS0S3U1S0S3U0S0S3U2S0S3U3S0S3U4S0S3U5S0S3U6S2S3A1A3A3A3A3A3A3A3A1S2S6dA1A3").
Definition XB : list axform := ltac2:(tb__ "0|1|
S0S6dS71U0M0A1S0S6dS6eS0S3G0S0S3U5S0S3U4S0S3U6S0S3U1S0S3U7S0S3U2S0S3U3S2S3A1A3A3A3A3A3A3A3A3A1S0S6dS70G0A1S2S6dA1A3A3A3").
Definition G_S : axst := Eval vm_compute in match apply_axforms R_S XS with Some A => A | None => R_S end.
Definition G_B : axst := Eval vm_compute in match apply_axforms R_B XB with Some A => A | None => R_B end.
Definition P_mci0 : axst := ltac2:(tb__ "0|1|
S64S1dS53S69S6aS67A1S0SbS3S12A2M0SaS3S12UaS11S30S39S10P8cA1A3A4S2G0A1A3A2S68S1bScS12A1S54S3aP8dS8A9S52A2").
Definition F_post : list sprop := ltac2:(tb__ "0|0|
S0SdS17S10P8cA1S10P10A1A2S2SdA1A3").
Definition P_mci : axst := ax_add_facts F_post P_mci0.
Definition Posts_mci : list leafA := ltac2:(tb__ "0|0|
S0S28S2cS3dS74A2S2S28A1A3").
Definition sp_S : wsub := Eval vm_compute in infer_sub NF (ax_S G_S) (ax_S P_mci0).
Definition sp_B : wsub := Eval vm_compute in infer_sub NF (ax_S G_B) (ax_S P_mci0).

Lemma mci_wf : ltac2:(tb__ "0|0|
S27S26S4S2eS3eA1S1A3S27S26S4S20S29S3eA1A1S1A3S27S26S4S2eS3dA1S1A3S26S4S20S29S3dA1A1S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma run_call : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S3eS1A5S6G0S0S28S2cS3bS72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_call__R <: run_call__R = Some [mkLeafA E_call RsCut]). Qed.
Lemma efr_call : ltac2:(tb__ "0|1|
S26S5S7S14A1M0A1S85S3bS7aS42A3S6G0S49A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_call : ltac2:(tb__ "0|0|
S26S4S84S3bS7aS42S49S80S28S2aS2dS7cA4A5S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_call : ltac2:(tb__ "0|0|
S26S2aS86S42S7aS7bS3bS49A5S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_S : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4cS1A5S6G0S0S28S2cS48S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_S__R <: run_S__R = Some [mkLeafA R_S RsCut]). Qed.
Lemma run_B : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4bS1A5S6G0S0S28S2cS44S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_B__R <: run_B__R = Some [mkLeafA E_rip RsCut]). Qed.
Lemma split_rip : ltac2:(tb__ "0|0|
S26S5S1fA1S8eS29S44A1U1SeN850A1A3S6S1fS29S3cA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma efr_rip : ltac2:(tb__ "0|1|
S26S5S7S14A1M0A1S85S3cS79S4fA3S6G0S4aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_rip : ltac2:(tb__ "0|0|
S26S4S84S3cS79S4fS4aS80S28S2aS2dS8cA4A5S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_rip : ltac2:(tb__ "0|0|
S26S2aS86S4fS79S8aS3cS4aA5S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma run_B2 : ltac2:(tb__ "0|1|
S26S5S7S28A1M0A1S2bS63S38S37S4eS1A5S6G0S0S28S2cS47S72A2S2S28A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_B2__R <: run_B2__R = Some [mkLeafA R_B RsCut]). Qed.
Lemma xf_S : ltac2:(tb__ "0|0|
S26S5S2aA1S6fS48S5cA2S6S2aS46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma xf_B : ltac2:(tb__ "0|0|
S26S5S2aA1S6fS47S5bA2S6S2aS45A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_S : ltac2:(tb__ "0|0|
S26S4S2fS46S3dS56A3S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_B : ltac2:(tb__ "0|0|
S26S4S2fS45S3dS55A3S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mci : ltac2:(tb__ "0|0|
S27S26S4S82S56S67A2S1A3S26S4S82S55S67A2S1A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma shape_call : ltac2:(tb__ "0|2|
S27S26S33S13S29S3bA1A1S67A3S27S26S4S18S29S3eA1M0A1S8A3S27S26S33S13G0A1S67A3S26S12S83S42P10M1A2S10G1A1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_imp : ltac2:(tb__ "0|5|
S27S26S33S13S29S51A1M0A1P8dM1A3S27S26S4S18S29S4cA1M2A1S8A3S27S26S33S13G2A1G1A3S27S26S4S18S29S4bA1M3A1S8A3S27S26S33S13G3A1G1A3S27S26S4S7eSdS24S17S10P8cA1S10P10A1A2A1S25G0A1A3S1A3S27S26S4S7dSdS1eG1A1M4S9SdS5fS3aA3A3S1A3S26S4S7dSdG4S9SdS5eS3aA3A3S1A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_rip : ltac2:(tb__ "0|3|
S27S26S33S13S29S3cA1A1S13S29S44A1A1M0A3S27S26S33S13S29S4dA1A1Pb5M1A3S27S26S4S18S29S4eA1M2A1S8A3S27S26S33S13G2A1G1A3S27S26S4S7fP8dG0A2S1A3S26S4S7dSdS1eG1A1S0SdS17S10P8cA1S10P10A1A2S3aA3A3S1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shape_ret : ltac2:(tb__ "0|2|
S27S26S33S13S29S48A1A1M0S13S29S46A1A1A3S27S26S33S13S29S47A1A1M1S13S29S45A1A1A3S27S26S4S7fP8dG0A2S1A3S26S4S7fPb5G1A2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_memchr_st.

(* [comment removed for export] *)
Module Asan_memcpy.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "bool"; "true"; "prod"; "app"; "Some"; "list"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "mkCell"; "sprop"; "sobj"; "mkObj"; "DUnknown"; "SAlu"; "sprop_below"; "ss_next"; "SPBranch"; "SPUle"; "FcsrFrm0"; "mkSS"; "DImage"; "SPNot"; "SPAlign"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "tv"; "dst"; "cur"; "gl"; "gs"; "src"; "F_L"; "vBd"; "vBs"; "vLd"; "vLs"; "F8of"; "lastd"; "lasts"; "X_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "xor_facts"; "O_dst"; "O_real"; "O_rtc3"; "O_src"; "ord1"; "ord2"; "vOd"; "vOs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "add"; "shp"; "P_ret"; "shpk"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Asan_memcpy"; "mid_state"; "E_real"; "FT"; "E_dst"; "E_src"; "R_dst"; "R_src"; "s_dst"; "s_src"; "CLd_0"; "CLs_0"; "R_real"; "s_real"; "E_Ld_bk"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "P_amc"; "ld_regs"; "ls_regs"; "objs_mc"; "spm"; "CLd"; "CLs"; "E_dst_hi"; "E_dst_lo"; "E_src_hi"; "E_src_lo"; "FUELM"; "Pre_mc0"; "Pre_mc1"; "Pre_mc2"; "T1"; "T2"; "T3a"; "T3b"; "base_mc"; "cutpcs_mc"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "O_cstk"; "O_frame"; "O_rest"; "T1r"; "T2r"; "T3ar"; "T3br"; "cuts_mc"; "exits_mc"; "frame_cells"; "mid_regs"; "vDp"; "vcuts_mc"; "vexits_mc"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Asan_memcpy.AMCAddr"; "ld_head"; "ls_head"; "musl_memcpy"; "mc_entry"; "mc_ret"; "ra_dst"; "ra_real"; "ra_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Pre_memcpyA"; "liftA"; "memcpy_entryA"; "Posts_memcpyA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "segs"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "P_retA"; "P_retB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module AMCAddr.
  Definition mc_entry : Z := 0x5c84c.
  Definition mc_ret : Z := 0x5c974.
  Definition ra_src : Z := 0x5cbf0.
  Definition ra_dst : Z := 0x5cc90.
  Definition ra_real : Z := 0x5c948.
  Definition ls_head : Z := 0x5cbc0.
  Definition ld_head : Z := 0x5cc64.
  Definition musl_memcpy : Z := 0xddf74.
End AMCAddr.
Import AMCAddr.

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SfN48A1Z8M0SeP2bA1A3S0S10S11SfN40A1G0SeP2aA1A3S0S10S11SfN38A1G0SeP29A1A3S0S10S11SfN30A1G0SeP28A1A3S0S10S11SfN28A1G0SeP27A1A3S0S10S11SfN20A1G0SeP26A1A3S0S10S11SfN18A1G0SeP1dA1A3S0S10S11SfN10A1G0SeP1cA1A3S0S10S11SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SfN860A1SfZ0A1Vcs;S15A5").
Definition spm : sv := add (SVar 10) (SLit (-2144)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S14S67SfN50A1SfZ0A1S3S10A1S15A5").
Definition vDp : sv := SVar 95.
Definition O_rest : sobj := ltac2:(tb__ "0|0|
S14SePaA1S87SfN8b0A1S3S10A1S15A5").
Definition objs_mc (fr : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S7dVfr;A1S0S13S7cS0S13S7eS0S13S3dS0S13S40S0S13S3fS0S13S51S0S13S3eS3S13A1A3A3A3A3A3A3A3A3SabA3").

Definition base_mc : list sprop := ltac2:(tb__ "0|3|
S7S12S3bS31S33S43PfA4S7S12S3bS32S34S44P13A4S0S12S1aSfZ1A1S4cA2S0S12S1aS4cSfS8aZ2M0Z28A2A1A2S0S12S1fPaM1Z4A2S0S12S1aSfS8bSaaZ900A2A1SeG1A1M2A2S0S12S1aG2SfS8aG0Z3fA2A1A2S3S12A1A3A3A3A3A3A3A3").
Definition FT : list sprop := xor_facts ++ base_mc.

Definition Pre_mc0 : axst := ltac2:(tb__ "0|1|
Sa8S1cS9dS8fS90S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S3G0A1A3A3A3A2S8eS1bSbSdA1S66S3S10A1A1S76S8dScA9S38A2").
Definition Pre_mc1 : axst := ltac2:(tb__ "0|0|
S47S0S12S41S3cA3S6fA2").
Definition Pre_mc2 : axst := ltac2:(tb__ "0|0|
S47S0S12S42S3cA3S6fA2").

Definition P_amc : axst := ltac2:(tb__ "0|1|
Sa8S1cS9eS8fS92S8dA1S0S6S2SdA2M0S1S2SdUaS2bA4S3G0A1A3A2S8eS1bSbSdA1S66S3S10A1A1S76S91ScA9S38A2").
Definition Posts_mc : list leafA := ltac2:(tb__ "0|0|
S0S25S29S63SadA2S3S25A1A3").

Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|17|
S8fS90S7S6S2SdA2M0S0G0S1S2SdU1M1S2aG1A1A4S0G0S1S2SdU2S67A4S0G0S1S2SdU5M2S2aG2A1A4S0G0S1S2SdU6M3S2aG3A1A4S0G0S1S2SdU7M4S2aG4A1A4S0G0S1S2SdU8SePaA1A4S0G0S1S2SdU9M5S2aG5A1A4S0G0S1S2SdUaM6S2aG6A1A4S0G0S1S2SdUbM7S2aG7A1A4S0G0S1S2SdUcM8S2aG8A1A4S0G0S1S2SdUdM9S2aG9A1A4S0G0S1S2SdUeMaS2aGaA1A4S0G0S1S2SdUfMbS2aGbA1A4S0G0S1S2SdU10McS2aGcA1A4S0G0S1S2SdU11MdS2aGdA1A4S0G0S1S2SdU12MeS2aGeA1A4S0G0S1S2SdU13MfS2aGfA1A4S0G0S1S2SdU14S67A4S0G0S1S2SdU15M10S2aG10A1A4S0G0S1S2SdU16M11S2aG11A1A4S0G0S1S2SdU17M12S2aG12A1A4S0G0S1S2SdU1cM13S2aG13A1A4S0G0S1S2SdU1dM14S2aG14A1A4S0G0S1S2SdU1eM15S2aG15A1A4S0G0S1S2SdU1fM16S2aG16A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sa8S1cVpc;S86Vl;A1S8eS1bSbSdA1S66S85A1S7S12Vfacts;S54A3PbeScA9S38A2").

Definition E_src : axst := ltac2:(tb__ "0|1|
S52SacS0S6S2SdA2M0S1S2SdU1SfSa1A1A4S0G0S1S2SdUaS2fA4S0G0S1S2SdUbS4cA4S0G0S1S2SdU9S4cA4S0G0S1S2SdU13S4dS2bS4cA2A4S0G0S1S2SdU15S2bA4S0G0S1S2SdU16S4dS4cSfN41A1A2A4S0G0S1S2SdU17S2fA4S3G0A1A3A3A3A3A3A3A3A3S3S12A1A3").

Definition E_dst : axst := ltac2:(tb__ "0|1|
S52SacS0S6S2SdA2M0S1S2SdU1SfS9fA1A4S0G0S1S2SdUaS2bA4S0G0S1S2SdUbS4cA4S0G0S1S2SdU9S2bA4S0G0S1S2SdU15S2fA4S0G0S1S2SdU12S4cA4S3G0A1A3A3A3A3A3A3S3S12A1A3").

Definition E_src_hi : axst := ltac2:(tb__ "0|0|
S47S0S12S39S32A1S3S12A1A3S56A2").
Definition E_src_lo : axst := ltac2:(tb__ "0|0|
S47S0S12S3aS32S34A2S3S12A1A3S56A2").
Definition E_dst_hi : axst := ltac2:(tb__ "0|0|
S47S0S12S39S31A1S3S12A1A3S55A2").
Definition E_dst_lo : axst := ltac2:(tb__ "0|0|
S47S0S12S3aS31S33A2S3S12A1A3S55A2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S52S9cS0S6S2SdA2M0S1S2SdU1SfSa0A1A4S0G0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S3G0A1A3A3A3A3S3S12A1A3").

Definition ls_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS4eS2dA1A4S0G0S1S2SdU13S4dS2bS4cA2A4S0G0S1S2SdU16S4dS4cSfN41A1A2A4S3G0A1A3A3A3A3A3A3A3").
Definition CLs_0 : axst := ltac2:(tb__ "0|0|
S52S9bS65S4eS2cA1A1S3S12A1A3").
Definition CLs : axst := ltac2:(tb__ "0|0|
S47S30S32S34S37A3S5cA2").
Definition E_Ls_in : axst := ltac2:(tb__ "0|1|
S52S9bS65S4eS2eA1M0A1S7S12S35S2eP8eS2fA3S7S12S35S2dP8dS37A3S0S12S1eS19S4aG0S4eS2dA1A3A1S3S12A1A3A3A3A3").
Definition E_Ls_bk : axst := ltac2:(tb__ "0|1|
S52S9bS65S50S2cZ1A2M0A1S7S12S30S32S34S37A3S0S12S19S4bG0S4eS2dA1A3S3S12A1A3A3A3").

Definition ld_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2bA4S0G0S1S2SdUbS2fA4S0G0S1S2SdUcS4cA4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS4eS2dA1A4S3G0A1A3A3A3A3A3").
Definition CLd_0 : axst := ltac2:(tb__ "0|0|
S52S9aS64S4eS2cA1A1S3S12A1A3").
Definition CLd : axst := ltac2:(tb__ "0|0|
S47S30S31S33S36A3S5bA2").
Definition E_Ld_in : axst := ltac2:(tb__ "0|1|
S52S9aS64S4eS2eA1M0A1S7S12S35S2eP8eS2bA3S7S12S35S2dP8dS36A3S0S12S1eS19S4aG0S4eS2dA1A3A1S3S12A1A3A3A3A3").
Definition E_Ld_bk : axst := ltac2:(tb__ "0|1|
S52S9aS64S50S2cZ1A2M0A1S7S12S30S31S33S36A3S0S12S19S4bG0S4eS2dA1A3S3S12A1A3A3A3").

Definition s_src : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLs) :: infer_sub 1 (ax_S E_src) (ax_S Pre_rip)) in exact x).
Definition s_dst : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_dst) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 (ax_S E_real) (ax_S Pre_memcpyA)) in exact x).
Definition R_src : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_src_hi Pre_rip s_src with Some R => R | None => [] end) in exact x).
Definition R_dst : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_dst_hi Pre_rip s_dst with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_memcpyA s_real with Some R => R | None => [] end) in exact x).

Lemma fr_src_hi : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6cS94S5aA3S8G0S58A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_src_lo : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6dS95S5aA3S8G0S58A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_hi : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6aS94S59A3S8G0S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_lo : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S6bS95S59A3S8G0S57A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S22SaS9S13A1M0A1S98S53Sa3S5eA3S8G0S5dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_hi : ltac2:(tb__ "0|0|
S22S4S97S6cS94S5aS58S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_lo : ltac2:(tb__ "0|0|
S22S4S97S6dS95S5aS58S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_hi : ltac2:(tb__ "0|0|
S22S4S97S6aS94S59S57S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_lo : ltac2:(tb__ "0|0|
S22S4S97S6bS95S59S57S96S25S24S27Sa2A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S22S4S97S53Sa3S5eS5dS96S25S24S27Sa6A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T1r : axst := ltac2:(tb__ "0|0|
S99S5aS94S4fS56S58A5").
Definition T2r : axst := ltac2:(tb__ "0|0|
S99S59S94S4fS55S57A5").
Definition T3ar : axst := ltac2:(tb__ "0|0|
S99S5eSa3Sa4SaeSa5A1A1S53S5dA5").
Definition T3br : axst := ltac2:(tb__ "0|0|
S99S5eSa3Sa4SafSa5A1A1S53S5dA5").
Definition T1 : axst := ax_add_facts FT T1r.
Definition T2 : axst := ax_add_facts FT T2r.
Definition T3a : axst := ax_add_facts FT T3ar.
Definition T3b : axst := ax_add_facts FT T3br.

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S0S24S70S0S24S71S0S24S72S0S24S73S0S24S74S0S24S75S0S24S69S0S24S68S3S24A1A3A3A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S0S24S63S0S24S56S0S24S55S0S24S53S0S24S62S0S24S61S0S24S60S0S24S5fS3S24A1A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S21SacS0S21S9cS0S21S9bS0S21S9aS3S21A1A3A3A3A3").
Definition FUELM : nat := 800%nat.

Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S45S46S70Zc8M0SfZ0A1M1A3S0S45S46S71G0G1A3S0S45S46S72Z77SfS8aZ2M2Z3dA2A1A3S0S45S46S73Z4fSfS8aG2Z3fA2M3A1A3S0S45S46S74Z27M4SfS8bG3Z8A2A1M5A3S0S45S46S75G4G5A3S0S45S46S69Z96S2cA3S0S45S46S68Z64S4dS2cSfS8aG2Z3eA2A1A2A3S3S45A1A3A3A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S45S46S63Z0SfS8cS8aZ2M0Z40A2Z1M1A2A1A3S0S45S46S56Z78SfS8aG0Z3dA2A1A3S0S45S46S55Z50SfS8aG0Z3fA2M2A1A3S0S45S46S53Z28SfS8bG2Z8A2A1A3S0S45S46S62Z97M3S2eA3S0S45S46S61G3S4dS2cSfG1A1A2A3S0S45S46S60Z65M4S4dS2eSfS8aG0Z3eA2M5A1A2A3S0S45S46S5fG4S4dS2cSfS8bG5G1A2A1A2A3S3S45A1A3A3A3A3A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S22S4Sb0Sa9S6eS77S8dS88S89A6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_mc : ltac2:(tb__ "0|0|
S22S4S48Sa9S6eS77S8dS83S84A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Definition s_Ls_in : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS2eA4S3G0A1A3").
Definition s_Ls_bk : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS4dS2cSfZ1A1A2A4S3G0A1A3").
Definition s_Ld_in : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS2eA4S3G0A1A3").
Definition s_Ld_bk : wsub := ltac2:(tb__ "0|1|
S0S6S20SdA2M0S1S20SdP8cS4dS2cSfZ1A1A2A4S3G0A1A3").
Lemma ent_Ls_in : ltac2:(tb__ "0|0|
S22S4S28S62S5cS7bA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ls_bk : ltac2:(tb__ "0|0|
S22S4S28S61S5cS7aA3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_in : ltac2:(tb__ "0|0|
S22S4S28S60S5bS79A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_bk : ltac2:(tb__ "0|0|
S22S4S28S5fS5bS78A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mc : ltac2:(tb__ "0|0|
S23S22S4Sa7S7bS8dA2S5A3S23S22S4Sa7S7aS8dA2S5A3S23S22S4Sa7S79S8dA2S5A3S22S4Sa7S78S8dA2S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FLs_below : ltac2:(tb__ "0|0|
S22S4S93S12S17S18S26S5cA1A1A1S30S32S34S37A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FLd_below : ltac2:(tb__ "0|0|
S22S4S93S12S17S18S26S5bA1A1A1S30S31S33S36A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma FT_below_E : ltac2:(tb__ "0|0|
S22S4S93S12S17P64A1S54A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S23S22S4S93S12S17S18S26S7fA1A1A1S54A3S5A3S23S22S4S93S12S17S18S26S80A1A1A1S54A3S5A3S23S22S4S93S12S17S18S26S81A1A1A1S54A3S5A3S22S4S93S12S17S18S26S82A1A1A1S54A3S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Asan_memcpy.

(* [comment removed for export] *)
Module Start5bStates.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "Some"; "option"; "list"; "bool"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SLit"; "SVar"; "SPUle"; "ss_objs"; "sprop_eqb"; "SPAlign"; "ss_next"; "ss_pc"; "SAlu"; "SPEq"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "SPIN_MMAPORDIE"; "ECALL_MMAP"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Start5bStates"; "E_s14"; "E_s15"; "E_s15u"; "ECALL_MUNMAP"; "SPIN13"; "SPIN14"; "S_s13ok"; "S_s14ok"; "F13"; "F14"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_SLL"; "@Stdlib.Lists.List"; "existsb"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates"; "E_s13g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MUNMAP : Z := 0x70518.

Definition F13 : list sprop := ltac2:(tb__ "0|3|
S0S13S1aP4dM0ZcA2S0S13S17S15Z1000M1A1S16G0A1M2A2S0S13S17G2S15S39Z7fffff800000G1A2A1A2S1S13A1A3A3A3").
Definition S_s13ok : axst := ltac2:(tb__ "0|2|
S36S3bS2eS37SdS35A1M0S16P4dM1A1S7S14S18G0A1S0S14S38G1Z1000A2S1S14A1A3A3P4eA4A2A1").
Definition run13_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Ubb8S0S8S21S1S8A1A3S2cS2A5").
Local Strategy expand [run13_ok__R].
Definition E_s14 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_s13ok (ro1__)))) run13_ok__R).
Definition run13_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Uc8S0S8S20S1S8A1A3S22S35A1S2A5").
Local Strategy expand [run13_fail__R].
Definition SPIN13 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 (fail_state E_s13g) (ro2__)))) run13_fail__R).
Lemma run13_ok : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Ubb8S0S8S21S1S8A1A3S2cS2A5S3G0S0ScSfS26S23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run13_ok__R <: run13_ok__R = Some [mkLeafA E_s14 RsCut]). Qed.
Lemma run13_fail : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Uc8S0S8S20S1S8A1A3S22S35A1S2A5S3G0S0ScSfS2aS23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run13_fail__R <: run13_fail__R = Some [mkLeafA SPIN13 RsCut]). Qed.
Lemma spin13 : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12U2S0S8S20S1S8A1A3S2aS2A5S3G0S0ScSfS2aS23A2S1ScA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s14_at : ltac2:(tb__ "0|2|
SbSaS8S1cSdS26A1M0A1M1S21A3SbSaS9S1bG0A1P4eA3SaS4S30A1S24S12G1A2S3S30S31A2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F14 : list sprop := ltac2:(tb__ "0|3|
S0S13S1aP4eM0ZcA2S0S13S17S15Z1000M1A1S16G0A1M2A2S0S13S17G2S15S39Z7fffff800000G1A2A1A2S1S13A1A3A3A3").
Definition S_s14ok : axst := ltac2:(tb__ "0|2|
S36S3bS2fS37SdS26A1M0S16P4eM1A1S7S14S18G0A1S0S14S38G1Z1000A2S1S14A1A3A3P4fA4A2A1").
Definition run14_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Ubb8S0S8S29S0S8S21S1S8A1A3A3S2dS2A5").
Local Strategy expand [run14_ok__R].
Definition E_s15 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1 S_s14ok (ro3__)))) run14_ok__R).
Definition run14_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS12Uc8S0S8S20S1S8A1A3S22S26A1S2A5").
Local Strategy expand [run14_fail__R].
Definition SPIN14 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1 (fail_state E_s14) (ro4__)))) run14_fail__R).
Lemma run14_ok : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Ubb8S0S8S29S0S8S21S1S8A1A3A3S2dS2A5S3G0S0ScSfS27S23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run14_ok__R <: run14_ok__R = Some [mkLeafA E_s15 RsCut]). Qed.
Lemma run14_fail : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12Uc8S0S8S20S1S8A1A3S22S26A1S2A5S3G0S0ScSfS2bS23A2S1ScA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run14_fail__R <: run14_fail__R = Some [mkLeafA SPIN14 RsCut]). Qed.
Lemma spin14 : ltac2:(tb__ "0|1|
SaS4S5ScA1M0A1SeS12U2S0S8S20S1S8A1A3S2bS2A5S3G0S0ScSfS2bS23A2S1ScA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15_at : ltac2:(tb__ "0|2|
SbSaS8S1cSdS27A1M0A1M1S29A3SbSaS9S1bG0A1P4fA3SaS4S30A1S24S12G1A2S3S30S31A2A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_s15u : axst := Eval vm_compute in (drop_last_obj E_s15).
Lemma E_s15_split : ltac2:(tb__ "0|1|
SaS5S14A1S18SdS27A1A1M0S7S14S18SdS28A1A1S0S14S34S14G0S38P4eZ1000A2A3S1S14A1A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_s15u_eq : ltac2:(tb__ "0|0|
SaS11S10S27S25SdS27A1S18SdS28A1A1A2A2S28A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition S_s15ok : axst := ltac2:(tb__ "0|1|
S36S37SdS28A1M0S15Z0A1S18G0A1P4fA4A1").
Lemma E_s15u_facts : ltac2:(tb__ "0|3|
SbSaS6S33S13S19S17S16P1M0A1S15Z7fffffffff20A1A2A1S1fSdS28A1A1M1A3S2A3SbSaS6S33S13S19S1eS1dS32S16P23A1M2S15Z3A1A3S16P22A1A2A1G1A3S2A3SbSaS6S33S13S19S17G2S15S39S3aZ2Z3dA2Z1A2A1A2A1G1A3S2A3SaS6S33S13S19S1aG0Z4A2A1G1A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start5bStates.

