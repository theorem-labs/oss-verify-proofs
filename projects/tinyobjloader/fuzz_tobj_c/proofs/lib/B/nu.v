(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_out DrvExitStates.

(* [comment removed for export] *)
Module Lib_vec_reserveN_eqs.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "SLit"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "nil"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "E_r15f"; "E_rW1f"; "E_c8"; "E_cW0"; "Pre_c"; "Xk_r"; "inj"; "kbytes"; "s_c"; "s_r"; "vW"; "xf_rback"; "E_r15x"; "E_rW1x"; "R_c8"; "R_cW0"; "R_r15"; "R_rW1"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW0"; "XW1"; "kn15"; "tvf0"; "xf_rcall"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW0"; "NW1"; "T_c8n0"; "T_c8ok"; "T_c8ok0"; "T_c8ok2"; "T_cW0n0"; "T_cW0ok"; "T_cW0ok0"; "T_cW0ok2"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.RA"; "Pre_ra"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "tv_factsA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_calloc_null"; "L_calloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "zlog15"; "KU"; "bitem"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bd_subst"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "sobj"; "SLit"; "sprop_eqb"; "ss_next"; "SVar"; "SPUle"; "holds"; "SPBranch"; "SPNot"; "mkObj"; "rw"; "DUnknown"; "ob_cells"; "sprop_below"; "eval"; "ss_objs"; "DZero"; "cell"; "obj_range"; "obj_wf"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "xr_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "nil"; "cons"; "app"; "Some"; "None"; "option"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN"; "vK"; "kbytes"; "bdP"; "nd0"; "vN"; "s_r"; "vDt"; "vE"; "vW"; "cutsE"; "vAl"; "E_c8'"; "E_cW0'"; "O_data"; "Pre_c"; "Xk_r"; "inj"; "kn15"; "s_c"; "vV"; "O_W"; "O_vec"; "tv0"; "vC"; "B32"; "PD_ra"; "z0"; "E_r15f"; "E_rW1f"; "Pre_vr"; "R_c8"; "R_cW0"; "X15"; "X8"; "XW0"; "XW1"; "X_vr"; "ndG"; "ndN"; "spm"; "tvf0"; "B_EW"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "O_alv"; "P_fail"; "P_grown"; "P_keep"; "exitsE"; "tvP"; "two47"; "two48"; "vKn"; "xf_rback"; "xf_rcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "tv_factsA"; "JA_pre"; "ND"; "emeasA"; "ffinA"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf.Sum"; "baseF"; "basez"; "s_rbd"; "JL"; "Posts_vr"; "injF"; "injz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "import_subA"; "J_ofPA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN.RA"; "Pre_ra"; "P0_ra"; "tv0"; "P_fail"; "P_ok"; "bd0"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "csz"; "payA"; "site_okA"; "T_afterA"; "call_checkTA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "ulink"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "FBx"; "T0"; "T_ok"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "robjs_okF"; "xrs_okF"; "FFx"; "PostsC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_eqs.
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
Module Lib_builder_dispose_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "edescA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SLit"; "SVar"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "app"; "nat"; "nil"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose"; "NP"; "cutsE"; "exitsE"; "FUEL_bd"; "bd_chk_live"; "cutpcs_bd"; "lives"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_builder_dispose_chk"; "H_bd_ejcert_ok"; "keep_bd_ejcert_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideE"; "hide_setE"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_builder_dispose.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr BDAddr.

Lemma bd_chk_ok : ltac2:(tb__ "0|0|
ScS7S1aSaS12S14A3S8A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_bd_ejcert_ok : list sprop := ltac2:(tb__ "0|2|
S6S2S3S5PcA1S4Z800000000000A1M0A2S6S2S3S4Z643000A1S5P10A1M1A2S6S2S3G1G0A2SbS2A1A3A3A3").
Definition H_bd_ejcert_ok : list sprop := ltac2:(tb__ "0|0|
S19S17S9S0SfS10A3A2").
Lemma bd_ejcert_ok : ltac2:(tb__ "0|1|
ScS7S1S15SeS11S13SeSdS0S0S18S16A1M0SfA4SdS0S0G0S10A4A7S8A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_builder_dispose_chk.

(* [comment removed for export] *)
Module Lib_builder_dispose_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sv_eqb"; "ss_facts"; "sprop"; "SLit"; "SPBranch"; "sprop_eqb"; "ss_next"; "SPNot"; "ob_hi"; "ob_lo"; "obj_range"; "rw"; "ss_objs"; "cell"; "holds"; "mkObj"; "ob_base"; "odefault"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@Corelib.Init.Datatypes"; "prod"; "nat"; "pair"; "list"; "bool"; "true"; "andb"; "nil"; "cons"; "S"; "fst"; "option"; "snd"; "Some"; "app"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "edescA"; "ND"; "emeasA"; "JA_pre"; "ffinA"; "nd_below"; "ANone"; "JA"; "JLA"; "NDA"; "nd_tv"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose"; "NP"; "ndL"; "lives"; "NV"; "nlive"; "rL"; "E_"; "bdK"; "live"; "tvL"; "tvE"; "C_"; "s_of"; "z0"; "N_"; "R_of"; "cutsE"; "fr_obj"; "fr_xr"; "L_"; "P_bd"; "Pre_bd"; "chkE"; "chkN"; "exitsE"; "isSomeb"; "live_from"; "ndP"; "Cnode"; "Nd_"; "Nnode"; "chkC"; "didx"; "lit_in"; "sN"; "vAl"; "vB"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "pow"; "mul"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_builder_dispose_pf"; "P0_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkPA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "Pre_free"; "L_free"; "JL_free"; "J_free_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "KU"; "bd_below"; "bd_subst"; "bd_wpos"; "bud_le"; "bud_pay"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_builder_dispose_pf.Sum"; "Posts_bd"; "JLb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tnz"; "tv_sub_eqb"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "cmaddrA"; "robjs_checkA"; "T_afterA"; "call_checkTA";
"payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builder_dispose OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_builder_dispose_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr BDAddr.

Lemma chkE_unfold : forall j, chkE j = ltac:(let b := eval cbv beta delta [chkE chkE'] in (chkE j) in exact b).
Proof. intros j. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma chkN_unfold : ltac2:(tb__ "0|d|
S1cS2bS1fS5dR1A1S26S2A1S1fLx;S43S2SfS17S54R1A1A1A1S66R1A1A3S2S21S21S21S21S21S21S21S21S21S3S13R1A1S25S0S0S50R2A1M0A3M1A2S3ScR1A1S6Z0A1M2A2A2S3SbR1A1S27S0S0G0A3A2A2S41S5S8S7S99G1G2A3A1S4S17S54R2A1M3A1A1A3A2S1aS63R2G3A2M4S59S24R2A1M5A1S68R2G3A2M6A3A2S93G6S46A2A2SafS46S9S17G4A1M7A1M8A2A2S35G8S31Sa3S1bS0S0A2M9U0S23G9G0S4fG5A1MaA3A3MbS22S1bS1bS0S15A2S0A2A1S4dS4aR2A1A1McA3A2A2Sa5G6GbGaA3A2S8cS4G7A1S8aG6S4dS4aG5A1A1A2GcA3A2Lo;S2aX26x2A3Fj;").
Proof. intros j. match goal with |- _ = ?b => exact (@eq_refl bool b) end. Qed.
Lemma exitsE_eq : ltac2:(tb__ "0|3|
S2bS1eS30A1S5eS29S30S9fS1cS30S62S48A4S29S30S9fS1cS30S64S48A4S23S1bS1bS16S2eA2M0S1bS15S0A2M1A2M2S1dG0G1S1dS16S2eS5aS61A4S1dS15S0Z0S53A4A4S22G2A1A3A3A3A3").
Proof. match goal with |- _ = ?b => exact (@eq_refl _ b) end. Qed.

Lemma lives_specb : ltac2:(tb__ "0|0|
S2bS1fS42S1cS1cS21Sb5R1S49A2S4eR1A1A2Lj;S48A3S20A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lives_spec : ltac2:(tb__ "0|0|
S1cS40S1cR1S48A3S2cS8eR2S49A2S2bS1fS4eR2A1S20A3A2F_;Fj;").
Proof.
  intros j H. pose proof (proj1 (forallb_forall _ _) lives_specb j H) as X. cbn beta in X.
  apply andb_prop in X as [A B]. apply Nat.ltb_lt in A. split; [exact A | exact B].
Qed.
Lemma live_from_cons : ltac2:(tb__ "0|0|
S1cS8eR1S49A2S2bS1fS4eR2A1S20A3S2bS1eS1cA1S60R3A1S23S1cR3S60S24R3A1A1A3A3F_;F_;Fj;").
Proof.
  intros j Hj Hl. unfold live_from.
  replace (NV - j)%nat with (S (NV - S j))%nat by lia. cbn [seq List.filter]. rewrite Hl. reflexivity.
Qed.
Lemma tvL_cons : ltac2:(tb__ "0|1|
S1cS8eR1S49A2S2bS1fS4eR2A1S20A3S2bS1eS1bS0S0A2M0A1S4fR3A1S23G0S50R3A1S4fS24R3A1A1A3A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold tvL. rewrite (live_from_cons j Hj Hl). reflexivity. Qed.
Lemma nlive_cons : ltac2:(tb__ "0|0|
S1cS8eR1S49A2S2bS1fS4eR2A1S20A3S2bS15S4aR3A1S70S4aS24R3A1A1Z1A2A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold nlive. rewrite (live_from_cons j Hj Hl). cbn [length]. lia. Qed.
Lemma ndL_cons : ltac2:(tb__ "0|0|
S1cS8eR1S49A2S2bS1fS4eR2A1S20A3S2bS2eS47R3A1S31S23S1bS0S0A2S50R3A1S4fS24R3A1A1A3S22S1bS1bS0S15A2S0A2A1S4dS4aR3A1A1A3A3F_;F_;Fj;").
Proof. intros j Hj Hl. unfold ndL. rewrite (tvL_cons j Hj Hl). reflexivity. Qed.

Lemma chk_live_at : ltac2:(tb__ "0|0|
S1cS40S1cR1S48A3S2cS2bS1fS65R2A1S20A3S2cS2bS1fS5cR2A1S20A3S2bS1fS5dR2A1S20A3A2A2F_;Fj;").
Proof.
  intros j Hin. pose proof bd_chk_ok as H.
  pose proof (proj1 (forallb_forall _ _) H j Hin) as X. cbn beta in X.
  apply andb_prop in X as [X1 X]. apply andb_prop in X as [X2 X3].

  split; [exact X1 | split; [exact X2 | exact X3]].
Qed.
Lemma R_of_spec : ltac2:(tb__ "0|2|
S1cS16S2bS1fS5fS1eS2A1M0S78R1S7eS7bS22S7dA1S7cA3M1S52R2R1A2A3A2S20A3S2bS26G0A1S78R2G1S52R3R2A2A3S28G0S55R3R2A2A2A3F_;FE;Fj;").
Proof. intros j E H. unfold R_of, optR. destruct (entails_frA E (Pre_free AE_A [] UStopLe) (s_of j E)); [reflexivity | discriminate]. Qed.

Lemma L_in_cutsE : ltac2:(tb__ "0|3|
S1cS8eR1S49A2S40S1bS1bS16S2eA2M0S1bS15S0A2M1A2S1dG0G1S1dS16S2eS59S24R2A1M2A1S47G2A1A4S1dS15S0S4bG2A1S53A4A4S56A3F_;Fj;").
Proof.
  intros j Hj. unfold cutsE. right. apply in_or_app. left.
  apply (in_map Lnode (seq 1 NV) (S j)). apply in_seq. lia.
Qed.
Lemma T_in_cutsE : ltac2:(tb__ "0|6|
S1cS40S1cR1S48A3S40S1bS1bS16S2eA2M0S1bS15S0A2M1A2S1dG0G1S1dS16S2eSa9S7eS7bS22S7dA1M2S7cA3S4cR2A1M3S52R2G3A2S55R2G3A2S7fS7bG2S7cA3A5S39Sa3S1bS0S0A2M4U0S23G4S50R2A1S4fS24R2A1M5A1A3A3S22S1bS1bS0S15A2S0A2A1S4dS4aG5A1A1S36A4A4S1dS15S0S6fS4bR2A1Z3A2S53A4A4S56A3F_;Fj;").
Proof. intros j Hin. unfold cutsE. right. apply in_or_app. right. exact (in_map Tnode lives j Hin). Qed.

Lemma edesc_eq3 : ltac2:(tb__ "0|2|
S16S16S2eS2eS1bS15S0A2M0G0S2bS1bS1bS16S2eA2M1G0A2S1dG1G0S1dS16S2eR6R4A4R2A4S1dG1G0S1dS16S2eR5R3A4R1A4A3S2cS2bS16R7R6A3S2cS2bS2eR5R4A3S2bG0R3R2A3A2A2F_;Fc';Fc;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' c c' H. injection H as E1 E2 E3. subst. auto. Qed.
Lemma edesc_eq2 : ltac2:(tb__ "0|0|
S16S16S2eS2eS2bS1bS16S2eA2S1dS16S2eR4R2A4S1dS16S2eR3R1A4A3S2cS2bS16R5R4A3S2bS2eR3R2A3A2F_;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' H. injection H as E1 E2. subst. auto. Qed.

Lemma rL_S : ltac2:(tb__ "0|0|
S1cS2bS15S4bS24R1A1A1S6fS4bR1A1ZaA2A3Fj;").
Proof. intros j. unfold rL. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma rL_pos : ltac2:(tb__ "0|0|
S1cS8eR1S49A2S6cZ12S4bS24R2A1A1A2F_;Fj;").
Proof. intros j Hj. unfold rL, NV in *. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S16S2eS15S1S2bS15S32S1dS1bS16S2eA2S1bS15S0A2S1dS16S2eR4R3A4S1dS15S0R2S53A4A4R1A2S6eR2S6dZ2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros T nd r rho. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho z0)) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Definition P0_bd (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S2cS9eVFF;S45Q40M0SeVr;PcA2A2Z518A3S9eVFF;S45G0SeVr;P10A2A2Z30A3A2").

Lemma lit_in_sound : ltac2:(tb__ "0|2|
S1S0S0S0S15S15S1eS10A1S14S6bR4S6dZ2Z3eA2A2S2bS1fS67R7R6R5A3S20A3S2cS6cS25S15S15SdRaS12R9R8R7R4R3A5A2M0A3R5A2S6bR5S27S15S15G0A3A2A2S2cS6cS86RbRaA2M1R6A2S6bR6S70G1R7A2A2A2F_;F_;F_;Fdflt;Fcells;Fa;Fn;Fhi;Flo;Fbase;Frho;").
Proof.
  intros rho base lo hi n a cells dflt Hn H Hr. unfold lit_in in H.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. unfold uval. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S95S1S1eS44Q40A1A1S97OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S84S2dVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S15SaeVCST;R1A2S2cS6cZ0R2A2S6bR2SadA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S15SaeVXGL;R1A2S2cS6cZ0R2A2S6bR2SadA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1eS1bS1bS15S15A2S15A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Variable rho0 : valuation.

Definition JLb (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S38VAInv;VCST;VXGL;VKc;S71VFB;VFF;A2VFB;VFF;VBX;S2fVnd;Aa").
Definition Posts_bd : list (axst * jpostA) := ltac2:(tb__ "0|1|
S23S1bS16S76A2M0S1dS16S76S5aS9bS61A1A4S22G0A1A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S37VAInv;VCST;VXGL;S46VKc;Vrho0;S71VFB;VFF;A2VFB;VFF;VBX;S2fVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S1bS16S2eA2Sb0Fn;") := ltac2:(tb__ "0|0|
S3bVAInv;VCST;VXGL;S46VKc;Vrho0;S71VFB;VFF;A2VFB;VFF;VBX;S2fAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S77S2dS46Vrho0;Vtp0;S9aA5").

Lemma P0b_now : ltac2:(tb__ "0|0|
S1S9cS46Vrho0;R1A3S71VFB;VFF;Vrho0;A3S2cS9eVFF;S86R3S6aA2Z518A3S9eVFF;S86R3S69A2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [H1 H2]. unfold uval, vB, vAl. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 16%positive eq_refl). split; [exact H1 | exact H2].
Qed.

Lemma fr_obj_cmaddrA : ltac2:(tb__ "0|1|
S95S1S26S15A1S2S15S9cS46Vrho0;R4A3S71VFB;VFF;Vrho0;A3S34VFF;R7A2S2bS1fS57R5A1S20A3S2cS6cS25S15S15SdR8R6A2M0A3R5A2S6bR5S27S15S15G0A3A2A2Sa7VCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fo;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [base lo hi cells dflt] a Hav HP0 HFF H Hr. destruct (P0b_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact (lit_in_sound rho vAl lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_xr_cmaddrA : ltac2:(tb__ "0|1|
S95S1S26S15A1S1bS0S0A2S15S9cS46Vrho0;R4A3S71VFB;VFF;Vrho0;A3S34VFF;R7A2S2bS1fS58R5A1S20A3S2cS6cS86R8S25S0S0R6A3A2M0R5A2S6bR5S70G0S86R8S27S0S0R6A3A2A2A2A2Sa7VCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fr;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [rb rn] a Hav HP0 HFF H Ha. destruct (P0b_now rho Hav HP0) as [PB PA].
  unfold fr_xr in H. cbn [fst snd] in H, Ha. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hn]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hn; subst rb rn.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact Ha].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact Ha].
Qed.

Lemma site_E : ltac2:(tb__ "0|3|
S16S92S1eS2A1S1S1bS0S0A2M0S1eG0A1S1eS87A1S2bS1fSa8S4S17R7A1A1S23G0R3R2A3S28S1cU0A2S57R5A5S20A3S2bS1fS42G0S58S18R8A1A3S20A3S2bS1fS3S25S0S0R5A3S8fR8PcM1A2A2S20A3S2bS1fS3S27S0S0R6A3S8fR9PdM2A2A2S20A3S2bS1fS41S5S8SaS7S99S25S0S0R7A3S6Z0A1A3A1A1S4S17RbA1A1A3S20A3SacVAInv;VCST;VXGL;S46Vrho0;S71VFB;VFF;A2VFB;VFF;RcRbRaR9S31S23G0R8R7A3S22S1bS1bS0S15A2S0A2A1R6A3S28S15S86R9S8fRbG1A2A2A2S95S96S2cSa4RbRaA2S2cS2bS1bS15S15A2Sa6RbRaA2S1dS15S15S86RbS8fRdG1A2A2S86RbS8fRdG2A2A2A4A3S85S22S7dA1S7cS91S90RbRcR1A3RdA2A3A2A2Lms;LAi;AfF_;F_;F_;F_;F_;Fbd;Ftv;Ft;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho t tv bd HR HX H12 H13 Hnzb Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr ND] in HN, HD, HZ, HFR.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13. rewrite <- H12, <- H13.
  assert (Hnz : tnz rho t).
  { pose proof (holds_mem _ _ _ HF Hnzb) as X. apply (proj1 (holds_nbeq _ _ _)) in X. unfold tnz. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in X. rewrite uval_lit in X by lia. exact X. }
  split; [|split; [|split; [exact Hnz | split; [reflexivity | exact I]]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E)) (t :: tv) (Some 0%nat) fr_obj R _ r1 t1 m1 HM HF HN HD HZ HTK HR).
    + intros o a Ho Hfo Hr. exact (fr_obj_cmaddrA Ai rho _ o a Hav HP0 HFF Hfo Hr).
    + exists t. split; [reflexivity|]. split; [exact Hnz | reflexivity].
  - intros r a Hr Ha. left. exact (fr_xr_cmaddrA Ai rho _ r a Hav HP0 HFF (proj1 (forallb_forall _ _) HX r Hr) Ha).
Qed.

Lemma SPA_drop_null_dat : ltac2:(tb__ "0|2|
S2eS1S16S1cS2S1bS0S0A2M0S1eS44Q40A1A1S75S2bS26S2A1S43S2SfS17R6A1A1R5A3S28S2R4A2A3S40G0R4S3aR9A1A3S2bS1fS3ScR6A1S6Z0A1M1A2S20A3S2bS1fS3SbR7A1S27S0S0R6A3A2S20A3S2bS1fS41S5S8S7S99S25S0S0R7A3G1A3A1S4S17RaA1A1A3S20A3S3dS2dVJAv;RdA1RbRcR7R6A6S3dS2dVJAv;ReA1S19RcSb2S17RcA1RbA2A2RdR8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Ft;Fo;Fi;FA;Frho;Fnd;").
Proof.
  intros nd rho A i o t tp w Hn Hin Hlo Hhi Hz Hw.
  apply sv_eqb_sound in Hlo. apply sv_eqb_sound in Hhi.
  assert (HJ : exists tr md, JAv nd rho tp tr md).
  { destruct w as [tr [ms md]]. destruct Hw as [_ HJ]. exists tr, md. exact HJ. }
  destruct HJ as (tr & md & HJ).
  apply (SPA_drop_empty segs (JAv nd) rho A i o tp w Hn); [|exact Hw].
  intros HF. pose proof (holds_mem _ _ _ HF Hz) as X. apply (proj1 (holds_beq _ _ _)) in X.
  change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in X. rewrite uval_lit in X by lia.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue nd rho tp tr md t HJ Hin X) as Hs0.
  unfold obj_hi_of, obj_lo_of. rewrite Hlo, Hhi. rewrite soff_lit_small by lia.
  rewrite (soff_smallu rho (snd t)) by (unfold uval; rewrite Hs0; lia). unfold uval. rewrite Hs0. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S1eS5A1S1eS87A1S2bS1fS8bR1A1S20A3SabS46Vrho0;S71VFB;VFF;A2R3S6Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S15S1eS44Q40A1A1S72F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3eS16S1S1eS44Q40A1A1S72Sa0S5S11R3A1S4S17R4A1A1A3VTR;S3dS2dR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S72S72S72S75R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3eS3eS16S16S92S1eS2A1M0S1eS1bS16S76A2M1A1S1eS1bS0S0A2M2A1S72S1S1eS44Q40A1A1M3G2S40G2R1R5A3S40G2R2S18RbA1A3F_;Fr;S2bS26G0A1S78RaR9R8A3S28G0R7A2A3S2bS1fS79RbRaR9R8S9fG1S16S25S16S76A2R7A4A5S20A3S1G3VTR;S3dS2dRfRdR2R1A5S77S2dS9S17RdA1A1R2R1RaA5A2Ftp1;Frho1;S1eS98A1M4S96S97S3fS2dR9R8R10S1dG4Sa1R3Sa2R2R1A2A4A5R13RaR9R4R2A4R13S91S90RbRfS94R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S16S76G4S96S97S1G3G4S96S97S40G1S1dS16S76RaR9A4R14A3S3fS2dR12R11R19S1dG4Sa1R9Sa2R8R7A2A4A5R1cR13R12RaR8A4S9cS9S17R1aA1A1S91S90R14R18S94R9R13RaA3A3R19A2R8A3S3fS2dR9R8ReS1dG4Sa1R7Sa2R6R5A2A4A5ReS91S90R16R1aS94RbR15RcA3A3R1bA2R15RaR9R8R6A6S2cSb3R17S94RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1S9dR18S94RdR17ReA3R1cR1dS17R1eA1S17R1fA1S17R11A1R1RcA9VTR;S3dS2dS7aR11S91S90R19R1dS94ReR18RfA3A3R1eA2R18RdRcA5Sb4R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S3dS2dR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CFREE : ltac2:(tb__ "0|2|
S95S1S1eS44Q40A1A1VTR;S3dS2dS81VAInv;S22S7dA1M0S7cR3VKc;A5S7eS7bG0S7cA3R2R1A5S77S2dSb1R2R1S23S1bS16S76A2M1S1dS16S76S7fS7bG0S7cA3S80VAInv;VCST;VXGL;R3VKc;A5A4S22G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis MINI : ltac2:(tb__ "0|1|
S1cS1S1eS44Q40A1A1M0S72S40S1cR4S48A3S1G0VTR;S3dS2dVJAv;S47R7A1A1S4cR7A1R2R1A5R4A2Ftp';Frho';VTR;S3dS2dVJAv;S47R6A1A1S51R6A1R5R4A5R3A2F_;F_;FQ';Ftp;Frho;Fj;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S16S2eS1bS15S0A2M0S1S1eS44Q40A1A1M1S15G1S40S1bS1bS16S2eA2M2G0A2S1dG2G0S1dS16S2eR7R6A4R5A4S56A3S2cS6cZ0S32S1dG2G0S1dS16S2eR8R7A4R6A4R5A2M3A2S6bG3R3A2A2VTR;S3dS2dVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S16S2eS1S1eS44Q40A1A1M0S15G0S40S1bS16S76A2S1dS16S76R6S9bR5A1A4S9aA3VTR;S3dS2dVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Lemma X_N : ltac2:(tb__ "0|1|
S1cS1S1eS44Q40A1A1M0S15G0S40S1cR5S48A3S6bS6eS4bS24R6A1A1S6dZ2Z40A2A2R3A2VTR;S3dS2dVJAv;S47R7A1A1S54R7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. destruct (lives_spec j Hin) as [Hj Hl].
  destruct (chk_live_at j Hin) as (_ & _ & HK). rewrite (chkN_unfold j) in HK.
  destruct (nth_error (ss_objs (ax_S (N_ j))) (didx j)) as [o|] eqn:Ho; [|discriminate].
  apply andb_prop in HK as [HK Hbl]. apply andb_prop in HK as [HK Htv]. apply andb_prop in HK as [HK Hnb]. apply andb_prop in HK as [HK Hnp].
  apply andb_prop in HK as [HK Hid]. apply andb_prop in HK as [HK Hent]. apply andb_prop in HK as [HK Hz].
  apply andb_prop in HK as [HK Hhi]. apply andb_prop in HK as [Hb0 Hlo].
  rewrite (ndL_cons j Hj Hl).
  eapply TR_pre.
  { intros w Hw.
    pose proof (SPA_drop_null_dat (ND (tvE j :: tvL (S j)) [] (bdK (nlive j))) rho (N_ j) (didx j) o (tvE j) tp w Ho ltac:(left; reflexivity) Hlo Hhi Hz Hw) as Hw1.
    revert Hw1. apply (SPA_JA_drop_tv_fact segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue (tvE j :: tvL (S j)) [] (bdK (nlive j)) 0%nat
                         (ax_setS (N_ j) (drop_obj_at (ax_S (N_ j)) (didx j))) rho tp w).

    intros t Ht. cbn [nth_error] in Ht. injection Ht as <-.
    assert (EF : forall (A : axst) i, ss_facts (ax_S (ax_setS A (drop_obj_at (ax_S A) i))) = ss_facts (ax_S A)) by (intros; reflexivity).
    rewrite EF. exact Hz. }
  eapply TR_pre.
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc (Nd_ j (N_ j)) (L_ (S j)) (sN j (N_ j))
                    (ND (remove_nth 0 (tvE j :: tvL (S j))) [] (bdK (nlive j))) (ndL (S j)) rho tp w Hent Hid Hnp Hnb Htv eq_refl Hbl eq_refl Hw). }
  apply (REENTER (L_ (S j)) (ndL (S j)) (rL (S j), z0) _ tp b tp0 (L_in_cutsE j Hj)). rewrite emeas_z0. pose proof (rL_pos j Hj). lia.
Qed.

Lemma X_E : ltac2:(tb__ "0|1|
S1cS1S1eS44Q40A1A1M0S15G0S40S1cR5S48A3S6bS6eS6fS4bR6A1Z3A2S6dZ2Z40A2A2R3A2VTR;S3dS2dVJAv;S47R7A1A1S4cR7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. destruct (lives_spec j Hin) as [Hj Hl].
  destruct (chk_live_at j Hin) as (_ & HK & _). rewrite (chkE_unfold j) in HK.
  apply andb_prop in HK as [HK HXr]. apply andb_prop in HK as [HK HR]. apply andb_prop in HK as [HK Hnz]. apply andb_prop in HK as [HK H13].
  apply andb_prop in HK as [HK H12]. apply andb_prop in HK as [HK Hpay]. apply andb_prop in HK as [HK Hbb]. apply andb_prop in HK as [HK Hnb].
  apply andb_prop in HK as [HK Hnp]. apply andb_prop in HK as [HK Htp]. apply andb_prop in HK as [Hsome Hchk].
  apply (R_of_spec j (E_ j)) in Hsome.
  rewrite (ndL_cons j Hj Hl).
  apply (free_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe (E_ j) (s_of j (E_ j)) (R_of j (E_ j)) rho tp (ND (tvE j :: tvL (S j)) [] (bdK (nlive j))) 0%nat (tvE j) (bdK (nlive (S j))) (FAM b tp0) CFREE
           Hsome Hchk Htp Hnp Hnb Hbb (@eq_refl _ (Some (tvE j)))).
  - cbn [nd_bd ND]. apply payA_of_bud_pay. exact Hpay.
  - intros A A' _ _. exact I.
  - exact (site_E (E_ j) (s_of j (E_ j)) (R_of j (E_ j)) rho (tvE j) (tvL (S j)) (bdK (nlive j)) HR HXr H12 H13 Hnz).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ND].
    apply (REENTER _ _ (rL j - 3, z0) rho' tp' b tp0 (T_in_cutsE j Hin)). rewrite emeas_z0. pose proof (rL_pos j Hj). rewrite rL_S in *. lia.
Qed.

Lemma X_C : ltac2:(tb__ "0|1|
S1cS1S1eS44Q40A1A1M0S15G0S40S1cR5S48A3S6bS6eS6fS4bR6A1Z3A2S6dZ2Z40A2A2R3A2VTR;S3dS2dVJAv;S47R7A1A1S51R7A1R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Fj;").
Proof.
  intros j rho tp b tp0 Hin Hb. apply (MINI j rho tp (FAM b tp0) Hin). intros rho' tp'. apply X_E; [exact Hin | exact Hb].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S16S2eS1bS15S0A2M0S1S1eS44Q40A1A1M1G1S40S1bS1bS16S2eA2M2G0A2S1dG2G0S1dS16S2eR6R5A4R4A4S5eA3VTR;S3dS2dVJAv;R6A1R7R4R3A5VFAM;S32S1dG2G0S1dS16S2eR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. rewrite exitsE_eq in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|apply in_app_or in Hin as [Hin|Hin]].
  - apply in_map_iff in Hin as (j & Heq & Hj). destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). destruct (lives_spec j Hj) as [Hlt _].
    apply X_C; [exact Hj|]. rewrite emeas_z0. pose proof (rL_pos j Hlt). nia.
  - apply in_map_iff in Hin as (j & Heq & Hj). destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). destruct (lives_spec j Hj) as [Hlt _].
    apply X_N; [exact Hj|]. rewrite emeas_z0, rL_S. pose proof (rL_pos j Hlt). nia.
  - destruct Hin as [Heq|[]]. destruct (edesc_eq3 _ _ _ _ _ _ Heq) as (<- & <- & <-). apply POST. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S3cS2dVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S82S2dS7bVAInv;VCST;VXGL;A5").

Lemma MINI_s : ltac2:(tb__ "0|1|
S72S1cS1S1eS44Q40A1A1M0S72S40S1cR4S48A3S1G0S74S2dVok;S3dS2dVJAv;S47R7A1A1S4cR7A1R2R1A5R4A4Ftp';Frho';S74S2dVok;S3dS2dVJAv;S47R6A1A1S51R6A1R5R4A5R3A4F_;F_;FQ';Ftp;Frho;Fj;FQF;").
Proof.
  intros QF j rho tp Q' Hin HE. destruct (chk_live_at j Hin) as (HC & _ & _). unfold chkC in HC.
  apply (cfg_sound_JA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA FUEL_bd cutpcs_bd NP
           (map edropA [Cnode j]) (map edropA [Enode j]) ok Q' Hok (ejcertA_jcertA segs NP _ _ _ _ _ HC)) with (ndT := ndL j); [|left; reflexivity].
  intros X ndX rho1 tp1 [H|[]]. cbn [edropA Enode eda_state eda_nd fst snd] in H. destruct (edesc_eq2 _ _ _ _ H) as [<- <-].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HE].
Qed.

Theorem builder_dispose_sum : ltac2:(tb__ "0|0|
S1eS44Q40A1A1S74S2dVok;S3dS2dS33VAInv;VCST;VXGL;VKc;S71VFB;VFF;A2VFB;VFF;VBX;S2fS47U0A1AaS5bVrho0;R1A5S77S2dS46Vrho0;R1S9aA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA_h segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA H_bd_ejcert_ok FUEL_bd cutpcs_bd NP cutsE exitsE ok (Q tp0) Hok bd_ejcert_ok)
         with (ndT := ndL 0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros j rho1 tp1 Q' Hj HE. exact (MINI_s (Q tp0) j rho1 tp1 Q' Hj HE).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NP Kc (P0_bd FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_bd P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S83S2dS7bVAInv;VCST;VXGL;A5").

Lemma MINI_e : ltac2:(tb__ "0|1|
S1cS1S1eS44Q40A1A1M0S72S40S1cR4S48A3S1G0S73S2dS3dS2dVJAv;S47R7A1A1S4cR7A1R2R1A5R4A3Ftp';Frho';S73S2dS3dS2dVJAv;S47R6A1A1S51R6A1R5R4A5R3A3F_;F_;FQ';Ftp;Frho;Fj;").
Proof.
  intros j rho tp Q' Hin HE. destruct (chk_live_at j Hin) as (HC & _ & _). unfold chkC in HC.
  apply (cfg_complete_JA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA FUEL_bd cutpcs_bd NP [Cnode j] [Enode j] Q' HC)
    with (ndT := ndL j) (rv := (rL j - 1, z0)); [|left; reflexivity].
  intros X ndX rv rho1 tp1 [H|[]]. destruct (edesc_eq3 _ _ _ _ _ _ H) as (<- & <- & <-).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HE].
Qed.

Theorem builder_dispose_sum_ex : ltac2:(tb__ "0|0|
S1eS44Q40A1A1S73S2dS3dS2dS33VAInv;VCST;VXGL;VKc;S71VFB;VFF;A2VFB;VFF;VBX;S2fS47U0A1AaS5bVrho0;R1A5S77S2dS46Vrho0;R1S9aA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA_h segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue HKc ALA H_bd_ejcert_ok FUEL_bd cutpcs_bd NP cutsE exitsE (Q tp0) bd_ejcert_ok)
         with (ndT := ndL 0) (rv := (rL 0, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros j rho1 tp1 Q' Hj HE. exact (MINI_e j rho1 tp1 Q' Hj HE).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_bd FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NP Kc (P0_bd FB FF) FB FF BX PTrue rho0 tp0 nd Posts_bd P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_builder_dispose_pf.

(* [comment removed for export] *)
Module DrvExitStates2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "ax_X"; "ax_base"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "true"; "list"; "pair"; "bool"; "prod"; "false"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sv"; "SLit"; "sobj"; "ss_next"; "ss_lenient"; "reg_sv"; "ss_facts"; "ss_pc"; "DRom"; "cell"; "mkObj"; "mkSS"; "sprop"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_out.WLoutS"; "Pre_wl2"; "D"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvExitStates"; "CUTS_X"; "W_2"; "W_3"; "W_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "facts_exit"; "exit_ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExitStates2"; "C_2"; "C_3"; "C_4"; "Tf_2"; "Tf_3"; "Tf_4"; "obind"; "s_2"; "s_3"; "s_4"; "R_2"; "R_3"; "R_4"; "splits"; "F_2"; "F_3"; "F_4"; "T_2"; "T_3"; "T_4"; "O_b2z"; "S5_2"; "S5_3"; "S5_4"; "app_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.PFAddr"; "SBUF"; "FILE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_out RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvExitStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvExitStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition obind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

Definition O_b2z : sobj := ltac2:(tb__ "0|1|
S1fS16Z0A1M0G0G0SaS1eA1S1dP6A1A5").
Definition app_obj (S : sstate) (o : sobj) : sstate := ltac2:(tb__ "0|0|
S20S1cVS;A1S25VS;A1S23VS;A1S22VS;A1S26VS;A1S13S17S24VS;A1S9S17Vo;SaS17A1A3A3S1bVS;A1S18VS;A1S19VS;A1A9").

Definition splits (m : Z) (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S3dS14S14S33VS;U0S16N88A1A3S14S3dS14S14S33R1U1S16N68A1A3S14S3dS14S14S33R1U5S16S58S51Z78A2A1A3S14S3dS14S14S33R1U6S16S58S51Z7cA2A1A3S14S33R1U8S16S58S50Vm;A2A1A3LS4;A4LS3;A4LS2;A4LS1;A4").

Definition finish (S5 : sstate) : sstate := ltac2:(tb__ "0|0|
S4fS5dVS5;U8P5A3S4bA2").

Definition wl_sub_head (m : Z) : wsub := ltac2:(tb__ "0|2|
S9S11S2aS15A2M0SfS2aS15PcS16S50A1A4S9G0SfS2aS15PdS16Vm;A1A4S9G0SfS2aS15PeS16Z0A1M1A4S9G0SfS2aS15PfG1A4SaG0A1A3A3A3A3").

Definition S5_2 : sstate := Eval vm_compute in (match splits 2 (ax_S W_2) with Some s => s | None => ax_S W_2 end).
Lemma splits_2 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z2S4S2eA1A2SbS14S4cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_2s : sstate := Eval vm_compute in (finish S5_2).
Lemma finish_2 : finish S5_2 = C_2s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_2 : axst := ax_setS W_2 C_2s.
Definition s_2 : wsub := Eval vm_compute in (wl_sub_head 2 ++ infer_sub 10 C_2s (ax_S WLoutS.Pre_wl2)).
Definition R_2 : list sobj := Eval vm_compute in (match entails_frA C_2 WLoutS.Pre_wl2 s_2 with Some R => R | None => [] end).
Lemma efr_2 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S37S28S3eA3SbG0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_2 : ltac2:(tb__ "0|0|
S0S10S55S37S28S3eS41S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_2 : axst := Eval vm_compute in (import_postA s_2 WLoutS.Pre_wl2 WLoutS.D C_2 R_2).
Lemma T_2_eq : ltac2:(tb__ "0|0|
S0S2S57S3eS28S29S37S41A5S48A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_2 : axst := Eval vm_compute in (ax_add_facts facts_exit T_2).
Lemma Tf_2_eq : ltac2:(tb__ "0|0|
S0S2S54S35S48A2S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F2__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3aSdA5").
Local Strategy expand [run_F2__R].
Definition F_2 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1X Tf_2 (ro1__)))) run_F2__R).
Lemma run_F2 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3aSdA5SbG0S9S3S6S45S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F2__R <: run_F2__R = Some [mkLeafA F_2 RsCut]). Qed.

Definition S5_3 : sstate := Eval vm_compute in (match splits 4 (ax_S W_3) with Some s => s | None => ax_S W_3 end).
Lemma splits_3 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z4S4S2fA1A2SbS14S4dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_3s : sstate := Eval vm_compute in (finish S5_3).
Lemma finish_3 : finish S5_3 = C_3s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_3 : axst := ax_setS W_3 C_3s.
Definition s_3 : wsub := Eval vm_compute in (wl_sub_head 4 ++ infer_sub 10 C_3s (ax_S WLoutS.Pre_wl2)).
Definition R_3 : list sobj := Eval vm_compute in (match entails_frA C_3 WLoutS.Pre_wl2 s_3 with Some R => R | None => [] end).
Lemma efr_3 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S38S28S3fA3SbG0S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_3 : ltac2:(tb__ "0|0|
S0S10S55S38S28S3fS42S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_3 : axst := Eval vm_compute in (import_postA s_3 WLoutS.Pre_wl2 WLoutS.D C_3 R_3).
Lemma T_3_eq : ltac2:(tb__ "0|0|
S0S2S57S3fS28S29S38S42A5S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_3 : axst := Eval vm_compute in (ax_add_facts facts_exit T_3).
Lemma Tf_3_eq : ltac2:(tb__ "0|0|
S0S2S54S35S49A2S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F3__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3bSdA5").
Local Strategy expand [run_F3__R].
Definition F_3 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1X Tf_3 (ro2__)))) run_F3__R).
Lemma run_F3 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3bSdA5SbG0S9S3S6S46S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F3__R <: run_F3__R = Some [mkLeafA F_3 RsCut]). Qed.

Definition S5_4 : sstate := Eval vm_compute in (match splits 6 (ax_S W_4) with Some s => s | None => ax_S W_4 end).
Lemma splits_4 : ltac2:(tb__ "0|0|
S0ScS14A1S44Z6S4S30A1A2SbS14S4eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_4s : sstate := Eval vm_compute in (finish S5_4).
Lemma finish_4 : finish S5_4 = C_4s. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_4 : axst := ax_setS W_4 C_4s.
Definition s_4 : wsub := Eval vm_compute in (wl_sub_head 6 ++ infer_sub 10 C_4s (ax_S WLoutS.Pre_wl2)).
Definition R_4 : list sobj := Eval vm_compute in (match entails_frA C_4 WLoutS.Pre_wl2 s_4 with Some R => R | None => [] end).
Lemma efr_4 : ltac2:(tb__ "0|1|
S0ScSeS17A1M0A1S56S39S28S40A3SbG0S43A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_4 : ltac2:(tb__ "0|0|
S0S10S55S39S28S40S43S9S2S29SaS2A1A3A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_4 : axst := Eval vm_compute in (import_postA s_4 WLoutS.Pre_wl2 WLoutS.D C_4 R_4).
Lemma T_4_eq : ltac2:(tb__ "0|0|
S0S2S57S40S28S29S39S43A5S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_4 : axst := Eval vm_compute in (ax_add_facts facts_exit T_4).
Lemma Tf_4_eq : ltac2:(tb__ "0|0|
S0S2S54S35S4aA2S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_F4__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S2cU7d0S2dS3cSdA5").
Local Strategy expand [run_F4__R].
Definition F_4 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1X Tf_4 (ro3__)))) run_F4__R).
Lemma run_F4 : ltac2:(tb__ "0|1|
S0ScSeS3A1M0A1S5S2cU7d0S2dS3cSdA5SbG0S9S3S6S47S52A2SaS3A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_F4__R <: run_F4__R = Some [mkLeafA F_4 RsCut]). Qed.

Lemma F_at : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S45S9S2S46S9S2S47SaS2A1A3A3A3A3S1S0S2bS1cS4R2A1M0A1M1S36A3S1S0ScS59A1S53S2cG1A2SbS59S5aA2A3S1S0S15S1aG0Z11A2S16Z5eA1A3S0S15S1aG0ZaA2S16Z0A1A3A2A2A2F_;FF;").
Proof. intros F [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Tf_shape : ltac2:(tb__ "0|1|
S2S34S2R1S9S2S3aS9S2S3bS9S2S3cSaS2A1A3A3A3A3S1S0S10S19S4R2A1M0A1S12A3S0S2aS18G0A1P7dA3A2F_;FT;").
Proof. intros T [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C_shape : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S37S9S2S38S9S2S39SaS2A1A3A3A3A3S1S0S2aS18S4R2A1M0A1S5cA3S1S0SeS11S15S15A2M1A1S7R2A1SaG1A1A3S1S0S15S8R2A1S16S5bA1A3S0S10S27G0A1SdA3A2A2A2F_;FC;").
Proof. intros C [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma W_shape : ltac2:(tb__ "0|2|
S2S34S2R1S9S2S2eS9S2S2fS9S2S30SaS2A1A3A3A3A3S1S0S2aS18S4R2A1M0A1S5cA3S1S0SeS11S15S15A2M1A1S7R2A1SaG1A1A3S1S0S15S8R2A1S16S5bA1A3S1S0S10S19G0A1S12A3S0SeS21A1S1bG0A1S35A3A2A2A2A2F_;FW;").
Proof. intros W [<-|[<-|[<-|[]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma s_vals : ltac2:(tb__ "0|2|
S31S2bS34S11S31S2bA2M0SfS31S2bR2R1A4S9G0SfS31S2bS3eZ2A4S9G0SfS31S2bS3fZ4A4S9G0SfS31S2bS40Z6A4SaG0A1A3A3A3A3S1S0S15S32R3PcA2S16S50A1A3S1S0S15S32R3PdA2S16R2A1A3S1S0S15S32R3PeA2S16Z0A1M1A3S0S15S32R3PfA2G1A3A2A2A2F_;Fm;Fs;").
Proof. intros s m H; repeat (destruct H as [H|H]; [injection H as <- <-; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]); destruct H. Qed.
End DrvExitStates2.

(* [comment removed for export] *)
Module DrvExit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "Some"; "option"; "true"; "false"; "app"; "nat"; "length"; "prod"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "WriteEv"; "ExitEv"; "m_fs"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "SLit"; "ss_next"; "sstate"; "ss_lenient"; "ob_dflt"; "rl"; "dflt_writable"; "is_arr"; "ob_cells"; "ob_hi"; "ob_lo"; "reg_sv"; "smatch"; "sprop"; "ss_objs"; "swf"; "agree_below"; "holds"; "rw"; "ss_pc"; "sprop_below"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "mkLeafA"; "sym_runA"; "ax_base"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "cells_bytes"; "beval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.PFAddr"; "SBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "PEND"; "facts_exit"; "Pre_exitP"; "supportedP"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_tr"; "etriple"; "triple"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit.Exit"; "Kf"; "ch1"; "Kw"; "EVS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_out.WLoutS"; "Pre_wl2"; "D"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "to_nat"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit.Exit.Flush"; "Jp"; "rho_wl"; "WLF"; "f6"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvExitStates"; "CUTS_X"; "FUEL_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExitStates2"; "S5_2"; "S5_3"; "S5_4"; "C_2s"; "C_3s"; "C_4s"; "splits"; "T_2"; "T_3"; "T_4"; "Tf_2"; "Tf_3"; "Tf_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_out.WLout"; "Kw"; "MSG"; "Posts_wl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "rho_set_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "state_nolist"; "set_rl"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "mat_equiv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundI SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_out RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvExitStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvExitStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExitStates2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma SPA_morph : ltac2:(tb__ "0|1|
S4eS4eS3bS22S1dS1dS4S11Q40A1A1S51S0S4SfS1fS1fA2M0A1S3fR6A1S7G0A1A3S0S5S36S21R6A1S3eR7A1A2SaA3S2cS37R6S39R8A1S8aR4R3A2A4S2cS37R6R8S8aR5R4A2A4F_;RbR7R5S52R4A1S86S55R4A1A1A4RbR7R6S52R5A1S86S55R5A1A1A4F_;S4cS37RcRaR8R6R5A6S4cS37RcS40RbRaA2R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FS';FA;FJ';FJ;").
Proof.
  intros J J' A S' rho rho' tp w HX Hb HS HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|apply HJ; exact Hk].
  split; [apply HS; exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf; cbn [ax_S ax_X ax_base ax_setS]; rewrite HX; cbn [forallb]; exact Hb|].
  split; [|exact Hhz]. unfold shadow_ok. cbn [ax_X ax_setS]. rewrite HX. constructor.
Qed.

Lemma smatch_splits : ltac2:(tb__ "0|0|
S4bS22S22S1dSfS4S14A1S87A2S0S9S22A1S76R5R4A2S8S22R3A2A3S2cS37R3R5R2A4S2cS37R4R5R3A4F_;F_;Fw;Frho;FS5;FS;Fm;").
Proof.
  intros m S S5 rho w H Hsm. unfold splits, obind in H.
  destruct (split_obj_at S 0 (SLit (-136))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-104))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 5 (SLit (FILE + 120))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 6 (SLit (FILE + 124))) as [S4|] eqn:E4; [|discriminate].
  eapply smatch_split; [exact H|]. eapply smatch_split; [exact E4|]. eapply smatch_split; [exact E3|].
  eapply smatch_split; [exact E2|]. eapply smatch_split; [exact E1|]. exact Hsm.
Qed.

Lemma agree_below_sym : ltac2:(tb__ "0|0|
S4aS1dS1dS30R3R2R1A3S30R4R2R3A3F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' (A & B & C). split; [intros i Hi; symmetry; apply A; exact Hi|].
  split; [intros l; symmetry; apply B | intros a; symmetry; apply C].
Qed.

Section Exit.
Variable ok : assn.
Variable J0 : jpredA.
Variable Spec : list event -> Prop.
Variables n c : Z.

Definition ch1 : word := Z_to_bv 64 1.
Definition EVS (k : nat) : list event := ltac2:(tb__ "0|1|
S5bS11Q8A1M0S14S16S58A1S5dG0Vk;S46Vn;A1A3A4").

Definition Kw (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1S4S14A1M0S15S2G0G0S1VJ0;R5R4R1R2A4S0G0R3ScS14R1S5aVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").

Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15VJ0;R4R3R2R1A4S0S9S19A1S1bS1cR2A1S58A2S8S19S1aS58A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
SdS4fS37Vok;S59R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SdS89S37Vok;S59R1A1A3Fk;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis Hspec : ltac2:(tb__ "0|1|
S1dS4S11Q40M0A1A1S4S14A1S15VJ0;R4R3R2R1A4VSpec;ScS14R3ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R2A1A2S7S14A1A3A3A3A1F_;Fmd;Ftr;Ft;Fr;").

Definition Kf (r1 : valuation) (tp : list word) (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1M0S4S14A1S15S1S0G0R3Vtp;A3S59Vk;Vr1;R3R2R1A5A2Lmd;Ltr;Lt;L_;").

Lemma J0_mat : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15S15S8bS37R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.

Lemma Kf_stable : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS4aS50S37R1S57R4R3R2A3A3Flvl;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS4fS37Vok;S57R3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md msv' [_ HK]. exact (HokK k r1 t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1SdS89S37Vok;S57R3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md x8 [_ HK]. exact (HokP k r1 t tr ms md x8 HK). Qed.

Lemma Kw0_of_J0 : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15VJ0;R4R3R2R1A4S59U0R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md HJ. exists tr. split; [exact HJ|]. unfold EVS. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma okK_J0 : ok_frameA segs ok J0.
Proof. intros r t tr ms md msv' HJ. exact (HokK 0%nat r t tr ms md msv' (Kw0_of_J0 _ _ _ _ HJ)). Qed.
Lemma okP_J0 : ok_pframeA segs ok J0.
Proof. intros r t tr ms md x8 HJ. exact (HokP 0%nat r t tr ms md x8 (Kw0_of_J0 _ _ _ _ HJ)). Qed.

Section Plain.
Variables P E : axst.
Hypothesis HPEND : PEND n = [].
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eS6fS6eVP;SaA5S8G0S6S3aS3cVE;S82A2S7S3aA1A3A2A3").
Hypothesis HnP : ltac2:(tb__ "0|0|
S0S4aS21S39VP;A1A1S56A3").
Hypothesis HlP : ltac2:(tb__ "0|0|
S0S5S23S39VP;A1A1SbA3").
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S9S65A1S83S5eS33S39VE;A1A1A2S8S65S66A2A3").
Hypothesis H17 : ltac2:(tb__ "0|0|
S0S1fS2bS39VE;A1Z11A2S20Z5eA1A3").
Hypothesis H10 : ltac2:(tb__ "0|0|
S0S1fS2bS39VE;A1ZaA2S20Vc;A1A3").
Hypothesis HnE : ltac2:(tb__ "0|0|
S0S4aS21S39VE;A1A1S56A3").
Hypothesis Hc : 0 <= c < 256.

Lemma plain_sum : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;VP;R2R1A5S51S3L_;A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (runA_tr segs ok FUEL_X CUTS_X P _ J0 rho tp); [exact Hrun | exact HlP | apply okK_J0 | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (triple_exitA segs ok Spec J0 E rho1 tp c okK_J0 okP_J0 Hokh); [rewrite HnE; exact Hst0 | exact Hi | left; exact H17 | exact H10 | exact Hc |].
  intros tr md HJ. pose proof (Hspec _ _ _ _ HJ) as X. rewrite HPEND in X. cbn [map app] in X. exact X.
Qed.

Lemma plain_sum_ex : ltac2:(tb__ "0|2|
S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;VP;R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_X CUTS_X P _ J0 rho tp); [exact Hrun | exact HlP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exitA segs J0 E rho1 tp c); [rewrite HnE; exact Hst0 | exact Hi | left; exact H17 | exact H10 | exact Hc]].
  intros w' (tr & md & HJ & Hw). exists tr, md. split; [| rewrite HPEND; cbn [map app]; exact Hw].
  eapply Hst0; [apply agree_below_sym; rewrite <- HnP; exact Hag1 | apply mat_equiv_refl | exact HJ].
Qed.
End Plain.

Section Flush.
Variable m : Z.
Variable W : axst.
Variables S5 Cs : sstate.
Variable o8 : sobj.
Variable bl : list bexp.
Variable s : wsub.
Variable R : list sobj.
Variables T Tf F : axst.

Variable P : axst.
Hypothesis Hc0 : c = 0.
Hypothesis HrunW : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eS6fS6eVP;SaA5S8G0S6S3aS3cVW;S82A2S7S3aA1A3A2A3").
Hypothesis HnP : ltac2:(tb__ "0|0|
S0S4aS21S39VP;A1A1S56A3").
Hypothesis HlP : ltac2:(tb__ "0|0|
S0S5S23S39VP;A1A1SbA3").
Hypothesis HnW : ltac2:(tb__ "0|0|
S0S4aS21S39VW;A1A1S56A3").
Hypothesis HXW : ax_X W = [].
Hypothesis HbW : ltac2:(tb__ "0|0|
S0S1fS3eVW;A1S20S38A1A3").
Hypothesis HfW : ltac2:(tb__ "0|0|
S0S4S2dA1S35S39VW;A1A1S47A3").
Hypothesis Hsplits : ltac2:(tb__ "0|0|
S0S9S22A1S76Vm;S39VW;A1A2S8S22VS5;A2A3").
Hypothesis Hfinish : finish S5 = Cs.
Hypothesis Hnl : state_nolist S5 = true.
Hypothesis Hrl5 : state_has_rl 5 S5 = false.
Hypothesis Ho8 : ltac2:(tb__ "0|0|
S0S9S1eA1S6bS1eS2eVS5;A1U8A3S8S1eVo8;A2A3").
Hypothesis Ho8lo : ltac2:(tb__ "0|0|
S0S1fS2aVo8;A1S20S45A1A3").
Hypothesis Ho8hi : ltac2:(tb__ "0|0|
S0S1fS29Vo8;A1S20S61S45Vm;A2A1A3").
Hypothesis Ho8w : ltac2:(tb__ "0|0|
S0S5S26S24Vo8;A1A1SaA3").
Hypothesis Ho8a : ltac2:(tb__ "0|0|
S0S5S27S24Vo8;A1A1SbA3").
Hypothesis Hcb : ltac2:(tb__ "0|1|
S0S9S4S41A1M0A1S43S28Vo8;A1S20S45A1Z0S63S62S61S45Vm;A2S45A2A1A4S8G0Vbl;A2A3").
Hypothesis Hbl : ltac2:(tb__ "0|1|
S1dS0S4S11Q8A1M0A1S5bS41G0S44R1A1Vbl;A4S46Vn;A1A3Fr;").
Hypothesis Hm1 : ltac2:(tb__ "0|0|
S0S4bS64SeS11Q8A1S46Vn;A1A2A1Vm;A3").
Hypothesis Hm2 : 1 <= m <= 6.
Hypothesis HswfC : swf Cs = true.
Hypothesis HnC : ss_next Cs = NF.
Let C : axst := ax_setS W Cs.
Hypothesis Hefr : ltac2:(tb__ "0|1|
S0S9S4S1eA1M0A1S8eVC;S5fVs;A3S8G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S5S8dVC;S5fVs;VR;S6S3bS60S7S3bA1A3A5SaA3").
Hypothesis S12 : ltac2:(tb__ "0|0|
S0S1fS88Vs;PcA2S20S45A1A3").
Hypothesis S13 : ltac2:(tb__ "0|0|
S0S1fS88Vs;PdA2S20Vm;A1A3").
Hypothesis S14 : wsub_get s 14 = SLit 0.
Hypothesis S15 : wsub_get s 15 = SLit 0.
Hypothesis HT : ltac2:(tb__ "0|0|
S0S3bS8fVs;S5fS60VC;VR;A5VT;A3").
Hypothesis HnT : ss_next (ax_S T) = 125%positive.
Hypothesis HTf : ltac2:(tb__ "0|0|
S0S3bS8cS47VT;A2VTf;A3").
Hypothesis HlTf : ltac2:(tb__ "0|0|
S0S5S23S39VTf;A1A1SbA3").
Hypothesis HrunF : ltac2:(tb__ "0|1|
S0S9S4S3aA1M0A1S3dS5eU7d0S6eVTf;SaA5S8G0S6S3aS3cVF;S82A2S7S3aA1A3A2A3").
Hypothesis HiF : ltac2:(tb__ "0|0|
S0S9S65A1S83S5eS33S39VF;A1A1A2S8S65S66A2A3").
Hypothesis H17F : ltac2:(tb__ "0|0|
S0S1fS2bS39VF;A1Z11A2S20Z5eA1A3").
Hypothesis H10F : ltac2:(tb__ "0|0|
S0S1fS2bS39VF;A1ZaA2S20Z0A1A3").

Definition f6 (r : valuation) : positive -> list byte := ltac2:(tb__ "0|1|
S4aS5S4S11Q8A1M0A1L_;S90R1P6A2S7G0A1S25Vr;R1A2X5x2Ll;").
Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S81S85Vr;S6aVr;A1A2P5S46Vn;A1A3").

Lemma rho_wl_5 : ltac2:(tb__ "0|0|
S1dS0S4S11Q8A1A1S25S68R1A1P5A2S46Vn;A1A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_6 : ltac2:(tb__ "0|1|
S1dS0S4S11Q8A1M0A1S25S68R1A1P6A2S7G0A1A3Fr;"). Proof. intros r. reflexivity. Qed.

Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S4S11Q8A1M0A1M1S25Vr;P5A2S46Vn;A1A3S1S0G1S25Vr;P6A2S7G0A1A3S1S0S4bS13Q40M2S32Vr;PdA2A2Vm;A3S0S4bS13G2S32Vr;PfA2A2Z0A3A2A2A2").
Definition Jp (r1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S4S14A1S15S1S69R4A1S57Vr1;Vtp;U0R4R3R2R1A7A2Lmd;Ltr;Lt;Lr;").

Lemma Jp_stable : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S50S37P5cS67R2R1A2A3Ftp;Fr1;").
Proof.
  intros r1 tp r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable r1 tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.

Lemma Kw_Jp_Kf : ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1M0SdS1dG0S4S14A1S15S7dS67R7R6A2S46Vn;A1S7S11Q8A1A1R5R4R3R2R1A8S57R8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ft;Fr;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLout.TRk, WLout.MSG, EVS. cbn [firstn map]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma MSG_len : ltac2:(tb__ "0|2|
S0SdSeS11Q8A1M0S7eS46Vn;A1M1S7G0A1A2A2SeG0G1A2A3").
Proof. unfold WLout.MSG. rewrite app_nil_r. reflexivity. Qed.

Lemma wl_call : ltac2:(tb__ "0|5|
S1dS4S11Q40A1A1M0S1dG0S54S37Vok;S4cS37S67R4R3A2M1S5fR2R1A5S4dS37S7dG1S46Vn;A1M2S7S11Q8A1M3A1M4SeG3S7eG2G4A2A2A4P5cR2R1S7fA6A4Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ (Jp r1 tp)); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLout.wl2_sum ok (Jp r1 tp) rho2 tp2 (PEND n) [] A5 A6).
  - rewrite A13. symmetry. exact Hm1.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep.
    exact (Kf_okK r1 tp k r t tr0 ms md0 msv' (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho.
    exact (Kf_okP r1 tp k r t tr0 ms md0 x8 (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd _ _ _ _ HJ).
  - lia.
Qed.

Lemma wl_call_ex : ltac2:(tb__ "0|5|
S1dS4S11Q40A1A1M0S1dG0S53S37S4cS37S67R4R3A2M1S5fR2R1A5S4dS37S7dG1S46Vn;A1M2S7S11Q8A1M3A1M4SeG3S7eG2G4A2A2A4P5cR2R1S7fA6A3Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLout.wl2_sum_ex (Jp r1 tp) rho2 tp2 (PEND n) [] A5 A6).
  - rewrite A13. symmetry. exact Hm1.
  - rewrite A15. reflexivity.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd _ _ _ _ HJ).
  - lia.
  - exact Hw.
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S1dS4S11Q40A1A1S1dS51S4cS37S57R4R3U0M0A3VW;R2R3R1A6S4cS37S57R5R4G0A3VC;S68R3A1R4R2A6F_;Fw;Frho;Ftp;Fr1;").
Proof.
  intros r1 tp rho w Hsp.
  unfold C. eapply (SPA_morph (Kf r1 tp 0) (Kf r1 tp 0) W Cs rho (rho_wl rho)); [exact HXW | rewrite HnC, HbW; reflexivity | | intros HK; exact HK | exact Hsp].
  intros Hsm. rewrite <- Hfinish. unfold finish.
  pose proof (smatch_splits m (ax_S W) S5 rho (virt tp w) Hsplits Hsm) as H5.
  pose proof (smatch_set_rl segs rho (f6 rho) S5 (virt tp w) Hnl H5) as H6.
  pose proof (smatch_obj_to_list segs _ S5 (virt tp w) 8 5 o8 SBUF (SBUF + m) bl H6 Ho8 Ho8lo Ho8hi
                ltac:(unfold SBUF; lia) ltac:(unfold SBUF; lia) Ho8w Ho8a Hcb Hrl5) as H7.
  rewrite Hbl in H7. change (rho_set_rl (set_rl rho (f6 rho)) 5 (PEND n)) with (rho_wl rho) in H7.
  apply (smatch_carve_rom segs (rho_wl rho) (obj_to_list S5 8 5) (virt tp w) 0 0 6 (ss_next (obj_to_list S5 8 5)) H7).
  - rewrite <- Hfinish in HswfC. exact HswfC.
  - lia.
  - lia.
  - lia.
  - rewrite rho_wl_6. reflexivity.
  - intros k Hk. exfalso. lia.
  - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S1dS5cS2dS31R1A1S47A3S5cS2dS31S68R2A1A1S47A3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_exit in Hp. destruct Hp as [<-|[<-|[<-|[<-|[<-|[]]]]]]; exact X.
Qed.

Lemma fb_facts : ltac2:(tb__ "0|0|
S0S5S6dS2dS34S56A1S47A3SaA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma flush_sum : ltac2:(tb__ "0|0|
S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;VP;R2R1A5S51S3L_;A4Ftp;Frho;").
Proof.
  intros rho tp.

  eapply (runA_tr segs ok FUEL_X CUTS_X P _ J0 rho tp); [exact HrunW | exact HlP | apply okK_J0 | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. rewrite HfW. intros HF1.
  pose proof (facts_rho_wl rho1 HF1) as HFw.

  eapply triple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply reshape. destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }

  apply (call_soundA segs ok (Kf rho1 tp 0) (Jp rho1 tp) (WLout.Kw (Jp rho1 tp) (PEND n) [] (length (WLout.MSG (PEND n) [])))
           (Kf rho1 tp (length (PEND n))) C WLoutS.Pre_wl2 s R WLout.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [| reflexivity].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf rho1 tp (length (PEND n)))); [intros t md0 (HJ & _ & _); exact HJ|].

    assert (HF' : Forall (holds rho') facts_exit).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) HFw p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf rho1 tp (length (PEND n))) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }

    eapply (runA_tr segs ok 2000%nat CUTS_X Tf _ (Kf rho1 tp (length (PEND n))) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
    apply (triple_exitA segs ok Spec (Kf rho1 tp (length (PEND n))) F rho3 tp 0 (Kf_okK _ _ _) (Kf_okP _ _ _) Hokh (Kf_stable _ _ _ _) HiF (or_introl H17F) H10F ltac:(lia)).
    intros tr2 md2 [_ (tr0 & HJ0 & ->)]. pose proof (Hspec _ _ _ _ HJ0) as X. rewrite Hc0 in X.
    unfold EVS. rewrite firstn_all, <- app_assoc. exact X.
Qed.

Lemma flush_sum_ex : ltac2:(tb__ "0|2|
S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;VP;R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_X CUTS_X P _ J0 rho tp); [exact HrunW | exact HlP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. rewrite HfW. intros HF1.
  pose proof (facts_rho_wl rho1 HF1) as HFw.
  eapply etriple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply reshape. destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_completeA segs (Kf rho1 tp 0) (Jp rho1 tp) (WLout.Kw (Jp rho1 tp) (PEND n) [] (length (WLout.MSG (PEND n) [])))
           (Kf rho1 tp (length (PEND n))) C WLoutS.Pre_wl2 s R WLout.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [| reflexivity].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_exit).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) HFw p Hp). }
    assert (HE : etriple segs (SPA segs (Kf rho1 tp (length (PEND n))) Tf rho' tp)
              (fun w' => exists tr md, J0 rho tp tr md /\ w_tr w' = tr ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)])).
    { eapply (erunA_tr segs 2000%nat CUTS_X Tf _ (Kf rho1 tp (length (PEND n))) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
      eapply etriple_conseq; [intros w Hw; exact Hw | | apply (etriple_exitA segs (Kf rho1 tp (length (PEND n))) F rho3 tp 0 (Kf_stable _ _ _ _) HiF (or_introl H17F) H10F ltac:(lia))].
      intros w' (tr2 & md2 & [_ (tr0 & HJ0 & ->)] & Hw). exists tr0, md2. split.
      - eapply Hst0; [apply agree_below_sym; rewrite <- HnP; exact Hag1 | apply mat_equiv_refl | exact HJ0].
      - rewrite Hw. unfold EVS. rewrite firstn_all, <- app_assoc, Hc0. reflexivity. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm0 | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.
End Flush.

Lemma o8_2 : ltac2:(tb__ "0|4|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS70A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z2A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1S6S41S42ZaA1S7S41A1A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma o8_3 : ltac2:(tb__ "0|6|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS71A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z4A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1M4S6S41S42ZaA1M5S6S41G4S6S41G5S7S41A1A3A3A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma o8_4 : ltac2:(tb__ "0|6|
S2S1eS1eS1S0S9S1eA1S6bS1eS2eS72A1U8A3S8S1eR1A2A3S1S0S1fS2aR1A1S20S45A1M0A3S1S0S1fS29R1A1S20S61S45Z6A2M1A1A3S1S0S5S26S24R1A1M2A1SaA3S1S0S5S27G2A1SbA3S0S9S4S41A1M3A1S43S28R1A1G0Z0S63S62G1S45A2A1A4S8G3S6S41S42Z30A1M4S6S41S42ZaA1M5S6S41G4S6S41G5S6S41G4S6S41G5S7S41A1A3A3A3A3A3A3A2A3A2A2A2A2A2Lo;A2").
Proof. eexists. split; [reflexivity|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_2 : ltac2:(tb__ "0|0|
S1S0S5S84S70A1SaA3S1S0S5S80P5S70A2SbA3S1S0S5S2fS73A1SaA3S1S0S4aS21S73A1S56A3S1S0S4aS21S39S77A1A1P7dA3S0S5S23S39S7aA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_3 : ltac2:(tb__ "0|0|
S1S0S5S84S71A1SaA3S1S0S5S80P5S71A2SbA3S1S0S5S2fS74A1SaA3S1S0S4aS21S74A1S56A3S1S0S4aS21S39S78A1A1P7dA3S0S5S23S39S7bA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma side_4 : ltac2:(tb__ "0|0|
S1S0S5S84S72A1SaA3S1S0S5S80P5S72A2SbA3S1S0S5S2fS75A1SaA3S1S0S4aS21S75A1S56A3S1S0S4aS21S39S79A1A1P7dA3S0S5S23S39S7cA1A1SbA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Local Ltac in3 k := match k with 1 => exact (or_introl eq_refl) | 2 => exact (or_intror (or_introl eq_refl)) | 3 => exact (or_intror (or_intror (or_introl eq_refl))) end.

Theorem exit_sumP (ph : bool) : ltac2:(tb__ "0|0|
S6cSfS4bS4bA2S10S4bS4bVn;Vc;A4S49Vph;A1A3S1dS4S11Q40A1A1S54S37Vok;S4cS37VJ0;S48Vph;Vn;Vc;A3R2R1A5S51S3L_;A4Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. destruct ph; unfold supportedP in Hin; [change (Pre_exitP true n c) with (Pre_exit n c) | change (Pre_exitP false n c) with (Pre_exit0 n c)].
  2:{
    destruct Hin as [E|[]]; injection E as En Ec.
    destruct E0_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit0 n c) true = Some [mkLeafA E0_02 RsCut]) by (rewrite <- En, <- Ec; exact run0_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E0_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit0 n c) E0_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp). }
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as En Ec.
  - destruct E_00_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_00 RsCut]) by (rewrite <- En, <- Ec; exact run_00).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_00) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_00 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_02 RsCut]) by (rewrite <- En, <- Ec; exact run_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_10_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_10 RsCut]) by (rewrite <- En, <- Ec; exact run_10).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_10) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum (Pre_exit n c) E_10 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct o8_2 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_2 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_2 ltac:(in3 1)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_2 ltac:(in3 1)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_2 2 ltac:(in3 1)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_2 RsCut]) by (rewrite <- En, <- Ec; exact run_20).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 2) by (rewrite <- En; reflexivity).
    exact (flush_sum 2 W_2 S5_2 C_2s o _ s_2 R_2 T_2 Tf_2 F_2 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_2 finish_2 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_2 chk_2 S13 S15 T_2_eq HnT Tf_2_eq HlTf run_F2 HiF H17F H10F rho tp).
  - destruct o8_3 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_3 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_3 ltac:(in3 2)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_3 ltac:(in3 2)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_3 4 ltac:(in3 2)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_3 RsCut]) by (rewrite <- En, <- Ec; exact run_30).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 4) by (rewrite <- En; reflexivity).
    exact (flush_sum 4 W_3 S5_3 C_3s o _ s_3 R_3 T_3 Tf_3 F_3 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_3 finish_3 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_3 chk_3 S13 S15 T_3_eq HnT Tf_3_eq HlTf run_F3 HiF H17F H10F rho tp).
  - destruct o8_4 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_4 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_4 ltac:(in3 3)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_4 ltac:(in3 3)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_4 6 ltac:(in3 3)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_4 RsCut]) by (rewrite <- En, <- Ec; exact run_40).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 6) by (rewrite <- En; reflexivity).
    exact (flush_sum 6 W_4 S5_4 C_4s o _ s_4 R_4 T_4 Tf_4 F_4 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_4 finish_4 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_4 chk_4 S13 S15 T_4_eq HnT Tf_4_eq HlTf run_F4 HiF H17F H10F rho tp).
Qed.

Theorem exit_sumP_ex (ph : bool) : ltac2:(tb__ "0|2|
S6cSfS4bS4bA2S10S4bS4bVn;Vc;A4S49Vph;A1A3S1dS4S11Q40M0A1A1S53S37S4cS37VJ0;S48Vph;Vn;Vc;A3R2R1A5S51S2S4S14A1M1G1S2S15S15S1VJ0;R5R4R2R1A4S0G1S52R3A1ScS14R2ScS14S5bS11Q8A1S14S16S58A1S46Vn;A1A4S6S14S17S12G0Vc;A2S18R1A1A2S7S14A1A3A3A3A3A2Lmd;A2Ltr;A2Lw';A3Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. destruct ph; unfold supportedP in Hin; [change (Pre_exitP true n c) with (Pre_exit n c) | change (Pre_exitP false n c) with (Pre_exit0 n c)].
  2:{
    destruct Hin as [E|[]]; injection E as En Ec.
    destruct E0_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit0 n c) true = Some [mkLeafA E0_02 RsCut]) by (rewrite <- En, <- Ec; exact run0_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E0_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit0 n c) E0_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp). }
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as En Ec.
  - destruct E_00_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_00 RsCut]) by (rewrite <- En, <- Ec; exact run_00).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_00) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_00 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_02_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_02 RsCut]) by (rewrite <- En, <- Ec; exact run_02).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_02) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_02 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct E_10_at as (_ & Hi & H17 & H10 & HnE).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA E_10 RsCut]) by (rewrite <- En, <- Ec; exact run_10).
    assert (HP : PEND n = []) by (rewrite <- En; reflexivity).
    assert (H10' : reg_sv (ax_S E_10) 10 = SLit c) by (rewrite <- Ec; exact H10).
    exact (plain_sum_ex (Pre_exit n c) E_10 HP Hrun' eq_refl eq_refl Hi H17 H10' HnE ltac:(lia) rho tp).
  - destruct o8_2 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_2 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_2 ltac:(in3 1)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_2 ltac:(in3 1)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_2 2 ltac:(in3 1)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_2 RsCut]) by (rewrite <- En, <- Ec; exact run_20).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 2) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 2 W_2 S5_2 C_2s o _ s_2 R_2 T_2 Tf_2 F_2 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_2 finish_2 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_2 chk_2 S13 S15 T_2_eq HnT Tf_2_eq HlTf run_F2 HiF H17F H10F rho tp).
  - destruct o8_3 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_3 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_3 ltac:(in3 2)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_3 ltac:(in3 2)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_3 4 ltac:(in3 2)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_3 RsCut]) by (rewrite <- En, <- Ec; exact run_30).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 4) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 4 W_3 S5_3 C_3s o _ s_3 R_3 T_3 Tf_3 F_3 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_3 finish_3 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_3 chk_3 S13 S15 T_3_eq HnT Tf_3_eq HlTf run_F3 HiF H17F H10F rho tp).
  - destruct o8_4 as (o & Ho & Hlo & Hhi & Hw & Ha & Hcb). destruct side_4 as (Hnl & Hrl & Hswf & HnC & HnT & HlTf).
    destruct (W_shape W_4 ltac:(in3 3)) as (HnW & HXW & HbW & HlW & HfW).
    destruct (F_at F_4 ltac:(in3 3)) as (_ & HiF & H17F & H10F).
    destruct (s_vals s_4 6 ltac:(in3 3)) as (_ & S13 & _ & S15).
    assert (Hrun' : sym_runA segsA FUEL_X CUTS_X (Pre_exit n c) true = Some [mkLeafA W_4 RsCut]) by (rewrite <- En, <- Ec; exact run_40).
    assert (Hbl : forall r, map (beval r) [BLit 48; BLit 10; BLit 48; BLit 10; BLit 48; BLit 10] = PEND n) by (intros r; rewrite <- En; reflexivity).
    assert (Hm1 : Z.of_nat (length (PEND n)) = 6) by (rewrite <- En; reflexivity).
    exact (flush_sum_ex 6 W_4 S5_4 C_4s o _ s_4 R_4 T_4 Tf_4 F_4 (Pre_exit n c) (eq_sym Ec) Hrun' eq_refl eq_refl HnW HXW HbW HfW splits_4 finish_4 Hnl Hrl
             Ho Hlo Hhi Hw Ha Hcb Hbl Hm1 ltac:(lia) Hswf HnC efr_4 chk_4 S13 S15 T_4_eq HnT Tf_4_eq HlTf run_F4 HiF H17F H10F rho tp).
Qed.

Definition supported : list (Z * Z) := supportedP true.

End Exit.
End DrvExit.

