(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "andb"; "app"; "Some"; "option"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "sprop_eqb"; "ss_facts"; "SLit"; "ss_next"; "SPUlt"; "sprop_below"; "SPEq"; "SVar"; "ss_objs"; "sv"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv1c"; "sd_chk"; "cur_ok"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "cur0"; "cur_of"; "E_sd1"; "T_sd0"; "i_nums"; "nums_mat"; "E_sd1r"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "K_hv0c"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "sd_ok"; "xf_sd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "g5"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "E_hv0"; "K_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "P_none"; "P_num"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA"; "add_cells8"; "add_cells8_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Lemma hv_checks_entry : ltac2:(tb__ "0|5|
S1S0S1eS5fS49S1fS49A1M0S46Z4Z12A5S4aA3S1S0S16S20S49A1SfS60A1A3S1S0S2S23S4SbS13S22S46A1S48A2S4SbScS14S46A1SfS62S61Z2Z3dA2Z1A2A1A2S5SbA1A3A3SeS1dS49A1M1A1M2A2S3A3S1S0S2S18S1dS4aA1M3A1S3A3S1S0S2S59G2S50S4fS58S15G1A1A5S3A3S1S0S2S57G2S50S4fS56G0A5S3A3S1S0S2S55G2A1S3A3S1S0S2S5eG3S28S29A3S3A3S1S0S1eS21S4aS5dG3S28S29A3A2S32A3S1S0S2S54S47S10G3A1M4A2S3A3S1S0S2S52G4S4dA2S3A3S1S0S2S53G4S4eA2S3A3S1S0S2S1bSbSdS11S4cS4bA2A1G2A3S3A3S1S0S2S1bSbSdScS4bS45A2A1G2A3S3A3S0S2S1bSbSdScS45SfZ4000000A1A2A1G2A3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cur_ok (E T0 : axst) : bool := ltac2:(tb__ "0|4|
S6S6SaS17S24S25VE;A1M0A2S1bSbSdScS24G0A2A1SeS1dVT0;A1M1A1M2A3A2S1bSbSdScG0S25VT0;A1M3A2A1G2A3A2S1cSbS12S10G1A1A1S4SbScS24G3A2S5SbA1A3A3A2").
Definition sd_chk (E Tn Ty : axst) : Prop := ltac2:(tb__ "0|6|
S1S0S2S43VE;A1S3A3S1S0S2S54S47S10S1dVE;A1M0A1M1A2S3A3S1S0S2S52G1S4dA2S3A3S1S0S2S1cSbS12G1A1SeG0A1M2A3S3A3S1S0S2S1aVE;S27VE;S5aA2M3A2S3A3S1S0S2S1aVE;S27VE;S5bA2M4A2S3A3S1S0S1eS51G3S7SbS4SbScS24S25G3A1A2S5SbA1M5A3SeS1dG3A1A1A3A2VTn;A3S1S0S1eS51G4S7SbS4SbScS24S25G4A1A2G5A3SeS1dG4A1A1A3A2VTy;A3S1S0S2S53G1S4eA2S3A3S1S0S2S1bSbSdS11S4cS4bA2A1G2A3S3A3S1S0S2S1bSbSdScS4bS45A2A1G2A3S3A3S0S2S1bSbSdScS45SfZ4000000A1A2A1G2A3S3A3A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv_checks_sd1 : ltac2:(tb__ "0|0|
S1S0S9S1eA1S5cS2aS44A2S8S1eS26A2A3S19S26S33S34A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd2 : ltac2:(tb__ "0|0|
S19S2bS35S36A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd3 : ltac2:(tb__ "0|0|
S19S2cS37S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd4 : ltac2:(tb__ "0|0|
S19S2dS39S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd5 : ltac2:(tb__ "0|0|
S19S2eS3bS3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd6 : ltac2:(tb__ "0|0|
S19S2fS3dS3eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd7 : ltac2:(tb__ "0|0|
S19S30S3fS40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv_checks_sd8 : ltac2:(tb__ "0|0|
S19S31S41S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
