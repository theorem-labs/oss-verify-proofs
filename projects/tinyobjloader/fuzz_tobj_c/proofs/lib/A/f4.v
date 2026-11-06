(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_024.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3 ek.

(* [comment removed for export] *)
Module Lib_load_obj_hv1c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "andb"; "app"; "Some"; "option"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "sprop_eqb"; "ss_facts"; "SLit"; "ss_next"; "SPUlt"; "sprop_below"; "SPEq"; "SVar"; "ss_objs"; "sv"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv1c"; "sd_chk"; "cur_ok"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "cur0"; "cur_of"; "E_sd1"; "T_sd0"; "i_nums"; "nums_mat"; "E_sd1r"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "K_hv0c"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "sd_ok"; "xf_sd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "g5"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "E_hv0"; "K_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "P_none"; "P_num"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA"; "add_cells8"; "add_cells8_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Lemma hv_checks_entry : ltac2:(tb__ "0|5|
S1S0S1eS5fS49S1fS49A1M0S46Z4Z1eA5S4aA3S1S0S16S20S49A1SfS60A1A3S1S0S2S23S4SbS13S22S46A1S48A2S4SbScS14S46A1SfS62S61Z2Z3dA2Z1A2A1A2S5SbA1A3A3SeS1dS49A1M1A1M2A2S3A3S1S0S2S18S1dS4aA1M3A1S3A3S1S0S2S59G2S50S4fS58S15G1A1A5S3A3S1S0S2S57G2S50S4fS56G0A5S3A3S1S0S2S55G2A1S3A3S1S0S2S5dG3S28S29A3S3A3S1S0S1eS21S4aS5cG3S28S29A3A2S32A3S1S0S2S54S47S10G3A1M4A2S3A3S1S0S2S52G4S4dA2S3A3S1S0S2S53G4S4eA2S3A3S1S0S2S1bSbSdS11S4cS4bA2A1G2A3S3A3S1S0S2S1bSbSdScS4bS45A2A1G2A3S3A3S0S2S1bSbSdScS45SfZ4000000A1A2A1G2A3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cur_ok (E T0 : axst) : bool := ltac2:(tb__ "0|4|
S6S6SaS17S24S25VE;A1M0A2S1bSbSdScS24G0A2A1SeS1dVT0;A1M1A1M2A3A2S1bSbSdScG0S25VT0;A1M3A2A1G2A3A2S1cSbS12S10G1A1A1S4SbScS24G3A2S5SbA1A3A3A2").
Definition sd_chk (E Tn Ty : axst) : Prop := ltac2:(tb__ "0|6|
S1S0S2S43VE;A1S3A3S1S0S2S54S47S10S1dVE;A1M0A1M1A2S3A3S1S0S2S52G1S4dA2S3A3S1S0S2S1cSbS12G1A1SeG0A1M2A3S3A3S1S0S2S1aVE;S27VE;S5aA2M3A2S3A3S1S0S2S1aVE;S27VE;S5bA2M4A2S3A3S1S0S1eS51G3S7SbS4SbScS24S25G3A1A2S5SbA1M5A3SeS1dG3A1A1A3A2VTn;A3S1S0S1eS51G4S7SbS4SbScS24S25G4A1A2G5A3SeS1dG4A1A1A3A2VTy;A3S1S0S2S53G1S4eA2S3A3S1S0S2S1bSbSdS11S4cS4bA2A1G2A3S3A3S1S0S2S1bSbSdScS4bS45A2A1G2A3S3A3S0S2S1bSbSdScS45SfZ4000000A1A2A1G2A3S3A3A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv_checks_sd1 : ltac2:(tb__ "0|0|
S1S0S9S1eA1S5eS2aS44A2S8S1eS26A2A3S19S26S33S34A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
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
End Lib_load_obj_hv1c.

(* [comment removed for export] *)
Module Lib_load_obj_hv2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "pair"; "true"; "nat"; "nil"; "prod"; "list"; "option"; "Some"; "false"; "length"; "andb"; "app"; "S"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "ax_setS"; "has_facts"; "g8"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sobj"; "SPUle"; "sv"; "SVar"; "sprop_eqb"; "ss_objs"; "ss_facts"; "SPUlt"; "ss_next"; "DUnknown"; "sstate"; "swf"; "SAlu"; "SPEq"; "cell"; "mkCell"; "ob_cells"; "sprop_below"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "s1A"; "mH"; "sel_front"; "extra_hv"; "robjs_chkR"; "PhisH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "NP"; "g5"; "vDp"; "vLEN"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2"; "Pre_ms"; "s_ms"; "L_ms"; "da_chk"; "ms_chk"; "s_da"; "E_ms10"; "E_ms20"; "E_ms30"; "R_ms"; "T_da1"; "T_da2"; "T_da3"; "T_ms1"; "T_ms2"; "T_ms3"; "cutsH2"; "exitsH2"; "objs_nl"; "zcells"; "B_da1"; "B_da2"; "B_da3"; "E_da1c"; "E_da2c"; "E_da3c"; "E_ms1"; "E_ms1r"; "E_ms2"; "E_ms2r"; "E_ms3"; "E_ms3r"; "H_ecertH2_ok"; "R_da"; "T_da0"; "T_da10"; "T_da20"; "T_da30"; "T_ms0"; "T_ms10"; "T_ms1b"; "T_ms1z"; "T_ms20"; "T_ms2b"; "T_ms2z"; "T_ms30"; "T_ms3b"; "T_ms3z"; "da_ok"; "keep_ecertH2_ok"; "ms_cut"; "ms_ok"; "optS'"; "pure_posts_ok"; "rel_ms"; "sh_of"; "xf_da"; "xf_ms"; "xfb_da"; "xfb_ms"; "zc8"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "P_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "V_B"; "A1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "V_below"; "ejcertAF"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "optL'"; "E_da1"; "E_da2"; "E_da3"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "xextraLO"; "xrs_chkC"; "robjs_chkC"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "sub"; "add"; "eqb"; "to_nat"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "local_ok"; "shadow_release_stateA"; "shobj"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code";
"segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "sh_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition xf_da (T : axst) : list axform := ltac2:(tb__ "0|1|
SbS22S27S12VT;A1A1A2S4S0S1aS3eS0S4S3bS3cS45VT;A3S0S4S3bS3cS20N30A1VT;A3S5S4A1A3A3R1A2S0S1aS1dU0M0A1S0S1aS1cG0S20N60A1A2S5S1aA1A3A3A3Tn;").
Definition s_da (E : axst) : wsub := ltac2:(tb__ "0|0|
SacPaS12VE;A1S12S88A1A3").
Definition R_da (E : axst) : list sobj := ltac2:(tb__ "0|0|
S47S9cVE;S88S4dVE;A1A3A1").
Definition da_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S8S7S22A1M0A1S1Lx;S9cVE;S88S4dVE;A1M1A3G0S9dVE;S88G1R1S92S19S11S18S8aA4A5LR;SaX8x2").
Definition T_da0 (E : axst) : axst := ltac2:(tb__ "0|0|
Sb9S28S12VE;A1A1S9fS4dVE;A1S88S89VE;S69VE;A1A5A2").

Definition xfb_da (T : axst) : list axform := ltac2:(tb__ "0|0|
SbS22S27S12VT;A1A1A2S4S0S1aS3eS0S4S3bS3cS45VT;A3S0S4S3bS3cS20N60A1VT;A3S5S4A1A3A3R1A2S0S1aS1dU0A1S5S1aA1A3A3Tn;").

Definition E_da1c : axst := Eval vm_compute in optL' (apply_axforms E_da1 (xf_da E_da1)).
Definition E_da2c : axst := Eval vm_compute in optL' (apply_axforms E_da2 (xf_da E_da2)).
Definition E_da3c : axst := Eval vm_compute in optL' (apply_axforms E_da3 (xf_da E_da3)).
Definition T_da10 : axst := Eval vm_compute in T_da0 E_da1c.
Definition T_da20 : axst := Eval vm_compute in T_da0 E_da2c.
Definition T_da30 : axst := Eval vm_compute in T_da0 E_da3c.
Definition B_da1 : axst := Eval vm_compute in optL' (apply_axforms T_da10 (xfb_da T_da10)).
Definition B_da2 : axst := Eval vm_compute in optL' (apply_axforms T_da20 (xfb_da T_da20)).
Definition B_da3 : axst := Eval vm_compute in optL' (apply_axforms T_da30 (xfb_da T_da30)).
Definition T_da1 : axst := Eval vm_compute in ax_tidy B_da1.
Definition T_da2 : axst := Eval vm_compute in ax_tidy B_da2.
Definition T_da3 : axst := Eval vm_compute in ax_tidy B_da3.

Definition da_chk (E0 Ec T0 B T : axst) : Prop := ltac2:(tb__ "0|4|
S10SfS8S11A1M0S1bVE0;S80VE0;A1A2S9S11VEc;A2A3S10SfS1S78VEc;A1S3A3S10SfS1Sb2S43S2aS12VEc;A1M1A1M2A2S3A3S10SfS1S38G2S35A2S3A3S10SfS1S86S21S33G2A1S28G1A1M3A3S3A3S10SfS11S6aVEc;A1VT0;A3S10SfG0S1bVT0;S82VT0;A1A2S9S11VB;A2A3S10SfS11Sb7VB;A1VT;A3S10SfS1S90G2S8dA2S3A3S10SfS1S85S21S26S29S9bS9aA2A1G3A3S3A3S10SfS1S85S21S26S23S9aS46A2A1G3A3S3A3SfS1S85S21S26S23S46S20Z4000000A1A2A1G3A3S3A3A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv2_checks_da1 : ltac2:(tb__ "0|0|
S4bS96S5fS6bS5cS52A5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_da2 : ltac2:(tb__ "0|0|
S4bS97S60S6cS5dS53A5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_da3 : ltac2:(tb__ "0|0|
S4bS98S61S6dS5eS54A5"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_ms10 : axst := Eval vm_compute in leafL (runL 400 cps_v T_da1) memset_pc 0.
Definition E_ms20 : axst := Eval vm_compute in leafL (runL 400 cps_v T_da2) memset_pc 0.
Definition E_ms30 : axst := Eval vm_compute in leafL (runL 400 cps_v T_da3) memset_pc 0.

Definition objs_nl (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Definition sh_of (A : axst) : sobj := ltac2:(tb__ "0|0|
S87S22S27S12VA;A1A1Sb5A3").
Definition rel_ms (A : axst) : axst := ltac2:(tb__ "0|1|
Sb0VA;S5aVA;A1P6eS0S6S39S39A2M0S2S39S39Z20Z40A4S5G0A1A3A4").

Definition xf_ms (n : Z) (T : axst) : list axform := ltac2:(tb__ "0|5|
S3bS42S20Z20M0A1VT;A3S4S1S7S1aA1L_;Sa8Vn;Z0A2S0S1aS1cR1S20Z38A1M1A2S0S1aS1eR1G0A2S5S1aA1M2A3A3S0S1aS1cR1S20Sa7G0Sa5Z8Vn;A2A2M3A1A2S0S1aS1cSeR1A1M4G1A2S0S1aS1eG4G3A2G2A3A3A3X1x2Ti;").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_ms (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S6S3aS24A2M0S2S3aS24P35S2eSb3S42S20Z20A1A3A4S0G0S2S3aS24P36S20Z40A1A4S0G0S2S3aS24Sc1S45A4SacPaS12VE;A1S12S48A1A3A3A3A3").
Definition R_ms (E : axst) : list sobj := ltac2:(tb__ "0|0|
S47S9cVE;S48S49VE;A1A3A1").
Definition ms_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S8S7S22A1M0A1S1Lx;S9cVE;S48S49VE;A1M1A3G0S9eVE;S48G1R1S0S11S4aS5S11A1A3A5LR;SaX8x2").
Definition T_ms0 (E : axst) : axst := ltac2:(tb__ "0|0|
SbeS48VE;S49VE;A1S51VE;A1S4aA5").

Definition zc8 (k : Z) : cell := ltac2:(tb__ "0|1|
S31S20Sa5Z8M0Vk;A2A1G0S20Z0A1A3").
Definition zcells (m : nat) : list cell := ltac2:(tb__ "0|0|
S92S4S30S4S84SaaR1A1A1Lk;S93U0Vm;A2A4").
Definition optS' (S0 : sstate) (x : option sstate) : sstate := match x with Some s => s | None => S0 end.
Definition ms_z (n : Z) (T : axst) : axst := ltac2:(tb__ "0|1|
S15VT;S7cS12VT;A1M0SadG0U1S5bSa9Sa6Z3Vn;A2A1A1A3A2A2").
Definition xfb_ms (n : Z) (T : axst) : list axform := ltac2:(tb__ "0|7|
S95S1bVT;S0S1aS1fU1A1M0S5S1aA1M1A3A2A1S11SbS22S27S12R1A1A1A2S4S1S7S1aA1L_;Sa8Vn;Z0A2S0S1aG0S0S1aS3eS0S4S3bS42S20Z20M2A1R2A3M3S0S4S3bS42S20Z38A1R2A3S5S4A1A3M4A3R1A2S0S1aS1dU0A1M5G1A3M6A3A3S0S1aG0S0S1aS3eS0S4G3S0S4S3bS42S20Sa7G2Sa5Z8Vn;A2A2A1R2A3G4A3A3R1A2S0S1aG5G6A3A3A3X1x2Tm;TT2;").

Definition ms_cut (T : axst) : axst := ltac2:(tb__ "0|0|
SaeVT;S94S44Z4Z1eA5S11S95S1bR1S0S1aS1cS3bS3cS45R1A3S20N30A1A2S5S1aA1A3A2A1TT1;").

Definition E_ms1r : axst := Eval vm_compute in rel_ms E_ms10.
Definition E_ms2r : axst := Eval vm_compute in rel_ms E_ms20.
Definition E_ms3r : axst := Eval vm_compute in rel_ms E_ms30.
Definition E_ms1 : axst := Eval vm_compute in optL' (apply_axforms E_ms1r (xf_ms 0 E_ms1r)).
Definition E_ms2 : axst := Eval vm_compute in optL' (apply_axforms E_ms2r (xf_ms 1 E_ms2r)).
Definition E_ms3 : axst := Eval vm_compute in optL' (apply_axforms E_ms3r (xf_ms 2 E_ms3r)).
Definition T_ms10 : axst := Eval vm_compute in T_ms0 E_ms1.
Definition T_ms20 : axst := Eval vm_compute in T_ms0 E_ms2.
Definition T_ms30 : axst := Eval vm_compute in T_ms0 E_ms3.
Definition T_ms1z : axst := Eval vm_compute in ms_z 0 T_ms10.
Definition T_ms2z : axst := Eval vm_compute in ms_z 1 T_ms20.
Definition T_ms3z : axst := Eval vm_compute in ms_z 2 T_ms30.
Definition T_ms1b : axst := Eval vm_compute in optL' (apply_axforms T_ms1z (xfb_ms 0 T_ms1z)).
Definition T_ms2b : axst := Eval vm_compute in optL' (apply_axforms T_ms2z (xfb_ms 1 T_ms2z)).
Definition T_ms3b : axst := Eval vm_compute in optL' (apply_axforms T_ms3z (xfb_ms 2 T_ms3z)).
Definition T_ms1 : axst := Eval vm_compute in ms_cut T_ms1b.
Definition T_ms2 : axst := Eval vm_compute in ms_cut T_ms2b.
Definition T_ms3 : axst := Eval vm_compute in ms_cut T_ms3b.

Definition pure_posts_ok (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
S86S11S11ScScS7S22A1M0S1Lx;Sb8S12VPre;A1S12R1A1A2S3S22G0SaLl;Ls;X7x2Sa0VPre;R1A2A2S34S13R1A1S13VPre;A1A2A2LL;VLs;A3").
Definition ms_chk (n : Z) (E0 Er E T0 Tz Tb T : axst) : Prop := ltac2:(tb__ "0|12|
S10SfS7S22A1S27S12VE0;A1M0A1SdS22S5aVE0;A1M1S0S22Sb1S44Z4M2Z1eM3S32S7fVE0;A1A1M4S2bA5S5S22A1A3A3A3S10SfS24S13VE0;A1S20Sc0A1M5A3S10SfS1S16S0S21S2fS17S44A1S42A2S0S21S23S25S44A1S20Sa6SabZ2Z3dA2Z1A2A1A2S5S21A1A3A3M6S28G0A1M7A2S3A3S10SfS1S86S6S39S39A2M8SafG4S2bG2G3A4S0G8S2S39S39Z20Z40A4S5G8A1A3A3S3A3S10SfS1S38S2aG0A1M9S35A2S3A3S10SfS1S40G7S8cS8bS3fG1A5S3A3S10SfS1Sa1G7A1S3A3S10SfS11S7eVE0;A1VEr;A3S10SfS8S11A1MaS1bVEr;S81Vn;VEr;A2A2S9S11VE;A2A3S10SfS1S7bVE;A1S3A3S10SfS1SbfS43S49VE;A1A2S3A3S10SfS1Sb2S43S2aS12VE;A1MbA1McA2S3A3S10SfS1S38GcS35A2S3A3S10SfS1SbaGcS36S8eA1A2S3A3S10SfS1S7dS48S0S11S4aS5S11A1A3A2S3A3S10SfS1Sa4S28GbA1MdS8cS8bS3fS51VE;A1A5S3A3S10SfS1Sa3GdS8cS8bSa2S14VE;A1A5S3A3S10SfS1Sa1GdA1S3A3S10SfS11S6eVE;A1VT0;A3S10SfS8S2cA1SadS12VT0;A1U1S5bSa9Sa6Z3Vn;A2A1A1A3S9S2cS12VTz;A1MeA2A3S10SfS11S15VT0;GeA2VTz;A3S10SfS1S2dGeA1S3A3S10SfGaS1bVTz;S83Vn;VTz;A2A2S9S11VTb;A2A3S10SfS24S13VTb;A1G5A3S10SfS1S16G6S28S12VTb;A1MfA1M10A2S3A3S10SfS1SbdS94S14VTb;A1A2S3A3S10SfS1S2dS12SaeVTb;S94S44G2G3A5M11A1A1S3A3S10SfS1S40G10S8cS8bS3fS27GfA1A5S3A3S10SfS1Sa3G10S8cS8bSa2S94A5S3A3S10SfS1Sa1G10A1S3A3S10SfS11S7aVTb;A1VT;A3S10SfGaS1bG11S0S1aS1cS3bS3cS45G11A3S20N30A1A2S5S1aA1A3A2S9S11VT;A2A3S10SfS1S90G9S8dA2S3A3S10SfS1S85S21S26S29S9bS9aA2A1G7A3S3A3S10SfS1S85S21S26S23S9aS46A2A1G7A3S3A3SfS1S85S21S26S23S46S20Z4000000A1A2A1G7A3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv2_checks_ms1 : ltac2:(tb__ "0|0|
S4cZ0S4eS63S62S6fS71S70S55A8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_ms2 : ltac2:(tb__ "0|0|
S4cZ1S4fS65S64S72S74S73S56A8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv2_checks_ms3 : ltac2:(tb__ "0|0|
S4cZ2S50S67S66S75S77S76S57A8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsH2 : list efnode := ltac2:(tb__ "0|8|
S0S6S6S6S11S37A2M0S4A2M1S6S39S24A2M2A2M3S2G1G2S2G0S4S2S11S37S52S35A4U1M4A4S3dZ10M5Z3A2M6A4S0G3S2G1G2S2G0S4S2S11S37S53S35A4G4A4G6A4S0G3S2G1G2S2G0S4S2S11S37S54S35A4G4A4G6A4S0G3S2G1G2S2G0S4S2S11S37S55S35A4G4A4S3dG5Z1A2M7A4S0G3S2G1G2S2G0S4S2S11S37S56S35A4G4A4G7A4S0G3S2G1G2S2G0S4S2S11S37S57S35A4G4A4G7A4S5G3A1A3A3A3A3A3A3").
Definition exitsH2 : list efnode := ltac2:(tb__ "0|6|
S0S6S6S6S11S37A2M0S4A2M1S6S39S24A2M2A2M3S2G1G2S2G0S4S2S11S37S4eS35A4U1M4A4S3dZ10Z2A2M5A4S0G3S2G1G2S2G0S4S2S11S37S4fS35A4G4A4G5A4S0G3S2G1G2S2G0S4S2S11S37S50S35A4G4A4G5A4S0G3S2G1G2S2G0S4S2S11S37Sb6S35A4G4A4S3dZfZ64A2A4S5G3A1A3A3A3A3").

Definition keep_ecertH2_ok : list sprop := ltac2:(tb__ "0|2|
S0S21S29S25P1ccA1S25P1d3A1M0A2S0S21S23S25P191A1S20Z10000000000A1A2S0S21S23G0S25PeA1M1A2S0S21S23S20Z7fff7f800000A1S25PaA1A2S0S21S23G1S20Z4000000A1A2S5S21A1A3A3A3A3A3").
Definition H_ecertH2_ok : list sprop := ltac2:(tb__ "0|0|
SbcS79SdS8fS58S59A3A2").
Lemma ecertH2_ok : ltac2:(tb__ "0|1|
SfS1S91Sb4S43S41U258S99S43S92S8fS8fSbbS68A1M0S58A4S92S8fS8fG0S59A4A8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_hv2.

(* [comment removed for export] *)
Module Lib_load_obj_al.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "pair"; "app"; "prod"; "nil"; "Some"; "nat"; "fst"; "option"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SAlu"; "SLit"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al"; "s_l"; "E_l"; "R_l"; "brest_l"; "T_l_f0"; "T_l_ok"; "T_l_ok0"; "Xk_l"; "bd_l"; "hand_l"; "payC_l"; "tv_l"; "B_l_f"; "B_l_ok"; "LAr"; "PDk_l"; "kept_l"; "payX_l"; "payY_l"; "rates_l"; "xfb_l"; "T_l_f"; "T_l_okR"; "bd_l_f"; "bd_l_ok"; "bdrest_l"; "cg_lc"; "cg_li"; "d_lc"; "d_li"; "gLC'"; "gLI'"; "k_lc"; "k_li"; "nd_l_f"; "nd_l_ok"; "passed_l"; "qCURl"; "rate_glc"; "rate_gli"; "tv_l_f"; "tv_l_ok"; "xf_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al.HL"; "Pre_hl"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "gLI"; "pE0"; "HNEXT"; "gLC"; "pCP"; "pLNL"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_al.HL2"; "P_fail"; "P_ok"; "Posts_hl"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.
Module HL. Include Lib_handle_l. End HL.
Module HL2. Include Lib_handle_l_s2. End HL2.

Definition c_li : sv := t_c (v_li vsP).  Definition d_li : sv := t_d (v_li vsP).  Definition k_li : sv := t_k (v_li vsP).
Definition c_lc : sv := t_c (v_lc vsP).  Definition d_lc : sv := t_d (v_lc vsP).  Definition k_lc : sv := t_k (v_lc vsP).
Definition xf_l : list axform := ltac2:(tb__ "0|2|
S2S51S56U7M0S12N120M1A1A2S2S51S53G0G1A2S8S51A1A3A3").
Definition E_l : axst := Eval vm_compute in optL (apply_axforms E_hl xf_l).

Definition s_l : wsub := ltac2:(tb__ "0|1|
S2S7S57SfA2M0S5S57SfP81S6aA4S2G0S5S57SfP82S6dA4S2G0S5S57SfS59S69A4S2G0S5S57SfP13S11S67S80S12Z120A1A3A4S92PaS1bS25A1S1bS4fA1A3A3A3A3A3").
Definition R_l : list sobj := Eval vm_compute in optR (entails_frA E_l HL.Pre_hl s_l).
Definition PDk_l : list pdescK := ltac2:(tb__ "0|0|
S96S74S7cS59S3A3A1").
Definition passed_l : list (sv * sv) := ltac2:(tb__ "0|1|
S2S7SfSfA2M0S5SfSfS41S79ZcS45A2A4S2G0S5SfSfS40S79Z4S44A2A4S8G0A1A3A3").
Definition kept_l : list (sv * sv) := Eval vm_compute in (firstn 11 tvL ++ skipn 13 tvL).
Definition tv_l : list (sv * sv) := kept_l ++ passed_l.

Definition LAr : bitem := ltac2:(tb__ "0|1|
S21Z1Z0S2S7S58S1eA2M0S5S58S1eS5bS1fS81A1A4S2G0S5S58S1eS99S5bA1S1fS70A1A4S2G0S5S58S1eN48S1fS6fA1A4S8G0A1A3A3A3S9aS5bZ18A2A4").
Definition bdrest_l : list bitem := Eval vm_compute in (firstn 22 bd_rest ++ skipn 26 bd_rest).
Definition brest_l : list bitem := ltac2:(tb__ "0|0|
S2S1dS32S2S1dS8fS8eA1S3dA3A3").
Definition hand_l : list bitem := Eval vm_compute in bd_subst s_l (nd_bd (ndh h0 true HL.nd0)).
Definition bd_l : list bitem := Eval vm_compute in (firstn 4 (skipn 22 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_l).
Definition Xk_l : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_li) && negb (sv_eqb (fst r) d_lc)) (ax_X E_l).

Definition payX_l : list bitem := [LA A1].
Definition payY_l : list bitem := ltac2:(tb__ "0|1|
S2S1dS32S2S1dS75S1dU0S2dS5dZ0A1M0A4S2S1dS75S1dU5S2dG0A4S8S1dA1A3A3A3").
Definition payC_l : list bitem := Eval vm_compute in (firstn 4 (skipn 22 bd_rest) ++ LAK AK1 :: bdrest_l).

Lemma al_checks : ltac2:(tb__ "0|a|
S1S0ScS1aA1S52S91S4eA2S9S1aS25A2A3S1S0ScSeS14A1M0A1S85S25S4fS24A3S9G0S26A2A3S1S0S4S84S25S4fS24S26S76S7S7S1aS5fA2M1S17S17OF_;F_;M2A2M3S1aG3SbS1aS5fSbG1G2R1A3A3Ld;S33A4A5S3A3S1S0S4S97S7fS24A2S3A3S1S0S4S93S24S78A2S3A3S1S0S4S87S24S48S63S73S59S3S50A3M4A1A3S3A3S1S0S4S65S61S24S62G4A1A2S60S69S3A2M5A2S3A3S1S0S4S8cS7S89G2A2M6G6S8aS4fS78S24S16S1bS25A1M7A1M8SbS89G2R1A3A5Ld;S33A3S3A3S1S0S4S72S5cS2fA2S3A3S1S0S4S72S2fS5cA2S3A3S1S0S4S71S90S5bA1S2cA2S3A3S1S0S4S8bS2bS1cS25A1A2S3A3S1S0S4S71S2cS6S1dS2eS35A3A2S3A3S1S0S4S71S6S1dS2eS36A3S6S1dS2dS27A3A2S3A3S1S0S4S23S2eA1S3A3S1S0S4S95S15G7A1S12Z0M9A1G9S35S36A5S3A3S1S0S4S66G8S5eS2fS5aS2cG5A4A2S3A3S1S0S4S22G8S27A2S3A3S1S0S4S98S7fG8A2S3A3S0S57G8S6cA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_l_ok0 : axst := Eval vm_compute in T_afterA3 HL.Pre_hl E_l s_l R_l HL2.P_ok Xk_l.
Definition T_l_f0 : axst := Eval vm_compute in T_afterA3 HL.Pre_hl E_l s_l R_l HL2.P_fail Xk_l.
Definition isub_ok_l : wsub := Eval vm_compute in import_subA s_l HL.Pre_hl HL2.P_ok E_l.
Definition isub_f_l : wsub := Eval vm_compute in import_subA s_l HL.Pre_hl HL2.P_fail E_l.
Definition tv_l_ok : list (sv * sv) := Eval vm_compute in (kept_l ++ import_tv isub_ok_l (nd_tv HL2.nd_ok)).
Definition bd_l_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_l (nd_bd HL2.nd_ok) ++ brest_l).
Definition tv_l_f : list (sv * sv) := Eval vm_compute in (kept_l ++ import_tv isub_f_l (nd_tv HL2.nd_fail)).
Definition bd_l_f : list bitem := Eval vm_compute in (bd_subst isub_f_l (nd_bd HL2.nd_fail) ++ brest_l).
Definition nd_l_ok : ndesc := ltac2:(tb__ "0|0|
S5eS4dS5aS3cS60S69S3A2A4").
Definition nd_l_f : ndesc := ltac2:(tb__ "0|0|
S5eS4cS5aS3bS60S69S3A2A4").
Definition xfb_l (T : axst) : list axform := ltac2:(tb__ "0|2|
S2S51S53U0M0Z120A2S2S51S55S2SaG0S2SaU3S2SaU1S2SaU2S77U4M1S8dSdS14S19S1bVT;A1A1A2G1A2A2A3A3A3A3A1S2S51S54G0A1S8S51A1A3A3A3").
Definition B_l_ok : axst := Eval vm_compute in optL (apply_axforms T_l_ok0 (xfb_l T_l_ok0)).
Definition B_l_f : axst := Eval vm_compute in optL (apply_axforms T_l_f0 (xfb_l T_l_f0)).
Definition T_l_ok : axst := Eval vm_compute in ax_tidy B_l_ok.
Definition T_l_f : axst := Eval vm_compute in ax_tidy B_l_f.

Definition qCURl : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qCUR.
Definition gLI' : sv := ltac2:(tb__ "0|0|
S11S67S6aS11S68S49S6eA3A3").
Definition gLC' : sv := SAlu ALU_ADD gLC (SLit 1).

Definition rate_gli : sprop := ltac2:(tb__ "0|0|
S13S43S11S67S6bS12Z1A1A3A2").
Definition rate_glc : sprop := ltac2:(tb__ "0|0|
S13S42S11S67S6bS12Z1A1A3A2").

Definition qCl : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qC.
Definition qC2l : sv := Eval vm_compute in sv_subst isub_ok_l HL2.qC2.
Definition cg_li : sprop := SPUle qCl gLI'.
Definition cg_lc : sprop := SPUle qC2l gLC'.
Definition rates_l : list sprop := ltac2:(tb__ "0|0|
S2S10S4bS2S10S4aS2S10S3fS2S10S3eS8S10A1A3A3A3A3").
Definition T_l_okR : axst := Eval vm_compute in ax_add_facts rates_l T_l_ok.
Lemma al_checks_nd : ltac2:(tb__ "0|7|
S1S0S5fS5eS6S7SfSfA2M0S34S86S83S24S4fS7bS25A4M1S63S73S59S3S7eA3M2A1A2A3S5aS6S1dS20G1S64G2A1A2S27A3S61G1S62G2A1A2A4S47A3S1S0S5fS5eS6G0S34S86S83S24S4fS7aS25A4M3S63S73S59S3S7dA3M4A1A2A3S5aS6S1dS20G3S64G4A1A2S27A3S61G3S62G4A1A2A4S46A3S1S0S1aS88S4fS25S24S26S7bS2bA6S2aA3S1S0S1aS88S4fS25S24S26S7aS2bA6S28A3S1S0ScS1aA1M5S52S2aS38S2aA1A2S9S1aS31A2A3S1S0G5S52S28S38S28A1A2S9S1aS30A2A3S1S0S1aS82S31A1S29A3S1S0S1aS82S30A1S39A3S1S0S1aS94S29S6S10S37S15S1bS29A1M6A1A3A2S3aA3S0S4S8cS10S18S16G6A1A1S37A3S3A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_al.

(* [comment removed for export] *)
Module Lib_load_obj_ap.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "app"; "pair"; "prod"; "nil"; "Some"; "nat"; "fst"; "option"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap"; "s_p"; "E_p"; "R_p"; "brest_p"; "T_p_f0"; "T_p_ok"; "T_p_ok0"; "Xk_p"; "bd_p"; "payC_p"; "tv_p"; "B_p_f"; "B_p_ok"; "LAr"; "PDk_p"; "hand_p"; "kept_p"; "payX_p"; "payY_p"; "xfb_p"; "T_p_f"; "T_p_okR"; "bd_p_f"; "bd_p_ok"; "bdrest_p"; "d_pi"; "gPI'"; "k_pi"; "nd_p_f"; "nd_p_ok"; "passed_p"; "qCURp"; "rate_gp"; "tv_p_f"; "tv_p_ok"; "xf_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "SLit"; "sprop"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "SPUle"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap.HP"; "Pre_hp"; "P_fail"; "P_ok"; "Posts_hp"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "gPI"; "HNEXT"; "pCP"; "pE0"; "pLNL"; "pNX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HPAddr.
Module HP. Include Lib_handle_p. End HP.

Definition c_pi : sv := t_c (v_pi vsP).  Definition d_pi : sv := t_d (v_pi vsP).  Definition k_pi : sv := t_k (v_pi vsP).
Definition xf_p : list axform := ltac2:(tb__ "0|2|
S3S4fS54U7M0S3fN120M1A1A2S3S4fS51G0G1A2S8S4fA1A3A3").
Definition E_p : axst := Eval vm_compute in optL (apply_axforms E_hp xf_p).

Definition s_p : wsub := ltac2:(tb__ "0|1|
S3S7S55S3dA2M0S6S55S3dP95S66A4S3G0S6S55S3dS57S65A4S3G0S6S55S3dP13S3eS6cS75S3fZ120A1A3A4S8aPaS10S13A1S10S48A1A3A3A3A3").
Definition R_p : list sobj := Eval vm_compute in optR (entails_frA E_p HP.Pre_hp s_p).
Definition PDk_p : list pdescK := ltac2:(tb__ "0|0|
S8eS71S4bS57S2A3A1").
Definition passed_p : list (sv * sv) := ltac2:(tb__ "0|1|
S3S7S3dS3dA2M0S6S3dS3dS2bS73ZcS2dA2A4S8G0A1A3").
Definition kept_p : list (sv * sv) := Eval vm_compute in (firstn 13 tvL ++ skipn 14 tvL).
Definition tv_p : list (sv * sv) := kept_p ++ passed_p.

Definition LAr : bitem := ltac2:(tb__ "0|1|
S3aZ1Z0S3S7S56S37A2M0S6S56S37S59S38S76A1A4S3G0S6S56S37S91S59A1S38S6bA1A4S3G0S6S56S37N48S38S6aA1A4S8G0A1A3A3A3S59A4").
Definition bdrest_p : list bitem := Eval vm_compute in (firstn 26 bd_rest ++ skipn 28 bd_rest).
Definition brest_p : list bitem := ltac2:(tb__ "0|0|
S3S36S1fS3S36S87S86A1S2aA3A3").
Definition hand_p : list bitem := Eval vm_compute in bd_subst s_p (nd_bd (ndh h0 true HP.nd0)).
Definition bd_p : list bitem := Eval vm_compute in (firstn 2 (skipn 26 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_p).
Definition Xk_p : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_pi)) (ax_X E_p).

Definition payX_p : list bitem := [LA A1].
Definition payY_p : list bitem := ltac2:(tb__ "0|0|
S3S36S1fS3S36S84S36U2S21S5bZ0A1A4S8S36A1A3A3").
Definition payC_p : list bitem := Eval vm_compute in (firstn 2 (skipn 26 bd_rest) ++ LAK AK1 :: bdrest_p).

Lemma ap_checks : ltac2:(tb__ "0|a|
S1S0ScSfA1S50S89S35A2S9SfS13A2A3S1S0ScSeS41A1M0A1S7aS13S48S12A3S9G0S14A2A3S1S0S4S79S13S48S12S14S83S7S7SfS5dA2M1S44S44OF_;F_;M2A2M3SfG3SbSfS5dSbG1G2R1A3A3Ld;S20A4A5S2A3S1S0S4S8fS74S12A2S2A3S1S0S4S8bS12S72A2S2A3S1S0S4S7cS12S30S61S70S57S2S4cA3M4A1A3S2A3S1S0S4S63S5fS12S60G4A1A2S5eS65S2A2M5A2S2A3S1S0S4S81S7S7eG2A2M6G6S7fS48S72S12S43S10S13A1M7A1M8SbS7eG2R1A3A5Ld;S20A3S2A3S1S0S4S6fS5aS1cA2S2A3S1S0S4S6fS1cS5aA2S2A3S1S0S4S6eS88S59A1S1aA2S2A3S1S0S4S80S19S11S13A1A2S2A3S1S0S4S6eS1aS5S36S1bS23A3A2S2A3S1S0S4S6eS5S36S1bS24A3S5S36S21S15A3A2S2A3S1S0S4S3cS1bA1S2A3S1S0S4S8dS42G7A1S3fZ0M9A1G9S23S24A5S2A3S1S0S4S64G8S5cS1cS58S1aG5A4A2S2A3S1S0S4S3bG8S15A2S2A3S1S0S4S90S74G8A2S2A3S0S55G8S67A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_p_ok0 : axst := Eval vm_compute in T_afterA3 HP.Pre_hp E_p s_p R_p HP.P_ok Xk_p.
Definition T_p_f0 : axst := Eval vm_compute in T_afterA3 HP.Pre_hp E_p s_p R_p HP.P_fail Xk_p.
Definition isub_ok_p : wsub := Eval vm_compute in import_subA s_p HP.Pre_hp HP.P_ok E_p.
Definition isub_f_p : wsub := Eval vm_compute in import_subA s_p HP.Pre_hp HP.P_fail E_p.
Definition tv_p_ok : list (sv * sv) := Eval vm_compute in (kept_p ++ import_tv isub_ok_p (nd_tv HP.nd_ok)).
Definition bd_p_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_p (nd_bd HP.nd_ok) ++ brest_p).
Definition tv_p_f : list (sv * sv) := Eval vm_compute in (kept_p ++ import_tv isub_f_p (nd_tv HP.nd_fail)).
Definition bd_p_f : list bitem := Eval vm_compute in (bd_subst isub_f_p (nd_bd HP.nd_fail) ++ brest_p).
Definition nd_p_ok : ndesc := ltac2:(tb__ "0|0|
S5cS34S58S29S5eS65S2A2A4").
Definition nd_p_f : ndesc := ltac2:(tb__ "0|0|
S5cS33S58S28S5eS65S2A2A4").
Definition xfb_p (T : axst) : list axform := ltac2:(tb__ "0|2|
S3S4fS51U0M0Z120A2S3S4fS53S3SaG0S3SaU3S3SaU1S3SaU2S85U4M1S82SdS41S47S10VT;A1A1A2G1A2A2A3A3A3A3A1S3S4fS52G0A1S8S4fA1A3A3A3").
Definition B_p_ok : axst := Eval vm_compute in optL (apply_axforms T_p_ok0 (xfb_p T_p_ok0)).
Definition B_p_f : axst := Eval vm_compute in optL (apply_axforms T_p_f0 (xfb_p T_p_f0)).
Definition T_p_ok : axst := Eval vm_compute in ax_tidy B_p_ok.
Definition T_p_f : axst := Eval vm_compute in ax_tidy B_p_f.

Definition qCURp : sv := Eval vm_compute in sv_subst isub_ok_p HP.qCUR.
Definition gPI' : sv := ltac2:(tb__ "0|0|
S3eS6cS66S3eS6dS31S68A3A3").

Definition rate_gp : sprop := ltac2:(tb__ "0|0|
S45S2cS3eS6cS69S3fZ1A1A3A2").
Definition T_p_okR : axst := Eval vm_compute in ax_add_facts [rate_gp] T_p_ok.
Lemma ap_checks_nd : ltac2:(tb__ "0|8|
S1S0S5dS5cS5S7S3dS3dA2M0S22S7bS78S12S48S4aS13A4M1S61S70S57S2S4eA3M2A1A2A3S58S5S36S39G1S62G2A1A2S15A3S5fG1S60G2A1A2A4S2fA3S1S0S5dS5cS5G0S22S7bS78S12S48S49S13A4M3S61S70S57S2S4dA3M4A1A2A3S58S5S36S39G3S62G4A1A2S15A3S5fG3S60G4A1A2A4S2eA3S1S0SfS7dS48S13S12S14S4aS19A6S18A3S1S0SfS7dS48S13S12S14S49S19A6S16A3S1S0ScSfA1M5S50S18S25S18A1A2S9SfS1eA2A3S1S0G5S50S16S25S16A1A2S9SfS1dA2A3S1S0SfS77S1eA1S17A3S1S0SfS77S1dA1S26A3S1S0SfS8cS17S5S40S3S40S32S8S40A1A3M6S42S10S17A1M7A1A3A2S27A3S0S4S81S40S46S43G7A1A1G6A3S2A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_ap.

(* [comment removed for export] *)
Module Lib_load_obj_aus.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nat"; "pair"; "prod"; "cons"; "Some"; "option"; "nil"; "length"; "list"; "andb"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "la_state"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "SPUle"; "sprop_below"; "ss_objs"; "sv_eqb"; "SAlu"; "SPUlt"; "ob_base"; "ob_hi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_aus"; "s_u0"; "E_u1"; "E_u2"; "R_u1"; "R_u2"; "T_u10"; "T_u20"; "s_u1"; "s_u2"; "B_u1"; "B_u2"; "E_u20"; "T_u1"; "T_u2"; "xfb_leaf"; "cutsU"; "exitsU"; "is_winpiece"; "win_idx"; "xf_u1"; "xf_u2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "bdA"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "AHead"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "P_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find"; "Pre_mf"; "P_mf"; "Posts_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_mf"; "E_mf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "frL"; "tvL"; "A1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "filter"; "find"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "X_latch"; "pE"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "bud_le2"; "ejcertAF"; "wsub_id_on"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr MatFindAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Definition is_winpiece (hi : Z) (o : sobj) : bool := ltac2:(tb__ "0|0|
SdS20S23Vo;A1S21S74S19PaA1S18N200A1A3A2S20S24Vo;A1S18Vhi;A1A2A2").
Definition win_idx (hi : Z) (T : axst) : nat := ltac2:(tb__ "0|3|
S9S6S4S16A2M0A1S4Lx;S5fG0G0S36Vhi;SfS4S16R1A3A2Lp;S5dS4S16S62U0M1SbS16S1fS11VT;A1A1M2A2A2G2A4A3G0G0S4Lp;R1S4S16R2Ls;Li;X6x1Lp;G1X9x2").
Definition xfb_leaf (hi : Z) (T : axst) : list axform := ltac2:(tb__ "0|2|
SbS16S1fS11VT;A1A1A2S4S37Vhi;VT;A2S4S7S51S53S7S4R1S7S4U0M0S5eS4S4SeS7aR1R2A2A1Li;S62U1M1S73R2G1A2A2A3A3A3A1S7S51S52G0A1SaS51A1A3A3Tw;Tn;").

Definition xf_u1 : list axform := [AXSplit 7 (SLit (-32))].
Definition E_u1 : axst := Eval vm_compute in optL (apply_axforms E_mf xf_u1).
Definition s_u1 : wsub := ltac2:(tb__ "0|0|
S5aPaS11S26A1S11S4dA1A3").
Definition R_u1 : list sobj := Eval vm_compute in optR (entails_frA E_u1 Pre_mf s_u1).

Definition T_u10 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_u1)) (import_postA s_u1 Pre_mf P_mf E_u1 R_u1).
Definition B_u1 : axst := Eval vm_compute in optL (apply_axforms T_u10 (xfb_leaf (-32) T_u10)).
Definition T_u1 : axst := Eval vm_compute in ax_tidy B_u1.

Lemma aus_checks1 : ltac2:(tb__ "0|5|
S1S0S9S10A1M0S50S54S38A2S8S10S26A2A3S1S0S9ScS16A1M1A1S6dS26S4dS2cA3S8G1S28A2A3S1S0S3S6cS26S4dS2cS28S61S13S10S12S4fA4A5S2A3S1S0S3S60S3aS1cS11S26A1M2A1M3A2S2A3S1S0S3S45G3S3eA2S2A3S1S0S3S5cS17S1eG3A1S1bG2A1M4A3S2A3S1S0S10S6bG4S6eS2cS4dS4eS26S28A5A2S2aA3S1S0G0S50S2aS33N20S2aA2A2S8S10S2eA2A3S1S0S10S68S2eA1S31A3S0S3S6fG3S56A2S2A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_u20 : axst := Eval vm_compute in leafL_at (c_da :: cps_arm) T_u1 c_da 0.
Definition xf_u2 : list axform := [AXSplit 0 (SLit (-96))].
Definition E_u2 : axst := Eval vm_compute in optL (apply_axforms E_u20 xf_u2).
Definition s_u2 : wsub := ltac2:(tb__ "0|0|
S5aPaS11S27A1S11S4aA1A3").
Definition R_u2 : list sobj := Eval vm_compute in optR (entails_frA E_u2 Pre_da s_u2).
Definition T_u20 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_u2)) (import_postA s_u2 Pre_da P_da E_u2 R_u2).
Definition B_u2 : axst := Eval vm_compute in optL (apply_axforms T_u20 (xfb_leaf (-96) T_u20)).
Definition T_u2 : axst := Eval vm_compute in ax_tidy B_u2.

Lemma aus_checks2 : ltac2:(tb__ "0|5|
S1S0S9S10A1M0S50S30S39A2S8S10S27A2A3S1S0S9ScS16A1M1A1S6dS27S4aS2dA3S8G1S29A2A3S1S0S3S6cS27S4aS2dS29S61S13S10S12S4cA4A5S2A3S1S0S3S60S3aS1cS11S27A1M2A1M3A2S2A3S1S0S3S45G3S3eA2S2A3S1S0S3S5cS17S1eG3A1S1bG2A1M4A3S2A3S1S0S10S6bG4S6eS2dS4aS4bS27S29A5A2S2bA3S1S0G0S50S2bS33N60S2bA2A2S8S10S2fA2A3S1S0S10S68S2fA1S32A3S1S0S3S6fG3S56A2S2A3S1S0S3S5bS17S1aS22S67S63A2A1G4A3S2A3S1S0S3S5bS17S1aS1dS63S3bA2A1G4A3S2A3S0S3S5bS17S1aS1dS3bS18Z4000000A1A2A1G4A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_u0 : wsub := ltac2:(tb__ "0|0|
S7S6S3dS15A2S5S3dS15P1e3S65A4S5aS3aS11S55A1S11S54A1A3A3").
Lemma aus_checks0 : ltac2:(tb__ "0|6|
S1S0S3S14S55S54S25A3S2A3S1S0S3S6aS25S3aA2S2A3S1S0S3S60S3aS1cS11S55A1M0A1M1A2S2A3S1S0S3S45G1S3eA2S2A3S1S0S3S78S25S58S58A3S2A3S1S0S3S49S25S57S57A3S2A3S1S0S3S70S1bG0A1S79S25S42S59A1M2A2G2A3S2A3S1S0S3S47S48S25S46S66S2A2M3A2G3A2S2A3S1S0S3S72S56S25A2S2A3S1S0S15S69S25P1ccM4A2S19G4A1A3S0S15S69S25P1d3M5A2S19G5A1A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsU : list efnode := ltac2:(tb__ "0|5|
S7S6S6S6S10S44A2M0S4A2M1S6S3cS15A2M2A2M3S5G1G2S5G0S4S5S10S44S31S3eA4U1M4A4S5S3cS15S3fS40ZaS41A2A4A4S7G3S5G1G2S5G0S4S5S10S44S32S3eA4G4A4S5S3cS15S3fS40Z5S41A2A4A4SaG3A1A3A3").
Definition exitsU : list efnode := ltac2:(tb__ "0|5|
S7S6S6S6S10S44A2M0S4A2M1S6S3cS15A2M2A2M3S5G1G2S5G0S4S5S10S44S30S3eA4U1M4A4S5S3cS15S3fS40Z7S41A2A4A4S7G3S5G1G2S5G0S4S5S10S44S64S43A4G4A4S5S3cS15S3fS40Z1S41A2A4A4SaG3A1A3A3").
Lemma ecertU_ok : ltac2:(tb__ "0|0|
S0S3S71S75S3aS76Uc8S77S3aS34S35A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_aus.

