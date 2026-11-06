(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_035.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc Lib_load_obj_ago.

(* [comment removed for export] *)
Module Lib_load_obj_pro_chkn.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "Some"; "option"; "cons"; "prod"; "app"; "list"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "En_sf0"; "En_sf"; "En_sfD"; "s_pe"; "s_sfn"; "nd_rz"; "En_sfB"; "Fx"; "Rn_sf"; "nx"; "P_errN"; "Pre_sf"; "En_sfC"; "L_sf"; "Tn_sf0"; "nd_rn"; "zmid"; "Tn_sf"; "bd_pro"; "xf_nm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "DZero"; "SLit"; "cell"; "dflt_writable"; "ob_cells"; "ob_dflt"; "obj_wf"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "fr_lo"; "fpiece"; "g5"; "objs_butlast"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LI"; "nd_lo_err"; "P_err"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkn.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk"; "frameFb"; "lastO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bd_wpos"; "bud_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "flag_carve_stateA"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_FL"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module K2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2. End K2. Module HK. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit. End HK.

Lemma pro_chk_nsf : ltac2:(tb__ "0|c|
S1S0S27SfS12A1S2aS5aA1M0A3S1S0SaS26A1M1S28SdS12A1A1S9S26S35S12A1M2S7S26S58S34Z20Z40S2dS4aS12A1M3A1S2eG3A1M4A5S4S26A1A3A3A3S1S0S2S2cG4A1S3A3S1S0S2S49S12A1S3A3S1S0S2S3bS1bS12A1S21A2S3A3S1S0S2S44S19S12A1S4S8S27S27A2A1M5S32S3aG2A5S3A3S1S0ScS57S12G2P6eS4S8S43S43A2A1A4S18A3S1S0S6S26A1S5cS26S28SdS18A1M6A1U5M7A3S5S26S33Z1f0Z200S4S2bA1S29A4A2A3S1S0S2S2fS1bS18A1S22A2S3A3S1S0ScS10S18S4dG6G7S22A3A2S1eA3S1S0S6ScA1S4fS1eS25A2S5ScS14A2A3S1S0S27SfS14A1G0A3S1S0S2S30SdS56S14P78A2M8A1A1S3A3S1S0ScG8S13A3S1S0S2S44S19S14A1M9G5S32S3aS28SdS14A1A1A5S3A3S1S0S2S54G9G5SeS14A1A3S3A3S1S0S6G1A1S4cS13S1dS16A3S5G1S1aA2A3S1S0S2S4bS13S1dS16S1aS7ScS1fS4ScA1A3A5S3A3S1S0S2S55S31S16A2S3A3S1S0S2S47S31S1bS13A1MaA2S3A3S1S0S2S3bGaS21A2S3A3S1S0S2S51S24A1S3A3S1S0S2S59S19S13A1G5S32S5SbU0A2S3aS1aA6S3A3S1S0S27S45S16PcA2S36A3S1S0S27S45S16S5bA2S37A3S1S0ScS53S1dS13S16S1aS1fSeS13A1A6S20A3S1S0ScS48S20A1S23A3S1S0S2S11S1cS39S15A3S3A3S1S0S2S46S15S31A2S3A3S1S0S2S47S31S1bS1cA1MbA2S3A3S1S0S2S3bGbS17A2S3A3S1S0S2S4eS15S3fS17A1S3fS38A1A3S3A3S1S0S2S42S15S3eS17A1S3eS38A1A3S3A3S1S0S2S52S19S1cA1S50S15S3dS38A1A2S3dS17A1A3S3A3S0S2S40S41S15S3cS38A1A2S3cS17A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_pro_chkn.

(* [comment removed for export] *)
Module Lib_load_obj_pro_chkv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "Some"; "option"; "cons"; "nil"; "S"; "false"; "list"; "nat"; "orb"; "prod"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "BAD"; "Pre_ms"; "L_ms"; "NP"; "fr_lo"; "bslot"; "vF"; "z24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv_eqb"; "sobj"; "sv"; "SLit"; "sprop"; "sprop_eqb"; "sstate"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "obj_wf"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXRebase"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "Fx"; "nx"; "bd_pro"; "bk_xf3"; "bk_xf4"; "bk_xf5"; "cv_i"; "cv_xf"; "nd_r2"; "vl"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "vs_E"; "vs_R"; "vs_T"; "vs_b"; "vs_off"; "vs_s"; "vsn"; "vstep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk"; "fUle"; "wr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkv.K2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkv"; "VB1"; "VB2"; "VB3"; "VB4"; "VB5"; "VC1"; "VT0"; "pc_chk"; "rng_chk"; "spLo"; "vstep_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module K2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2. End K2. Module HK. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit. End HK.

Definition VC1 : list axst := Eval vm_compute in map (fun j => cv_1 (vl j) (vs_b (vsn j)) (vs_off (vsn j)) 24) (seq 0 34).
Definition VT0 : list axst := Eval vm_compute in map (fun j => T_afterA Pre_ms (vs_E (vsn j)) (vs_s (vsn j)) (vs_R (vsn j)) L_ms) (seq 0 34).
Definition VB1 : list axst := Eval vm_compute in map bk_1 VT0.
Definition VB2 : list axst := Eval vm_compute in map bk_2 VB1.
Definition VB3 : list axst := Eval vm_compute in map (fun j => bk_3 (nth j VB2 BAD) (vs_b (vsn j)) (vs_off (vsn j))) (seq 0 34).
Definition VB4 : list axst := Eval vm_compute in map (fun j => bk_4 (nth j VB3 BAD) (vs_b (vsn j)) (vs_off (vsn j))) (seq 0 34).
Definition VB5 : list axst := Eval vm_compute in map bk_5 VB4.

Definition spLo : sprop := SPUle (SLit 140735332483072) (SVar 10).
Definition rng_chk (A : axst) (b : sv) (off : Z) : bool := ltac2:(tb__ "0|2|
S11S8S8S8S1cVb;S1aA2S39S20S21S48A1S2fVA;A1M0A3A2S2dZ0M1Voff;A2A2S2dVoff;Z800A2A2S8S8S8S1cVb;S23PaA1A2S39S20S21S56A1G0A3A2S2dN1000Voff;A2A2S2dVoff;G1A2A2A2").
Definition pc_chk (A : axst) (i : nat) (b : sv) (off n : Z) : bool := ltac2:(tb__ "0|0|
SaS1dA1S6Lx;S3aS1dS28S1VA;A1A1Vi;A3S1dS8S8S1cS24R1A1Vb;A2S1cS26R1A1S1fVoff;A1A2A2S1cS25R1A1S1fS2eVoff;Vn;A2A1A2A2Lo;SeXax2").

Definition vstep_ok (j : nat) : Prop := ltac2:(tb__ "0|b|
S46Vj;A1S47S38Vj;A1S0S43R2A1S1eS44R3A1S3cS40R4A1S0S45R5A1S58S41R6A1SfS1dA1M0S13S0Vj;S52S14A4S0S13S0Vj;S53S14A4S0S13S0Vj;S4dS14A4S0S13S0Vj;S4eS14A4S0S13S0Vj;S4fS14A4S0S13S0Vj;S50S14A4S0S13S0Vj;S51S14A4S0S5S4SaS0A1M1S2aRdS36RdRcRbZ18M2A4A2S9S0R7A2A3S5S4S6S49R7SdS35RdRcRbA3A1M3A2S7A3S5S4S6S27S30R7A1S19RcRbG2A3M4A2S7A3S5S4S6S54R7G3RcRbG2A5S7A3S5S4S6S55R7RcRbA3S7A3S5S4S0S2R7S5bS1R7A1G3G4A3A2RaA3S5S4SaG0A1S5aRaS15R9A3S9G0R8A2A3S5S4S6S59RaS15R9R8SbS0S16ScS0A1A3A5S7A3S5S4S6S60S17R9A2S7A3S5S4S6S61S17S30RaA1M5A2S7A3S5S4S6S5eG5S37A2S7A3S5S4S6S5cG5S31A2S7A3S5S4S6S4aS2fRaA1M6SbS12S1eS1eA2M7S3fScG7A1A3M8S18S3dR8A5S7A3S5S4S6S4cG6G8S18S4bS3RaA1A5S7A3S5S4S0S5fS15RaR9R8S16A5R6A3S5S4SaS22A1S5dS1R6A1U1M9S1bA3S9S22S1R5A1MaA2A3S5S4S6S29GaA1S7A3S5S4S0S2R6GaA2R5A3S5S4G1S2aR5SbS2bS2cG9A1ScS2bA1A3A2S9S0R4A2A3S5S4G1S2aR4S32R4RcRbA3A2S9S0R3A2A3S5S4G1S2aR3S33R3RcRbA3A2S9S0R2A2A3S5S4G1S2aR2S34R2A1A2S9S0R1A2A3S4S0S3eR1A1S42ReA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TB5;TB4;TB3;TB2;TB1;TT0;TC1;TR;Ts;TE;Toff;Tb;TL;Tv;").
Lemma vq_0 : vstep_ok 0. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_1 : vstep_ok 1. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_2 : vstep_ok 2. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_3 : vstep_ok 3. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_4 : vstep_ok 4. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_5 : vstep_ok 5. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_6 : vstep_ok 6. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_7 : vstep_ok 7. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_8 : vstep_ok 8. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_9 : vstep_ok 9. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_10 : vstep_ok 10. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_11 : vstep_ok 11. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_12 : vstep_ok 12. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_13 : vstep_ok 13. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_14 : vstep_ok 14. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_15 : vstep_ok 15. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_16 : vstep_ok 16. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_17 : vstep_ok 17. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_18 : vstep_ok 18. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_19 : vstep_ok 19. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_20 : vstep_ok 20. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_21 : vstep_ok 21. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_22 : vstep_ok 22. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_23 : vstep_ok 23. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_24 : vstep_ok 24. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_25 : vstep_ok 25. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_26 : vstep_ok 26. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_27 : vstep_ok 27. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_28 : vstep_ok 28. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_29 : vstep_ok 29. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_30 : vstep_ok 30. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_31 : vstep_ok 31. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_32 : vstep_ok 32. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_33 : vstep_ok 33. Proof. unfold vstep_ok. conj_vmc. Qed.
Lemma vq_all : ltac2:(tb__ "0|0|
S10S3bR1U22A2S57R2A1F_;Fj;").
Proof.
  intros j H.
  destruct j as [|j]; [exact vq_0|].
  destruct j as [|j]; [exact vq_1|].
  destruct j as [|j]; [exact vq_2|].
  destruct j as [|j]; [exact vq_3|].
  destruct j as [|j]; [exact vq_4|].
  destruct j as [|j]; [exact vq_5|].
  destruct j as [|j]; [exact vq_6|].
  destruct j as [|j]; [exact vq_7|].
  destruct j as [|j]; [exact vq_8|].
  destruct j as [|j]; [exact vq_9|].
  destruct j as [|j]; [exact vq_10|].
  destruct j as [|j]; [exact vq_11|].
  destruct j as [|j]; [exact vq_12|].
  destruct j as [|j]; [exact vq_13|].
  destruct j as [|j]; [exact vq_14|].
  destruct j as [|j]; [exact vq_15|].
  destruct j as [|j]; [exact vq_16|].
  destruct j as [|j]; [exact vq_17|].
  destruct j as [|j]; [exact vq_18|].
  destruct j as [|j]; [exact vq_19|].
  destruct j as [|j]; [exact vq_20|].
  destruct j as [|j]; [exact vq_21|].
  destruct j as [|j]; [exact vq_22|].
  destruct j as [|j]; [exact vq_23|].
  destruct j as [|j]; [exact vq_24|].
  destruct j as [|j]; [exact vq_25|].
  destruct j as [|j]; [exact vq_26|].
  destruct j as [|j]; [exact vq_27|].
  destruct j as [|j]; [exact vq_28|].
  destruct j as [|j]; [exact vq_29|].
  destruct j as [|j]; [exact vq_30|].
  destruct j as [|j]; [exact vq_31|].
  destruct j as [|j]; [exact vq_32|].
  destruct j as [|j]; [exact vq_33|].
  lia.
Qed.
End Lib_load_obj_pro_chkv.

(* [comment removed for export] *)
Module Lib_load_obj_pro_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "nat"; "bool"; "true"; "nil"; "cons"; "Some"; "option"; "fst"; "S"; "andb"; "snd"; "None"; "app"; "false"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "sprop"; "SLit"; "holds"; "ss_facts"; "SAlu"; "SVar"; "ss_next"; "ss_objs"; "sv_eqb"; "cell"; "dflt_writable"; "ob_base"; "ob_hi"; "ob_lo"; "obj_wf"; "odefault"; "sprop_eqb"; "swf"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "ANone"; "frinA"; "TPA"; "tvinA"; "PTrue"; "nd_below"; "JA"; "amode"; "fbinA"; "ffinA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "fr_lo"; "NP"; "Pre_ms"; "W2"; "L_ms"; "g5"; "vF"; "L_00"; "L_f8"; "L_sm"; "Pre_00"; "Pre_f8"; "Pre_ma"; "Pre_sm"; "objs_butlast"; "E_f8a0"; "E_ma0"; "E_mo0"; "E_mz0"; "E_sm0"; "Pre_lo"; "T_f8a2"; "T_mo1"; "X_lo"; "bslot"; "vFL"; "E_f8a1"; "T_sm1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "PhisZ"; "Fx"; "z0"; "nd_r2"; "nd_r1"; "nx"; "cutsR"; "L_sf"; "Pre_sf"; "cv_i"; "En_sf"; "En_sf0"; "P_errN"; "nd_rn"; "nd_rz"; "XN"; "cv_xf"; "exitsR"; "vl"; "vrank"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "add"; "mul"; "opp"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "J_pure_pre"; "AE_A"; "UStopLe"; "JL_stack_free"; "JL_stack_malloc"; "J_alloc_pre"; "J_memset_pre"; "J_stack_free_pre"; "J_stack_malloc_pre"; "Posts_malloc"; "V_FL"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "bd_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "extraLO"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_pf.Sum.X"; "xrs_chkRo"; "f5_locals"; "xr_loc";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk"; "extraXlo"; "frameFb"; "fUle"; "pure_shape"; "wr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub"; "rho_sub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "shadow_reopen_stateA"; "shobj"; "local_ok"; "shadow_release_stateA"; "wclear"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "E_s00_0"; "L_mc48"; "Pre_mc48"; "E_mb0"; "E_mc0"; "T_ma_null"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkn.K2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LI"; "nd_lo0"; "P_err"; "nd_lo_err"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkn.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LND"; "E_blr0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_okL"; "robjs_okF"; "robjs_okL"; "xr_eqb"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "ccount"; "payA"; "site_okA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_pro_chkn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma uval_addk : ltac2:(tb__ "0|1|
S1bS1aS18S31S86Z0S89Sa5R3R2A2R1A2M0A2S88G0S87Z2Z40A2A2A2S30S18Sa5R4S21Sd7R3S1eR2A1A3A2S89Sa5R4R3A2R2A2A3F_;Fk;Fa;Frho;").
Proof.
  intros rho a k H. unfold uval in *. rewrite U_add, U_lit. unfold M64v. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.
Lemma efmeas_z0 : ltac2:(tb__ "0|1|
S13S38S4S18S1bS30S18S7eS3S1S1S13S38A2M0S4A2S1S18S1aA2S3G0S4S3S13S38R5R4A4R3A4S3S18S1aR2S6cA4A4R1A2S8aR2S87Z2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA, ef_rank, ef_var, z0. cbn [fst snd]. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4aS1bS2S2fQ40A1A1Sa3OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa2S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S18SdcVCST;R1A2S31S86Z0R2A2S88R2SdbA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S18SdcVXGL;R1A2S31S86Z0R2A2S88R2SdbA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S18SefR1A1SdcVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1S18S18A2S18A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1bOFr;") := ltac2:(tb__ "0|0|
SacVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S40VAInv;VCST;VXGL;S4eVKc;Vrho0;VP0;VFB;VFF;VBX;S3eVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S82VAInv;VCST;VXGL;S4eVKc;Vrho0;VP0;VFB;VFF;VBX;S3eVPhi;Vnd;Ad").

Lemma lo_robjsF : ltac2:(tb__ "0|0|
S4aS1bS2S1dA1S2S1S1aS1aA2A1S2S1S1S1aS18A2S1aA2A1S2S1cA1S1bS2S2fQ40A1A1Sa3VAInv;R9R3R2R1A4Sa9S1dS1fR9A1R8A3VP0;Vrho0;A1SadS4eVrho0;RbA3S3cVrho0;RdA2SbfRdS4cS4bReA1A1A2S3dVFB;RfReRcA4Sc0RfRdA2Sc1R10ReA2S3bVFF;R12R11ReA4S30S5Sd1R11R10RfSabReA5S6A3Se1VCST;Vrho0;VFB;VFF;R13R11R10RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (K2.robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv fr extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (K2.extraLO_pclMA CST rho0 FB FF rho tv fr o a Hav HP0 HE Hr).
Qed.
Lemma lo_robjsR : ltac2:(tb__ "0|0|
S4aS1bS2S1dA1S2S1S1aS1aA2A1S2S1S1S1aS18A2S1aA2A1S2S1cA1S1bS2S2fQ40A1A1Sa3VAInv;R9R3R2R1A4Sa9S1dS1fR9A1R8A3VP0;Vrho0;A1SadS4eVrho0;RbA3S3cVrho0;RdA2SbfRdS4cS4bReA1A1A2S3dVFB;RfReRcA4Sc0RfRdA2Sc1R10ReA2S3bVFF;R12R11ReA4S30S5Sd8R11R10RfSabReA5S6A3Sf8VCST;Vrho0;VFB;VFF;R13R11R10RfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (HK.robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv fr extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (K2.extraLO_pclMA CST rho0 FB FF rho tv fr o a Hav HP0 HE Hr).
Qed.
Lemma lo_xrsF : ltac2:(tb__ "0|1|
S4aS1bS2S1dA1S2S1S1aS1aA2A1M0S2S1S1S1aS18A2S1aA2A1G0S1bS2S2fQ40A1A1Sa3VAInv;R9R3R2R1A4Sa9S1dS1fR9A1R8A3VP0;Vrho0;A1SadS4eVrho0;RbA3S3cVrho0;RdA2SbfRdS4cS4bReA1A1A2S3dVFB;RfReRcA4Sc0RfRdA2Sc1R10ReA2S3bVFF;R12R11ReA4S30S5Sd3R11R10RfSd2ReA5S6A3Se5VCST;VXGL;Vrho0;VFB;VFF;R13R11R10RfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv fr X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (K2.xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv fr K2.xextraLO X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (K2.xextraLO_pclMA CST rho0 FB FF rho tv fr r a Hav HP0 HE Ha).
Qed.

Lemma site_rt : ltac2:(tb__ "0|0|
S13SbcS2S1cA1S1bS2S1S1aS1aA2A1S2S1S1S1aS18A2S1aA2A1S2Sa6A1S41S4aSb0OF_;F_;S30S5Sd1S20S14R9A1A1R5R4SabR7A5S6A3S30S5Sd3S20S14RaA1A1R6R5Sd2S15RaA1A5S6A3S4aSb0Sa9S1dS1fRaA1S20S14RdA1A1A3VP0;Vrho0;A1SadS4eVrho0;RcA3S3bVFF;R5RdRbA4R9R6R5A2F_;F_;F_;F_;Fms;FAi;SeaVAInv;VCST;VXGL;S4eVrho0;VP0;VFB;VFF;RcRbRaR9S39R8R7R6R5A4SfS18A1R4AfF_;F_;F_;Fextra;Fam;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv fr bd am extra CR CX HEX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (lo_robjsF Ai rho _ tv fr R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR) as HRF.
  pose proof (lo_xrsF Ai rho _ tv fr (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  split; [|split; [|exact (HEX Ai ms HF HP0 Hav HFR)]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.
Lemma payA_same : ltac2:(tb__ "0|1|
S2S1dA1S2Sa6A1S30S5Sa7R1A1S6A3Se9S4eVrho0;VP0;R3S1eZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Definition census5 (FFc : list (Z * Z * Z)) : Prop := ltac2:(tb__ "0|1|
S30S4Se8Z5SaaS1S1S18S18A2M0S18A2G0SbG0S18A2VFFc;A4A2U0A3").
Hypothesis HFF5 : census5 FF.
Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S18S2S2fQ40A1A1S90F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S35S13S1bS2S2fQ40A1A1S90Sa9S1dS1fR3A1S20S14R4A1A1A3VTR;S34S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S90S90S90S93R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S90OS90S93R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S35S35S13S13SbcS2S1cA1M0S2S1S13S45A2M1A1S2S1S1aS1aA2M2A1S90S1bS2S2fQ40A1A1M3G2S8cG2R1R5A3S8cG2R2S15RbA1A3F_;Fr;S30SaG0A1S48RaR9R8A3S9G0R7A2A3S30S5S47RbRaR9R8SaaG1S13SbS13S45A2R7A4A5S6A3S1bG3VTR;S34S0RfRdR2R1A5S46S0S23S14RdA1A1R2R1RaA5A2Ftp1;Frho1;S2Sa4A1M4Sb0Sa3S36S0R9R8R10S3G4Sb4R3Sb5R2R1A2A4A5R13RaR9R4R2A4R13SbdSbbRbRfSafR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S13S45G4Sb0Sa3S1bG3G4Sb0Sa3S8cG1S3S13S45RaR9A4R14A3S36S0R12R11R19S3G4Sb4R9Sb5R8R7A2A4A5R1cR13R12RaR8A4SadS23S14R1aA1A1SbdSbbR14R18SafR9R13RaA3A3R19A2R8A3S36S0R9R8ReS3G4Sb4R7Sb5R6R5A2A4A5ReSbdSbbR16R1aSafRbR15RcA3A3R1bA2R15RaR9R8R6A6S31Sf6R17SafRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1bSaeR18SafRdR17ReA3R1cR1dS14R1eA1S14R1fA1S14R11A1R1RcA9VTR;S34S0S49R11SbdSbbR19R1dSafReR18RfA3A3R1eA2R18RdRcA5Sf7R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S34S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S1bOF_;S38S13S1bS2S2fQ40A1A1S90R6R3A1VTR;S34S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S34S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CSM : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1VTR;S34S0S9dVAInv;Z5M0R3VKc;A4S5aR2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S56S99VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1VTR;S34S0S95VAInv;R3VKc;A3S58R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S55S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CUTR : ltac2:(tb__ "0|5|
S13S38S4S1S18S1aA2M0S1bS2S2fQ40A1A1M1S18G1S8cS1S1S1S13S38A2M2S4A2M3G0A2S3G3G0S3G2S4S3S13S38R8R7A4R6A4R5A4S70A3S7fS6aR7R5A3S31S86Z0S7eS3G3G0S3G2S4S3S13S38RaR9A4R8A4R7A4R6A2M4A2S88G4R4A2A2VTR;S34S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Ltac meas_z0 := rewrite !efmeas_z0; vm_compute; split; [discriminate | reflexivity].
Tactic Notation "cutR" integer(n) := cbn [cutsR app In]; do n right; left; reflexivity.
Lemma c5_ok : 0 <= 5 <= 6. Proof using . lia. Qed.
Lemma xrs_incl_of : ltac2:(tb__ "0|2|
S2S1S1aS1aA2M0A1M1G1S30S5Se4R2R1A2S6A3G0S8cG0R1R4A3S8cG0R2R4A3F_;Fr;F_;FY;FX;").
Proof using . intros X Y H. exact (xrs_inclb_sound _ _ H). Qed.

Lemma lo_xrsL : ltac2:(tb__ "0|4|
S4aS1bS2S1dA1S2S1S1aS1aA2A1M0S2S1S1S1aS18A2S1aA2M1A1M2SaS4A1M3S2S1cA1G0S1bS2S2fQ40A1A1Sa3VAInv;RbR3R2R1A4Sa9S1dS1fRbA1RaA3VP0;Vrho0;A1SadS4eVrho0;RdA3S3cVrho0;RfA2SbfRfS4cS4bR10A1A1A2S3dVFB;R11R10ReA4Sc0R11RfA2Sc1R12R10A2S3bVFF;R14R13R10A4S30S5Sc3VXGL;R13R12R11R10RfSb6ReA8S6A3Se0VCST;VXGL;Vrho0;VFB;VFF;R15R13G3G2Lskip;R11S4Sc2G1R1R13A3Li;R12Xax2RfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR Hchk.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXlo X rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hchk).
  intros r a Hr HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
  - left. exact (K2.xextraLO_pclMA CST rho0 FB FF rho tv _ r a Hav HP0 HE Ha).
  - right. apply HXlits. exact (K2.xr_inlits_sound r rho a HE Ha).
Qed.
Lemma CXL_sm : ltac2:(tb__ "0|0|
S30S5Sc3VXGL;S6bS68A1S7S1S1aS1aA2A1S4dS9S4U0A2S7S1cA1Sb6S64A8S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_E_sm0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2Sd4A2S60R3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S60Sd4A4G1A4S3S18S1aZbb7S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_sm as (_ & Cent & Cchk & Cta & Cnp & Cnb & Cwp & CvR & CpR & CvF & CpF & CR & CXr & C12 & CT & Csel & Cbase & Cobjs & CX & Cswf & Cnp1 & Cnb1 & Copen & CCpro & Cal & CpFn).
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 E_sm0 s_sm R_sm rho tp LI.nd_lo0 110 120 _ CSM).
  - lia.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cwp.
  - exact CvR.
  - exact CpR.
  - exact CvF.
  - exact CpF.
  - intros A A' _; exact I.
  - apply (site_rt E_sm0 s_sm R_sm rho [] [] LI.bd_lo0 ANone _ CR CXr).
    intros Ai ms HF HP0 Hav HFR. split.
    + rewrite C12. rewrite uval_lit by lia. change (fs_frame_size 5) with 2048. lia.
    + pose proof HFF5 as H5. unfold census5 in H5. unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite H5. cbn. lia.
  - intros rho' tp'. change (T_afterA (Pre_stack_malloc AE_A 5) E_sm0 s_sm R_sm (L_stack_malloc AE_A 5)) with (T_afterA Pre_sm E_sm0 s_sm R_sm L_sm). rewrite CT.
    cbn [nd_tv nd_fr nd_bd nd_am LI.nd_lo0].
    eapply TR_pre with (P := SPA segs (JAv nd_r1) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect (sel_last T_sm 3)] rho' T_sm T_sm1 tp' w Csel Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_r1) C_pro rho2 tp' w)).
    { intros w Hw. unfold nd_r1.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                  [] fr_lo LI.bd_lo0 ANone 0%nat 110 5 120 T_sm1 (objs_butlast T_sm1) X_lo [] rho' tp' w eq_refl ltac:(lia) Cbase Cobjs CX
                  Cswf Cnp1 Cnb1) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (lo_xrsL Ai rho' _ [] fr_lo (Some 0%nat) [] X_lo rho1 tp1 md1 HM HF2 HP0 Hav HT HTK HN HDt HZt HFR CXL_sm).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite Copen in Hw2. rewrite <- CCpro.
        apply (SPA_x_len0 segs (JAv (NDA [] fr_lo LI.bd_lo0 ANone)) C_pro0 110 5 rho2 tp' w); [exact Cal | lia | exact CpFn | exact Hw2]. }
    apply TR_exw. intros rho2. apply (CUTR C_pro nd_r1 0%nat (2990, z0) rho2 tp'); [cutR 1 | exact I | meas_z0].
Qed.

Lemma sh_release : ltac2:(tb__ "0|3|
S13S2S1S1aS1aA2A1S2Sa6A1S18S18S2S26A1S2cS2S1S18S18A2M0A1S1bS2S2fQ40A1A1S2Sa4A1M1Sb0Sa3S30S1aS16RdA1S1eSdaA1A3S30S2S1cA1S24S14ReA1A1S10S1cS5bReA1S8S1cSc5S52RbRaR9R8A5S7S1cA1M2A3A3A3S86Z0RcA2S31S86RdRcA2S86RcZ100A2A2S30S5S27RbA1S6A3S30S5Sb7R12A1S6A3S30S5S8eG0Sc6ReRdR10RfA4RcA3S6A3S30S5S3fS6fR14A1S39R13S4dR12S3aA4A2S6A3S30S5Sd8S6bR15A1R14S4dSabS5bR15A1A5S6A3S34S0VJAv;S39R15S4dR14S3aA4A1R16ReRdS3G1Sb4RcSb5RbRaA2A4A6S34S0VJAv;S39R16S4dR15S3aA4A1Sc7R17S5bR17A1P6eR10A4SbbRfS8S1cSc5S52R14R13R12R11A5G2A3SafRbReRcA3A3ReS3G1Sb4RdSb5RcRbA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FL;Fd;Fcells;Fk2;Fk1;Fbd;Ftv;FA;").
Proof using ALA HCST HXGL HKc HBX LFSH.
  intros A tv bd k1 k2 cells d L rho tp tr ms md Hbase Hobjs Hk1 Hk2 Hdw Hfe HL Hnb CR Hw.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tv fr_lo bd ANone 0%nat 110%positive 5 120%positive g5 k1 k2 cells d A (objs_butlast A) L rho tp tr ms md
           eq_refl c5_ok Hbase Hobjs Hk1 ltac:(change (fs_frame_size 5 / 8) with 256; exact Hk2) Hdw Hfe HL Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (lo_robjsR Ai rho _ tv fr_lo _ rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
Qed.

Definition f5_locals : list (Z * Z) := ltac2:(tb__ "0|1|
S8S1S18S18A2M0S3S18S18Z1d0Z30A4S8G0S3S18S18Z220Z518A4S7G0A1A3A3").
Definition xr_loc (k1 k2 : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|1|
S8dS1S18S18A2M0G0SdSe3Vr;Sc9P6eR1A2A2Sc8Vk1;Vk2;SbS18S18R1A3SeS18S18R1A3A4A2Lol;Sb2A3").
Definition xrs_chkRo (facts : list sprop) (tv : list (sv * sv)) (k1 k2 : Z) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S8eS1S1aS1aA2M0G0S12Sb3Vk1;Vk2;R1A3Sc3VXGL;Vfacts;Vtv;S4dS9S4U0A2S7S1cA1Sb6S8G0R1S7G0A1A3A8A2Lr;VX;A3").
Lemma sh_reopen : ltac2:(tb__ "0|2|
S13S2S1S1aS1aA2M0A1M1S2Sa6A1G1S18S18S1bS2S2fQ40A1A1S93S30S1aS16R9A1S1eSdaA1A3S86Z0R6A2S31S86R7R6A2S86R6Z100A2A2S30S5Sb7RcA1S6A3G0S8cG0R1RbA3S8cG0R2S15RfA1A3F_;Fr;S30S5S2eS14Sc4ReRbS52RaR9A5A1A1S6A3S30S5Sd8S6bRfA1ReS4dSabS24S14RfA1A1A5S6A3S30S5Sb1S6bR10A1RfRcRbRdA5S6A3S34S0VJAv;S39R10S4dRfS3aA4A1R11RbRaR9A6S34S0VJAv;S39R11S4dR10S3aA4A1Sc4R12RfS52ReRdA5RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fk2;Fk1;FX';Fbd;Ftv;FA;").
Proof using ALA HCST HXGL HKc HBX LFSH HXlits.
  intros A tv bd X' k1 k2 rho tp w Hbase Hk1 Hk2 Hfe Hincl Hwf CR CXL Hw.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tv fr_lo bd ANone 0%nat 110%positive 5 120%positive g5 k1 k2 A X' rho tp w eq_refl c5_ok Hbase Hk1
           ltac:(change (fs_frame_size 5 / 8) with 256; exact Hk2) Hfe Hincl Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (lo_robjsR Ai rho _ tv fr_lo _ rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR).
  - intros r y Hr Hy. unfold xrs_chkRo in CXL. pose proof (proj1 (forallb_forall _ _) CXL r Hr) as Hc. cbv beta in Hc. apply orb_prop in Hc as [Hc|Hc].
    + right. unfold xr_loc in Hc. apply existsb_exists in Hc as ([off len] & Hin & Hc). apply andb_prop in Hc as [He Hwc]. apply xr_eqb_sound in He.
      exists off, len. split; [exact He|]. cbn [fst snd] in Hwc. change (fs_frame_size 5) with 2048.
      cbn [f5_locals In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | split; [lia | split; [lia | exact Hwc]]]).
    + left. exact (lo_xrsL Ai rho _ tv fr_lo (Some 0%nat) [] [r] rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR Hc r y ltac:(left; reflexivity) Hy).
Qed.

Lemma CXL_f8a : ltac2:(tb__ "0|0|
S30S5Sb1S6bS67A1S7S1S1aS1aA2A1Z44Ze7S64A5S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXL_f8b : ltac2:(tb__ "0|0|
S30S5Sb1S6bS62A1S7S1S1aS1aA2A1Ze7Zf8S15S62A1A5S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_E_f8a0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6eA2S5cR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S5cS6eA4G1A4S3S18S1aZbadS6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_f8 as (Cb0 & Co0 & Cf0 & Cn0 & CR0 & CE1 & Cb1 & Cf1 & Ci1 & Cw2 & CE2 & CR1 & Cxf & Cent & Cchk & Cta & Cnp & Cnb & Cbb & Cshape & CR & CX & CT0 & Cxb
                          & CbT & CoT & CdT & CfT & CnT & CRT & CT2 & Cb2 & Cf2 & CwC & CC2 & CR2).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_r1) E_f8a rho1 tp w)).
  { intros [tr [ms md]] Hw. eexists. apply (SPA_axforms segs _ (xf_shcall E_f8a2 68) _ E_f8a2 E_f8a tp _ Cxf). rewrite <- CE2. unfold nd_r1.
    apply (sh_reopen E_f8a1 [] LI.bd_lo0 X_lo 68 231 _ tp _ Cb1 ltac:(lia) ltac:(lia) Cf1 (xrs_incl_of _ _ Ci1) Cw2 CR1 CXL_f8a).
    rewrite <- CE1. exact (sh_release E_f8a0 [] LI.bd_lo0 0 256 _ DZero [] rho tp tr ms md Cb0 Co0 ltac:(lia) ltac:(lia) eq_refl Cf0 eq_refl Cn0 CR0 Hw). }
  apply TR_exw. intros rho1.
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] E_f8a s_f8a R_f8a rho1 tp nd_r1 LI.bd_lo0 _).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply payA_same. reflexivity.
  - exact Cshape.
  - unfold nd_r1. exact (site_rt E_f8a s_f8a R_f8a rho1 [] fr_lo LI.bd_lo0 ANone _ CR CX (fun _ _ _ _ _ _ => I)).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_r1]. rewrite CT0.
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_r1) C_pro2 rho2 tp' w)).
    { intros [tr [ms md]] Hw. eexists. rewrite <- CC2. unfold nd_r1.
      apply (sh_reopen T_f8a2 [] LI.bd_lo0 (ax_X T_f8a2) 231 248 _ tp' _ Cb2 ltac:(lia) ltac:(lia) Cf2 (fun r H => H) CwC CR2 CXL_f8b).
      rewrite <- CT2.
      apply (sh_release T_f8a1 [] LI.bd_lo0 68 231 _ _ [] rho' tp' tr ms md CbT CoT ltac:(lia) ltac:(lia) CdT CfT eq_refl CnT CRT).
      exact (SPA_axforms segs _ (xf_shback T_f8a0) rho' T_f8a0 T_f8a1 tp' _ Cxb Hw). }
    apply TR_exw. intros rho2. apply (CUTR C_pro2 nd_r1 0%nat (2980, z0) rho2 tp'); [cutR 2 | exact I | meas_z0].
Qed.

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1VTR;S34S0S9bVAInv;R3VKc;A3S4fR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S51S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMALLOC : ltac2:(tb__ "0|0|
S4aS1bS2S2fQ40A1A1VTR;S34S0S9aVAInv;S50S97R3VKc;S22PcA1A6S59R2R1A5S46S0S69R2R1S9eS96VAInv;VCST;VXGL;S50S97R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Lemma ms_site : ltac2:(tb__ "0|2|
S13SbcS2S1cA1M0S1bS2S2fQ40A1A1M1S2S1S1aS1aA2A1S2Sa6A1S90S30SaG0A1S48R8S4fR7A3S9G0R6A2A3S30S5S47R9S4fR8R7S8S13S51S7S13A1A3A5S6A3S30S5Se7S4eR9A2S6A3S30S5SebS4eS6fRbA1A2S6A3S30S5S3fS6fRcA1S39R7S4dR6S3aA4A2S6A3S30S5Sa8S6fRdA1R7A2S6A3S30S5Sa7R8A1S6A3S30S5Sd1S6bRfA1RaS4dSabRdA5S6A3S30S5Sd3S6bR10A1RbS4dSd2S15R10A1A5S6A3S1bG1VTR;S34S0VJAv;S39ReS4dRdS3aA4A1Se6S4fR13R12R11S51A5R2R1A5RcA2Ftp';Frho';VTR;S34S0VJAv;S39RdS4dRcS3aA4A1R12RfReA5RbA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd;Ftv;Ftp;Frho;FR;Fs;FE;").
Proof using ALA HCST HXGL HKc HXlits TR_callP TR_ex TR_facts TR_pre CMEMSET.
  intros E s R rho tp tv bd Q Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX Tcont.
  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E s R rho tp (NDA tv fr_lo bd ANone) bd Q).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd]. apply payA_same. exact Cwp.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 pro_chk_mo))))))))))))).
  - exact (site_rt E s R rho tv fr_lo bd ANone _ CR CX (fun _ _ _ _ _ _ => I)).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E memset_pc s R rho tp tr ms md Hsm HM HX' Cent).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am]. exact (Tcont rho' tp').
Qed.

Lemma CXL_mo : ltac2:(tb__ "0|0|
S30S5Sb1S6bS63A1S7S1S1aS1aA2A1Z20Z40S15S63A1A5S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_E_mo0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6eA2S5eR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S5eS6eA4G1A4S3S18S1aZba3S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_mo as (Cb0 & Co0 & Cd0 & Cf0 & Cn0 & CR0 & CE1 & Cent & Cchk & Cta & Cnp & Cnb & Cbb & _ & CR & CX & CT0 & Csel & CbT & CfT & CwC & CC3 & CRT).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_r1) E_mo1 rho1 tp w)).
  { intros [tr [ms md]] Hw. eexists. rewrite <- CE1. exact (sh_release E_mo0 [] LI.bd_lo0 231 248 _ _ [] rho tp tr ms md Cb0 Co0 ltac:(lia) ltac:(lia) Cd0 Cf0 eq_refl Cn0 CR0 Hw). }
  apply TR_exw. intros rho1. unfold nd_r1.
  apply (ms_site E_mo1 s_mo R_mo rho1 tp [] LI.bd_lo0 _ Cent Cchk Cta Cnp Cnb Cbb eq_refl CR CX).
  intros rho' tp'. rewrite CT0.
  eapply TR_pre; [|apply (CUTR C_pro3 nd_r1 0%nat (2970, z0) rho' tp'); [cutR 3 | exact I | meas_z0]].
  intros w Hw. rewrite <- CC3. unfold nd_r1.
  apply (sh_reopen T_mo1 [] LI.bd_lo0 (ax_X T_mo1) 32 64 rho' tp' w CbT ltac:(lia) ltac:(lia) CfT (fun r H => H) CwC CRT CXL_mo).
  exact (SPA_axforms segs _ [AXSelect (sel_last T_mo0 1)] rho' T_mo0 T_mo1 tp' w Csel Hw).
Qed.

Lemma fk_rng : ltac2:(tb__ "0|0|
S1bS2S1dA1S18Sa9S1dS1fR3A1R2A3S30S5S8dS1dS2dSb8A1R3A3S6A3S31S86Z0R3A2S86R3Z800A2A2S30S18Sa5R6S21Sd7S53S1eR4A1A3A2S89Sa5R6S53A2R4A2A3F_;F_;F_;Fk;FF;Fr;").
Proof using .
  intros r F k HF Hm Hk. pose proof (holds_mem _ _ _ HF Hm) as A. apply (proj1 (h_ule _ _ _)) in A. rewrite uval_lit in A by (vm_compute; split; [discriminate | reflexivity]).
  pose proof (uval_range r vF). apply uval_addk. lia.
Qed.
Lemma X_E_mz0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6eA2S5fR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S5fS6eA4G1A4S3S18S1aZb99S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_mz as (Cb0 & Co0 & Cd0 & Cf0 & Cn0 & Cloc & CR0 & CE1 & Cxf & Con & Cwf & CfU & CEmz & Cent & Cchk & Cta & Cnp & Cnb & Cbb & CR & CX & CT0 & Cxb).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_r1) E_mz rho1 tp w)).
  { intros [tr [ms md]] Hw. eexists. rewrite <- CEmz.
    apply (SPA_reshape segs _ _ E_mz2 (S (idxF E_mz1)) _ (fslot 496 16 [] DUnknown) tp _ Con); [reflexivity | reflexivity | reflexivity | exact Cwf | |].
    { intros HF. unfold fslot, fpiece, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      change (bv_unsigned (eval ?r (SAlu ALU_ADD (SVar 110) (SLit 496)))) with (uval r (SAlu ALU_ADD vF (SLit 496))).
      rewrite (fk_rng _ _ 496 HF CfU) by lia. unfold uval, vF. lia. }
    apply (SPA_axforms segs _ _ _ E_mz1 E_mz2 tp _ Cxf). rewrite <- CE1.
    exact (sh_release E_mz0 [] LI.bd_lo0 32 64 _ _ [(464, 48)] rho tp tr ms md Cb0 Co0 ltac:(lia) ltac:(lia) Cd0 Cf0 Cloc Cn0 CR0 Hw). }
  apply TR_exw. intros rho1. unfold nd_r1.
  apply (ms_site E_mz s_mz R_mz rho1 tp [] LI.bd_lo0 _ Cent Cchk Cta Cnp Cnb Cbb eq_refl CR CX).
  intros rho' tp'. rewrite CT0.
  eapply TR_pre; [|apply (CUTR T_mz1 nd_r1 0%nat (2960, z0) rho' tp'); [cutR 4 | exact I | meas_z0]].
  intros w Hw. exact (SPA_axforms segs _ [AXRebase 1] rho' T_mz0 T_mz1 tp' w Cxb Hw).
Qed.

Lemma CXL_n : ltac2:(tb__ "0|0|
S30S5Sb1S6bScfA1S7S1S1aS1aA2A1Z20Z40S79ScfA1A5S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_E_ma0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6eA2S5dR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S5dS6eA4G1A4S3S18S1aZb8fS6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_ma as (Cxf & Cent & Cchk & Cta & Cnp & Cnb & Cbb & Cs12 & Cres & Cpay & CR & CX & C12 & CAR & CTn & Cbn & Cfn & Cin & Cwn & CTn8 & CRn & CTo & Cfb & Cnz).
  apply (TR_pre (SPA segs (JAv nd_r1) E_ma rho tp)).
  { intros w Hw. exact (SPA_axforms segs _ _ rho E_ma0 E_ma tp w Cxf Hw). }
  unfold Pre_ma in Cent, Cchk, Cres, CTn, CTo.
  apply (malloc_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           W2 UStopLe E_ma s_ma R_ma rho tp nd_r1 bd_pro _ CMALLOC Cent Cchk Cta Cnp Cnb Cbb Cs12 Cres).
  - apply payA_of_bud_pay. exact Cpay.
  - intros A A' _ _. exact I.
  - unfold nd_r1. apply (site_rt E_ma s_ma R_ma rho [] fr_lo LI.bd_lo0 ANone _ CR CX).
    intros Ai ms HF HP0 Hav HFR. split; [rewrite C12; rewrite uval_lit by lia; lia | exact I].
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_r1]. rewrite CTn.
    eapply TR_pre; [|apply (CUTR Tn8 nd_rn 0%nat (2400, z0) rho' tp'); [cutR 9 | exact I | meas_z0]].
    intros w Hw. rewrite <- CTn8. unfold nd_rn.
    exact (sh_reopen T_ma_null [] bd_pro (XN T_ma_null) 32 64 rho' tp' w Cbn ltac:(lia) ltac:(lia) Cfn (xrs_incl_of _ _ Cin) Cwn CRn CXL_n Hw).
  - intros rho' tp' _ _. cbn [nd_tv nd_fr nd_am nd_r1]. unfold nx in CAR. rewrite CTo, C12, CAR.
    eapply TR_pre; [|apply (CUTR T_ma_ok nd_r2 0%nat (2950, z0) rho' tp'); [cutR 5 | exact I | meas_z0]].
    intros w Hw. unfold T_ma_ok. apply (SPA_refacts_JA segs); [exact Hw | exact Cfb |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF Cnz).
Qed.

Hypothesis CMC48 : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1VTR;S34S0S95VAInv;R3VKc;A3SccR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45ScbS94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis C00 : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1VTR;S34S0S95VAInv;R3VKc;A3S57R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S54S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A2Ftp1;Frho1;FAi;").

Lemma pr_site : ltac2:(tb__ "0|4|
S13S13S13SbcS2S1cA1M0S1bS2S2fQ40A1A1M1S2S1S1aS1aA2A1S2Sa6A1S90S4aS1bG1VTR;S34S0S95VAInv;R3VKc;A3RdR2R1A5S46S0S69R2R1S8S1S13S45A2M2S3S13S45RcS94VAInv;VCST;VXGL;R3VKc;A5A4S7G2A1A3A5A2Ftp1;Frho1;FAi;S30S19S23S14RbA1A1S69A3S30S1aS16RcA1S1eSdaA1A3S30S5Sb9RdS8S13RcS7S13A1M3A3A2S6A3S30SaG0A1S48RcReRbA3S9G0RaA2A3S30S5S47RdRfRcRbS8S13ReG3A3A5S6A3S30S5Se7S4eRdA2S6A3S30S5SebS4eS6fRfA1A2S6A3S30S5S3fS6fR10A1S39RbS4dRaS3aA4A2S6A3S30S5Sa8S6fR11A1RbA2S6A3S30S5Sa7RcA1S6A3S30S5Sd1S6bR13A1ReS4dSabR11A5S6A3S30S5Sd3S6bR14A1RfS4dSd2S15R14A1A5S6A3S1bG1VTR;S34S0VJAv;S39R12S4dR11S3aA4A1Se6R19R17R16R15R18A5R2R1A5R10A2Ftp';Frho';VTR;S34S0VJAv;S39R11S4dR10S3aA4A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd;Ftv;Ftp;Frho;FR;Fs;FE;FLp;FPre;").
Proof using ALA HCST HXGL HKc HXlits TR_callP TR_ex TR_facts TR_pre.
  intros Pre Lp E s R rho tp tv bd Q CC Cnf Cbp Cshape Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX Tcont.
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre [Lp] E s R rho tp (NDA tv fr_lo bd ANone) bd Q).
  - intros Ai rho1 tp1. cbn [map]. exact (CC Ai rho1 tp1).
  - exact Cnf.
  - exact Cbp.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd]. apply payA_same. exact Cwp.
  - exact Cshape.
  - exact (site_rt E s R rho tv fr_lo bd ANone _ CR CX (fun _ _ _ _ _ _ => I)).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am]. exact (Tcont rho' tp').
Qed.

Lemma X_E_mc0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6dA2SceR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38SceS6dA4G1A4S3S18S1aZb85S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_mc as (Cx1 & Cz & Cwz & Cez & Cx3 & Cx4 & Cx5 & Cx6 & Cent & Cchk & Cta & Cnp & Cnb & Cbb & Cwp & Cshape & Cnf & Cbp & CR & CX & CT).
  apply (TR_pre (SPA segs (JAv nd_r2) E_mc rho tp)).
  { intros w Hw. apply (SPA_axforms segs _ _ rho E_mc5 E_mc tp w Cx6). apply (SPA_axforms segs _ _ rho E_mc4 E_mc5 tp w Cx5).
    apply (SPA_axforms segs _ _ rho E_mc3 E_mc4 tp w Cx4). apply (SPA_axforms segs _ _ rho E_mc2 E_mc3 tp w Cx3). rewrite <- Cez.
    apply (SPA_zero_cells segs _ rho E_mc1 _ _ (ax_S E_mc2) tp w Cz Cwz). exact (SPA_axforms segs _ _ rho E_mc0 E_mc1 tp w Cx1 Hw). }
  unfold nd_r2. apply (pr_site Pre_mc48 L_mc48 E_mc s_mc R_mc rho tp [blkAR] bd_pro _ CMC48 Cnf Cbp Cshape Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX).
  intros rho' tp'. rewrite CT. apply (CUTR T_mc nd_r2 0%nat (2940, z0) rho' tp'); [cutR 6 | exact I | meas_z0].
Qed.

Lemma CXL_s00 : ltac2:(tb__ "0|1|
S30S5Sb1S6bScaA1S8S1S1aS1aA2M0Sd0S7G0A1A3Z44Ze7S15ScaA1A5S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_E_s00_0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6dA2ScaR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38ScaS6dA4G1A4S3S18S1aZb7bS6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_s00 as (Cb0 & Cf0 & Cw1 & CE1 & CR0 & Cxf & Cent & Cchk & Cta & Cnp & Cnb & Cbb & Cshape & CR & CX & CT0 & Cxb & CbT & CoT & CdT & CfT & CnT & Cloc & CRT & CTs).
  pose proof pro_chk_mc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cwp & _).
  apply (TR_pre (SPA segs (JAv nd_r2) E_s00 rho tp)).
  { intros w Hw. apply (SPA_axforms segs _ _ rho E_s00_1 E_s00 tp w Cxf). rewrite <- CE1. unfold nd_r2.
    exact (sh_reopen E_s00_0 [blkAR] bd_pro (ax_X E_s00_0) 68 231 rho tp w Cb0 ltac:(lia) ltac:(lia) Cf0 (fun r H => H) Cw1 CR0 CXL_s00 Hw). }
  unfold nd_r2. apply (pr_site Pre_00 L_00 E_s00 s_s00 R_s00 rho tp [blkAR] bd_pro _ C00 eq_refl eq_refl Cshape Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX).
  intros rho' tp'. rewrite CT0.
  apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_r2) T_s00 rho2 tp' w)).
  { intros [tr [ms md]] Hw. eexists. rewrite <- CTs. unfold nd_r2.
    apply (sh_release T_s00_1 [blkAR] bd_pro 68 231 _ _ [(544, 1304)] rho' tp' tr ms md CbT CoT ltac:(lia) ltac:(lia) CdT CfT Cloc CnT CRT).
    exact (SPA_axforms segs _ _ rho' T_s00_0 T_s00_1 tp' _ Cxb Hw). }
  apply TR_exw. intros rho2. apply (CUTR T_s00 nd_r2 0%nat (2930, z0) rho2 tp'); [cutR 7 | exact I | meas_z0].
Qed.

Lemma carve_ok : ltac2:(tb__ "0|2|
S13S13S1aS18S18S35S1bS2S2fQ40A1A1S93S30SaS13A1Sf3R9S7aR9R7R6R5A4A2S9S13R8A2A3S30S5SbaR9ScS73RaR8R7A3A1A2S6A3S30S5S2bS6fRaA1S65R9R8R7A3A2S6A3S30S5SaS1cA1S5Lx;S8fS1cS24S14RbA1A1ScS73RcRaR9A3A1A3S1cSdSdS25S28R1A1RbA2S25S2aR1A1S1eRaA1A2A2S25S29R1A1S1eS89RaR9A2A1A2A2Lo;S11Xax2S6A3S31S86S8bS87Z2Z3eA2M0A1RaA2S88RaG0A2M1A2S31S86Z0RaA2G1A2Sa9S1dS1fR9A1S6bReA1A3S30S18Sa5RaS21Sd7ReS1eRdA1A3A2S89Sa5RaReA2RdA2A3F_;S34S0RbR10RaR9R8A6S34S0RcS17R10Sf2S14R10A1ScS73R11RfReA3A1S65RfReRdA3A3A2RbRaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FJ;Fn;Foff;Fb;FC1;FL;").
Proof using .
  intros L C1 b off n J rho tp w Cxf Cwr Cwf Cpc Hoff Hn Hrng Hw.
  pose proof (SPA_axforms segs J _ rho L C1 tp w Cxf Hw) as Hw1.
  unfold wr_at in Cwr. destruct (nth_error (ss_objs (ax_S C1)) (S (cv_i L b off))) as [o|] eqn:Hn0; [|discriminate].
  apply andb_prop in Cpc as [Cpc Ch]. apply andb_prop in Cpc as [Cb Cl]. apply sv_eqb_sound in Cb. apply sv_eqb_sound in Cl. apply sv_eqb_sound in Ch.
  apply (SPA_reshape segs J rho C1 (S (cv_i L b off)) o (bslot b off n) tp w Hn0); [reflexivity | reflexivity | exact Cwr | exact Cwf | | exact Hw1].
  intros HF. unfold bslot, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Cb, Cl, Ch. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD b (SLit off)))) with (uval rho (SAlu ALU_ADD b (SLit off))). rewrite (Hrng HF). unfold uval. lia.
Qed.

Lemma X_E_mb0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S6dA2ScdR3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38ScdS6dA4G1A4S3S18S1aZb71S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_mb as (Cxf & Cwr & Cwf & CfU & Cpc & CEmb & Cent & Cchk & Cta & Cnp & Cnb & Cbb & CR & CX & CT0 & Cxb).
  pose proof pro_chk_mc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cwp & _).
  apply (TR_pre (SPA segs (JAv nd_r2) E_mb rho tp)).
  { intros w Hw. rewrite <- CEmb. apply (carve_ok E_mb0 _ vF 640 1208 _ rho tp w Cxf Cwr Cwf Cpc ltac:(lia) ltac:(lia)); [|exact Hw].
    intros HF. exact (fk_rng rho _ 640 HF CfU ltac:(lia)). }
  unfold nd_r2. apply (ms_site E_mb s_mb R_mb rho tp [blkAR] bd_pro _ Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX).
  intros rho' tp'. rewrite CT0.
  eapply TR_pre; [|apply (CUTR T_mb nd_r2 0%nat (2920, z0) rho' tp'); [cutR 8 | exact I | meas_z0]].
  intros w Hw. exact (SPA_axforms segs _ [AXRebase 1] rho' T_mb0 T_mb tp' w Cxb Hw).
Qed.

Lemma X_vl : ltac2:(tb__ "0|4|
S4S1bS2S2fQ40A1A1M0G0SecR4U22A2VTR;S34S0VJAFv;S7fS6aU0M1A2S6dA2S7cR5A1M2R4R3A5VFAM;S7eS3S1S1S13S38A2M3S4A2S1S18S1aA2S3G3S4S3S13S38G2S6dA4G1A4S3S18S1aS89S7dR5A1Z9A2S6cA4A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Fj;").
Proof.
  intros j rho tp tp0 Hj. apply TR_JAF. intros _.
  destruct (vq_all j Hj) as (Cxf & Cwr & Cwf & Cpc & Crng & CE & Cent & Cchk & Cta & Cnp & Cnb & Cbb & CR & CX & CT0 & Cz & Cwz & Cez & Cx2 & Cx3 & Cx4 & Cx5 & Ctidy).
  pose proof pro_chk_mc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cwp & _).
  set (v := vsn j) in *. set (L := vl j) in *. set (b := vs_b v) in *. set (off := vs_off v) in *. set (C1 := nth j VC1 BAD) in *.
  apply (TR_pre (SPA segs (JAv nd_r2) (vs_E v) rho tp)).
  { intros w Hw. rewrite <- CE. unfold rng_chk in Crng. apply orb_prop in Crng as [Crng|Crng].
    - apply andb_prop in Crng as [Crng H2]. apply andb_prop in Crng as [Crng H1]. apply andb_prop in Crng as [Hb Hf]. apply sv_eqb_sound in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2.
      apply (carve_ok L C1 b off 24 _ rho tp w Cxf Cwr Cwf Cpc ltac:(lia) ltac:(lia)); [|exact Hw]. intros HF. rewrite Hb. exact (fk_rng rho _ off HF Hf ltac:(lia)).
    - apply andb_prop in Crng as [Crng H2]. apply andb_prop in Crng as [Crng H1]. apply andb_prop in Crng as [Hb Hf]. apply sv_eqb_sound in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2.
      apply (carve_ok L C1 b off 24 _ rho tp w Cxf Cwr Cwf Cpc ltac:(lia) ltac:(lia)); [|exact Hw]. intros HF. rewrite Hb.
      pose proof (holds_mem _ _ _ HF Hf) as A. apply (proj1 (h_ule _ _ _)) in A. rewrite uval_lit in A by lia. pose proof (uval_range rho (SVar 10)). apply uval_addk. lia. }
  unfold nd_r2. apply (ms_site (vs_E v) (vs_s v) (vs_R v) rho tp [blkAR] bd_pro _ Cent Cchk Cta Cnp Cnb Cbb Cwp CR CX).
  intros rho' tp'. rewrite CT0.
  eapply TR_pre; [|apply (CUTR (vs_T v) nd_r2 0%nat (vrank j, z0) rho' tp');
                    [unfold cutsR; apply in_or_app; right; unfold cutsV; apply in_map_iff; exists j; split; [reflexivity | apply in_seq; lia] | exact I
                    | rewrite !efmeas_z0; unfold vrank; lia]].
  intros w Hw. rewrite <- Ctidy. apply (K2.SPA_tidy segs). apply (SPA_axforms segs _ _ rho' _ _ tp' w Cx5). apply (SPA_axforms segs _ _ rho' _ _ tp' w Cx4).
  apply (SPA_axforms segs _ _ rho' _ _ tp' w Cx3). apply (SPA_axforms segs _ _ rho' _ _ tp' w Cx2). rewrite <- Cez.
  exact (SPA_zero_cells segs _ rho' _ 1%nat z24 _ tp' w Cz Cwz Hw).
Qed.

Hypothesis CSF : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1VTR;S34S0S9cVAInv;Z5M0R3VKc;A4S72R2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S71S98VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A2Ftp1;Frho1;FAi;").

Lemma site_sf : ltac2:(tb__ "0|8|
S13SbcS2S1cA1S1bS30S5Sf9S20S14R4A1A1S7S1S1aS1aA2A1M0S4dS9S4U0M1A2M2SabR2A6S6A3S30S5Sc3VXGL;S20S14R5A1A1G0S4dG2S7S1cA1Sb6S15R5A1A8S6A3S30S1aSbeR5PcM3A2S53A3S30S1aSbeR6S9fA2S66A3S4aSa9S1dS1fR6A1S20S14R9A1A1A3VP0;Vrho0;A1SadS4eVrho0;R8A3S42VFB;R4A2S43VFF;R5A2S3dVFB;R6RbG0A4Sc0RcG0A2Sc1RdG0A2S3bVFF;R9ReS4dA4S32S1bS1bS32S2S2fQ40A1A1M4G4S32Sa3Sa3VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S3cVrho0;RbA2SbfR11S4cS4bRcA1A1A2S31Se2VCST;Vrho0;VFB;VFF;R12G0Sc2S1S1S1aS18A2M5S1aA2G1S4dA3M6R13A8S31Se0VCST;VXGL;Vrho0;VFB;VFF;R12G0G6S15R15A1A9S31S30S18Sa5R12SbeR14G3A2A2Sa5R12SbS1aS18SbG5S1aS3G5S1aS3S1aS18S53Z5A4S66A4M7A3A3A2A3S30S18Sa5R12SbeR14S9fA2A2Sa5R12SeG5S1aG7A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;Frho;FR;Fs;FE;").
Proof using ALA HXlits.
  intros E s R rho HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr.
    apply (TobjJAT.robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] fr_lo (Some 0%nat) extraLO R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HR) with (o := o); [| exact Ho | exact Hr].
    intros o' a' _ HE Hr'. exact (K2.extraLO_pclMA CST rho0 FB FF rho [] _ o' a' Hav HP0 HE Hr').
  - exact (lo_xrsL Ai rho _ [] fr_lo (Some 0%nat) [] (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR HX).
Qed.
Lemma CXL_sf : ltac2:(tb__ "0|0|
S30S5Sc3VXGL;S6bS74A1S7S1S1aS1aA2A1S4dS9S4U0A2S7S1cA1Sb6S15S74A1A8S6A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_En_sf0 : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S77A2S75R3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S75S77A4G1A4S3S18S1aZ95fS6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_nsf as (Cb0 & Co0 & Cd0 & Cf0 & Cn0 & CR0 & CEB & Co5 & Cwf5 & CEC & Cxf & CbD & CwfF & CEF & CRD & CXD & Cent & Cchk & Cta & Cnp & Cnb & Cwp & CRsf & C12 & C16 & CT0 & Ctidy & _).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_rn) En_sf rho1 tp w)).
  { intros [tr [ms md]] Hw. eexists. rewrite <- CEF. unfold nd_rn.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             [] fr_lo bd_pro ANone 0%nat 110%positive 5 120%positive En_sfD _ tp (tr, mkCfg ms md) eq_refl c5_ok CbD ltac:(rewrite CEF; rewrite <- CEF; exact CwfF)).
    - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      + intros o a Ho Hr. destruct (lo_robjsR Ai _ _ [] fr_lo _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRD o a Ho Hr) as [X|X]; [left; exact X | right; left; exact X].
      + exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai _ _ [] _ rho3 tp3 md3 HM HF HN HZ CXD).
    - apply (SPA_axforms segs _ xf_nm _ En_sfC En_sfD tp _ Cxf). rewrite <- CEC.
      apply (SPA_reshape segs _ _ En_sfB 5 _ zmid tp _ Co5); [reflexivity | reflexivity | reflexivity | exact Cwf5 | intros _; split; reflexivity |].
      rewrite <- CEB. exact (sh_release En_sf0 [] bd_pro 32 64 _ _ [] rho tp tr ms md Cb0 Co0 ltac:(lia) ltac:(lia) Cd0 Cf0 eq_refl Cn0 CR0 Hw). }
  apply TR_exw. intros rho1.
  unfold Pre_sf, L_sf in Cent, Cchk, CT0.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 En_sf s_sfn Rn_sf (ax_X En_sf) rho1 tp nd_rn 0%nat (vF, 5, vFL) _ CSF c5_ok).
  - intros r H. exact H.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cwp.
  - reflexivity.
  - reflexivity.
  - intros A A' _. exact I.
  - exact (site_sf En_sf s_sfn Rn_sf rho1 CRsf CXL_sf C12 C16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am nd_rn remove_nth fr_lo]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_rz) Tn_sf rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply (K2.SPA_tidy segs). exact Hw. }
    apply (CUTR Tn_sf nd_rz 0%nat (2390, z0) rho' tp'); [cutR 10 | exact I | meas_z0].
Qed.

Hypothesis CONT_blr : ltac2:(tb__ "0|1|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAv;S6dA1Sd9R3R2A5VFAM;S8aZa09S87Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis XPOST : ltac2:(tb__ "0|1|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAv;Sd6A1Sd5R3R2A5VFAM;S8aZ955S87Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").

Lemma X_P_errN : ltac2:(tb__ "0|3|
S1bS2S2fQ40A1A1M0G0VTR;S34S0VJAFv;S7fS6aU0M1A2S78A2S76R3R2A5VFAM;S7eS3S1S1S13S38A2M2S4A2S1S18S1aA2S3G2S4S3S13S38S76S78A4G1A4S3S18S1aZ955S6cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof pro_chk_nsf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  rewrite efmeas_z0. apply (TR_pre (SPA segs (JAv LI.nd_lo_err) LI.P_err (rho_sub rho s_pe) tp)); [|apply XPOST].
  intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc P_errN LI.P_err s_pe nd_rz LI.nd_lo_err rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam Hw).
Qed.

Lemma exitsR_ok : ltac2:(tb__ "0|4|
S13S38S4S1S18S1aA2M0S1bS2S2fQ40A1A1M1G1S8cS1S1S1S13S38A2M2S4A2M3G0A2S3G3G0S3G2S4S3S13S38R7R6A4R5A4R4A4S7bA3VTR;S34S0VJAFv;S7fS6aR6A2R7A2R8R4R3A5VFAM;S7eS3G3G0S3G2S4S3S13S38R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. unfold exitsR in Hin. apply in_app_or in Hin as [Hin|Hin].
  - cbn [In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]; injection E as <- <- <- <-.
    + apply X_E_sm0.
    + apply X_E_f8a0.
    + apply X_E_mo0.
    + apply X_E_mz0.
    + apply X_E_ma0.
    + apply X_E_mc0.
    + apply X_E_s00_0.
    + apply X_E_mb0.
    + apply TR_JAF. intros _. rewrite efmeas_z0. apply CONT_blr.
    + apply X_En_sf0.
    + apply X_P_errN.
  - unfold exitsV in Hin. apply in_map_iff in Hin as (j & E & Hj). injection E as <- <- <- <-. apply in_seq in Hj. apply X_vl. lia.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S44S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sa0S0S96VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S18S8cS18R1S8S18Z0S8S18Zf5S8S18Zf8S7S18A1A3A3A3A3SedS0S96VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
SdeS0S96VAInv;VCST;VXGL;SddA6").
Variable Q : assn.

Hypothesis CONT_blr_T : ltac2:(tb__ "0|0|
S1bS2S2fQ40A1A1S92S0Vok;S34S0VJAv;S6dA1Sd9R2R1A5VQ;A4Ftp;Frho;").
Hypothesis XPOST_T : ltac2:(tb__ "0|0|
S1bS2S2fQ40A1A1S92S0Vok;S34S0VJAv;Sd6A1Sd5R2R1A5VQ;A4Ftp;Frho;").

Lemma okA : ltac2:(tb__ "0|0|
S35S1bS2S2fQ40A1A1S2Sa4A1Sa3R5R4R3R2R1A4VKc;R3R2A2F_;Fm;Ft;Fp;Fr;S37S0Vok;R2A3F_;FJ;").
Proof. intros J HJ. eapply ok_frameA_of_K; [exact Hok | exact HJ]. Qed.
Lemma CSM_T : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S9dVAInv;Z5M0R3VKc;A4S5aR2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S56S99VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.
Lemma CF8_T : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S95VAInv;R3VKc;A3S58R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S55S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.
Lemma C00_T : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S95VAInv;R3VKc;A3S57R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S54S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 0 ltac:(cbn; tauto)); [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.
Lemma CMEMSET_T : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S9bVAInv;R3VKc;A3S4fR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S51S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.
Lemma CMALLOC_T : ltac2:(tb__ "0|0|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S9aVAInv;S50S97R3VKc;S22PcA1A6S59R2R1A5S46S0S69R2R1S9eS96VAInv;VCST;VXGL;S50S97R3VKc;A8A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [right; left; reflexivity | exact HKc | exact (proj1 Hok) | exact (proj2 Hok)]. Qed.
Lemma CMC48_T : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S95VAInv;R3VKc;A3SccR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45ScbS94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48; [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.
Lemma CSF_T : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1S92S0Vok;S34S0S9cVAInv;Z5M0R3VKc;A4S72R2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S71S98VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. apply okA. intros r p t m (_ & K & _). exact K. Qed.

Let famS : Z -> list word -> assn := ltac2:(tb__ "0|0|
S18S2S2fQ40A1A1S93S33Sf5S0SaaS81Sf1S85VAInv;VCST;VXGL;S4eVKc;Vrho0;VP0;VFB;VFF;VBX;S3eS6aAcSaaS80S81S83S70A4A4R1A3VQ;R1A1A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|5|
S13S38S4S1S18S1aA2M0S1bS2S2fQ40A1A1M1S18G1S8cS1S1S1S13S38A2M2S4A2M3G0A2S3G3G0S3G2S4S3S13S38R8R7A4R6A4R5A4S70A3S7fS6aR7R5A3S31S86Z0S7eS3G3G0S3G2S4S3S13S38RaR9A4R8A4R7A4R6A2M4A2S88G4R4A2A2S92S0Vok;S34S0VJAv;RaA1RbR7R6A5VfamS;R5R4A2A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisZ ok (map efdrop cutsR) T nd k Q rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|0|
S90S18S2S2fQ40A1A1S92S0Vok;R3VQ;A4S92S0Vok;R4VfamS;R3R2A2A4F_;Ftp0';Fb;FP;").
Proof. intros P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma R_T : ltac2:(tb__ "0|3|
S13S38S4S1S18S1aA2M0S1bS2S2fQ40A1A1S8cS1S1S1S13S38A2M1S4A2M2G0A2S3G2G0S3G1S4S3S13S38R6R5A4R4A4R3A4S70A3S7fS6aR5R3A3S92S0Vok;S34S0VJAv;R7A1R8R4R3A5VQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_lo cpsR NP (map efdrop cutsR) (map efdrop exitsR) ok Q Hok
           (ejcertAF_jcertAF segs NP PhisZ _ _ _ _ _ ecertR_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsR_ok (triple segs ok) famS (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q' H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q' H)
           CSM_T CF8_T reenterS CMEMSET_T CMALLOC_T CMC48_T C00_T CSF_T
           (fun rho tp tp0' => rightS _ _ tp0' (CONT_blr_T rho tp)) (fun rho tp tp0' => rightS _ _ tp0' (XPOST_T rho tp)) X' nd' k' rv' rho1 tp1 [] HinX).
Qed.

Theorem pro_T : ltac2:(tb__ "0|0|
S2S2fQ40A1A1S92S0Vok;S34S0VJAv;Sd4A1S61Vrho0;R1A5VQ;A4Ftp0;").
Proof. intros tp0. exact (R_T Pre_lo LI.nd_lo0 0%nat (3000, z0) rho0 tp0 ltac:(left; reflexivity) I). Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sa1S0S96VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S18S8cS18R1S8S18Z0S8S18Zf5S8S18Zf8S7S18A1A3A3A3A3SeeS0S96VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
SdfS0S96VAInv;VCST;VXGL;SddA6").
Variable FAM : ltac2:(tb__ "0|0|
S18S2S2fQ40A1A1S90F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S18S18S2S2fQ40A1A1S93S86R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis CONT_blr_E : ltac2:(tb__ "0|1|
S1bS2S2fQ40A1A1M0G0S91S0S34S0VJAv;S6dA1Sd9R3R2A5VFAM;S8aZa09S87Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPOST_E : ltac2:(tb__ "0|1|
S1bS2S2fQ40A1A1M0G0S91S0S34S0VJAv;Sd6A1Sd5R3R2A5VFAM;S8aZ955S87Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CSM_E : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1S91S0S34S0S9dVAInv;Z5M0R3VKc;A4S5aR2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S56S99VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CF8_E : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S91S0S34S0S95VAInv;R3VKc;A3S58R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S55S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma C00_E : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S91S0S34S0S95VAInv;R3VKc;A3S57R2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S54S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 0 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CMEMSET_E : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S91S0S34S0S9bVAInv;R3VKc;A3S4fR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45S51S94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc. Qed.
Lemma CMALLOC_E : ltac2:(tb__ "0|0|
S4aS1bS2S2fQ40A1A1S91S0S34S0S9aVAInv;S50S97R3VKc;S22PcA1A6S59R2R1A5S46S0S69R2R1S9eS96VAInv;VCST;VXGL;S50S97R3VKc;A8A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [right; left; reflexivity | exact HKc]. Qed.
Lemma CMC48_E : ltac2:(tb__ "0|1|
S4aS1bS2S2fQ40A1A1S91S0S34S0S95VAInv;R3VKc;A3SccR2R1A5S46S0S69R2R1S8S1S13S45A2M0S3S13S45ScbS94VAInv;VCST;VXGL;R3VKc;A5A4S7G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48X. exact HKc. Qed.
Lemma CSF_E : ltac2:(tb__ "0|2|
S4aS1bS2S2fQ40A1A1S91S0S34S0S9cVAInv;Z5M0R3VKc;A4S72R2R1A5S46S0S69R2R1S8S1S13S45A2M1S3S13S45S71S98VAInv;VCST;VXGL;G0R3VKc;A6A4S7G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.

Let famE (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S18S2S2fQ40A1A1S93S33Sf4S0SaaS80Sf0S84VAInv;VCST;VXGL;S4eVKc;Vrho0;VP0;VFB;VFF;VBX;S3eS6aAcS70A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|5|
S2S2fQ40A1A1M0S13S38S4S1S18S1aA2M1S1bG0S18G0S8cS1S1S1S13S38A2M2S4A2M3G1A2S3G3G1S3G2S4S3S13S38R8R7A4R6A4R5A4S70A3S7fS6aR7R5A3S31S86Z0S7eS3G3G1S3G2S4S3S13S38RaR9A4R8A4R7A4R6A2M4A2S88G4R4A2A2S91S0S34S0VJAv;RaA1RbR7R6A5VfamE;RcR5R4A3A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;").
Proof.
  intros tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisZ cutsR T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S2S2fQ40A1A1M0S90S18G0S91S0R3VFAM;R2R4A2A3S91S0R4VfamE;R5R3R2A3A3F_;Ftp0';Fb;FP;Ftp0;").
Proof. intros tp0 P b tp0' H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma R_E : ltac2:(tb__ "0|4|
S13S38S4S1S18S1aA2M0S1bS2S2fQ40A1A1M1G1S8cS1S1S1S13S38A2M2S4A2M3G0A2S3G3G0S3G2S4S3S13S38R7R6A4R5A4R4A4S70A3S7fS6aR6R4A3S91S0S34S0VJAv;R8A1R9R5R4A5VFAM;S7eS3G3G0S3G2S4S3S13S38R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisZ k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisZ PhisZ_reads FUEL_lo cpsR NP cutsR exitsR (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertR_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsR_ok (etriple segs) (famE tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q' H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q' H)
           CSM_E CF8_E (reenterE tp0) CMEMSET_E CMALLOC_E CMC48_E C00_E CSF_E
           (fun rho tp tp0' => rightE tp0 _ _ tp0' (CONT_blr_E rho tp tp0)) (fun rho tp tp0' => rightE tp0 _ _ tp0' (XPOST_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem pro_E : ltac2:(tb__ "0|0|
S2S2fQ40A1A1S91S0S34S0VJAv;Sd4A1S61Vrho0;R1A5VFAM;S8aZbb8S87Z2Z40A2A2R1A2A3Ftp0;").
Proof. intros tp0. rewrite <- (efmeas_z0 Pre_lo LI.nd_lo0 0%nat 3000 rho0). exact (R_E Pre_lo LI.nd_lo0 0%nat (3000, z0) rho0 tp0 tp0 ltac:(left; reflexivity) I). Qed.
End Existence.
End Sum.
End Lib_load_obj_pro_pf.

(* [comment removed for export] *)
Module Lib_load_obj_hv4w.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "pair"; "list"; "nat"; "option"; "prod"; "Some"; "app"; "orb"; "S"; "false"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "g8"; "has_facts"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sprop"; "sv"; "SPUle"; "sv_eqb"; "sprop_eqb"; "ss_facts"; "ss_next"; "ss_objs"; "ss_pc"; "DUnknown"; "SAlu"; "SVar"; "cell"; "ob_cells"; "SPEq"; "SPUlt"; "c_off"; "mkObj"; "mkSS"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "NP"; "g5"; "vLEN"; "optR"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w"; "PreR"; "E_o3"; "s_w"; "LR"; "T_w0"; "T_w1"; "R_w"; "w_chk"; "Ew0"; "Ew0r"; "Ew1"; "Ew1r"; "Lp0"; "Lp1"; "Lw0"; "Lw1"; "T_w0_0"; "T_w0b"; "T_w1_0"; "T_w1b"; "T_wc"; "drop_rgb"; "relw"; "s_o3j"; "w_ok"; "xf_w"; "xfb_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "filter"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "objs_nl"; "sh_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "bd_op1"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "c_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "AHead"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "cps_v"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "pure_posts_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH";
"@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition Lw0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_op1) memcpy_pc 0.
Definition Lw1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_op1) memcpy_pc 1.
Definition PreR : axst := Pre_memcpyR AE_A white_hv 12.
Definition LR : axst := L_memcpyR AE_A white_hv 12.
Definition relw (A : axst) : axst := ltac2:(tb__ "0|2|
S8fVA;S75VA;A1P6eS2SaS1dS1dA2M0S6S1dS1dZc0ZcM1A4S2G0S6S1dS1dZe0G1A4S5G0A1A3A3A4").
Definition xf_w (T : axst) : list axform := ltac2:(tb__ "0|2|
S66S45S1fZ20A1VT;A3S8S2S3fS41R1S1fZe0M0A1A2S2S3fS41SeR1A1M1S1fZecA1A2S2S3fS44G1G0A2S5S3fA1A3A3A3Tj;").
Definition s_w (E : axst) : wsub := ltac2:(tb__ "0|1|
S2SaS1eS22A2M0S6S1eS22P35S2bS70S45S1fZe0A1A3A4S2G0S6S1eS22P36S1fZcA1A4S2G0S6S1eS22S92S4aA4S7dPaS13VE;A1S13S4bA1A3A3A3A3").
Definition R_w (E : axst) : list sobj := ltac2:(tb__ "0|0|
S49S7eVE;S4bS4dVE;A1A3A1").
Definition w_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S9S7S20A1M0A1S3Lx;S7eVE;S4bS4dVE;A1M1A3G0S7fVE;S4bG1R1S2S12S4eS5S12A1A3A5LR;SfX9x2").
Definition T_wc (E : axst) : axst := ltac2:(tb__ "0|0|
S8cS4bVE;S4dVE;A1S51VE;A1S4eA5").
Definition xfb_w (T : axst) : list axform := ltac2:(tb__ "0|3|
S2S3fS43S66S2bS70S45S1fZe0A1M0A3S1fZ0A1VT;A3A1S5S3fA1M1A3S7S3fA1S85S40VT;R1A2A1S12ScS3fR2S2S3fS69S2S8S66S45S1fZ20A1R1A3S2S8S66S45G0R1A3S2S8S66S45S1fZecA1R1A3S5S8A1A3A3A3S10S20S28S13R1A1A1A2A2S2S3fS42U0A1M2S2S3fG2G1A3A3A3A3TT1;Tpre;").
Definition Ew0r : axst := Eval vm_compute in relw Lw0.       Definition Ew1r : axst := Eval vm_compute in relw Lw1.
Definition Ew0 : axst := Eval vm_compute in optL' (apply_axforms Ew0r (xf_w Ew0r)).
Definition Ew1 : axst := Eval vm_compute in optL' (apply_axforms Ew1r (xf_w Ew1r)).
Definition T_w0_0 : axst := Eval vm_compute in T_wc Ew0.    Definition T_w1_0 : axst := Eval vm_compute in T_wc Ew1.
Definition T_w0b : axst := Eval vm_compute in optL' (apply_axforms T_w0_0 (xfb_w T_w0_0)).
Definition T_w1b : axst := Eval vm_compute in optL' (apply_axforms T_w1_0 (xfb_w T_w1_0)).
Definition T_w0 : axst := Eval vm_compute in ax_tidy T_w0b.  Definition T_w1 : axst := Eval vm_compute in ax_tidy T_w1b.

Definition w_chk (tv : list (sv * sv)) (bd : list bitem) (L Er E T0 Tb T : axst) : Prop := ltac2:(tb__ "0|e|
S1S0S7S20A1S28S13VL;A1M0A1ScS20S75VL;A1M1S2S20S90S47Z4M2Z1eM3S2eS76VL;A1A1M4S2aA5S5S20A1A3A3A3S1S0S22S17VL;A1S1fS91A1A3S1S0S3S1bS2S21S2fS1aS47A1S45A2S2S21S23S2cS47A1S1fS96S95Z2Z3dA2Z1A2A1A2S5S21A1A3A3S26G0A1M5A2S4A3S1S0S3S6eSaS1dS1dA2M6S8eG4S2aG2G3A4S2G6S6S1dS1dZc0ZcM7A4S2G6S6S1dS1dZe0G7A4S5G6A1A3A3A3S4A3S1S0S3S80S27G0A1M8S82Vtv;S6aVbd;S81S7bS4A2A4M9A2S4A3S1S0S3S68G5Vtv;S6aS67G1A5S4A3S1S0S3S71G5A1S4A3S1S0S12S61VL;A1VEr;A3S1S0S9S12A1MaS40VEr;S64VEr;A1A2SbS12VE;A2A3S1S0S3S63VE;A1S4A3S1S0S3S8dS46S4dVE;A1A2S4A3S1S0S3S94S46S27S13VE;A1MbA1McA2S4A3S1S0S3S80GcG9A2S4A3S1S0S3S8aGcVbd;A2S4A3S1S0S3S8bVbd;A1S4A3S1S0S3S87S4bS2S12S4eS5S12A1A3A2S4A3S1S0S3S72S26GbA1MdVtv;S6aS67S51VE;A1A5S4A3S1S0S3S74GdVtv;S6aS73S16VE;A1A5S4A3S1S0S3S71GdA1S4A3S1S0S3S83GcS6bA2S4A3S1S0S12S5fVE;A1VT0;A3S1S0GaS40VT0;S65VT0;A1A2SbS12VTb;A2A3S1S0S12S88VTb;A1VT;A3S1S0S3S83G8S6bA2S4A3S1S0S3S6dS21S25S30S7cS7aA2A1G5A3S4A3S1S0S3S6dS21S25S23S7aS48A2A1G5A3S4A3S0S3S6dS21S25S23S48S1fZ4000000A1A2A1G5A3S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv4_checks_w0 : ltac2:(tb__ "0|0|
S52S78S77S59S54S53S5bS5cS4fA8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv4_checks_w1 : ltac2:(tb__ "0|0|
S52S78S77S5aS56S55S5dS5eS50A8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Lp0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_w0) c_op 0.
Definition Lp1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_w1) c_op 0.
Definition drop_rgb (o : sobj) : sobj := ltac2:(tb__ "0|2|
S3S20L_;S24S34Vo;A1M0S45A2S32G0S37Vo;A1S36Vo;A1S6fS2dS2dS11SdSdS24S31R1A1M1S1fZc0A1A2S24G1S1fZc4A1A2A2S24G1S1fZc8A1A2A2A1Lc;S2eVo;A1A3S35Vo;A1A5Vo;X3x2").
Definition gen_o3 (L C : axst) : axst := ltac2:(tb__ "0|0|
S13VL;A1S3dS27R1A1S1eS2cR1A1S22S18VL;S33S29R3A1S89S22S3bR3A1UfR1A4S39R3A1S38R3A1S3cR3A1S6cS20S20S60S28R3A1A4S2S21S23R1S1fZ1A1A2S26S13VC;A1A1A3S93R2P1A2S3aR3A1A9A2Tpw;Tn;TS;").
Definition E_o3 : axst := Eval vm_compute in gen_o3 Lp0 T_op1.
Definition s_o3j (L : axst) : wsub := ltac2:(tb__ "0|0|
S7dS46S13VL;A1S13S4cA1A3").
Lemma hv4_checks_o3j : ltac2:(tb__ "0|4|
S1S0S3S14S4cA1S4A3S1S0S3S3eS13S4cA1M0A1S4A3S1S0S1dS29G0A1S79A3S1S0S7S7S1dA1M1A1S6cS12G1S12S6cS15S1dS15S29S13S1cR1A1A1A1LL;S86U258S84R1A3A4LT;S2S12S4fS2S12S50S5S12A1M2A3A3A4S2G1S2S1dS79S5S1dA1A3M3S2G1G3S5G1A1A3A3A3S1S0S3S6eS12S12S19R1S4cS62R1A1A3LL;S2S12S57S2S12S58G2A3A3A3S4A3S1S0S3S14S4fA1S4A3S0S3S14S50A1S4A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv4w.

(* [comment removed for export] *)
Module Lib_load_obj_ago_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "cons"; "nat"; "prod"; "app"; "nil"; "length"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_facts"; "ss_next"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "V_B"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_eqs"; "Yf_go"; "Xs_nop"; "Xs_ok"; "Ys_nop"; "Ys_ok"; "Xf_fz"; "Xf_go"; "bdX_nop"; "bdX_ok"; "bd_fzX"; "bd_go_fX"; "comm_nop"; "comm_ok"; "commf_fz"; "commf_go"; "extra_go"; "nd_fzX"; "nd_go_fX"; "nd_nopX"; "nd_okX"; "cutsG"; "exitsG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "LAX"; "LAXK"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "V_below"; "ejcertAF"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago"; "kept_fs"; "kept_go"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "T_go_f"; "nd_go_ok"; "E_fs"; "E_fs0"; "E_go"; "LAr1"; "LAr1K"; "LAr2"; "LAr2K"; "R_fs"; "R_go"; "T_go_ok"; "Xk_fs"; "Xk_go"; "bd_fs_fz"; "bd_fs_nop"; "bd_fs_ok"; "bd_go_f"; "qHk"; "qHn"; "qHz"; "tvL_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "robj_ent"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "xLK"; "X_latch"; "pH"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndXEf"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_finalize_shape Lib_finalize_shape_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_ago.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition Xf_go : list bitem := ltac2:(tb__ "0|0|
S3ScS47S3ScS48S7ScA1A3A3").
Definition Yf_go : list bitem := ltac2:(tb__ "0|1|
S3ScS36Z0M0A1S3ScS37G0A1S7ScA1A3A3").
Definition commf_go : list bitem := Eval vm_compute in bd_minus bd_go_f Xf_go.
Definition bd_go_fX : list bitem := Yf_go ++ commf_go.
Definition nd_go_fX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S27S14S62S9A2A4").
Lemma ago_checks_payf1 : ltac2:(tb__ "0|2|
SbSaS0S1bS53S6ScS2bS23A3A2S1A3SbSaS0S1bS6ScS2bS1dA3S27A2S1A3SbSaS0S39SeS12S42A1M0A1S10Z0M1A1G1S23S1dA5S1A3SaS0S16SfG0A1S2eA2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Lnop : axst := Eval vm_compute in leafL (runL 200 cps_arm T_fs_nop) pc_latch 0.
Definition s_latch_nop : wsub := Eval vm_compute in infer_sub NP (ax_S Lnop) (ax_S X_latch).
Definition bdX_nop : list bitem := Eval vm_compute in bd_subst s_latch_nop (bdX 0).
Definition nd_nopX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S24S14S55S1A2A4").
Definition comm_nop : list bitem := Eval vm_compute in bd_common bd_fs_nop bdX_nop.
Definition Xs_nop : list bitem := Eval vm_compute in bd_minus bd_fs_nop bdX_nop.
Definition Ys_nop : list bitem := Eval vm_compute in bd_minus bdX_nop bd_fs_nop.

Definition Lok : axst := Eval vm_compute in leafL (runL 200 cps_arm T_fs_ok) pc_latch 0.
Definition s_latch_ok : wsub := Eval vm_compute in infer_sub NP (ax_S Lok) (ax_S X_latch).
Definition bdX_ok : list bitem := Eval vm_compute in bd_subst s_latch_ok (bdX 0).
Definition nd_okX : ndesc := ltac2:(tb__ "0|0|
S15S57S17S25S14S54S1A2A4").
Definition comm_ok : list bitem := Eval vm_compute in bd_common bd_fs_ok bdX_ok.
Definition Xs_ok : list bitem := Eval vm_compute in bd_minus bd_fs_ok bdX_ok.
Definition Ys_ok : list bitem := Eval vm_compute in bd_minus bdX_ok bd_fs_ok.

Lemma ago_checks_pay2 : ltac2:(tb__ "0|5|
SbSaS0S1bS51S6ScS28S1eA3A2S1A3SbSaS0S1bS6ScS28S20A3S24A2S1A3SbSaS0S39SeS12S40A1M0A1S10Z0M1A1M2G1S1eS20A5S1A3SbSaS0S16SfG0A1S2fA2S1A3SbSaS0S1bS52S6ScS29S1fA3A2S1A3SbSaS0S1bS6ScS29S21A3S25A2S1A3SbSaS0S39SeS12S41A1M3A1G2G1S1fS21A5S1A3SbSaS0S16SfG3A1S30A2S1A3SbSaS0S3cS8ScS1eA2UcM4A2S1A3SbSaS0S3cS8ScS20A2G4A2S1A3SbSaS0S3cS8ScS1fA2G4A2S1A3SaS0S3cS8ScS21A2G4A2S1A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xf_fz : list bitem := ltac2:(tb__ "0|0|
S3ScS49S3ScS4aS7ScA1A3A3").
Definition commf_fz : list bitem := Eval vm_compute in bd_minus bd_fs_fz Xf_fz.
Definition bd_fzX : list bitem := Yf_go ++ commf_fz.
Definition nd_fzX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S26S14S56S9A2A4").
Lemma ago_checks_payf2 : ltac2:(tb__ "0|2|
SbSaS0S1bS50S6ScS2aS22A3A2S1A3SbSaS0S1bS6ScS2aS1dA3S26A2S1A3SbSaS0S39SeS12S3fA1M0A1S10Z0M1A1G1S22S1dA5S1A3SaS0S16SfG0A1S2dA2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsG : list efnode := ltac2:(tb__ "0|7|
S3S5S5S5S11S13A2M0S4A2M1S5S1cSdA2M2A2M3S2G1G2S2G0S4S2S11S13S4dS43A4U1M4A4S2S1cSdS33S34ZaS35A2A4M5A4S3G3S2G1G2S2G0S4S2S11S13S42S2eA4G4A4G5A4S3G3S2G1G2S2G0S4S2S11S13S40S2fA4G4A4S2S1cSdS33S34Z5S35A2A4M6A4S3G3S2G1G2S2G0S4S2S11S13S41S30A4G4A4G6A4S3G3S2G1G2S2G0S4S2S11S13S3fS2dA4G4A4G6A4S7G3A1A3A3A3A3A3").
Definition exitsG : list efnode := ltac2:(tb__ "0|6|
S3S5S5S5S11S13A2M0S4A2M1S5S1cSdA2M2A2M3S2G1G2S2G0S4S2S11S13S45S43A4U1M4A4S2S1cSdS33S34Z7S35A2A4A4S3G3S2G1G2S2G0S4S2S11S13S61S38A4G4A4S2S1cSdS33S34Z1S35A2A4M5A4S3G3S2G1G2S2G0S4S2S11S13S67S68A4G4A4G5A4S7G3A1A3A3A3").
Lemma ecertG_ok : ltac2:(tb__ "0|0|
SaS0S3bS64S5eS65Uc8S66S5eS31S32A8S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_go (o : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;S1aVo;A1S1S5dVo;A1X0x2").
Lemma ago_checks3 : ltac2:(tb__ "0|3|
SbSaS0S5aSeS12S46A1A1M0S3eS17S2cS4cA5S1A3SbSaS0S5cG0S3eS17S5bS4fA5S1A3SbSaS0S59G0A1S1A3SbSaS0S5aSeS12S44A1M1A1M2S3dS17S2cS4bA5S1A3SbSaS0S5cG2S3dS17S5bS4eA5S1A3SbSaS0S59G2A1S1A3SaS0S3aSfG1A1S19A2S1A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_go : ltac2:(tb__ "0|0|
S63S5SdSdA2S2SdSdS5fS58Z10S60A2A4S3eA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_kept_fs : ltac2:(tb__ "0|0|
S63S5SdSdA2S2SdSdS5fS58Z10S60A2A4S3dA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
End Lib_load_obj_ago_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_ago_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nat"; "true"; "bool"; "cons"; "app"; "fst"; "Some"; "nil"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sprop"; "holds"; "ss_next"; "SLit"; "SPUle"; "rw"; "sprop_eqb"; "SVar"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "TPA"; "fbinA"; "ffinA"; "frinA"; "tvinA"; "AHead"; "JA"; "NDA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tblB"; "P0_lo"; "V_B"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.FSP"; "P0_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.IRP"; "P0_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "keptK"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago"; "kept_fs"; "kept_go"; "PDk_fs"; "PDk_go"; "E_fs"; "R_fs"; "R_go"; "E_fs0"; "E_fs1"; "E_go"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "Xk_fs"; "Xk_go"; "brest_go"; "nd_go_ok"; "nnPhi"; "passed_fs"; "passed_go"; "qH1"; "s_fs"; "s_go"; "tv_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_eqs"; "cutsG"; "nd_fzX"; "nd_nopX"; "nd_okX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.FS"; "NP"; "Pre_fs"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_pf.IR"; "Pre_ir"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "HNEXT"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE";
"X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_finalize_shape Lib_finalize_shape_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_ago.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_ago_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module IR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest. End IR.  Module IRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_pf. End IRP.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include Lib_finalize_shape_pf. End FSP.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3cS2S1SfA1M0S10OF_;M1A2M2G2S4aS9G0G1R1A3SdG0G1R1A3A2Lp;S77A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma V_B_agree_ge : ltac2:(tb__ "0|0|
SfS10S10S34S6S9bS85R3A2S5A3S4eR4R3R2A3SfS3aSfR1S39A3S34S1fQ40A1S18R5R2A2S18R6R2A2A3F_;Fv;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn [HV HL]. apply V_B_agree. split; [|exact HL].
  intros i Hi. apply HV. apply Pos.leb_le in Hn. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S8bS10S1S1fQ40A1A1S3eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S9aS0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SeS8eVCST;R1A2S33S56Z0R2A2S57R2S96A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SeS8eVXGL;R1A2S33S56Z0R2A2S57R2S96A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SeS9dR1A1S8eVXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2SeSeA2SeA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
S38VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S29VAInv;VCST;VXGL;S78VKc;Vrho0;VP0;VFB;VFF;VBX;S21Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;S78VKc;Vrho0;VP0;VFB;VFF;VBX;S21VPhi;Vnd;Ad").

Lemma HIN_go : ltac2:(tb__ "0|1|
S10S58S8bS10S1S1fQ40A1A1S3eS3cS13S14R6A1S12S1dS68A1A1A3VP0;Vrho0;A1S4eS78Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S90RbS8dS8cR9A1A1A2S24VFB;RaA2S25VFF;RbA2S27VFB;RcReS8S2S11S11A2S60S72A3M0A4S91RfG0A2S92R10G0A2S26VFF;RfR11S36A4S33S94VCST;Vrho0;VFB;VFF;R12S60S36S65A8S33S95VCST;VXGL;Vrho0;VFB;VFF;R12S60S36S6dA9S41VCST;S8fVFB;R12S60A3S93VFF;R12S36A3S4cS4bR12S65R11A3S75A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ago_checks3 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_go) by (apply (tvinA_sublist FB Ai rho (kept_go ++ passed_go)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_go) by (exact (tvd_app_l rho kept_go passed_go HD)).
  assert (HZk : tvz rho kept_go) by (apply (tvz_sublist rho (kept_go ++ passed_go)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_go frL extra_go R_go rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_go in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_go frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_go frL o a HF CLN HT0 HZk lines_in_kept_go HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_go frL xextraLO Xk_go rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_go frL r a Hav HP0 HE Ha).
  - pose proof ago_checks1 as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold IRP.P0_ir, uval, Lib_scan_double.vB, Lib_scan_double.vL, IR.vBld. cbn [eval]. rewrite !rw_call'.
    change (wsub_get s_go 15) with vBUF. change (wsub_get s_go 18) with vLEN. change (wsub_get s_go 12) with bA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_go rho R_go ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_go) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_go) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
Qed.

Lemma HIN_fs : ltac2:(tb__ "0|1|
S10S58S8bS10S1S1fQ40A1A1S3eS3cS13S14R6A1S12S1dS63A1A1A3VP0;Vrho0;A1S4eS78Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S90RbS8dS8cR9A1A1A2S24VFB;RaA2S25VFF;RbA2S27VFB;RcReS8S2S11S11A2S5fS71A3M0A4S91RfG0A2S92R10G0A2S26VFF;RfR11S36A4S33S94VCST;Vrho0;VFB;VFF;R12S5fS36S64A8S33S95VCST;VXGL;Vrho0;VFB;VFF;R12S5fS36S6cA9S40S8fVFB;R12S5fA3S93VFF;R12S36A3S4cS4bR12S64R11A3S74A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ago_checks3 as (_ & _ & _ & CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_fs) by (apply (tvinA_sublist FB Ai rho (kept_fs ++ passed_fs)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_fs) by (exact (tvd_app_l rho kept_fs passed_fs HD)).
  assert (HZk : tvz rho kept_fs) by (apply (tvz_sublist rho (kept_fs ++ passed_fs)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_fs frL extra_go R_fs rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_go in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_fs frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_fs frL o a HF CLN HT0 HZk lines_in_kept_fs HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_fs frL xextraLO Xk_fs rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_fs frL r a Hav HP0 HE Ha).
  - unfold FSP.P0_fs. rewrite !rw_call'.
    change (wsub_get s_fs 12) with bA. change (wsub_get s_fs 100) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SeS1S1fQ40A1A1S2fF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2dS1cS10S1S1fQ40A1A1S2fS3cS13S14R3A1S12S1dR4A1A1A3VTR;S2cS0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2fS2fS2fS32R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2fOS2fS32R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2dS2dS1cS1cS4dS1S1bA1M0S1S2S1cS43A2M1A1S1S2S11S11A2M2A1S2fS10S1S1fQ40A1A1M3G2S3aG2R1R5A3S3aG2R2S1eRbA1A3F_;Fr;S34ScG0A1S46RaR9R8A3SaG0R7A2A3S34S6S45RbRaR9R8S3dG1S1cS9S1cS43A2R7A4A5S5A3S10G3VTR;S2cS0RfRdR2R1A5S42S0S15S1dRdA1A1R2R1RaA5A2Ftp1;Frho1;S1S3fA1M4S58S3eS2eS0R9R8R10S3G4S79R3S7aR2R1A2A4A5R13RaR9R4R2A4R13S4cS4bRbRfS50R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1cS43G4S58S3eS10G3G4S58S3eS3aG1S3S1cS43RaR9A4R14A3S2eS0R12R11R19S3G4S79R9S7aR8R7A2A4A5R1cR13R12RaR8A4S4eS15S1dR1aA1A1S4cS4bR14R18S50R9R13RaA3A3R19A2R8A3S2eS0R9R8ReS3G4S79R7S7aR6R5A2A4A5ReS4cS4bR16R1aS50RbR15RcA3A3R1bA2R15RaR9R8R6A6S33S9fR17S50RcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S4fR18S50RdR17ReA3R1cR1dS1dR1eA1S1dR1fA1S1dR11A1R1RcA9VTR;S2cS0S44R11S4cS4bR19R1dS50ReR18RfA3A3R1eA2R18RdRcA5Sa0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2cS0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S10OF_;S20S1cS10S1S1fQ40A1A1S2fR6R3A1VTR;S2cS0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S2cS0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHI : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2VTR;S2cS0S22VAInv;VCST;VXGL;VKc;S41VCST;R6R5A3R6R5R4S21S83AaS82R3R2A5S42S0S8aR3R2S54VAInv;VCST;VXGL;VKc;S41VCST;A1S21S62R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CHF : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2VTR;S2cS0S22VAInv;VCST;VXGL;VKc;S40R6R5A2R6R5R4S21S81AaS80R3R2A5S42S0S7fR3R2S54VAInv;VCST;VXGL;VKc;S40S21S61R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma tblB_call : ltac2:(tb__ "0|3|
S1cS1S2S11S11A2M0A1SfS10S10S3cS13S14R2A1S12S1dR5A1A1A3S34S6S9eS12S1dR6A1A1A1S5A3S34S6S3bS13S19S17S1aP1eA1M1S16Z7fffff800000A1A2A1S12S1dR7A1A1A3S5A3S34S6S3bS13S19S17S16Z7fff7f800000A1G1A2A1S12S1dR8A1A1A3S5A3S34S6S9bS85R7A2S5A3S4eR8R7R6A3S55VCST;Vrho0;VFB;VFF;R8RaS36R7A8S3aG0S3S11S11S86S9cZ10S87A2A4RbA3S35S34SeS53RaS86A2Z0A3A1S37RbA1M2G2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fn;Fkept;FA;").
Proof.
  intros A kept n rho rho' HF CLN C30 C30a Hn Hag HK Hin Hdnz HPHI.
  pose proof (holds_mem _ _ _ HF C30) as HtB. rewrite h_ule, uval_lit in HtB by lia.
  pose proof (holds_mem _ _ _ HF C30a) as HtA. rewrite h_ule, uval_lit in HtA by lia.
  destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
  apply (tblB_kept rho rho' (V_B_agree_ge n rho rho' Hn Hag)); [| exact HiC | exact HcK | exact HPHI].
  apply (keptK_lines CST FB FF rho0 rho kept frL rho' HK Hin Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia].
Qed.

Lemma nnPhi_holds : ltac2:(tb__ "0|0|
S10S1S1fQ40A1A1S1S3fA1S3eS3cS13S14R4A1S12S1dS67A1A1A3VJAv;S2aS76S36S6eS28S73S5A2A4R5R4R3R2A5S14R6S70A2F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md HF (Ai & kc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBU & _).
  cbn [nd_bd] in HBU. destruct HBU as (_ & _ & _ & _ & _ & _ & Hnn & _).
  assert (Hin : In (nth 14 brest_go (BIc 0 0 0)) brest_go) by (apply (nth_error_In _ 14); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (Forall_forall _ _) Hnn _ Hin) as N0.
  change (nth 14 brest_go (BIc 0 0 0)) with (PHIe 128 (t_c (v_sh vsP)) (t_k (v_sh vsP))) in N0.
  unfold PHIe in N0. cbv beta iota delta [bival lfval aval bi_f bi_c] in N0.
  fact HF (SPUle (kb 128 (t_k (v_sh vsP))) (SLit 4294967295)) F1. fact HF (SPUle (t_c (v_sh vsP)) (t_k (v_sh vsP))) F2. fact HF (SPUle (t_k (v_sh vsP)) (SLit 4294967295)) F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F1, F3 by lia.
  pose proof (uval_range rho (t_c (v_sh vsP))) as Rc. pose proof (uval_range rho (kb 128 (t_k (v_sh vsP)))) as Rk.
  assert (Ec : uval rho (kb 128 (t_c (v_sh vsP))) = 128 * uval rho (t_c (v_sh vsP))) by (unfold kb; apply uval_mul_lit; lia).
  rewrite uval_lit in N0 by lia.
  unfold nnPhi. rewrite h_ule.
  rewrite (uval_mul_lit rho 4 (kb 128 (t_k (v_sh vsP)))) by lia.
  rewrite uval_add_small; rewrite ?uval_lit by lia; rewrite ?(uval_mul_lit rho 6 (kb 128 (t_c (v_sh vsP)))) by lia; lia.
Qed.

Lemma site_fs : ltac2:(tb__ "0|4|
S10S1S1fQ40A1A1M0S2fS37R3A1M1S1cS20S10G0S3aS2S1cS20A2M2S3S1cS20R4R3A4S7G2S3S1cS20S6aS7dA4S7G2S3S1cS20S6bS7eA4S7G2S3S1cS20S69S7cA4SbG2A1A3A3A3A3G1S3cS13S14RaA1S12S1dS63A1M3A1A3S4eS15G3A1RbR5A3VTR;S2cS0VJAv;R7A1R8R6R5A5RaA2F_;F_;F_;F_;Ftp';Frho';Fnd;FT;VTR;S2cS0VJAv;S6fA1S66R5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HPHI HKont.
  pose proof ago_checks2 as (_ & _ & Cxf & Cfeq & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnh).
  pose proof ago_checks3 as (_ & _ & _ & _ & _ & CLN & _).
  set (ndv := NDA tv_fs frL brest_go (AHead qH1 true)).
  apply (TR_pre (SPA segs (JAv ndv) E_fs rho tp)).
  { intros w Hw. rewrite <- Cfeq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_fs rho E_fs0 E_fs1 tp w Cxf).
      unfold ndv, tv_fs. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL brest_go _ E_fs0 rho tp w Cptv Hw).
    -
      intros tr md HJ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor].
      exact (nnPhi_holds rho tp tr md HF1 HJ). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_fs HF CLN HTK HZ). unfold tv_fs. apply in_or_app. left. exact lines_in_kept_fs. }
  intros Hdnz.
  unfold ndv, tv_fs.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX FSP.P0_fs PTrue (fun _ H => H) (fun _ _ _ H => H)
           FS.Pre_fs FS.nd0 PDk_fs FS.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_fs s_fs R_fs Xk_fs rho tp kept_fs passed_fs frL brest_go brest_fs (AHead qH1 true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - unfold payA. apply (pay_okF_split _ _ _ _ brest_go _ bdrest_fs payX_fs payY_fs PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_fs rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : tblB rho').
    { apply (tblB_call E_fs kept_fs _ rho rho' HF CLN ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Cnh Hag HK lines_in_kept_fs Hdnz HPHI). }
    pose proof ago_checks2_nd as (Cndn & Cndo & Cndz & CTn & CTo & CTf & CTz & Bn & Bo & Bz & Tin & Tio & Tiz & Pn & Po & Pz & CABS & _).
    cbn [PDk_fs liftPD FSP.PD_fs map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTn, Cndn.
      apply (TR_pre (SPA segs (JAv nd_fs_nop) T_fs_nop rho' tp')).
      { intros w Hw. rewrite <- Tin. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_nop) (xfb_fs T_fs_nop0) rho' T_fs_nop0 B_fs_nop tp' w Bn Hw). }
      apply TR_facts. intros HFn. pose proof ago_checks_pay2 as (Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_nopX) T_fs_nop rho' tp')).
      { intros w Hw. unfold nd_nopX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_nop tvL frL bdX_nop (AHead qHn true) T_fs_nop rho' tp' w Pn).
        unfold nd_fs_nop in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_nop frL (AHead qHn true) bd_fs_nop comm_nop Xs_nop Ys_nop bdX_nop _ T_fs_nop rho' tp' w Q1 Q2 HFn QPay Hw). }
      apply (HKont T_fs_nop nd_nopX rho' tp'); [left; reflexivity | exact HPHI' | exact HF | exact Hag].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_fs_ok) T_fs_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_ok) (xfb_fs T_fs_ok0) rho' T_fs_ok0 B_fs_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof ago_checks_pay2 as (_ & _ & _ & _ & Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_okX) T_fs_ok rho' tp')).
      { intros w Hw. unfold nd_okX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_ok tvL_ok frL bdX_ok (AHead qHk true) T_fs_ok rho' tp' w Po).
        unfold nd_fs_ok in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_ok frL (AHead qHk true) bd_fs_ok comm_ok Xs_ok Ys_ok bdX_ok _ T_fs_ok rho' tp' w Q1 Q2 HFo QPay Hw). }
      apply (HKont T_fs_ok nd_okX rho' tp'); [right; left; reflexivity | exact HPHI' | exact HF | exact Hag].
    +
      rewrite CTf. apply TR_facts. intros HFf. exfalso.
      pose proof (holds_mem _ _ _ HFf CABS) as FA. cbn [holds f_absurd] in FA. apply FA. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    +
      rewrite CTz, Cndz.
      apply (TR_pre (SPA segs (JAv nd_fs_fz) T_fs_fz rho' tp')).
      { intros w Hw. rewrite <- Tiz. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fs_fz) (xfb_fs T_fs_fz0) rho' T_fs_fz0 B_fs_fz tp' w Bz Hw). }
      apply TR_facts. intros HFz. pose proof ago_checks_payf2 as (Q1 & Q2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_fzX) T_fs_fz rho' tp')).
      { intros w Hw. unfold nd_fzX.
        apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_fz tvL frL bd_fzX (AHead qHz false) T_fs_fz rho' tp' w Pz).
        unfold nd_fs_fz in Hw.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fs_fz frL (AHead qHz false) bd_fs_fz commf_fz Xf_fz Yf_go bd_fzX _ T_fs_fz rho' tp' w Q1 Q2 HFz QPay Hw). }
      apply (HKont T_fs_fz nd_fzX rho' tp'); [right; right; left; reflexivity | exact HPHI' | exact HF | exact Hag].
Qed.

Hypothesis CUTV : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S3aS2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7bA3S48S77R7R5A3S33S56Z0S47S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S57G4R4A2A2VTR;S2cS0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_go : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0VTR;S2cS0VJAFv;S37S59A2S5eR3R2A5VFAM;S47S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S5eS59A4U1A4S3SeS11S5aS5bZ11S5cA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof ago_checks1 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Ctv & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof ago_checks3 as (_ & _ & CLN & _).
  set (ndv := NDA tv_go frL (bdA A1) (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_go rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_go rho E_ir E_go tp w Cxf). unfold ndv. rewrite Ctv. exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_go HF CLN HTK HZ). unfold tv_go. apply in_or_app. left. exact lines_in_kept_go. }
  intros Hdnz.
  unfold ndv, tv_go.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (IRP.P0_ir CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           IR.Pre_ir IR.nd0 PDk_go NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHI eq_refl
           E_go s_go R_go Xk_go rho tp kept_go passed_go frL (bdA A1) brest_go (AHead pH true) (FAM (efmeasA (E_ir, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - unfold payA. apply (pay_okF_split _ _ _ _ (bdA A1) _ bd_rest payX_go payY_go PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_go rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : tblB rho').
    { apply (tblB_call E_go kept_go (ss_next (ax_S E_go)) rho rho' HF CLN ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(rewrite Cnx; reflexivity) Hag HK lines_in_kept_go Hdnz HPHI). }
    rewrite Cnx in Hag.
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof ago_checks1_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & _).
    cbn [PDk_go liftPD IRP.PD_ir map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_go_f) T_go_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_go_f) (xfb_go T_go_f0) rho' T_go_f0 B_go_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof ago_checks_payf1 as (QP1 & QP2 & QPay & _).
      apply (TR_pre (SPA segs (JAv nd_go_fX) T_go_f rho' tp')).
      { intros w Hw. unfold nd_go_fX, nd_go_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_go_f frL (AHead pH false) bd_go_f commf_go Xf_go Yf_go bd_go_fX _ T_go_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_go_f nd_go_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_ir T_go_f ndA1 nd_go_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_go_ok) T_go_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_go_ok) (xfb_go T_go_ok0) rho' T_go_ok0 B_go_ok tp' w Bo Hw). }
      apply (CUTV T_go_ok nd_go_ok 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_ir T_go_ok ndA1 nd_go_ok 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2bS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S98S0S97VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S5dA2S84R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2f : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S89A2S88R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHI_T : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2S31S0Vok;S2cS0S22VAInv;VCST;VXGL;VKc;S41VCST;R6R5A3R6R5R4S21S83AaS82R3R2A5S42S0S8aR3R2S54VAInv;VCST;VXGL;VKc;S41VCST;A1S21S62R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_go.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (IRP.P0_ir CST) PTrue IR.Pre_ir IR.nd0 IRP.PD_ir NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (IRP.intern_rest_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma CHF_T : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2S31S0Vok;S2cS0S22VAInv;VCST;VXGL;VKc;S40R6R5A2R6R5R4S21S81AaS80R3R2A5S42S0S7fR3R2S54VAInv;VCST;VXGL;VKc;S40S21S61R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs.
  eapply (sum_PostsC_k segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (FSP.finalize_shape_sum AInv CST XGL ALA HCST HXGL HTOP Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S3aS2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7bA3S48S77R7R5A3S33S56Z0S47S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S57G4R4A2A2S31S0Vok;S2cS0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsG) (map efdrop exitsG) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertG_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsG In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_fs (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHF_T rho1 tp1 _ HP1).
    intros T' nd'' rho' tp' HinT HP' _ _.
    apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsG) T' nd'' 1%nat (FAMQ tp0') rho' tp'); [| exact HP'].
    cbn [In] in HinT. destruct HinT as [E|[E|[E|[]]]]; injection E as <- <-; cbn [map efdrop cutsG fst snd In]; tauto.
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2f rho1 tp1 tp0')].
Qed.

Theorem arm_go_T : ltac2:(tb__ "0|1|
S10S1S1fQ40A1A1M0G0S31S0Vok;S2cS0VJAFv;S37S59A2S5eR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_go (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHI_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S99S0S97VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SeS1S1fQ40A1A1S2fF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SeSeS1S1fQ40A1A1S32S56R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S5dA2S84R3R2A5VFAM;S47S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S84S5dA4U1A4S3SeS11S5aS5bZ1S5cA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2f : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S89A2S88R3R2A5VFAM;S47S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S88S89A4U1A4S3SeS11S5aS5bZ1S5cA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHI_E : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2S30S0S2cS0S22VAInv;VCST;VXGL;VKc;S41VCST;R6R5A3R6R5R4S21S83AaS82R3R2A5S42S0S8aR3R2S54VAInv;VCST;VXGL;VKc;S41VCST;A1S21S62R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_go.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (IRP.P0_ir CST) PTrue IR.Pre_ir IR.nd0 IRP.PD_ir NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (IRP.intern_rest_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma CHF_E : ltac2:(tb__ "0|1|
S1S2SeSeA2M0A1S1S2G0SeA2A1S52S10S1S1fQ40A1A1S51Z5R3A2S30S0S2cS0S22VAInv;VCST;VXGL;VKc;S40R6R5A2R6R5R4S21S81AaS80R3R2A5S42S0S7fR3R2S54VAInv;VCST;VXGL;VKc;S40S21S61R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (FSP.finalize_shape_sum_ex AInv CST XGL ALA HCST HXGL HTOP Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S1cS20S4S2SeS11A2M0S10S1S1fQ40A1A1M1SeG1S3aS2S2S2S1cS20A2M2S4A2M3G0A2S3G3G0S3G2S4S3S1cS20R8R7A4R6A4R5A4S7bA3S48S77R7R5A3S33S56Z0S47S3G3G0S3G2S4S3S1cS20RaR9A4R8A4R7A4R6A2M4A2S57G4R4A2A2S30S0S2cS0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsG exitsG (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertG_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsG In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    apply (site_fs (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs) CHF_E rho1 tp1 _ HP1).
    intros T' nd'' rho' tp' HinT HP' HF Hag.
    pose proof ago_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cnh).
    assert (E460 : rw rho' 460%positive = rw rho1 460%positive) by (symmetry; apply (proj1 Hag); apply Pos.leb_le in Cnh; unfold HNEXT in Cnh; lia).
    assert (E467 : rw rho' 467%positive = rw rho1 467%positive) by (symmetry; apply (proj1 Hag); apply Pos.leb_le in Cnh; unfold HNEXT in Cnh; lia).
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
    fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    cbn [In] in HinT. destruct HinT as [E|[E|[E|[]]]]; injection E as <- <-.
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_nop nd_nopX 1%nat (RL, VLA 5 z0));
        [right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_nop nd_go_ok nd_nopX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_ok nd_okX 1%nat (RL, VLA 5 z0));
        [right; right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_ok nd_go_ok nd_okX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsG T_fs_fz nd_fzX 1%nat (RL, VLA 5 z0));
        [right; right; right; right; left; reflexivity | exact HP' |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_fs0 T_fs_fz nd_go_ok nd_fzX 1%nat 1%nat); [exact E460 | exact E467 | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2f rho1 tp1 tp0')].
Qed.

Theorem arm_go_E : ltac2:(tb__ "0|2|
S10S1S1fQ40A1A1M0G0S30S0S2cS0VJAFv;S37S59A2S5eR3R2A5VFAM;S47S3S2S2S1cS20A2M1S4A2S2SeS11A2S3G1S4S3S1cS20S5eS59A4U1A4S3SeS11S5aS5bZ11S5cA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_go (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHI_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

End Lib_load_obj_ago_pf.

