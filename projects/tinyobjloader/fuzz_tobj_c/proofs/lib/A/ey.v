(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_039.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu ew.

(* [comment removed for export] *)
Module Lib_handle_f_g5c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "sv_eqb"; "ss_facts"; "SAlu"; "SPUle"; "sv_below"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "lDmm"; "lKmm"; "pL"; "cMM"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "pair"; "prod"; "app"; "list"; "andb"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "E_mm4"; "s_mm4"; "T_mm4f"; "E_mm4_0"; "R_mm4"; "JR_mm4"; "T_mm4g"; "T_mm4k"; "JF_mm4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "kept_mm4"; "brest_mm4"; "E_mm41x"; "T_mm4k1"; "s_mm4g"; "s_mm4k"; "land_chk"; "T_mm4f0"; "T_mm4g0"; "T_mm4k0"; "bd2_mm4g"; "bd2_mm4k"; "bdG_mm4"; "bdK_mm4"; "s_mm4f"; "xff_chk"; "liveF"; "reopen_chk"; "tv2_mm4f"; "tv2_mm4g"; "tv2_mm4k"; "vlF"; "vrLF"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndL4c"; "ndL4b"; "ndL4cf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "NMM"; "vr_need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "XnoLoc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pA"; "mm_c"; "mm_n"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_mm41x_eq : ltac2:(tb__ "0|0|
SaS19S1aA1S58S20S62U11Z230A2A2S18S1aS36A2A3"). Proof. vmr. Qed.
Lemma E_mm4_eq2 : ltac2:(tb__ "0|0|
SaS1aS63S56Z4S6S5eSeSdA1S1Z1A1A3S55S5fA1A3S36A2S1dA3"). Proof. vmr. Qed.
Lemma mm4_xff : ltac2:(tb__ "0|0|
SaSfS43S36S56Z4S6S5eSeSdA1S1Z1A1A3S55S5fA1A3A2S10A3"). Proof. vmr. Qed.
Lemma mm4_needF : ltac2:(tb__ "0|0|
SaSfS4aZ4Z1Z8S60S61S5S1bS36A1A1A6S10A3"). Proof. vmr. Qed.
Lemma mm4_tvp : ltac2:(tb__ "0|1|
SaSfS66S4fS51A1S15S14S0S0A2M0S34S11G0S13S0S0SbS26Z4ScA2A4S12G0A1A3A3A2S10A3"). Proof. vmr. Qed.
Lemma mm4_chk : ltac2:(tb__ "0|0|
SaSfS4bVXGL;S1dS34SbScZ4Z230S4eS51A1S35S1eS21S53SbS1cS20A1A2AcS10A3"). Proof. vmr. Qed.
Lemma mm4_iK : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4dS1eS2aS2cS1dA4S2eA2S11G0S13S0S0SbS26Z4ScA2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma mm4_iF : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4dS1eS2aS2dS1dA4S2eA2S11G0S13S0S0SbS26Z4ScA2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma mm4_iG : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4dS1eS2aS2bS1dA4S31A2S11G0S13S0S0S2P230A1S26Z4S2P231A1A2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma mm4_bK : ltac2:(tb__ "0|0|
SaS16S28A1S29S4dS1eS2aS2cS1dA4S4eS30A1A2S41A3"). Proof. vmr. Qed.
Lemma mm4_bG : ltac2:(tb__ "0|0|
SaS16S28A1S29S4dS1eS2aS2bS1dA4S2fS33S32A2A2S40A3"). Proof. vmr. Qed.
Lemma T_mm4k0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2aS1dS1eS21S2cS53SbS1cS20A1A2A6S3dA3"). Proof. vmr. Qed.
Lemma T_mm4k1_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S58S3dS54U10U1eZ230A3A2S18S1aS37A2A3"). Proof. vmr. Qed.
Lemma T_mm4k_eq2 : ltac2:(tb__ "0|0|
SaS1aS63S11S3S7S1S64A1SbA2S12S3A1A3S37A2S24A3"). Proof. vmr. Qed.
Lemma mm4k_xff : ltac2:(tb__ "0|0|
SaSfS43S37S11S3S7S1S64A1SbA2S12S3A1A3A2S10A3"). Proof. vmr. Qed.
Lemma mm4k_land : ltac2:(tb__ "0|1|
SaSfS3aS24S22S39S15S14S0S0A2M0S34S11G0S13S0S0SbS26Z4ScA2A4S12G0A1A3A3S48S15S28S41S35A3S3fS4fS50A1A8S10A3"). Proof. vmr. Qed.
Lemma mm4k_bd : ltac2:(tb__ "0|0|
SaS16S28A1S29S39S4eS50A1A2S3fA3"). Proof. vmr. Qed.
Lemma mm4k_live : ltac2:(tb__ "0|0|
SaSfS44SeSdA1Z1ScS5S1bS37A1A1A4S10A3"). Proof. vmr. Qed.
Lemma T_mm4f0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2aS1dS1eS21S2dS53SbS1cS20A1A2A6S3bA3"). Proof. vmr. Qed.
Lemma T_mm4f_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S58S3bS54U10U1eZ230A3A2S18S1aS1fA2A3"). Proof. vmr. Qed.
Lemma mm4f_ro0 : ltac2:(tb__ "0|1|
SaSfS45VXGL;S1fS59S1fA1S15S14S0S0A2M0S34S11G0S13S0S0SbS26Z4ScA2A4S12G0A1A3A3Z1cZ21A6S10A3"). Proof. vmr. Qed.
Lemma mm4f_ro1 : ltac2:(tb__ "0|2|
SaSfS65VXGL;S5cS1fS59S1fA1M0S27Z1cZ21A5G0S15S14S0S0A2M1S34S11G1S13S0S0SbS26Z4ScA2A4S12G1A1A3A3Z26Z27A6S10A3"). Proof. vmr. Qed.
Lemma mm4f_land : ltac2:(tb__ "0|3|
SaSfS3aS5cS5cS1fS59S1fA1M0S27Z1cZ21A5G0S27Z26Z27A5S25S42S15S14S0S0A2M1S34S11G1S13S0S0SbS26Z4ScA2A4S12G1A1A3A3S46S5dS28U1S35A3M2G2S4fS52A1A8S10A3"). Proof. vmr. Qed.
Lemma mm4f_bd : ltac2:(tb__ "0|0|
SaS16S28A1S29S42S4eS52A1A2S5dS28U1S35A3A3"). Proof. vmr. Qed.
Lemma T_mm4g0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2aS1dS1eS21S2bS53SbS1cS20A1A2A6S3cA3"). Proof. vmr. Qed.
Lemma T_mm4g_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S58S3cS54U10U1eZ230A3A2S18S1aS23A2A3"). Proof. vmr. Qed.
Lemma mm4g_land : ltac2:(tb__ "0|1|
SaSfS3aS23S22S38S15S14S0S0A2M0S34S11G0S13S0S0S2P230A1S26Z4S2P231A1A2A4S12G0A1A3A3S47S15S28S40S35A3S3eS4fS50A1A8S10A3"). Proof. vmr. Qed.
Lemma mm4g_bd : ltac2:(tb__ "0|0|
SaS16S28A1S29S38S4eS50A1A2S3eA3"). Proof. vmr. Qed.
Lemma mm4f_wp : bd_wpos brest_mm4 = true. Proof. vmr. Qed.
Lemma mm4_vlF : ltac2:(tb__ "0|0|
SaSfS49S5S1bS20A1A1A1S10A3"). Proof. vmr. Qed.
Lemma mm4_meas : ltac2:(tb__ "0|1|
SaSfS17S17S17S17S17S4S57S39S4cA2S4cA2S4S57S39SdA2SdA2A2S4S57S38S4cA2S4cA2A2S4S57S38SdA2SdA2A2S8S9S1bS1dA1A1M0S4cA2A2S8G0SdA2A2S10A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g5c.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "nat"; "None"; "negb"; "prod"; "Some"; "cons"; "nil"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "div"; "modulo"; "add"; "eqb"; "ltb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "fr_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "bF"; "feF"; "fF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "local_okP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "ss_facts"; "sv"; "sv_eqb"; "swf"; "dflt_writable"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xlocal"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.Lists.List"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "is_shx"; "xloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ANone"; "NDA"; "nd_below"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_shx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx.

Definition releaseP_chk (A : axst) (objs : list sobj) (k1 k2 : Z) (cells : list cell) (d : odefault) (L : list (Z * Z)) (tv : list (sv * sv)) (bd : list bitem) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S0S0S21S12VA;A1S1dS2aA1A2S9Z0Vk1;A2A2S9Vk1;Vk2;A2A2S9Vk2;Z40A2A2S23Vd;A1A2S18S1fS11VA;A1M0A1M1A1A2S2cS4SfSfA2S1cVcells;Vd;Vk1;Vk2;A4VL;A3A2S31S24G0A1S30Vtv;S10Vbd;S2fA4A2A2S17G1A1A2S27G1Vtv;S10S2S1A1S15Vobjs;A6A2").

Definition reopenC_chk (XGL : list (Z * Z)) (A : axst) (X' : list (sv * sv)) (tv : list (sv * sv)) (k1 k2 off len : Z) : bool := ltac2:(tb__ "0|a|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S21S12VA;A1S1dS2aA1A2S9Z0M0Vk1;A2A2S9Vk1;Vk2;A2A2S9Vk2;Z40A2A2S18S1fS11VA;A1M1A1M2A1A2S26VX';S13VA;A1M3A2A2S26S6S4S20S20A2M4S28Pa0S8SfSfVoff;Vlen;A4A2S7G4A1A3G3A2A2S9G0Voff;A2A2SdSbVoff;Z8M5A2G0A2A2S9Z1M6Vlen;A2A2S9G6SbScVoff;Vlen;A2M7G5A2M8A2A2S9G7Z200A2A2S9Vk1;SaVoff;G5A2A2A2SeSaG7G5A2Vk2;A2A2S22S11S1bVA;VX';S14Vk1;Vk2;S1aVoff;Vlen;G0A3A6A1A1A2S22S11S1bVA;VX';S14Vk1;Vk2;S1aVoff;Vlen;G8A3A6A1A1A2S17G2A1A2S19G2A1A2S27G2Vtv;S10S2S1A1S15S2bS1eS1eS3S2dVk1;Vk2;R1A3A1Lo;S25G1A1M9A3A6A2S29VXGL;G2Vtv;S10S5S1U0A2G9S16S2bG4G4S3S2eVk1;Vk2;R1A3A1Lr;VX';A3A8A2").
End Lib_handle_f_gdefs5.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "cons"; "nil"; "prod"; "app"; "fst"; "pair"; "None"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "sprop_eqb"; "sv_eqb"; "SLit"; "sv"; "SAlu"; "SVar"; "ss_facts"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "s_pg"; "Xk_pg"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "nd_bd"; "nd_below"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "NPH"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "fr_hf"; "xfo"; "pA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs4"; "E_pgF"; "PD_pgF"; "Pre_pgF"; "R_pgF"; "P_invF"; "P_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDrp"; "pDts"; "pKts"; "needA"; "pKrp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2.PGC"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "bF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2.

Definition Pre_pgS : axst := Eval vm_compute in optAp (apply_axforms PG.Pre_pg [AXSplit 3 (SLit 16)]).
Definition xF (r : sv * sv) : list sprop := ltac2:(tb__ "0|4|
S1SaSbS10S1dS5SfSfVr;A3M0S9SfSfVr;A3M1A3SeS3eZ2M2Z2fA2A1M3A2S1SaSbG1SeS3eG2Z28A2A1A2S1SaSbG0G3A2S2SaA1A3A3A3").

Definition X_pgF : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (xr_post_ok PG.P_ok [] r)) (ax_X PG.P_ok).
Definition F_pg : list sprop := Eval vm_compute in flat_map xF X_pgF.
Definition Pre_pgF : axst := Eval vm_compute in ax_add_facts F_pg Pre_pgS.
Definition P_okF : axst := Eval vm_compute in ax_add_facts F_pg PG.P_ok.
Definition P_invF : axst := Eval vm_compute in ax_add_facts F_pg PG.P_inv.
Definition PD_pgF : list (axst * ndesc) := ltac2:(tb__ "0|1|
S1S3S1aS1eA2M0S6S1aS1eS2eS37A4S1G0S6S1aS1eS2fS37A4S2G0A1A3A3").

Definition E_pgS : axst := Eval vm_compute in optAp (apply_axforms E_pg [AXSplit 5 (SLit 16)]).
Definition F_pgC : list sprop := Eval vm_compute in subst_facts s_pg F_pg.
Definition E_pgF : axst := Eval vm_compute in ax_add_facts F_pgC E_pgS.
Definition R_pgF : list sobj := Eval vm_compute in optR (entails_frA E_pgF Pre_pgF s_pg).
Definition T_pgo0F : axst := Eval vm_compute in T_afterA3 Pre_pgF E_pgF s_pg R_pgF P_okF Xk_pg.
Definition T_pgi0F : axst := Eval vm_compute in T_afterA3 Pre_pgF E_pgF s_pg R_pgF P_invF Xk_pg.

Definition facts_sub (F G : list sprop) : bool := ltac2:(tb__ "0|0|
S18SaSaS17SaScR1A1VG;A3Lp;VF;A3").

Definition pg_call_chkF (XGL : list (Z * Z)) : bool := ltac2:(tb__ "0|7|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S49S16S1cS2aA1A2S46S2aS2cS15S2dS3fS3S1aS1eA2S1aS5S1aS1eA2S2bA4A5A2S4aS25S15A2A2S45S15S39A2A2S4dS25S13S1bS2aA1M0A1M1A2A2S22G1S20S4S3SfSfA2M2S23S38A1M3S2G2A1A3S27S4S3aS3cS15S2S3aA1A2S21S38A1M4A3S1fA4A2A2S3bG1G4A2A2S3dG4A1A2S18S48S47S2cS39S15G1A4S2bA3A2S42S12G0A1M5A1A2S4cG5G3S27S7S8A1M6S40S2dA6A2S4bVXGL;G5G3S27G6S14G0A1S41S16A8A2SdS19S15PcA2S28Z30A1A2A2SdS19S15PdA2S28Za0A1A2A2SdS19S15PeA2S29A2A2SdS19S15PfA2S32A2A2SdS19S15P10A2S30A2A2SdS19S15P11A2S33A2A2SdS19S15P12A2S35A2A2S43G5A1A2").

Definition pgEF (F : list sprop) : bool := ltac2:(tb__ "0|3|
S0S0S0S0S0S0S0S0S17SaScSbS10S1dS32S24Z4M0S36A2A3S11P1eA1M1A2A1VF;A3S17SaScSbS10S1dS30S24G0S31A2A3G1A2A1VF;A3A2S17SaScSbS10S1dS33S24Z1S34A2A3G1A2A1VF;A3A2S17SaScSbS10S1dS26SeZ200A1A3G1A2A1VF;A3A2S17SaScSbG1SeZ7fffff800000A1A2A1VF;A3A2S17SaScSbS32SeZ800000000000A1M2A2A1VF;A3A2S17SaScSbS30G2A2A1VF;A3A2S17SaScSbS26G2A2A1VF;A3A2S17SaScSbS34SeS44A1A2A1VF;A3A2").
End Lib_handle_f_gdefs4.

(* [comment removed for export] *)
Module Lib_handle_f_g7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "DUnknown"; "cell"; "ss_objs"; "ss_facts"; "ob_cells"; "ob_dflt"; "sprop"; "ss_next"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "true"; "cons"; "prod"; "app"; "list"; "Some"; "option"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_tv"; "nd_bd"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "shadow_release_stateA"; "shadow_reopen_stateA"; "release_objs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "ndEf"; "ndEo"; "co_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "release_chk"; "reopen_chk"; "feF"; "pure_chk"; "purec_chk"; "xff_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "XLJf"; "XEf6a1"; "XEf6b1"; "XEo61"; "XJ1"; "X_rlf1"; "X_rlo1"; "sh_f5f1"; "sh_f5o1"; "E_f5f1"; "E_f5o1"; "T_f5f1"; "T_f5o1"; "T_tdg2"; "T_wdg2"; "XLJ1"; "objs_Ef42"; "objs_Ef6a1"; "objs_Ef6b1"; "objs_Eo42"; "objs_Eo61"; "objs_J"; "carve_chk"; "objs_Ef6a"; "objs_Ef6b"; "objs_Eo6"; "objs_XJ"; "objs_f5f1"; "objs_f5o1"; "liveLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "E_f5f0"; "E_f5o0"; "NREL"; "XR"; "C_Ef2"; "XEf42"; "XEo42"; "C_Eo2"; "E_f5f"; "E_f5o"; "L_f5"; "Pre_f5"; "T_f5f0"; "T_f5o0"; "ilast"; "sel_rel"; "xf_shback"; "C_rlf"; "C_rlo"; "R_f5f"; "R_f5o"; "X_rlf"; "X_rlo"; "s_f5f"; "s_f5o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "release0_chk"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "XJ"; "XT"; "E_wdg"; "J"; "R_wdg"; "T_wdg"; "T_wdg0"; "s_wdg"; "sel_wdg"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndJN"; "ndLL"; "ndTR"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "XTR"; "pDtr"; "pKtr"; "E_tdg"; "R_tdg"; "T_tdg"; "T_tdg0"; "s_tdg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "XLJ"; "L14"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pKco"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "sel_da"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma tdg_chk : ltac2:(tb__ "0|0|
S0SbS2cS78S77S80S7bS84S81A6ScA3"). Proof. vmr. Qed.
Lemma T_tdg2_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS83SdS1aS1cS8bA1SdS1aS1dU0A1SaS1aA1A3A3A2S11S14S3cA2A3"). Proof. vmr. Qed.
Lemma T_tdg_eq2 : ltac2:(tb__ "0|0|
S0S14S88S3cS7dS7eS7fA2A2S82A3"). Proof. vmr. Qed.
Lemma tdg_xsub : ltac2:(tb__ "0|0|
S0SbS89S7dS7eS7fA2S16S3cA1A2ScA3"). Proof. vmr. Qed.
Lemma wdg_chk : ltac2:(tb__ "0|0|
S0SbS2cS78S77S6dS7cS72S6fA6ScA3"). Proof. vmr. Qed.
Lemma T_wdg2_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS71SdS1aS1cS73A1SdS1aS1dU0A1SaS1aA1A3A3A2S11S14S3dA2A3"). Proof. vmr. Qed.
Lemma T_wdg_eq2 : ltac2:(tb__ "0|0|
S0S14S88S3dS6cA2S70A3"). Proof. vmr. Qed.
Lemma wdg_xsub : ltac2:(tb__ "0|0|
S0SbS89S6cS16S3dA1A2ScA3"). Proof. vmr. Qed.

Lemma XJ_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S6bA1A1SfS1S49SdS1S22S19Z14Z17SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XJ_rel : ltac2:(tb__ "0|0|
S0SbS66S6bZ14Z17S2A4ScA3"). Proof. vmr. Qed.
Lemma XJ1_eq : ltac2:(tb__ "0|0|
S0S14S23S6bS49Pa0SaSeS18S18A2A1A4S33A3"). Proof. vmr. Qed.
Lemma XJ1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S33A1A1SfS1S44SdS1S22S19Z6ZfSaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XJ1_rel : ltac2:(tb__ "0|0|
S0SbS29S33S44Z6ZfSaS3A1S2SaSeS18S18A2A1S1fS79A1S20S79A1A9ScA3"). Proof. vmr. Qed.
Lemma J_eq2 : ltac2:(tb__ "0|0|
S0S14S23S33S44Pa0SaSeS18S18A2A1A4S6eA3"). Proof. vmr. Qed.

Lemma XLJ_xff : ltac2:(tb__ "0|0|
S0SbS2eS85SdS8S28SaS8A1A3A2ScA3"). Proof. vmr. Qed.
Lemma XLJ_live : ltac2:(tb__ "0|0|
S0SbS4cS8aS5S15S85A1A1A2ScA3"). Proof. vmr. Qed.
Lemma XLJ_ro0 : ltac2:(tb__ "0|0|
S0SbS2aVXGL;S2fS16S2fA1S1fS7aA1Z1cZ21A6ScA3"). Proof. vmr. Qed.
Lemma XLJ1_eq : ltac2:(tb__ "0|0|
S0S14S24S2fS16S2fA1S19Z1cZ21A5S3eA3"). Proof. vmr. Qed.
Lemma XLJ_ro1 : ltac2:(tb__ "0|0|
S0SbS67VXGL;S3eS16S2fA1S1fS7aA1Z26Z27A6ScA3"). Proof. vmr. Qed.
Lemma L14_eq2 : ltac2:(tb__ "0|0|
S0S14S24S3eS16S2fA1S19Z26Z27A5S86A3"). Proof. vmr. Qed.

Lemma XEf42_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S52A1A1SfS1S3fSdS1S22S19Z4Z5SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEf42_rel : ltac2:(tb__ "0|0|
S0SbS29S52S3fZ4Z5SaS3A1S2SaSeS18S18A2A1S1fS26A1S20S26A1A9ScA3"). Proof. vmr. Qed.
Lemma XEf42_eq2 : ltac2:(tb__ "0|0|
S0S14S23S52S3fPa0SaSeS18S18A2A1A4S51A3"). Proof. vmr. Qed.
Lemma XEo42_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S53A1A1SfS1S42SdS1S22S19Z4Z5SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEo42_rel : ltac2:(tb__ "0|0|
S0SbS29S53S42Z4Z5SaS3A1S2SaSeS18S18A2A1S1fS27A1S20S27A1A9ScA3"). Proof. vmr. Qed.
Lemma XEo42_eq2 : ltac2:(tb__ "0|0|
S0S14S23S53S42Pa0SaSeS18S18A2A1A4S54A3"). Proof. vmr. Qed.
Lemma XEf6a_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S68A1A1SfS1S46SdS1S22S19Z1cZ21SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEf6a_rel : ltac2:(tb__ "0|0|
S0SbS66S68Z1cZ21S2A4ScA3"). Proof. vmr. Qed.
Lemma XEf6a1_eq : ltac2:(tb__ "0|0|
S0S14S23S68S46Pa0SaSeS18S18A2A1A4S30A3"). Proof. vmr. Qed.
Lemma XEf6a1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S30A1A1SfS1S40SdS1S22S19Z26Z27SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEf6a1_rel : ltac2:(tb__ "0|0|
S0SbS29S30S40Z26Z27SaS3A1S2SaSeS18S18A2A1S1fS26A1S20S26A1A9ScA3"). Proof. vmr. Qed.
Lemma XEf6a_eq2 : ltac2:(tb__ "0|0|
S0S14S23S30S40Pa0SaSeS18S18A2A1A4S51A3"). Proof. vmr. Qed.
Lemma XEf6b_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S69A1A1SfS1S47SdS1S22S19Z26Z27SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEf6b_rel : ltac2:(tb__ "0|0|
S0SbS66S69Z26Z27S2A4ScA3"). Proof. vmr. Qed.
Lemma XEf6b1_eq : ltac2:(tb__ "0|0|
S0S14S23S69S47Pa0SaSeS18S18A2A1A4S31A3"). Proof. vmr. Qed.
Lemma XEf6b1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S31A1A1SfS1S41SdS1S22S19Z1cZ21SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEf6b1_rel : ltac2:(tb__ "0|0|
S0SbS29S31S41Z1cZ21SaS3A1S2SaSeS18S18A2A1S1fS26A1S20S26A1A9ScA3"). Proof. vmr. Qed.
Lemma XEf6b_eq2 : ltac2:(tb__ "0|0|
S0S14S23S31S41Pa0SaSeS18S18A2A1A4S51A3"). Proof. vmr. Qed.
Lemma XEo6_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S6aA1A1SfS1S48SdS1S22S19Z26Z27SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEo6_rel : ltac2:(tb__ "0|0|
S0SbS66S6aZ26Z27S2A4ScA3"). Proof. vmr. Qed.
Lemma XEo61_eq : ltac2:(tb__ "0|0|
S0S14S23S6aS48Pa0SaSeS18S18A2A1A4S32A3"). Proof. vmr. Qed.
Lemma XEo61_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S32A1A1SfS1S43SdS1S22S19Z1cZ21SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XEo61_rel : ltac2:(tb__ "0|0|
S0SbS29S32S43Z1cZ21SaS3A1S2SaSeS18S18A2A1S1fS27A1S20S27A1A9ScA3"). Proof. vmr. Qed.
Lemma XEo6_eq2 : ltac2:(tb__ "0|0|
S0S14S23S32S43Pa0SaSeS18S18A2A1A4S54A3"). Proof. vmr. Qed.

Lemma f5o_ro : ltac2:(tb__ "0|0|
S0SbS2aVXGL;S4eS50S4eA1S1fS27A1Z0Z40A6ScA3"). Proof. vmr. Qed.
Lemma E_f5o1_eq : ltac2:(tb__ "0|0|
S0S14S24S4eS50S4eA1S19Z0Z40A5S39A3"). Proof. vmr. Qed.
Lemma E_f5o_eq2 : ltac2:(tb__ "0|0|
S0S12S14A1S1bS39SdS1aS1eS5bS39A1S76A2SaS1aA1A3A2S11S14S56A2A3"). Proof. vmr. Qed.
Lemma f5o_chk : ltac2:(tb__ "0|0|
S0SbS2dVXGL;S58SdS14S57SaS14A1A3S56S1fS27A1S20S27A1S65S61A8ScA3"). Proof. vmr. Qed.
Lemma T_f5o1_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS5aS5dS5aA1A2S11S14S3bA2A3"). Proof. vmr. Qed.
Lemma T_f5o1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S3bA1A1SfS1S4bSdS1S37SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma sh_f5o1_eq : ltac2:(tb__ "0|0|
S0S1S37S22S19Z0Z40S6S37A1S7S37A1A5A3"). Proof. vmr. Qed.
Lemma f5o_carve : ltac2:(tb__ "0|0|
S0SbS45VXGL;S3bS4bS1fS27A1A4ScA3"). Proof. vmr. Qed.
Lemma T_f5o_eq2 : flag_carve_stateA T_f5o1 170 = T_f5o. Proof. vmr. Qed.
Lemma f5f_ro : ltac2:(tb__ "0|0|
S0SbS2aVXGL;S4dS50S4dA1S1fS26A1Z0Z40A6ScA3"). Proof. vmr. Qed.
Lemma E_f5f1_eq : ltac2:(tb__ "0|0|
S0S14S24S4dS50S4dA1S19Z0Z40A5S38A3"). Proof. vmr. Qed.
Lemma E_f5f_eq2 : ltac2:(tb__ "0|0|
S0S12S14A1S1bS38SdS1aS1eS5bS38A1S76A2SaS1aA1A3A2S11S14S55A2A3"). Proof. vmr. Qed.
Lemma f5f_chk : ltac2:(tb__ "0|0|
S0SbS2dVXGL;S58SdS14S57SaS14A1A3S55S1fS26A1S20S26A1S64S60A8ScA3"). Proof. vmr. Qed.
Lemma T_f5f1_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS59S5dS59A1A2S11S14S3aA2A3"). Proof. vmr. Qed.
Lemma T_f5f1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S3aA1A1SfS1S4aSdS1S36SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma sh_f5f1_eq : ltac2:(tb__ "0|0|
S0S1S36S22S19Z0Z40S6S36A1S7S36A1A5A3"). Proof. vmr. Qed.
Lemma f5f_carve : ltac2:(tb__ "0|0|
S0SbS45VXGL;S3aS4aS1fS26A1A4ScA3"). Proof. vmr. Qed.
Lemma T_f5f_eq2 : flag_carve_stateA T_f5f1 170 = T_f5f. Proof. vmr. Qed.

Lemma X_rlo1_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS63SdS1aS1cS5cA1SaS1aA1A3A2S11S14S35A2A3"). Proof. vmr. Qed.
Lemma rlo_chk : ltac2:(tb__ "0|1|
S0SbS13S13S25Pa0PaaS19Z3S75S1S4fS4S15S35A1M0A1A3A5S2bS5G0A1A1A2S21S9G0A1S27A2A2ScA3"). Proof. vmr. Qed.
Lemma C_rlo_eq2 : ltac2:(tb__ "0|1|
S0S14S17S35S87S15S35A1M0S74S1S4fS4G0A1A3A2A2S5fA3"). Proof. vmr. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS62SdS1aS1cS5cA1SaS1aA1A3A2S11S14S34A2A3"). Proof. vmr. Qed.
Lemma rlf_chk : ltac2:(tb__ "0|1|
S0SbS13S13S25Pa0PaaS19Z3S75S1S4fS4S15S34A1M0A1A3A5S2bS5G0A1A1A2S21S9G0A1S26A2A2ScA3"). Proof. vmr. Qed.
Lemma C_rlf_eq2 : ltac2:(tb__ "0|1|
S0S14S17S34S87S15S34A1M0S74S1S4fS4G0A1A3A2A2S5eA3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g7.

(* [comment removed for export] *)
Module Lib_handle_f_g6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "DUnknown"; "cell"; "mkObj"; "SAlu"; "ss_facts"; "ss_next"; "sprop"; "ss_objs"; "obj_wf"; "sprop_eqb"; "SPUle"; "SVar"; "sv_below"; "SPUlt"; "SMd"; "sstate"; "SExt"; "mkCell"; "swf"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "true"; "cons"; "Some"; "option"; "andb"; "list"; "prod"; "app"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hF"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pDco"; "reshapeA"; "pA"; "fv_c"; "pKco"; "fv_n"; "L_ms"; "Pre_ms"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "L_mc1"; "Pre_mc"; "pDfv"; "E_mc1"; "T_mc0"; "E_mc"; "R_mcf"; "s_mcf"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "fF"; "purec_chk"; "rsFk"; "vlF"; "gF"; "xff_chk"; "release_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_tv"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "off_c4"; "off_g1"; "off_g2"; "off_g3"; "off_m4"; "E_c4b"; "E_g1b"; "E_g2b"; "E_g3b"; "E_m4b"; "T_c4t"; "T_g1u"; "T_g2u"; "T_g3u"; "T_m4t"; "E_c4a"; "E_g1a"; "E_g1c"; "E_g2a"; "E_g2c"; "E_g3a"; "E_g3c"; "E_m4a"; "T_c4u"; "T_g1t"; "T_g2t"; "T_g3t"; "T_m4u"; "T_g3w"; "E_mdx"; "T_c4v"; "T_g1v"; "T_g2v"; "T_g3v"; "T_m4v"; "cells_g1a"; "cells_md"; "E_c4c"; "E_m4c"; "cells_g1b"; "cs_md"; "xf_c4"; "xf_g1"; "xf_g2"; "xf_g3"; "xf_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "g_need"; "pL"; "s_g"; "E_g1"; "E_g2"; "E_g3"; "E_g1_0"; "E_g1_3"; "E_g2_0"; "E_g3_0"; "R_g1"; "R_g2"; "R_g3"; "sel_g"; "cFV"; "cMI"; "T_g1"; "T_g2"; "T_g3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndLL"; "ndTS"; "ndFV"; "ndL4a"; "ndL4b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "pDf4"; "pDm4"; "E_c4"; "E_m4"; "R_c4"; "R_m4"; "s_c4"; "s_m4"; "E_c4_0"; "E_m4_0"; "pKf4"; "pKm4"; "T_c4"; "T_m4"; "sel_c4"; "sel_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_g6.G"; "E_g1_1x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "objs_butlast"; "E_md0"; "T_md2"; "T_md1"; "E_md"; "T_md3"; "E_md1"; "R_md"; "T_md0"; "s_md"; "xf_md"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "shadow_release_stateA"; "shadow_reopen_stateA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "release0_chk"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma mc_o32 : ltac2:(tb__ "0|2|
S0S1bS2A1S39S2SaS23S3eA1A1U20A3S1aS2S5S3dS2fZ4M0S34A2M1S6S26G1S1G0A1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma mc_wf : ltac2:(tb__ "0|1|
S0S17SbS8S23S3eA1A1S5S6S26S3dS11S27S34S1Z4A1M0A3A3S1Z0A1G0S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma mc_bnd : ltac2:(tb__ "0|0|
S0S17S48S3dS34S36S7S23S3eA1A1A4S18A3"). Proof. vmr. Qed.
Lemma mc_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S40S4dS92A1S4eS92A1S42S41A8S18A3"). Proof. vmr. Qed.
Lemma mc_to1 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S3fA1A1U1A3S1aS2S5S6S26S3dS11S27S34S1Z4A1M0A3A3S1Z0A1G0S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma mc_twf : ltac2:(tb__ "0|2|
S0S17SbS8S23S3fA1A1S5S3dS2fZ4M0S34A2M1S6S26G1S1G0A1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma mc_tbnd : ltac2:(tb__ "0|0|
S0S17S48S3dS34S36S7S23S3fA1A1A4S18A3"). Proof. vmr. Qed.

Lemma md_robjs : ltac2:(tb__ "0|0|
S0S1dS2A1SaS23Sa7A1A1S1fS2Sa6Sa7A1S19S2Sb6S30Z6ZfS73S3A5S16S2A1A3A3A3"). Proof. vmr. Qed.
Lemma md_rel : ltac2:(tb__ "0|1|
S0S17S4cSa7Sa6Sa7A1Z6ZfS73S3S19S1eS45S45A2M0S20S45S45Z30Z48A4S16G0A1A3S4dS91A1S4eS91A1A9S18A3"). Proof. vmr. Qed.
Lemma E_mdx_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29SacSb0A2S1aS22S6cA2A3"). Proof. vmr. Qed.
Lemma E_md_ub : ltac2:(tb__ "0|0|
S0S1bS22A1S29S6cS19S28S2dU2Z38A2S16S28A1A3A2S1aS22SaaA2A3"). Proof. vmr. Qed.
Lemma md_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S38S19S22S37S16S22A1A3SaaS4dS91A1S4eS91A1SafSadA8S18A3"). Proof. vmr. Qed.
Lemma T_md1_rb : ltac2:(tb__ "0|0|
S0S1bS22A1S29SaeS19S28S2cU1A1S16S28A1A3A2S1aS22Sa9A2A3"). Proof. vmr. Qed.
Lemma T_md2_zc : ltac2:(tb__ "0|0|
S0S1bS12A1SbbS23Sa9A1U1S77A3S1aS12S23Sa8A1A2A3"). Proof. vmr. Qed.
Lemma T_md2_wf : ltac2:(tb__ "0|0|
S0S17S15S23Sa8A1A1S18A3"). Proof. vmr. Qed.
Lemma T_md2_eq2 : ltac2:(tb__ "0|0|
S0S22S25Sa9S23Sa8A1A2Sa8A3"). Proof. vmr. Qed.
Lemma md_ro : ltac2:(tb__ "0|0|
S0S17SbaVXGL;SabS24SabA1S4dS91A1Z14Z17A6S18A3"). Proof. vmr. Qed.

Definition E_g1_1x : axst := Eval vm_compute in shadow_release_stateA E_g1_0 (objs_butlast E_g1_0) 160 [].
Lemma g1_robjs1 : ltac2:(tb__ "0|0|
S0S1dS2A1SaS23S83A1A1S1fS2Sa6S83A1S19S2Sb6S30Z26Z27S76S3A5S16S2A1A3A3A3"). Proof. vmr. Qed.
Lemma g1_rel1 : ltac2:(tb__ "0|0|
S0S17Sb9S83Z26Z27S3A4S18A3"). Proof. vmr. Qed.
Lemma E_g1_1x_eq : ltac2:(tb__ "0|0|
S0S22Sb7S83Sa6S83A1Pa0S16S1eS45S45A2A1A4Sa5A3"). Proof. vmr. Qed.
Lemma g1_robjs2 : ltac2:(tb__ "0|0|
S0S1dS2A1SaS23Sa5A1A1S1fS2Sa6Sa5A1S19S2Sb6S30Z1cZ21S72S3A5S16S2A1A3A3A3"). Proof. vmr. Qed.
Lemma g1_rel2 : ltac2:(tb__ "0|1|
S0S17S4cSa5Sa6Sa5A1Z1cZ21S72S3S19S1eS45S45A2M0S20S45S45Ze0Z24A4S16G0A1A3S4dS90A1S4eS90A1A9S18A3"). Proof. vmr. Qed.
Lemma E_g1_3x_eq : ltac2:(tb__ "0|1|
S0S22Sb7Sa5Sa6Sa5A1Pa0S19S1eS45S45A2M0S20S45S45Ze0Z24A4S16G0A1A3A4S84A3"). Proof. vmr. Qed.
Lemma E_g1a_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29S84S79A2S1aS22S5fA2A3"). Proof. vmr. Qed.
Lemma g1_o2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5fA1A1U2A3S1aS2S5S2eS1Ze0A1S1ZecA1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g1_wf2 : ltac2:(tb__ "0|2|
S0S17S1cSbS8S23S5fA1M0A1S5S6S26S2eS1Ze0M1A1A3S1Z0A1S1S43ZecG1A2A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma E_g1b_eq : ltac2:(tb__ "0|1|
S0S22S32S5fU2S5S6S26S2eS1Ze0M0A1A3S1Z0A1S1S43ZecG0A2A1S16S4A1S3A5A3S55A3"). Proof. vmr. Qed.
Lemma g1_oi : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S55A1A1U23A3S1aS2S5S31S50S6S26S50S1ZcA1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g1_wfi : ltac2:(tb__ "0|0|
S0S17SbS8S23S55A1A1S5S6S26S31S50A3S1Z0A1S1ZcA1S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma E_g1c_eq : ltac2:(tb__ "0|0|
S0S22S32S55U23S5S6S26S31S50A3S1Z0A1S1ZcA1S16S4A1S3A5A3S60A3"). Proof. vmr. Qed.
Lemma g1_bnd : ltac2:(tb__ "0|0|
S0S17S3aS9ScSdS31S1Sb1A1A2A1S7S23S55A1A1A3S18A3"). Proof. vmr. Qed.
Lemma E_g1_eq3 : ltac2:(tb__ "0|0|
S0S22Sb5S7dS84A1S60A2S80A3"). Proof. vmr. Qed.
Lemma g1_gneed : ltac2:(tb__ "0|2|
S0S1dS9A1S7dS84A1S19S9SdS6S26S6S26S31S11S27S13S21Q20SeP1e1A1A3S1ZcM0A1M1A3A3G1A3S6S26S31S2fG0S35A2A3A2S16S9A1A3A3"). Proof. vmr. Qed.
Lemma g1_xff : ltac2:(tb__ "0|0|
S0S17S4bS60S7dS84A1A2S18A3"). Proof. vmr. Qed.
Lemma g1_gF : ltac2:(tb__ "0|1|
S0S17S1cS4aS7S23S60A1A1M0A1S3aS9ScS10SeP1e1A1S33A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma g1_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S80S4dS90A1S4eS90A1S7fS80A1S87A8S18A3"). Proof. vmr. Qed.
Lemma R_g1_eq2 : ltac2:(tb__ "0|1|
S0S1bS1dS2A1M0A1Sb3S80S3cS7fS80A1A3S1aG0S87A2A3"). Proof. vmr. Qed.
Lemma T_g1t_eq : ltac2:(tb__ "0|0|
S0S22Sb4S3cS80S7fS80A1S87S3bA5S67A3"). Proof. vmr. Qed.
Lemma g1_to1 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S67A1A1U1A3S1aS2S5S6S26S2eS1Ze0M0A1A3S1Z0A1S1S43ZecG0A2A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g1_twf1 : ltac2:(tb__ "0|1|
S0S17S1cSbS8S23S67A1M0A1S5S2eS1Ze0A1S1ZecA1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma T_g1u_eq : ltac2:(tb__ "0|0|
S0S22S32S67U1S5S2eS1Ze0A1S1ZecA1S16S4A1S3A5A3S5aA3"). Proof. vmr. Qed.
Lemma g1_to2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5aA1A1U2A3S1aS2S5S6S26S31S50A3S1Z0A1S1ZcA1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g1_twf2 : ltac2:(tb__ "0|0|
S0S17SbS8S23S5aA1A1S5S31S50S6S26S50S1ZcA1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma T_g1v_eq : ltac2:(tb__ "0|0|
S0S22S32S5aU2S5S31S50S6S26S50S1ZcA1A3S16S4A1S3A5A3S6eA3"). Proof. vmr. Qed.
Lemma g1_tbnd : ltac2:(tb__ "0|0|
S0S17S3aS9ScSdS31S1Sb1A1A2A1S7S23S5aA1A1A3S18A3"). Proof. vmr. Qed.
Lemma T_g1_eq2 : ltac2:(tb__ "0|2|
S0S1bS22A1S29S6eS19S28S2bS8aA1S19S28S2aU1A1M0S19S28G0S19S28S2aU20A1M1S19S28G1S16S28A1A3A3A3A3A3A2S1aS22S8dA2A3"). Proof. vmr. Qed.
Lemma g1_vlF : ltac2:(tb__ "0|0|
S0S17S49S7S23S83A1A1A1S18A3"). Proof. vmr. Qed.
Lemma g1_meas : ltac2:(tb__ "0|1|
S0S17S1cSfS8S23S80A1A1M0Sb2A2SfG0S7eA2A2S18A3"). Proof. vmr. Qed.

Lemma E_g2a_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29S85S7aA2S1aS22S61A2A3"). Proof. vmr. Qed.
Lemma g2_o2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S61A1A1U2A3S1aS2S5S2eS1ZecA1S1Zf8A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g2_wf2 : ltac2:(tb__ "0|2|
S0S17S1cSbS8S23S61A1M0A1S5S6S26S2eS1ZecM1A1A3S1Z0A1S1S43Zf8G1A2A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma E_g2b_eq : ltac2:(tb__ "0|1|
S0S22S32S61U2S5S6S26S2eS1ZecM0A1A3S1Z0A1S1S43Zf8G0A2A1S16S4A1S3A5A3S56A3"). Proof. vmr. Qed.
Lemma g2_oi : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S56A1A1U23A3S1aS2S5S31S51S6S26S51S1ZcA1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g2_wfi : ltac2:(tb__ "0|0|
S0S17SbS8S23S56A1A1S5S6S26S31S51A3S1Z0A1S1ZcA1S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma E_g2c_eq : ltac2:(tb__ "0|0|
S0S22S32S56U23S5S6S26S31S51A3S1Z0A1S1ZcA1S16S4A1S3A5A3S62A3"). Proof. vmr. Qed.
Lemma g2_bnd : ltac2:(tb__ "0|1|
S0S17S1cS1cS3aS9ScSdS31S1Sb1A1A2A1S7S23S56A1A1M0A3S3aS9ScS10SeP1e2A1S33A2A1G0A3A2S3aS9ScSdS33S1S44Z2Z14A2A1A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma E_g2_eq3 : ltac2:(tb__ "0|0|
S0S22Sb5S7dS85A1S62A2S81A3"). Proof. vmr. Qed.
Lemma g2_gneed : ltac2:(tb__ "0|2|
S0S1dS9A1S7dS85A1S19S9SdS6S26S6S26S31S11S27SeP1e2A1S1ZcM0A1M1A3A3G1A3S6S26S31S2fG0S35A2A3A2S16S9A1A3A3"). Proof. vmr. Qed.
Lemma g2_xff : ltac2:(tb__ "0|0|
S0S17S4bS62S7dS85A1A2S18A3"). Proof. vmr. Qed.
Lemma g2_gF : ltac2:(tb__ "0|1|
S0S17S1cS4aS7S23S62A1A1M0A1S3aS9ScS10SeP1e2A1S33A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma g2_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S81S4dS90A1S4eS90A1S7fS81A1S88A8S18A3"). Proof. vmr. Qed.
Lemma R_g2_eq2 : ltac2:(tb__ "0|1|
S0S1bS1dS2A1M0A1Sb3S81S3cS7fS81A1A3S1aG0S88A2A3"). Proof. vmr. Qed.
Lemma T_g2t_eq : ltac2:(tb__ "0|0|
S0S22Sb4S3cS81S7fS81A1S88S3bA5S68A3"). Proof. vmr. Qed.
Lemma g2_to1 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S68A1A1U1A3S1aS2S5S6S26S2eS1ZecM0A1A3S1Z0A1S1S43Zf8G0A2A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g2_twf1 : ltac2:(tb__ "0|1|
S0S17S1cSbS8S23S68A1M0A1S5S2eS1ZecA1S1Zf8A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma T_g2u_eq : ltac2:(tb__ "0|0|
S0S22S32S68U1S5S2eS1ZecA1S1Zf8A1S16S4A1S3A5A3S5bA3"). Proof. vmr. Qed.
Lemma g2_to2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5bA1A1U2A3S1aS2S5S6S26S31S51A3S1Z0A1S1ZcA1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g2_twf2 : ltac2:(tb__ "0|0|
S0S17SbS8S23S5bA1A1S5S31S51S6S26S51S1ZcA1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma T_g2v_eq : ltac2:(tb__ "0|0|
S0S22S32S5bU2S5S31S51S6S26S51S1ZcA1A3S16S4A1S3A5A3S6fA3"). Proof. vmr. Qed.
Lemma g2_tbnd : ltac2:(tb__ "0|1|
S0S17S1cS1cS3aS9ScSdS31S1Sb1A1A2A1S7S23S5bA1A1M0A3S3aS9ScS10SeP1e2A1S33A2A1G0A3A2S3aS9ScSdS33S1S44Z2Z14A2A1A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma T_g2_eq2 : ltac2:(tb__ "0|2|
S0S1bS22A1S29S6fS19S28S2bS8aA1S19S28S2aU1A1M0S19S28G0S19S28S2aU20A1M1S19S28G1S16S28A1A3A3A3A3A3A2S1aS22S8eA2A3"). Proof. vmr. Qed.
Lemma g2_vlF : ltac2:(tb__ "0|0|
S0S17S49S7S23S85A1A1A1S18A3"). Proof. vmr. Qed.
Lemma g2_meas : ltac2:(tb__ "0|1|
S0S17S1cSfS8S23S81A1A1M0Sb2A2SfG0S7eA2A2S18A3"). Proof. vmr. Qed.

Lemma E_g3a_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29S86S7bA2S1aS22S63A2A3"). Proof. vmr. Qed.
Lemma g3_o2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S63A1A1U2A3S1aS2S5S2eS1Zf8A1S1Z104A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g3_wf2 : ltac2:(tb__ "0|2|
S0S17S1cSbS8S23S63A1M0A1S5S6S26S2eS1Zf8M1A1A3S1Z0A1S1S43Z104G1A2A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma E_g3b_eq : ltac2:(tb__ "0|1|
S0S22S32S63U2S5S6S26S2eS1Zf8M0A1A3S1Z0A1S1S43Z104G0A2A1S16S4A1S3A5A3S57A3"). Proof. vmr. Qed.
Lemma g3_oi : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S57A1A1U23A3S1aS2S5S31S52S6S26S52S1ZcA1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g3_wfi : ltac2:(tb__ "0|0|
S0S17SbS8S23S57A1A1S5S6S26S31S52A3S1Z0A1S1ZcA1S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma E_g3c_eq : ltac2:(tb__ "0|0|
S0S22S32S57U23S5S6S26S31S52A3S1Z0A1S1ZcA1S16S4A1S3A5A3S64A3"). Proof. vmr. Qed.
Lemma g3_bnd : ltac2:(tb__ "0|1|
S0S17S1cS1cS3aS9ScSdS31S1Sb1A1A2A1S7S23S57A1A1M0A3S3aS9ScS10SeP1e3A1S33A2A1G0A3A2S3aS9ScSdS33S1S44Z2Z14A2A1A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma E_g3_eq3 : ltac2:(tb__ "0|0|
S0S22Sb5S7dS86A1S64A2S82A3"). Proof. vmr. Qed.
Lemma g3_gneed : ltac2:(tb__ "0|2|
S0S1dS9A1S7dS86A1S19S9SdS6S26S6S26S31S11S27SeP1e3A1S1ZcM0A1M1A3A3G1A3S6S26S31S2fG0S35A2A3A2S16S9A1A3A3"). Proof. vmr. Qed.
Lemma g3_xff : ltac2:(tb__ "0|0|
S0S17S4bS64S7dS86A1A2S18A3"). Proof. vmr. Qed.
Lemma g3_gF : ltac2:(tb__ "0|1|
S0S17S1cS4aS7S23S64A1A1M0A1S3aS9ScS10SeP1e3A1S33A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma g3_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S82S4dS90A1S4eS90A1S7fS82A1S89A8S18A3"). Proof. vmr. Qed.
Lemma R_g3_eq2 : ltac2:(tb__ "0|1|
S0S1bS1dS2A1M0A1Sb3S82S3cS7fS82A1A3S1aG0S89A2A3"). Proof. vmr. Qed.
Lemma T_g3t_eq : ltac2:(tb__ "0|0|
S0S22Sb4S3cS82S7fS82A1S89S3bA5S69A3"). Proof. vmr. Qed.
Lemma g3_to1 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S69A1A1U1A3S1aS2S5S6S26S2eS1Zf8M0A1A3S1Z0A1S1S43Z104G0A2A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g3_twf1 : ltac2:(tb__ "0|1|
S0S17S1cSbS8S23S69A1M0A1S5S2eS1Zf8A1S1Z104A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma T_g3u_eq : ltac2:(tb__ "0|0|
S0S22S32S69U1S5S2eS1Zf8A1S1Z104A1S16S4A1S3A5A3S5cA3"). Proof. vmr. Qed.
Lemma g3_to2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5cA1A1U2A3S1aS2S5S6S26S31S52A3S1Z0A1S1ZcA1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma g3_twf2 : ltac2:(tb__ "0|0|
S0S17SbS8S23S5cA1A1S5S31S52S6S26S52S1ZcA1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma T_g3v_eq : ltac2:(tb__ "0|0|
S0S22S32S5cU2S5S31S52S6S26S52S1ZcA1A3S16S4A1S3A5A3S70A3"). Proof. vmr. Qed.
Lemma g3_tbnd : ltac2:(tb__ "0|1|
S0S17S1cS1cS3aS9ScSdS31S1Sb1A1A2A1S7S23S5cA1A1M0A3S3aS9ScS10SeP1e3A1S33A2A1G0A3A2S3aS9ScSdS33S1S44Z2Z14A2A1A2A1G0A3A2S18A3"). Proof. vmr. Qed.
Lemma T_g3w_eq : ltac2:(tb__ "0|2|
S0S1bS22A1S29S70S19S28S2bS8aA1S19S28S2aU1A1M0S19S28G0S19S28S2aU20A1M1S19S28G1S16S28A1A3A3A3A3A3A2S1aS22S6bA2A3"). Proof. vmr. Qed.

Lemma T_g3_eq2 : ltac2:(tb__ "0|0|
S0S22Sb8S6bS24S6bA1S30Z26Z27A5S8fA3"). Proof. vmr. Qed.
Lemma g3_vlF : ltac2:(tb__ "0|0|
S0S17S49S7S23S86A1A1A1S18A3"). Proof. vmr. Qed.
Lemma g3_meas : ltac2:(tb__ "0|1|
S0S17S1cSfS8S23S82A1A1M0Sb2A2SfG0S7eA2A2S18A3"). Proof. vmr. Qed.

Lemma E_c4a_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29S9dS78A2S1aS22S5eA2A3"). Proof. vmr. Qed.
Lemma c4_o2 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5eA1A1U2A3S1aS2S5S2eS1Ze0A1S1Z104A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma c4_wf2 : ltac2:(tb__ "0|2|
S0S17S1cSbS8S23S5eA1M0A1S5S6S26S2eS1Ze0M1A1A3S1Z0A1S1S43Z104G1A2A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma E_c4b_eq : ltac2:(tb__ "0|1|
S0S22S32S5eU2S5S6S26S2eS1Ze0M0A1A3S1Z0A1S1S43Z104G0A2A1S16S4A1S3A5A3S54A3"). Proof. vmr. Qed.
Lemma c4_oi : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S54A1A1U1fA3S1aS2S5S96S4fS6S26S4fS1Z24A1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma c4_wfi : ltac2:(tb__ "0|0|
S0S17SbS8S23S54A1A1S5S6S26S96S4fA3S1Z0A1S1Z24A1S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma E_c4c_eq : ltac2:(tb__ "0|0|
S0S22S32S54U1fS5S6S26S96S4fA3S1Z0A1S1Z24A1S16S4A1S3A5A3S74A3"). Proof. vmr. Qed.
Lemma c4_bnd : ltac2:(tb__ "0|0|
S0S17S48S96S8cS7eA1Sa0S7S23S54A1A1A4S18A3"). Proof. vmr. Qed.
Lemma E_c4_eq3 : E_c4c = E_c4. Proof. vmr. Qed.
Lemma c4_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S97S4dS93A1S4eS93A1S9bS99A8S18A3"). Proof. vmr. Qed.
Lemma R_c4_eq2 : ltac2:(tb__ "0|1|
S0S1bS1dS2A1M0A1Sb3S97S3cS9bA3S1aG0S99A2A3"). Proof. vmr. Qed.
Lemma T_c4t_eq : ltac2:(tb__ "0|0|
S0S22Sb4S3cS97S9bS99S3bA5S59A3"). Proof. vmr. Qed.
Lemma c4_to1 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S59A1A1U1A3S1aS2S5S6S26S96S4fA3S1Z0A1S1Z24A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma c4_twf1 : ltac2:(tb__ "0|0|
S0S17SbS8S23S59A1A1S5S96S4fS6S26S4fS1Z24A1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma T_c4u_eq : ltac2:(tb__ "0|0|
S0S22S32S59U1S5S96S4fS6S26S4fS1Z24A1A3S16S4A1S3A5A3S66A3"). Proof. vmr. Qed.
Lemma c4_to2 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S66A1A1U2A3S1aS2S5S6S26S2eS1Ze0M0A1A3S1Z0A1S1S43Z104G0A2A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma c4_twf2 : ltac2:(tb__ "0|1|
S0S17S1cSbS8S23S66A1M0A1S5S2eS1Ze0A1S1Z104A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma T_c4v_eq : ltac2:(tb__ "0|0|
S0S22S32S66U2S5S2eS1Ze0A1S1Z104A1S16S4A1S3A5A3S6dA3"). Proof. vmr. Qed.
Lemma c4_tbnd : ltac2:(tb__ "0|0|
S0S17S48S96S8cS7eA1Sa0S7S23S59A1A1A4S18A3"). Proof. vmr. Qed.
Lemma T_c4_eq2 : ltac2:(tb__ "0|2|
S0S1bS22A1S29S6dS19S28S2bSa3A1S19S28S2aU1A1M0S19S28G0S19S28S2aU1cA1M1S19S28G1S16S28A1A3A3A3A3A3A2S1aS22Sa1A2A3"). Proof. vmr. Qed.
Lemma c4_vlF : ltac2:(tb__ "0|0|
S0S17S49S7S23S9dA1A1A1S18A3"). Proof. vmr. Qed.
Lemma c4_meas : ltac2:(tb__ "0|1|
S0S17S1cSfS8S23S97A1A1M0Sb2A2SfG0S7eA2A2S18A3"). Proof. vmr. Qed.

Lemma E_m4a_eq : ltac2:(tb__ "0|0|
S0S1bS22A1S29S9eS7cA2S1aS22S65A2A3"). Proof. vmr. Qed.
Lemma m4_o2 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S65A1A1U2A3S1aS2S5S2eS1Z130A1M0S1Z134A1S19S4S14G0Z4S1Z3A1A3S16S4A1A3S3A5A2A3"). Proof. vmr. Qed.
Lemma m4_wf2 : ltac2:(tb__ "0|2|
S0S17S1cSbS8S23S65A1M0A1S5S6S26S2eS1Z130M1A1A3S1Z0A1S1S43Z134G1A2A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma E_m4b_eq : ltac2:(tb__ "0|1|
S0S22S32S65U2S5S6S26S2eS1Z130M0A1A3S1Z0A1S1S43Z134G0A2A1S16S4A1S3A5A3S58A3"). Proof. vmr. Qed.
Lemma m4_oi : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S58A1A1U20A3S1aS2S5S95S53S6S26S53S1Z4A1A3S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma m4_wfi : ltac2:(tb__ "0|0|
S0S17SbS8S23S58A1A1S5S6S26S95S53A3S1Z0A1S1Z4A1S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma E_m4c_eq : ltac2:(tb__ "0|0|
S0S22S32S58U20S5S6S26S95S53A3S1Z0A1S1Z4A1S16S4A1S3A5A3S75A3"). Proof. vmr. Qed.
Lemma m4_bnd : ltac2:(tb__ "0|0|
S0S17S48S95S8bS7eA1S9fS7S23S58A1A1A4S18A3"). Proof. vmr. Qed.
Lemma E_m4_eq3 : E_m4c = E_m4. Proof. vmr. Qed.
Lemma m4_chk : ltac2:(tb__ "0|0|
S0S17S47VXGL;S3cS19S22S3bS19S22S3bS16S22A1A3A3S98S4dS94A1S4eS94A1S9cS9aA8S18A3"). Proof. vmr. Qed.
Lemma R_m4_eq2 : ltac2:(tb__ "0|1|
S0S1bS1dS2A1M0A1Sb3S98S3cS9cA3S1aG0S9aA2A3"). Proof. vmr. Qed.
Lemma T_m4t_eq : ltac2:(tb__ "0|0|
S0S22Sb4S3cS98S9cS9aS3bA5S5dA3"). Proof. vmr. Qed.
Lemma m4_to1 : ltac2:(tb__ "0|0|
S0S1bS2A1S39S2SaS23S5dA1A1U1A3S1aS2S5S6S26S95S53A3S1Z0A1S1Z4A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma m4_twf1 : ltac2:(tb__ "0|0|
S0S17SbS8S23S5dA1A1S5S95S53S6S26S53S1Z4A1A3S16S4A1S3A5A2S18A3"). Proof. vmr. Qed.
Lemma T_m4u_eq : ltac2:(tb__ "0|0|
S0S22S32S5dU1S5S95S53S6S26S53S1Z4A1A3S16S4A1S3A5A3S6aA3"). Proof. vmr. Qed.
Lemma m4_to2 : ltac2:(tb__ "0|1|
S0S1bS2A1S39S2SaS23S6aA1A1U2A3S1aS2S5S6S26S2eS1Z130M0A1A3S1Z0A1S1S43Z134G0A2A1S16S4A1S3A5A2A3"). Proof. vmr. Qed.
Lemma m4_twf2 : ltac2:(tb__ "0|1|
S0S17S1cSbS8S23S6aA1M0A1S5S2eS1Z130A1S1Z134A1S16S4A1S3A5A2S46S7G0A1A1A2S18A3"). Proof. vmr. Qed.
Lemma T_m4v_eq : ltac2:(tb__ "0|0|
S0S22S32S6aU2S5S2eS1Z130A1S1Z134A1S16S4A1S3A5A3S71A3"). Proof. vmr. Qed.
Lemma m4_tbnd : ltac2:(tb__ "0|0|
S0S17S48S95S8bS7eA1S9fS7S23S5dA1A1A4S18A3"). Proof. vmr. Qed.
Lemma T_m4_eq2 : ltac2:(tb__ "0|2|
S0S1bS22A1S29S71S19S28S2bSa4A1S19S28S2aU1A1M0S19S28G0S19S28S2aU1dA1M1S19S28G1S16S28A1A3A3A3A3A3A2S1aS22Sa2A2A3"). Proof. vmr. Qed.
Lemma m4_vlF : ltac2:(tb__ "0|0|
S0S17S49S7S23S9eA1A1A1S18A3"). Proof. vmr. Qed.
Lemma m4_meas : ltac2:(tb__ "0|1|
S0S17S1cSfS8S23S98A1A1M0Sb2A2SfG0S7eA2A2S18A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g6.

(* [comment removed for export] *)
Module Lib_handle_f_chk1.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_0 : CC 0 Pre_hf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_7 : CC 7 JR_co = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 RW = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 T_mcq = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 K1Xb = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_35 : CC 35 JR_rp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_42 : CC 42 JF_ts = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_49 : CC 49 T_g1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_56 : CC 56 JF_fv4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_63 : CC 63 C_Eo2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk1.

