(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oi Lib_handle_f_g9 om o5 o0.

(* [comment removed for export] *)
Module Lib_handle_f_g4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "SPUle"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "bool"; "list"; "true"; "pair"; "prod"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "tr_d"; "ts_d"; "tr_k"; "rp_d"; "ts_k"; "X_body"; "pDco"; "pKco"; "rp_k"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "ndXA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "land_chk"; "kept_ts"; "brest_rp"; "brest_trb"; "brest_trg"; "brest_ts"; "kept_rp"; "kept_trb"; "kept_trg"; "xff_chk"; "E_ts1x"; "T_rpk1"; "T_trbk1"; "T_trgk1"; "T_tsk1"; "vr_chk"; "E_rp1x"; "E_trb1x"; "E_trg1x"; "T_rpf0"; "T_rpg0"; "T_rpk0"; "T_trbf0"; "T_trbg0"; "T_trbk0"; "T_trgf0"; "T_trgg0"; "T_trgk0"; "T_tsf0"; "T_tsg0"; "T_tsk0"; "bd2_rpg"; "bd2_rpk"; "bd2_trbg"; "bd2_trbk"; "bd2_trgg"; "bd2_trgk"; "bd2_tsg"; "bd2_tsk"; "bdG_rp"; "bdG_trb"; "bdG_trg"; "bdG_ts"; "bdK_rp"; "bdK_trb"; "bdK_trg"; "bdK_ts"; "liveTri"; "reopen_chk"; "s_rpf"; "s_rpg"; "s_rpk"; "s_trbf"; "s_trbg"; "s_trbk"; "s_trgf"; "s_trgg"; "s_trgk"; "s_tsf"; "s_tsg"; "s_tsk"; "liveRp"; "liveTs"; "triAF"; "tv2_rpf"; "tv2_rpg"; "tv2_rpk"; "tv2_trbf"; "tv2_trbg"; "tv2_trbk"; "tv2_trgf"; "tv2_trgg"; "tv2_trgk"; "tv2_tsf"; "tv2_tsg"; "tv2_tsk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndTR"; "ndRP"; "ndTRf"; "ndTS"; "ndRPf"; "ndTSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "E_trb"; "E_trg"; "s_trb"; "s_trg"; "R_trb"; "R_trg"; "XTR"; "pDtr"; "pKtr"; "JR_trb"; "JR_trg"; "T_trbf"; "T_trbg"; "T_trbk"; "T_trgf"; "T_trgg"; "T_trgk"; "E_trb0"; "E_trg0"; "JF_trb"; "JF_trg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "E_rp"; "E_ts"; "s_rp"; "s_ts"; "T_tsg"; "T_tsk"; "R_rp"; "R_ts"; "XRT"; "pDrp"; "pKrp"; "JR_rp"; "JR_ts"; "T_rpf"; "T_rpg"; "T_rpk"; "T_tsf"; "need_facts"; "E_rp0"; "E_ts0"; "JF_rp"; "JF_ts"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_trg1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32S99S2bU15Z310A2A2S12S7S45A2A3"). Proof. vmr. Qed.
Lemma E_trg_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S45A2S88A3"). Proof. vmr. Qed.
Lemma trg_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS31A1S11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma trg_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S88S3bS22S24Z4Z310S2dS31A1S37S8aS8cS2fS22S27S28S29A2A2AcSeA3"). Proof. vmr. Qed.
Lemma trg_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S18S88A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S19S88A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S17S88A4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS8aS16S18S88A4S2dS1cA1A2S60A3"). Proof. vmr. Qed.
Lemma trg_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS8aS16S17S88A4S1bS1fS1eA2A2S5cA3"). Proof. vmr. Qed.
Lemma T_trgk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS18S2fS22S27S28S29A2A2A6S4eA3"). Proof. vmr. Qed.
Lemma T_trgk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4eS30U14U22Z310A3A2S12S7S40A2A3"). Proof. vmr. Qed.
Lemma T_trgk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S22A2SaS1A1A3S40A2S97A3"). Proof. vmr. Qed.
Lemma trgk_xff : ltac2:(tb__ "0|0|
S6ScS3cS40SbS1S4S3Sb4A1S22A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma trgk_land : ltac2:(tb__ "0|1|
S6ScS33S97S91S6cS11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S7bS11S14S60S37A3S57S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trgk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6cS2dS81A1A2S57A3"). Proof. vmr. Qed.
Lemma trgk_live : ltac2:(tb__ "0|0|
S6ScS62S24S5S8S40A1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_trgf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS19S2fS22S27S28S29A2A2A6S4cA3"). Proof. vmr. Qed.
Lemma T_trgf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4cS30U14U22Z310A3A2S12S7S95A2A3"). Proof. vmr. Qed.
Lemma trgf_land : ltac2:(tb__ "0|2|
S6ScS33S95S9bS6aS11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S79Sb2S14U1S37A3M1G1S2eS83A1A8SeA3"). Proof. vmr. Qed.
Lemma trgf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6aS2dS83A1A2Sb2S14U1S37A3A3"). Proof. vmr. Qed.
Lemma T_trgg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS17S2fS22S27S28S29A2A2A6S4dA3"). Proof. vmr. Qed.
Lemma T_trgg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4dS30U14U22Z310A3A2S12S7S96A2A3"). Proof. vmr. Qed.
Lemma trgg_land : ltac2:(tb__ "0|1|
S6ScS33S96S91S6bS11S10S0S0A2M0S3bSbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S7aS11S14S5cS37A3S56S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trgg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6bS2dS81A1A2S56A3"). Proof. vmr. Qed.
Lemma trgf_wp : bd_wpos brest_trg = true. Proof. vmr. Qed.

Lemma E_trb1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32S98S2bU15Z310A2A2S12S7S44A2A3"). Proof. vmr. Qed.
Lemma E_trb_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S44A2S87A3"). Proof. vmr. Qed.
Lemma trb_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS31A1S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma trb_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S87S3aS22S24Z4Z310S2dS31A1S36S89S8bS2fS22S27S28S29A2A2AcSeA3"). Proof. vmr. Qed.
Lemma trb_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S18S87A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S19S87A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S17S87A4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS89S16S18S87A4S2dS1cA1A2S5fA3"). Proof. vmr. Qed.
Lemma trb_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS89S16S17S87A4S1bS1fS1eA2A2S5bA3"). Proof. vmr. Qed.
Lemma T_trbk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS18S2fS22S27S28S29A2A2A6S4bA3"). Proof. vmr. Qed.
Lemma T_trbk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4bS30U14U22Z310A3A2S12S7S3fA2A3"). Proof. vmr. Qed.
Lemma T_trbk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S22A2SaS1A1A3S3fA2S94A3"). Proof. vmr. Qed.
Lemma trbk_xff : ltac2:(tb__ "0|0|
S6ScS3cS3fSbS1S4S3Sb4A1S22A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma trbk_land : ltac2:(tb__ "0|1|
S6ScS33S94S90S69S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S78S11S14S5fS36A3S55S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trbk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S69S2dS81A1A2S55A3"). Proof. vmr. Qed.
Lemma trbk_live : ltac2:(tb__ "0|0|
S6ScS62S24S5S8S3fA1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_trbf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS19S2fS22S27S28S29A2A2A6S49A3"). Proof. vmr. Qed.
Lemma T_trbf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S49S30U14U22Z310A3A2S12S7S92A2A3"). Proof. vmr. Qed.
Lemma trbf_land : ltac2:(tb__ "0|2|
S6ScS33S92S9aS67S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S76Sb2S14U1S36A3M1G1S2eS83A1A8SeA3"). Proof. vmr. Qed.
Lemma trbf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S67S2dS83A1A2Sb2S14U1S36A3A3"). Proof. vmr. Qed.
Lemma T_trbg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS17S2fS22S27S28S29A2A2A6S4aA3"). Proof. vmr. Qed.
Lemma T_trbg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4aS30U14U22Z310A3A2S12S7S93A2A3"). Proof. vmr. Qed.
Lemma trbg_land : ltac2:(tb__ "0|1|
S6ScS33S93S90S68S11S10S0S0A2M0S3aSbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S77S11S14S5bS36A3S54S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trbg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S68S2dS81A1A2S54A3"). Proof. vmr. Qed.
Lemma trbf_wp : bd_wpos brest_trb = true. Proof. vmr. Qed.

Lemma E_rp1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32SaeS2bU14Z2f0A2A2S12S7S43A2A3"). Proof. vmr. Qed.
Lemma E_rp_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S43A2S9cA3"). Proof. vmr. Qed.
Lemma rp_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS81A1S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma rp_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S9cS39S25S2aZ4Z2f0S2dS81A1S35S9eSa2S2fS25S8dS8eS8fA2A2AcSeA3"). Proof. vmr. Qed.
Lemma rp_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S18S9cA4S1aA2SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S19S9cA4S1aA2SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S17S9cA4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9eS16S18S9cA4S2dS1cA1A2S5eA3"). Proof. vmr. Qed.
Lemma rp_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9eS16S17S9cA4S1bS1fS1eA2A2S5aA3"). Proof. vmr. Qed.
Lemma T_rpk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S18S2fS25S8dS8eS8fA2A2A6S48A3"). Proof. vmr. Qed.
Lemma T_rpk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S48S30U13U21Z2f0A3A2S12S7S3eA2A3"). Proof. vmr. Qed.
Lemma T_rpk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S25A2SaS1A1A3S3eA2SabA3"). Proof. vmr. Qed.
Lemma rpk_xff : ltac2:(tb__ "0|0|
S6ScS3cS3eSbS1S4S3Sb4A1S25A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma rpk_land : ltac2:(tb__ "0|1|
S6ScS33SabSa7S66S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3S75S11S14S5eS35A3S53S2eS82A1A8SeA3"). Proof. vmr. Qed.
Lemma rpk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S66S2dS82A1A2S53A3"). Proof. vmr. Qed.
Lemma rpk_live : ltac2:(tb__ "0|0|
S6ScS70S2aS5S8S3eA1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_rpf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S19S2fS25S8dS8eS8fA2A2A6S46A3"). Proof. vmr. Qed.
Lemma T_rpf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S46S30U13U21Z2f0A3A2S12S7Sa9A2A3"). Proof. vmr. Qed.
Lemma rpf_land : ltac2:(tb__ "0|2|
S6ScS33Sa9Sb0S64S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3S73Sb2S14U1S35A3M1G1S2eS85A1A8SeA3"). Proof. vmr. Qed.
Lemma rpf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S64S2dS85A1A2Sb2S14U1S35A3A3"). Proof. vmr. Qed.
Lemma T_rpg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S17S2fS25S8dS8eS8fA2A2A6S47A3"). Proof. vmr. Qed.
Lemma T_rpg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S47S30U13U21Z2f0A3A2S12S7SaaA2A3"). Proof. vmr. Qed.
Lemma rpg_land : ltac2:(tb__ "0|1|
S6ScS33SaaSa7S65S11S10S0S0A2M0S39SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S74S11S14S5aS35A3S52S2eS82A1A8SeA3"). Proof. vmr. Qed.
Lemma rpg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S65S2dS82A1A2S52A3"). Proof. vmr. Qed.
Lemma rpf_wp : bd_wpos brest_rp = true. Proof. vmr. Qed.

Lemma E_ts1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32SafS2bU16Z330A2A2S12S7S3dA2A3"). Proof. vmr. Qed.
Lemma E_ts_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SadS3dA2S9dA3"). Proof. vmr. Qed.
Lemma ts_xff : ltac2:(tb__ "0|0|
S6ScS3cS3dSadA2SeA3"). Proof. vmr. Qed.
Lemma ts_needF : ltac2:(tb__ "0|0|
S6ScS72S5S8S3dA1A1A1SeA3"). Proof. vmr. Qed.
Lemma ts_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS82A1S11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma ts_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S9dS34S23S26Z1Z330S2dS82A1S38S9fSa3S2fS23Sa4Sa5Sa6S23S26A4A2AcSeA3"). Proof. vmr. Qed.
Lemma ts_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S18S9dA4S1aA2SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S19S9dA4S1aA2SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S17S9dA4S1dA2SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9fS16S18S9dA4S2dS1cA1A2S61A3"). Proof. vmr. Qed.
Lemma ts_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9fS16S17S9dA4S1bS1fS1eA2A2S5dA3"). Proof. vmr. Qed.
Lemma T_tsk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S18S2fS23Sa4Sa5Sa6S23S26A4A2A6S51A3"). Proof. vmr. Qed.
Lemma T_tsk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S51S30U15U23Z330A3A2S12S7S41A2A3"). Proof. vmr. Qed.
Lemma T_tsk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S23A2SaS1A1A3S41A2Sa1A3"). Proof. vmr. Qed.
Lemma tsk_xff : ltac2:(tb__ "0|0|
S6ScS3cS41SbS1S4S3Sb4A1S23A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma tsk_ro0 : ltac2:(tb__ "0|1|
S6ScS63VXGL;Sa1S9Sa1A1S11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3Z6Z17A6SeA3"). Proof. vmr. Qed.
Lemma tsk_land : ltac2:(tb__ "0|1|
S6ScS33Sb6Sa1S9Sa1A1S21Z6Z17A5Sa8S6fS11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3S7eS11S14S61S38A3S59S2eS84A1A8SeA3"). Proof. vmr. Qed.
Lemma tsk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6fS2dS84A1A2S59A3"). Proof. vmr. Qed.
Lemma tsk_live : ltac2:(tb__ "0|0|
S6ScS71S26S5S8S41A1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_tsf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S19S2fS23Sa4Sa5Sa6S23S26A4A2A6S4fA3"). Proof. vmr. Qed.
Lemma T_tsf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4fS30U15U23Z330A3A2S12S7SacA2A3"). Proof. vmr. Qed.
Lemma tsf_land : ltac2:(tb__ "0|2|
S6ScS33SacSb1S6dS11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3S7cSb2S14U1S38A3M1G1S2eS86A1A8SeA3"). Proof. vmr. Qed.
Lemma tsf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6dS2dS86A1A2Sb2S14U1S38A3A3"). Proof. vmr. Qed.
Lemma T_tsg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S17S2fS23Sa4Sa5Sa6S23S26A4A2A6S50A3"). Proof. vmr. Qed.
Lemma T_tsg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S50S30U15U23Z330A3A2S12S7Sa0A2A3"). Proof. vmr. Qed.
Lemma tsg_ro0 : ltac2:(tb__ "0|1|
S6ScS63VXGL;Sa0S9Sa0A1S11S10S0S0A2M0S34SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3Z6Z17A6SeA3"). Proof. vmr. Qed.
Lemma tsg_land : ltac2:(tb__ "0|1|
S6ScS33Sb6Sa0S9Sa0A1S21Z6Z17A5Sa8S6eS11S10S0S0A2M0S34SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3S7dS11S14S5dS38A3S58S2eS84A1A8SeA3"). Proof. vmr. Qed.
Lemma tsg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6eS2dS84A1A2S58A3"). Proof. vmr. Qed.
Lemma tsf_wp : bd_wpos brest_ts = true. Proof. vmr. Qed.
End G.
End Lib_handle_f_g4.

(* [comment removed for export] *)
Module Lib_handle_f_g5c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "sv_eqb"; "ss_facts"; "SAlu"; "SPUle"; "sv_below"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "lDmm"; "lKmm"; "pL"; "cMM"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "pair"; "prod"; "app"; "list"; "andb"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b"; "E_mm4"; "s_mm4"; "T_mm4f"; "E_mm4_0"; "R_mm4"; "JR_mm4"; "T_mm4g"; "T_mm4k"; "JF_mm4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "kept_mm4"; "brest_mm4"; "E_mm41x"; "T_mm4k1"; "s_mm4g"; "s_mm4k"; "land_chk"; "T_mm4f0"; "T_mm4g0"; "T_mm4k0"; "bd2_mm4g"; "bd2_mm4k"; "bdG_mm4"; "bdK_mm4"; "s_mm4f"; "xff_chk"; "liveF"; "reopen_chk"; "tv2_mm4f"; "tv2_mm4g"; "tv2_mm4k"; "vlF"; "vrLF"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndL4c"; "ndL4b"; "ndL4cf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "NMM"; "vr_need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "XnoLoc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "mm_c"; "mm_n"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3.
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
SaS16S14S0S0A2M0A1S5aS4dS1eS2aS2bS1dA4S31A2S11G0S13S0S0S2P314A1S26Z4S2P315A1A2A4S12G0A1A3A3"). Proof. vmr. Qed.
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
SaSfS3aS23S22S38S15S14S0S0A2M0S34S11G0S13S0S0S2P314A1S26Z4S2P315A1A2A4S12G0A1A3A3S47S15S28S40S35A3S3eS4fS50A1A8S10A3"). Proof. vmr. Qed.
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
Module Lib_handle_f_g3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "ss_facts"; "SAlu"; "SPUle"; "sobj"; "DUnknown"; "ss_objs"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "pair"; "prod"; "list"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "mm_d"; "sg_d"; "fv_d"; "pA"; "mi_d"; "mm_k"; "sg_k"; "fv_k"; "pKco"; "mi_k"; "pDco"; "X_body"; "fv_c"; "mi_c"; "mm_c"; "sg_c"; "xf_vr"; "rp_d"; "rp_k"; "tr_d"; "tr_k"; "ts_d"; "ts_k"; "fv_n"; "mi_n"; "mm_n"; "sg_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "E_fv"; "E_mi"; "E_mm"; "s_fv"; "s_mi"; "s_mm"; "vr_need"; "co_live"; "T_migs"; "T_mik"; "T_miks"; "R_fv"; "R_mi"; "R_mm"; "T_fvk"; "T_mif"; "T_mig"; "T_mmk"; "XF1"; "XFV"; "pDfv"; "pKfv"; "T_fvf"; "T_mmf"; "E_fv0"; "JR_fv"; "JR_mi"; "NFV"; "NMI"; "NMM"; "NSG"; "T_fvf0"; "T_fvg"; "T_fvg0"; "T_fvk0"; "T_fvks"; "T_mif0"; "T_mifs"; "T_mig0"; "T_mik0"; "T_mmf0"; "T_mmg"; "T_mmg0"; "T_mmk0"; "X_face"; "ndXA"; "objs_fv0"; "pDmi"; "pKmi"; "E_fv1"; "E_mi0"; "E_mm0"; "JF_fv"; "JF_mi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "land_chk"; "xff_chk"; "kept_sg"; "kept_mi"; "reopen_chk"; "kept_fv"; "kept_mm"; "brest_fv"; "brest_mi"; "brest_mm"; "brest_sg"; "E_fv1x"; "E_mi1x"; "E_mm1x"; "E_sg1x"; "vr3F"; "vr_chk"; "live3F"; "liveF"; "bd2_fvg"; "bd2_fvk"; "bd2_mig"; "bd2_mik"; "bd2_mmg"; "bd2_mmk"; "bd2_sgg"; "bd2_sgk"; "bdG_fv"; "bdG_mi"; "bdG_mm"; "bdG_sg"; "bdK_fv"; "bdK_mi"; "bdK_mm"; "bdK_sg"; "cells_fv"; "s_fvf"; "s_fvg"; "s_fvk"; "s_mif"; "s_mig"; "s_mik"; "s_mmf"; "s_mmg"; "s_mmk"; "s_sgf"; "s_sgg"; "s_sgk"; "liveFa"; "release_chk"; "tv2_fvf"; "tv2_fvg"; "tv2_fvk"; "tv2_mif"; "tv2_mig"; "tv2_mik"; "tv2_mmf"; "tv2_mmg"; "tv2_mmk"; "tv2_sgf"; "tv2_sgg"; "tv2_sgk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3"; "E_sg"; "s_sg"; "XMM"; "XnoL"; "T_sgf"; "T_sgg"; "T_sgks"; "R_sg"; "T_sgk"; "pDmm"; "pKmm"; "JR_mm"; "JR_sg"; "T_mmks"; "T_sgf0"; "T_sgg0"; "T_sgk0"; "E_sg0"; "JF_mm"; "JF_sg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndMI"; "ndFV"; "ndMM"; "ndSG"; "ndFVf"; "ndMIf";
"ndMMf"; "ndSGf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "shobj"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_mi1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS78S39UfZ1f0A2A2S16SbS89A2A3"). Proof. vmr. Qed.
Lemma E_mi_eq2 : ltac2:(tb__ "0|0|
SaSbSd1S4cZcS5Sd3S36S2cA3S62S2cA1A3S89A2S47A3"). Proof. vmr. Qed.
Lemma mi_xff : ltac2:(tb__ "0|0|
SaSfS7eS89S4cZcS5Sd3S36S2cA3S62S2cA1A3A2S11A3"). Proof. vmr. Qed.
Lemma mi_needF : ltac2:(tb__ "0|0|
SaSfS8cZcZ3Z24S36S41S4ScS89A1A1A6S11A3"). Proof. vmr. Qed.
Lemma mi_tvp : ltac2:(tb__ "0|1|
SaSfSe0S27S73A1S15S13S0S0A2M0S80SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mi_chk : ltac2:(tb__ "0|0|
SaSfS8dVXGL;S47S80S2dS32ZcZ1f0S26S73A1S85S4aS52S44S2dS34S33S31A2A2AcS11A3"). Proof. vmr. Qed.
Lemma mi_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4aS1cS1eS47A4S20A2SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4aS1cS1fS47A4S20A2SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4aS1cS1dS47A4S23A2SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4aS1cS1eS47A4S26S22A1A2S9dA3"). Proof. vmr. Qed.
Lemma mi_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4aS1cS1dS47A4S21S25S24A2A2S99A3"). Proof. vmr. Qed.
Lemma T_mik0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS47S4aS52S1eS44S2dS34S33S31A2A2A6S6dA3"). Proof. vmr. Qed.
Lemma T_mik_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6dS45UeU1cZ1f0A3A2S16SbS4fA2A3"). Proof. vmr. Qed.
Lemma T_miks_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S6S3SdcA1S2dA2SeS1S4dS10S1A1A3A3S4fA2S50A3"). Proof. reflexivity. Qed.
Lemma mik_xff : ltac2:(tb__ "0|0|
SaSfS7eS4fSeS1S6S3SdcA1S2dA2SeS1S4dS10S1A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mik_ro0 : ltac2:(tb__ "0|1|
SaSfS81VXGL;S50SdS50A1S15S13S0S0A2M0S80SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3Z4Z5A6S11A3"). Proof. vmr. Qed.
Lemma mik_land : ltac2:(tb__ "0|1|
SaSfS7dSddS50SdS50A1S1bZ4Z5A5S60Sa6S15S13S0S0A2M0S80SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3Sb4S15S18S9dS85A3S93S27Sd4A1A8S11A3"). Proof. vmr. Qed.
Lemma mik_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa6S26Sd4A1A2S93A3"). Proof. vmr. Qed.
Lemma mik_live : ltac2:(tb__ "0|0|
SaSfSadS36S2cS32S4ScS4fA1A1A4S11A3"). Proof. vmr. Qed.
Lemma mik_colive : ltac2:(tb__ "0|0|
SaSfS8eS2cS31S4ScS4fA1A1A3S11A3"). Proof. vmr. Qed.
Lemma T_mif0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS47S4aS52S1fS44S2dS34S33S31A2A2A6S6aA3"). Proof. vmr. Qed.
Lemma T_mif_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6aS45UeU1cZ1f0A3A2S16SbS55A2A3"). Proof. vmr. Qed.
Lemma T_mifs_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S4dS10S1A1A3S55A2S6bA3"). Proof. reflexivity. Qed.
Lemma mif_xff : ltac2:(tb__ "0|0|
SaSfS7eS55SeS1S4dS10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mif_land : ltac2:(tb__ "0|2|
SaSfS7dS6bS7bSa4S15S13S0S0A2M0S80SeG0S12S0S0S2dS1aZcS32A2A4S10G0A1A3A3Sb2Sd2S18U1S85A3M1G1S27Sd9A1A8S11A3"). Proof. vmr. Qed.
Lemma mif_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa4S26Sd9A1A2Sd2S18U1S85A3A3"). Proof. vmr. Qed.
Lemma mif_colive : ltac2:(tb__ "0|0|
SaSfS8eS2cS31S4ScS55A1A1A3S11A3"). Proof. vmr. Qed.
Lemma T_mig0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS47S4aS52S1dS44S2dS34S33S31A2A2A6S6cA3"). Proof. vmr. Qed.
Lemma T_mig_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6cS45UeU1cZ1f0A3A2S16SbS56A2A3"). Proof. vmr. Qed.
Lemma T_migs_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S4dS10S1A1A3S56A2S4eA3"). Proof. reflexivity. Qed.
Lemma mig_xff : ltac2:(tb__ "0|0|
SaSfS7eS56SeS1S4dS10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mig_ro0 : ltac2:(tb__ "0|1|
SaSfS81VXGL;S4eSdS4eA1S15S13S0S0A2M0S80SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3Z4Z5A6S11A3"). Proof. vmr. Qed.
Lemma mig_land : ltac2:(tb__ "0|1|
SaSfS7dSddS4eSdS4eA1S1bZ4Z5A5S60Sa5S15S13S0S0A2M0S80SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3Sb3S15S18S99S85A3S92S27Sd4A1A8S11A3"). Proof. vmr. Qed.
Lemma mig_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa5S26Sd4A1A2S92A3"). Proof. vmr. Qed.
Lemma mig_colive : ltac2:(tb__ "0|0|
SaSfS8eS2cS31S4ScS56A1A1A3S11A3"). Proof. vmr. Qed.
Lemma mif_wp : bd_wpos brest_mi = true. Proof. vmr. Qed.

Lemma fv_robjs : ltac2:(tb__ "0|0|
SaS14S7A1S9ScS5eA1A1S15S7S74SeS7SdeS1bZ4Z5Sa0S8A5S10S7A1A3A3A3"). Proof. vmr. Qed.
Lemma fv_rel : ltac2:(tb__ "0|2|
SaSfSaeS5eS74Z4M0Z5Sa0S8SeS13SdfSdfA2M1S12SdfSdfZ20G0A4S10G1A1A3S27Sd4A1S26Sd4A1A9S11A3"). Proof. vmr. Qed.
Lemma E_fv1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS77S39U10Z210A2A2S16SbS88A2A3"). Proof. vmr. Qed.
Lemma E_fv_eq2 : ltac2:(tb__ "0|0|
SaSbSd1S4cZ4S5Sd3S35S3Z1A1A3S61S2cA1A3S88A2S46A3"). Proof. vmr. Qed.
Lemma fv_xff : ltac2:(tb__ "0|0|
SaSfS7eS88S4cZ4S5Sd3S35S3Z1A1A3S61S2cA1A3A2S11A3"). Proof. vmr. Qed.
Lemma fv_needF : ltac2:(tb__ "0|0|
SaSfS8cZ4Z1Z8S35S40S4ScS88A1A1A6S11A3"). Proof. vmr. Qed.
Lemma fv_tvp : ltac2:(tb__ "0|1|
SaSfSe0S27Sd4A1S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma fv_chk : ltac2:(tb__ "0|0|
SaSfS8dVXGL;S46S82S2bS30Z4Z210S26Sd4A1S84S49S51S44S2bS58A2AcS11A3"). Proof. vmr. Qed.
Lemma fv_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S49S1cS1eS46A4S20A2SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S49S1cS1fS46A4S20A2SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S49S1cS1dS46A4S23A2SeG0S12S0S0S2P208A1S1aZ4S2P209A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S49S1cS1eS46A4S26S22A1A2S9cA3"). Proof. vmr. Qed.
Lemma fv_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S49S1cS1dS46A4S21S25S24A2A2S98A3"). Proof. vmr. Qed.
Lemma T_fvk0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS46S49S51S1eS44S2bS58A2A6S68A3"). Proof. vmr. Qed.
Lemma T_fvk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS68S45UfU1dZ210A3A2S16SbS54A2A3"). Proof. vmr. Qed.
Lemma T_fvks_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S6S3SdcA1S2bA2S10S1A1A3S54A2S69A3"). Proof. reflexivity. Qed.
Lemma fvk_xff : ltac2:(tb__ "0|0|
SaSfS7eS54SeS1S6S3SdcA1S2bA2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma fvk_land : ltac2:(tb__ "0|1|
SaSfS7dS69S5fSa3S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3Sb1S15S18S9cS84A3S91S27Sd5A1A8S11A3"). Proof. vmr. Qed.
Lemma fvk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa3S26Sd5A1A2S91A3"). Proof. vmr. Qed.
Lemma fvk_live : ltac2:(tb__ "0|0|
SaSfS8fS35Z1S30S4ScS54A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_fvf0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS46S49S51S1fS44S2bS58A2A6S65A3"). Proof. vmr. Qed.
Lemma T_fvf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS65S45UfU1dZ210A3A2S16SbS5cA2A3"). Proof. vmr. Qed.
Lemma fvf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;S5cS72S75S2bS29S2aS33S3aS3cS3eS76S30S2eS2fS31S3bS3dS3fA10S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4M1S30A2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma fvf_land : ltac2:(tb__ "0|3|
SaSfS7dSddS5cS72S75S2bS29S2aS33S3aS3cS3eS76S30S2eS2fS31S3bS3dS3fA10S1bZ4M0Z5A5S7aSa1S15S13S0S0A2M1S82SeG1S12S0S0S2bS1aG0S30A2A4S10G1A1A3A3SafSd2S18U1S84A3M2G2S27Sd8A1A8S11A3"). Proof. vmr. Qed.
Lemma fvf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa1S26Sd8A1A2Sd2S18U1S84A3A3"). Proof. vmr. Qed.
Lemma T_fvg0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS46S49S51S1dS44S2bS58A2A6S67A3"). Proof. vmr. Qed.
Lemma T_fvg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS67S45UfU1dZ210A3A2S16SbS66A2A3"). Proof. vmr. Qed.
Lemma fvg_land : ltac2:(tb__ "0|1|
SaSfS7dS66S5fSa2S15S13S0S0A2M0S82SeG0S12S0S0S2P208A1S1aZ4S2P209A1A2A4S10G0A1A3A3Sb0S15S18S98S84A3S90S27Sd5A1A8S11A3"). Proof. vmr. Qed.
Lemma fvg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa2S26Sd5A1A2S90A3"). Proof. vmr. Qed.
Lemma fvf_wp : bd_wpos brest_fv = true. Proof. vmr. Qed.

Lemma E_mm1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS79S39U11Z230A2A2S16SbS8aA2A3"). Proof. vmr. Qed.
Lemma E_mm_eq2 : ltac2:(tb__ "0|0|
SaSbSd1S4cZ4S5Sd3S37S3Z1A1A3S63S2cA1A3S8aA2S48A3"). Proof. vmr. Qed.
Lemma mm_xff : ltac2:(tb__ "0|0|
SaSfS7eS8aS4cZ4S5Sd3S37S3Z1A1A3S63S2cA1A3A2S11A3"). Proof. vmr. Qed.
Lemma mm_needF : ltac2:(tb__ "0|0|
SaSfS8cZ4Z1Z8S37S42S4ScS8aA1A1A6S11A3"). Proof. vmr. Qed.
Lemma mm_tvp : ltac2:(tb__ "0|1|
SaSfSe0S27Sd5A1S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4S2eA2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mm_chk : ltac2:(tb__ "0|0|
SaSfS8dVXGL;S48S83S29S2eZ4Z230S26Sd5A1S86S4bS53S44S29S59S5aS5bA2A2AcS11A3"). Proof. vmr. Qed.
Lemma mm_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4bS1cS1eS48A4S20A2SeG0S12S0S0S29S1aZ4S2eA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4bS1cS1fS48A4S20A2SeG0S12S0S0S29S1aZ4S2eA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28S4bS1cS1dS48A4S23A2SeG0S12S0S0S2P314A1S1aZ4S2P315A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4bS1cS1eS48A4S26S22A1A2S9eA3"). Proof. vmr. Qed.
Lemma mm_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4bS1cS1dS48A4S21S25S24A2A2S9aA3"). Proof. vmr. Qed.
Lemma T_mmk0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS48S4bS53S1eS44S29S59S5aS5bA2A2A6S71A3"). Proof. vmr. Qed.
Lemma T_mmk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS71S45U10U1eZ230A3A2S16SbS57A2A3"). Proof. vmr. Qed.
Lemma T_mmks_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S6S3SdcA1S29A2S10S1A1A3S57A2ScaA3"). Proof. reflexivity. Qed.
Lemma mmk_xff : ltac2:(tb__ "0|0|
SaSfS7eS57SeS1S6S3SdcA1S29A2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mmk_land : ltac2:(tb__ "0|1|
SaSfS7dScaSc8Sa9S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4S2eA2A4S10G0A1A3A3Sb7S15S18S9eS86A3S95S27Sd6A1A8S11A3"). Proof. vmr. Qed.
Lemma mmk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa9S26Sd6A1A2S95A3"). Proof. vmr. Qed.
Lemma mmk_live : ltac2:(tb__ "0|0|
SaSfS8fS37Z1S2eS4ScS57A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_mmf0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS48S4bS53S1fS44S29S59S5aS5bA2A2A6S6eA3"). Proof. vmr. Qed.
Lemma T_mmf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6eS45U10U1eZ230A3A2S16SbS5dA2A3"). Proof. vmr. Qed.
Lemma mmf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;S5dSbfS29S2eA2S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4M1S2eA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma mmf_land : ltac2:(tb__ "0|3|
SaSfS7dSddS5dSbfS29S2eA2S1bZ4M0Z5A5ScfSa7S15S13S0S0A2M1S83SeG1S12S0S0S29S1aG0S2eA2A4S10G1A1A3A3Sb5Sd2S18U1S86A3M2G2S27SdaA1A8S11A3"). Proof. vmr. Qed.
Lemma mmf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa7S26SdaA1A2Sd2S18U1S86A3A3"). Proof. vmr. Qed.
Lemma T_mmg0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cS48S4bS53S1dS44S29S59S5aS5bA2A2A6S70A3"). Proof. vmr. Qed.
Lemma T_mmg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS70S45U10U1eZ230A3A2S16SbS6fA2A3"). Proof. vmr. Qed.
Lemma mmg_land : ltac2:(tb__ "0|1|
SaSfS7dS6fSc8Sa8S15S13S0S0A2M0S83SeG0S12S0S0S2P314A1S1aZ4S2P315A1A2A4S10G0A1A3A3Sb6S15S18S9aS86A3S94S27Sd6A1A8S11A3"). Proof. vmr. Qed.
Lemma mmg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa8S26Sd6A1A2S94A3"). Proof. vmr. Qed.
Lemma mmf_wp : bd_wpos brest_mm = true. Proof. vmr. Qed.

Lemma E_sg1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cSceS39U12Z250A2A2S16SbS8bA2A3"). Proof. vmr. Qed.
Lemma E_sg_eq2 : ltac2:(tb__ "0|0|
SaSbSd1S4cZ4S5Sd3S38S3Z1A1A3S64S2cA1A3S8bA2SbdA3"). Proof. vmr. Qed.
Lemma sg_xff : ltac2:(tb__ "0|0|
SaSfS7eS8bS4cZ4S5Sd3S38S3Z1A1A3S64S2cA1A3A2S11A3"). Proof. vmr. Qed.
Lemma sg_needF : ltac2:(tb__ "0|0|
SaSfS8cZ4Z1Z8S38S43S4ScS8bA1A1A6S11A3"). Proof. vmr. Qed.
Lemma sg_tvp : ltac2:(tb__ "0|1|
SaSfSe0S27Sd6A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma sg_chk : ltac2:(tb__ "0|0|
SaSfS8dVXGL;SbdS7fS2aS2fZ4Z250S26Sd6A1S87SbeSc4S44S2aSbfSc6Sc7A2A2AcS11A3"). Proof. vmr. Qed.
Lemma sg_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28SbeS1cS1eSbdA4S20A2SeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28SbeS1cS1fSbdA4S20A2SeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbbS28SbeS1cS1dSbdA4S23A2SeG0S12S0S0S2P290A1S1aZ4S2P291A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28SbeS1cS1eSbdA4S26S22A1A2S9fA3"). Proof. vmr. Qed.
Lemma sg_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28SbeS1cS1dSbdA4S21S25S24A2A2S9bA3"). Proof. vmr. Qed.
Lemma T_sgk0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cSbdSbeSc4S1eS44S2aSbfSc6Sc7A2A2A6ScdA3"). Proof. vmr. Qed.
Lemma T_sgk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cScdS45U11U1fZ250A3A2S16SbSc5A2A3"). Proof. vmr. Qed.
Lemma T_sgks_eq2 : ltac2:(tb__ "0|0|
SaSbSd1SeS1S6S3SdcA1S2aA2S10S1A1A3Sc5A2Sc3A3"). Proof. reflexivity. Qed.
Lemma sgk_xff : ltac2:(tb__ "0|0|
SaSfS7eSc5SeS1S6S3SdcA1S2aA2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma sgk_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc3Sc0Sc3A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4M1S2fA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgk_land : ltac2:(tb__ "0|2|
SaSfS7dSddSc3Sc0Sc3A1S1bZ4M0Z5A5Sc9SacS15S13S0S0A2M1S7fSeG1S12S0S0S2aS1aG0S2fA2A4S10G1A1A3A3SbaS15S18S9fS87A3S97S27Sd7A1A8S11A3"). Proof. vmr. Qed.
Lemma sgk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SacS26Sd7A1A2S97A3"). Proof. vmr. Qed.
Lemma sgk_live : ltac2:(tb__ "0|0|
SaSfS8fS38Z1S2fS4ScSc5A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_sgf0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cSbdSbeSc4S1fS44S2aSbfSc6Sc7A2A2A6ScbA3"). Proof. vmr. Qed.
Lemma T_sgf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cScbS45U11U1fZ250A3A2S16SbSc1A2A3"). Proof. vmr. Qed.
Lemma sgf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc1Sc0Sc1A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4M1S2fA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgf_land : ltac2:(tb__ "0|3|
SaSfS7dSddSc1Sc0Sc1A1S1bZ4M0Z5A5Sd0SaaS15S13S0S0A2M1S7fSeG1S12S0S0S2aS1aG0S2fA2A4S10G1A1A3A3Sb8Sd2S18U1S87A3M2G2S27SdbA1A8S11A3"). Proof. vmr. Qed.
Lemma sgf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SaaS26SdbA1A2Sd2S18U1S87A3A3"). Proof. vmr. Qed.
Lemma T_sgg0_ta : ltac2:(tb__ "0|0|
SaSbSbcS1cSbdSbeSc4S1dS44S2aSbfSc6Sc7A2A2A6SccA3"). Proof. vmr. Qed.
Lemma T_sgg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cSccS45U11U1fZ250A3A2S16SbSc2A2A3"). Proof. vmr. Qed.
Lemma sgg_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc2Sc0Sc2A1S15S13S0S0A2M0S7fSeG0S12S0S0S2P290A1S1aZ4M1S2P291A1A2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgg_land : ltac2:(tb__ "0|2|
SaSfS7dSddSc2Sc0Sc2A1S1bZ4M0Z5A5Sc9SabS15S13S0S0A2M1S7fSeG1S12S0S0S2P290A1S1aG0S2P291A1A2A4S10G1A1A3A3Sb9S15S18S9bS87A3S96S27Sd7A1A8S11A3"). Proof. vmr. Qed.
Lemma sgg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SabS26Sd7A1A2S96A3"). Proof. vmr. Qed.
Lemma sgf_wp : bd_wpos brest_sg = true. Proof. vmr. Qed.
End G.
End Lib_handle_f_g3.

(* [comment removed for export] *)
Module Lib_handle_f_g7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "DUnknown"; "cell"; "ss_objs"; "ss_facts"; "ob_cells"; "ob_dflt"; "sprop"; "ss_next"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "true"; "cons"; "prod"; "app"; "list"; "Some"; "option"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_tv"; "nd_bd"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "shadow_release_stateA"; "shadow_reopen_stateA"; "release_objs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "ndEf"; "ndEo"; "co_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "release_chk"; "reopen_chk"; "feF"; "pure_chk"; "purec_chk"; "xff_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "XLJf"; "XEf6a1"; "XEf6b1"; "XEo61"; "XJ1"; "X_rlf1"; "X_rlo1"; "sh_f5f1"; "sh_f5o1"; "E_f5f1"; "E_f5o1"; "T_f5f1"; "T_f5o1"; "T_tdg2"; "T_wdg2"; "XLJ1"; "objs_Ef42"; "objs_Ef6a1"; "objs_Ef6b1"; "objs_Eo42"; "objs_Eo61"; "objs_J"; "carve_chk"; "objs_Ef6a"; "objs_Ef6b"; "objs_Eo6"; "objs_XJ"; "objs_f5f1"; "objs_f5o1"; "liveLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi"; "E_f5f0"; "E_f5o0"; "NREL"; "XR"; "C_Ef2"; "XEf42"; "XEo42"; "C_Eo2"; "E_f5f"; "E_f5o"; "L_f5"; "Pre_f5"; "T_f5f0"; "T_f5o0"; "ilast"; "sel_rel"; "xf_shback"; "C_rlf"; "C_rlo"; "R_f5f"; "R_f5o"; "X_rlf"; "X_rlo"; "s_f5f"; "s_f5o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "release0_chk"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "XJ"; "XT"; "E_wdg"; "J"; "R_wdg"; "T_wdg"; "T_wdg0"; "s_wdg"; "sel_wdg"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndJN"; "ndLL"; "ndTR"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "XTR"; "pDtr"; "pKtr"; "E_tdg"; "R_tdg"; "T_tdg"; "T_tdg0"; "s_tdg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "XLJ"; "L14"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H"; "P_bwH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pKco"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "sel_da"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma tdg_chk : ltac2:(tb__ "0|0|
S0SbS2cS8bS8aS7eS79S82S7fA6ScA3"). Proof. vmr. Qed.
Lemma T_tdg2_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS81SdS1aS1cS8dA1SdS1aS1dU0A1SaS1aA1A3A3A2S11S14S3cA2A3"). Proof. vmr. Qed.
Lemma T_tdg_eq2 : ltac2:(tb__ "0|0|
S0S14S86S3cS7bS7cS7dA2A2S80A3"). Proof. vmr. Qed.
Lemma tdg_xsub : ltac2:(tb__ "0|0|
S0SbS87S7bS7cS7dA2S16S3cA1A2ScA3"). Proof. vmr. Qed.
Lemma wdg_chk : ltac2:(tb__ "0|0|
S0SbS2cS88S89S6dS7aS72S6fA6ScA3"). Proof. vmr. Qed.
Lemma T_wdg2_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS71SdS1aS1cS73A1SdS1aS1dU0A1SaS1aA1A3A3A2S11S14S3dA2A3"). Proof. vmr. Qed.
Lemma T_wdg_eq2 : ltac2:(tb__ "0|0|
S0S14S86S3dS6cA2S70A3"). Proof. vmr. Qed.
Lemma wdg_xsub : ltac2:(tb__ "0|0|
S0SbS87S6cS16S3dA1A2ScA3"). Proof. vmr. Qed.

Lemma XJ_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S6bA1A1SfS1S49SdS1S22S19Z14Z17SaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XJ_rel : ltac2:(tb__ "0|0|
S0SbS66S6bZ14Z17S2A4ScA3"). Proof. vmr. Qed.
Lemma XJ1_eq : ltac2:(tb__ "0|0|
S0S14S23S6bS49Pa0SaSeS18S18A2A1A4S33A3"). Proof. vmr. Qed.
Lemma XJ1_objs : ltac2:(tb__ "0|0|
S0S10S1A1S4S15S33A1A1SfS1S44SdS1S22S19Z6ZfSaS3A1S2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma XJ1_rel : ltac2:(tb__ "0|0|
S0SbS29S33S44Z6ZfSaS3A1S2SaSeS18S18A2A1S1fS77A1S20S77A1A9ScA3"). Proof. vmr. Qed.
Lemma J_eq2 : ltac2:(tb__ "0|0|
S0S14S23S33S44Pa0SaSeS18S18A2A1A4S6eA3"). Proof. vmr. Qed.

Lemma XLJ_xff : ltac2:(tb__ "0|0|
S0SbS2eS83SdS8S28SaS8A1A3A2ScA3"). Proof. vmr. Qed.
Lemma XLJ_live : ltac2:(tb__ "0|0|
S0SbS4cS8cS5S15S83A1A1A2ScA3"). Proof. vmr. Qed.
Lemma XLJ_ro0 : ltac2:(tb__ "0|0|
S0SbS2aVXGL;S2fS16S2fA1S1fS78A1Z1cZ21A6ScA3"). Proof. vmr. Qed.
Lemma XLJ1_eq : ltac2:(tb__ "0|0|
S0S14S24S2fS16S2fA1S19Z1cZ21A5S3eA3"). Proof. vmr. Qed.
Lemma XLJ_ro1 : ltac2:(tb__ "0|0|
S0SbS67VXGL;S3eS16S2fA1S1fS78A1Z26Z27A6ScA3"). Proof. vmr. Qed.
Lemma L14_eq2 : ltac2:(tb__ "0|0|
S0S14S24S3eS16S2fA1S19Z26Z27A5S84A3"). Proof. vmr. Qed.

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
S0S14S17S35S85S15S35A1M0S74S1S4fS4G0A1A3A2A2S5fA3"). Proof. vmr. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|0|
S0S12S14A1S1bS62SdS1aS1cS5cA1SaS1aA1A3A2S11S14S34A2A3"). Proof. vmr. Qed.
Lemma rlf_chk : ltac2:(tb__ "0|1|
S0SbS13S13S25Pa0PaaS19Z3S75S1S4fS4S15S34A1M0A1A3A5S2bS5G0A1A1A2S21S9G0A1S26A2A2ScA3"). Proof. vmr. Qed.
Lemma C_rlf_eq2 : ltac2:(tb__ "0|1|
S0S14S17S34S85S15S34A1M0S74S1S4fS4G0A1A3A2A2S5eA3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g7.

(* [comment removed for export] *)
Module Lib_handle_f_g8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "xr_below"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "cons"; "Some"; "option"; "pair"; "prod"; "app"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_facts"; "sv"; "ss_next"; "sprop"; "ss_objs"; "obj_wf"; "sprop_below"; "sstate"; "DUnknown"; "swf"; "SLit"; "SPUle"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "E_pg4"; "E_pg0t"; "T_pgi0"; "T_pgo0"; "xRFX"; "s_pg"; "xPRV"; "Xk_pg"; "xNXT"; "E_pg"; "E_pg3"; "objs_butlast"; "xP2D"; "E_pg0"; "O_nxt'"; "O_prv'"; "O_rfx'"; "R_pg"; "xOUT"; "E_pg1"; "news72"; "rt72"; "xPTS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "pgF"; "E_pg0r"; "E_pg3a"; "E_pg3b"; "T_pgi3"; "T_pgia"; "T_pgib"; "T_pgo3"; "T_pgoa"; "T_pgob"; "T_pgi2"; "T_pgi4"; "T_pgiR1"; "T_pgo2"; "T_pgo4"; "T_pgoR1"; "O_nxt1"; "O_prv1"; "O_rfx1"; "T_pgic"; "cells_pg"; "O_nxt"; "O_prv"; "O_rfx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "reshapeA"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "XT"; "O_nxt0"; "O_prv0"; "O_rfx0"; "T_pgi1"; "XT6"; "T_pgi"; "T_pgo"; "T_pgo1"; "xf_pgb1"; "xf_pgb2"; "T_pgiR"; "T_pgoR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_gdefs4"; "F_pg"; "E_pgF"; "Pre_pgF"; "E_pgS"; "Pre_pgS"; "facts_sub"; "R_pgF"; "T_pgi0F"; "T_pgo0F"; "F_pgC"; "P_invF"; "P_okF"; "pgEF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xr_eqb"; "T_afterA3"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "pKts"; "pDts"; "needA"; "pDrp"; "pKrp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_tv"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g8.AR"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "reopen_chk"; "xff_chk"; "release_chk"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA"; "arr_merge_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "retile_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ol.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_gdefs4.
Module AR. Include Lib_handle_f_arith. End AR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).
Lemma E_pg0t_rt : ltac2:(tb__ "0|0|
S0SbS19A1S92S1S2cA1U1S34S33A4SaS19S1S20A1A2A3"). Proof. vmr. Qed.
Lemma E_pg0t_eq2 : ltac2:(tb__ "0|0|
S0S2S5S2cS1S20A1A2S20A3"). Proof. vmr. Qed.
Lemma E_pg0t_wf : ltac2:(tb__ "0|0|
S0S6S1bS1S20A1A1S7A3"). Proof. vmr. Qed.
Lemma pg_robjs : ltac2:(tb__ "0|0|
S0S10S11A1S16S1S20A1A1SeS11S2aS20A1S9S11S85S61Z6Z17S4bS1aA5SfS11A1A3A3A3"). Proof. vmr. Qed.
Lemma pg_rel : ltac2:(tb__ "0|1|
S0S6S89S20S2aS20A1Z6Z17S4bS1aS9SdS36S36A2M0ScS36S36Za0Z18A4S9G0ScS36S36Z30Z48A4SfG0A1A3A3S7eS6fA1S7fS6fA1A9S7A3"). Proof. vmr. Qed.
Lemma E_pg0r_eq : ltac2:(tb__ "0|1|
S0S2S84S20S2aS20A1Pa0S9SdS36S36A2M0ScS36S36Za0Z18A4S9G0ScS36S36Z30Z48A4SfG0A1A3A3A4S38A3"). Proof. vmr. Qed.
Lemma E_pg1_eq2 : ltac2:(tb__ "0|0|
S0S2S8cS86S38A2S32A3"). Proof. vmr. Qed.
Lemma pg_xff : ltac2:(tb__ "0|0|
S0S6S88S38S86A2S7A3"). Proof. vmr. Qed.
Lemma pg_tsF : ltac2:(tb__ "0|1|
S0S6S8S8aS12S1S38A1A1M0A1S51S15S1eS1dS79S77A2A1G0A3A2S7A3"). Proof. vmr. Qed.
Lemma pg_o43 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S29A1A1U2bA3SaS11S4cA2A3"). Proof. vmr. Qed.
Lemma pg_wf43 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S29A1M0A1S2dA2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg3a_eq : ltac2:(tb__ "0|0|
S0S2S4fS29U2bS2dA3S39A3"). Proof. vmr. Qed.
Lemma pg_o45 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S39A1A1U2dA3SaS11S4dA2A3"). Proof. vmr. Qed.
Lemma pg_wf45 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S39A1M0A1S2eA2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg3b_eq : ltac2:(tb__ "0|0|
S0S2S4fS39U2dS2eA3S3aA3"). Proof. vmr. Qed.
Lemma pg_o47 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S3aA1A1U2fA3SaS11S4eA2A3"). Proof. vmr. Qed.
Lemma pg_wf47 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3aA1M0A1S2fA2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg4_eq2 : ltac2:(tb__ "0|0|
S0S2S4fS3aU2fS2fA3S1fA3"). Proof. vmr. Qed.
Lemma pg_pgF4 : ltac2:(tb__ "0|0|
S0S6S37S12S1S1fA1A1A1S7A3"). Proof. vmr. Qed.

Lemma pgx_rfx : ltac2:(tb__ "0|0|
S0S6S8S51SdS13S13A2S74ScS13S13S78S60Z1S77A2A4A1S3S1fA1A3S4S14S1S1fA1A1S23A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_prv : ltac2:(tb__ "0|1|
S0S6S8S51SdS13S13A2M0S74ScS13S13S78S60Z1S77A2A4A1S9G0S23S3S1fA1A3A3S4S14S1S1fA1A1S25A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_nxt : ltac2:(tb__ "0|1|
S0S6S8S51SdS13S13A2M0S74ScS13S13S78S60Z1S77A2A4A1S9G0S25S9G0S23S3S1fA1A3A3A3S4S14S1S1fA1A1S27A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_p2d : ltac2:(tb__ "0|1|
S0S6S8S51SdS13S13A2M0S74ScS13S13S78S60Z1S77A2A4A1S9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3S4S14S1S1fA1A1S2bA2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_out : ltac2:(tb__ "0|1|
S0S6S8S51SdS13S13A2M0S74ScS13S13S8eS60Z4S8fA2A4A1S9G0S2bS9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3A3S4S14S1S1fA1A1S31A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_pts : ltac2:(tb__ "0|1|
S0S6S8S51SdS13S13A2M0S74ScS13S13S7aS60Z4S7bA2A4A1S9G0S31S9G0S2bS9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3A3A3S4S14S1S1fA1A1S35A2A2S7A3"). Proof. vmr. Qed.

Lemma E_pgS_eq : ltac2:(tb__ "0|0|
S0SbS2A1S70S28S9S71S73U5S1cZ10A1A2SfS71A1A3A2SaS2S65A2A3"). Proof. vmr. Qed.
Lemma E_pgF_eq : ltac2:(tb__ "0|0|
S0S2S8cS6bS65A2S63A3"). Proof. vmr. Qed.
Lemma pgF_xff : ltac2:(tb__ "0|0|
S0S6S88S65S6bA2S7A3"). Proof. vmr. Qed.
Lemma pgF_site : ltac2:(tb__ "0|1|
S0S6S8S37S12S1S65A1A1M0A1S6eG0A1A2S7A3"). Proof. vmr. Qed.
Lemma pgF_callF : ltac2:(tb__ "0|0|
S0S6S37S12S1S63A1A1A1S7A3"). Proof. vmr. Qed.
Lemma pg_chkF : pg_call_chkF XGL = true. Proof. vmr. Qed.
Lemma R_pgF_eq : ltac2:(tb__ "0|1|
S0SbS10S11A1M0A1S90S63S64S24A3SaG0S68A2A3"). Proof. vmr. Qed.
Lemma Pre_pg_merge : ltac2:(tb__ "0|0|
S0SbS2A1S70S66S9S71S72U3A1SfS71A1A3A2SaS2S82A2A3"). Proof. vmr. Qed.
Lemma Pre_pgS_drop : ltac2:(tb__ "0|0|
S0S2S7cS64S12S1S66A1A1A2S66A3"). Proof. vmr. Qed.
Lemma Pre_pgS_chk : ltac2:(tb__ "0|3|
S0S6S8S8S8S52S15S18S14S1S64A1M0A1A1S12S1S66A1A1M1A3S67G1S12G0A1M2A2A2S67S62G2A2A2S52S15S18S91A1S62A3A2S7A3"). Proof. vmr. Qed.
Lemma P_okF_eq : ltac2:(tb__ "0|0|
S0S2S7cS81SeS15S62S12S1S81A1A1A3A2S6dA3"). Proof. vmr. Qed.
Lemma P_invF_eq : ltac2:(tb__ "0|0|
S0S2S7cS80SeS15S62S12S1S80A1A1A3A2S6cA3"). Proof. vmr. Qed.
Lemma P_F_below : ltac2:(tb__ "0|2|
S0S6S8S52S15S18S14S1S81A1M0A1A1SeS15S62S12G0A1A3A3S52S15S18S14S1S80A1M1A1A1SeS15S62S12G1A1A3A3A2S7A3").
Proof. vmr. Qed.
Lemma T_pgo0F_ta : ltac2:(tb__ "0|0|
S0S2S75S64S63S24S68S6dS26A6S6aA3"). Proof. vmr. Qed.
Lemma T_pgi0F_ta : ltac2:(tb__ "0|0|
S0S2S75S64S63S24S68S6cS26A6S69A3"). Proof. vmr. Qed.
Lemma T_pgo0_drop : ltac2:(tb__ "0|0|
S0S2S7cS6aS12S1S22A1A1A2S22A3"). Proof. vmr. Qed.
Lemma T_pgi0_drop : ltac2:(tb__ "0|0|
S0S2S7cS69S12S1S21A1A1A2S21A3"). Proof. vmr. Qed.
Lemma T_pg0_chk : ltac2:(tb__ "0|4|
S0S6S8S8S8S52S15S18S14S1S6aA1M0A1A1S12S1S22A1A1M1A3S67G1S12G0A1A2A2S52S15S18S14S1S69A1M2A1A1S12S1S21A1A1M3A3A2S67G3S12G2A1A2A2S7A3"). Proof. vmr. Qed.

Lemma T_pgo0_ta : ltac2:(tb__ "0|0|
S0S2S75S82S28S24S30S81S26A6S22A3"). Proof. vmr. Qed.
Lemma pgo_o8 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S22A1A1U8A3SaS11S47A2A3"). Proof. vmr. Qed.
Lemma pgo_wf8 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S22A1M0A1S54A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgoa_eq : ltac2:(tb__ "0|0|
S0S2S4fS22U8S54A3S3fA3"). Proof. vmr. Qed.
Lemma pgo_o9 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S3fA1A1U9A3SaS11S48A2A3"). Proof. vmr. Qed.
Lemma pgo_wf9 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3fA1M0A1S55A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgob_eq : ltac2:(tb__ "0|0|
S0S2S4fS3fU9S55A3S40A3"). Proof. vmr. Qed.
Lemma pgo_o10 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S40A1A1UaA3SaS11S49A2A3"). Proof. vmr. Qed.
Lemma pgo_wf10 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S40A1M0A1S56A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgo1_eq2 : ltac2:(tb__ "0|0|
S0S2S4fS40UaS56A3S5bA3"). Proof. vmr. Qed.
Lemma T_pgo2_eq : ltac2:(tb__ "0|0|
S0SbS2A1S70S5bS5cA2SaS2S44A2A3"). Proof. vmr. Qed.
Lemma T_pgo3_am : ltac2:(tb__ "0|0|
S0SbS19A1S8dS1S44A1U22A2SaS19S1S3eA1A2A3"). Proof. vmr. Qed.
Lemma T_pgo3_eq2 : ltac2:(tb__ "0|0|
S0S2S5S44S1S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma T_pgo4_eq : ltac2:(tb__ "0|0|
S0SbS2A1S70S3eS5dA2SaS2S45A2A3"). Proof. vmr. Qed.
Lemma T_pgo_eq2 : ltac2:(tb__ "0|0|
S0S2S7dS45S58A2S5aA3"). Proof. vmr. Qed.
Lemma pgo_xsub : ltac2:(tb__ "0|0|
S0S6S76S58S3S45A1A2S7A3"). Proof. vmr. Qed.
Lemma pgo_ro1 : ltac2:(tb__ "0|0|
S0S6S87VXGL;S5aS53S7eS6fA1Z6ZfA6S7A3"). Proof. vmr. Qed.
Lemma T_pgoR1_eq : ltac2:(tb__ "0|0|
S0S2S83S5aS53S61Z6ZfA5S46A3"). Proof. vmr. Qed.
Lemma pgo_ro2 : ltac2:(tb__ "0|0|
S0S6S8bVXGL;S46S53S7eS6fA1Z14Z17A6S7A3"). Proof. vmr. Qed.
Lemma T_pgoR_eq2 : ltac2:(tb__ "0|0|
S0S2S83S46S53S61Z14Z17A5S5fA3"). Proof. vmr. Qed.

Lemma T_pgi0_ta : ltac2:(tb__ "0|0|
S0S2S75S82S28S24S30S80S26A6S21A3"). Proof. vmr. Qed.
Lemma pgi_o8 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S21A1A1U8A3SaS11S47A2A3"). Proof. vmr. Qed.
Lemma pgi_wf8 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S21A1M0A1S54A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgia_eq : ltac2:(tb__ "0|0|
S0S2S4fS21U8S54A3S3cA3"). Proof. vmr. Qed.
Lemma pgi_o9 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S3cA1A1U9A3SaS11S48A2A3"). Proof. vmr. Qed.
Lemma pgi_wf9 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3cA1M0A1S55A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgib_eq : ltac2:(tb__ "0|0|
S0S2S4fS3cU9S55A3S3dA3"). Proof. vmr. Qed.
Lemma pgi_o10 : ltac2:(tb__ "0|0|
S0SbS11A1S50S11S16S1S3dA1A1UaA3SaS11S49A2A3"). Proof. vmr. Qed.
Lemma pgi_wf10 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3dA1M0A1S56A2S37S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgic_eq2 : ltac2:(tb__ "0|0|
S0S2S4fS3dUaS56A3S4aA3"). Proof. vmr. Qed.
Lemma T_pgi1_c : T_pgic = T_pgi1.     Proof. vmr. Qed.
Lemma T_pgi1_wf : ltac2:(tb__ "0|0|
S0S6S1bS1S57A1A1S7A3"). Proof. vmr. Qed.
Lemma T_pgi1_eq2 : ltac2:(tb__ "0|0|
S0S2S5S4aS1S57A1A2S57A3"). Proof. vmr. Qed.
Lemma T_pgi2_eq : ltac2:(tb__ "0|0|
S0SbS2A1S70S57S5cA2SaS2S41A2A3"). Proof. vmr. Qed.
Lemma T_pgi3_am : ltac2:(tb__ "0|0|
S0SbS19A1S8dS1S41A1U22A2SaS19S1S3bA1A2A3"). Proof. vmr. Qed.
Lemma T_pgi3_eq2 : ltac2:(tb__ "0|0|
S0S2S5S41S1S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma T_pgi4_eq : ltac2:(tb__ "0|0|
S0SbS2A1S70S3bS5dA2SaS2S42A2A3"). Proof. vmr. Qed.
Lemma T_pgi_eq2 : ltac2:(tb__ "0|0|
S0S2S7dS42S58A2S59A3"). Proof. vmr. Qed.
Lemma pgi_xsub : ltac2:(tb__ "0|0|
S0S6S76S58S3S42A1A2S7A3"). Proof. vmr. Qed.
Lemma pgi_ro1 : ltac2:(tb__ "0|0|
S0S6S87VXGL;S59S53S7eS6fA1Z6ZfA6S7A3"). Proof. vmr. Qed.
Lemma T_pgiR1_eq : ltac2:(tb__ "0|0|
S0S2S83S59S53S61Z6ZfA5S43A3"). Proof. vmr. Qed.
Lemma pgi_ro2 : ltac2:(tb__ "0|0|
S0S6S8bVXGL;S43S53S7eS6fA1Z14Z17A6S7A3"). Proof. vmr. Qed.
Lemma T_pgiR_eq2 : ltac2:(tb__ "0|0|
S0S2S83S43S53S61Z14Z17A5S5eA3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g8.

(* [comment removed for export] *)
Module Lib_handle_f_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sobj"; "SLit"; "holds"; "SAlu"; "ss_facts"; "ss_next"; "sprop_eqb"; "SPUle"; "DUnknown"; "ss_objs"; "soff"; "mkObj"; "cell"; "eval"; "SMd"; "odefault"; "sv_eqb"; "dflt_writable"; "obj_wf"; "SPBranch"; "SExt"; "SPUlt"; "sv_below"; "SPNot"; "agree_below"; "ob_dflt"; "obj_range"; "ob_base"; "ob_cells"; "obj_hi_of"; "obj_lo_of"; "SVar"; "sprop_below"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "False"; "True"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "cons"; "andb"; "nil"; "nat"; "app"; "option"; "Some"; "None"; "fst"; "snd"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "xr_ok"; "ax_base"; "la_state"; "xr_below"; "ax_setS"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_subst"; "bd_wpos"; "BXok_d"; "bxt"; "BUD"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "modulo"; "mul"; "lt"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "emeasA"; "ANone"; "NDA"; "PTrue"; "nd_tv"; "nd_bd"; "tvinA"; "nd_below"; "JA_pre"; "TPA"; "frinA"; "nd_am"; "nd_fr"; "fbinA"; "ffinA"; "JAi"; "am_subst"; "fr_sub_eqb"; "JA"; "JLA"; "am_eqb"; "amode"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "fr_hf"; "pA"; "pQ"; "reshapeA"; "am2"; "ndR"; "mi_c"; "nd0"; "pDco"; "pKco"; "E_co0"; "Pre_hf"; "mi_n"; "xfo"; "E_sm0"; "L_ms"; "L_sm"; "PD_vn"; "Pre_ms"; "Pre_sm"; "X_pro"; "co_need"; "pT0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "kb"; "hG"; "hF"; "tE"; "av_nv"; "av_k"; "tL"; "av_d"; "tB"; "tI"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_NE"; "ALU_SUB"; "BC_LTU"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "z0"; "ndLL"; "VL"; "ndTS"; "VR"; "ndTR"; "ndRP"; "ndFV"; "ndJ"; "ndJN"; "ndL4a"; "ndL4b"; "ndL4c"; "ndMI"; "ndMM"; "ndP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o0.Lib_handle_f_iface"; "P0_hf"; "P0_hf_b"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "import_subA"; "call_checkPA"; "import_postA"; "J_ofPA"; "call_checkA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "two47"; "B_EW"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals";
"call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "s_pg"; "Xk_pg"; "E_pg0"; "objs_butlast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "rho_absorb"; "wsub_get"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "shadow_release_stateA"; "xrs_checkL"; "robjs_checkF"; "shadow_reopen_stateA"; "flag_carve_stateA"; "release_objs_ok"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "nd0"; "tv0"; "bdP"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "pKts"; "needA"; "pDts"; "pKrp"; "E_rp0"; "E_ts0"; "X_avnull"; "pDrp"; "need_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf"; "VM"; "DW_rng"; "r8f"; "x16f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "ndEf"; "ndXA"; "ndEo"; "vr_need"; "E_fv0"; "E_mi0"; "E_mm0"; "NMI"; "X_conull"; "E_dg0"; "L_mc1"; "Pre_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "tvd"; "T_ok"; "FBx"; "import_tv"; "tv_sub_eqb"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.Sum"; "HNPH"; "Posts_hfJ"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "pL"; "E_g1_0"; "E_g2_0"; "E_g3_0"; "XLJ"; "cMI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "fF"; "release_chk"; "triAF"; "purec_chk"; "rsFk"; "vlF"; "vr3F"; "vrLF"; "xff_chk"; "bF"; "coF"; "feF"; "gF"; "land_chk"; "live3F"; "liveF"; "liveFa"; "liveRp"; "liveTri"; "liveTs"; "pure_chk"; "reopen_chk"; "roomF"; "rsF"; "slotF"; "vrF"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.AR"; "o4A"; "o16A"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "a16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.PGP"; "P0_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "AE_A"; "J_pure_pre"; "JL_stack_malloc"; "J_memcpy_pre"; "J_memset_pre"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_gdefs4"; "E_pgF"; "R_pgF"; "PD_pgF"; "Pre_pgF"; "F_pgC"; "facts_sub"; "pgEF"; "pg_call_chkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.PGC"; "nd0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "E_wdg0"; "XJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "PostsC"; "T_afterA3"; "pclMA"; "xrs_inclb"; "xr_eqb"; "pd_okA"; "pdescA"; "robjs_okF"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "T_afterA"; "payA"; "xrs_okA"; "call_checkTA"; "is_shadowZ"; "robjs_okA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pKtr"; "E_tdg0"; "E_trb0"; "E_trg0"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi"; "E_f5f0"; "E_f5o0"; "NREL"; "P_fail"; "P_ok"; "XEf42"; "XEo42"; "nd_fail"; "nd_ok"; "L_f5"; "Pre_f5"; "X_rlf"; "X_rlo"; "sel_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "pgF"; "carve_chk"; "liveLF"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "release0_chk"; "is_shx"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_gdefs5"; "releaseP_chk"; "reopenC_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "E_da0"; "E_pc0"; "xslot"; "pc_need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3"; "E_sg0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w"; "E_mi4_0_0"; "E_mi4_0_4"; "E_mi4_1w"; "L_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "E_fv4_0"; "E_mi4_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b"; "E_mm4_0"; "E_sg4_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_pf.Sum.X"; "PD_pg"; "avnullF"; "conullF"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3 SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_shx Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ol.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_g9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require om.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oi.Lib_handle_f_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oi.Lib_handle_f_eqs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_shx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_gdefs4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_gdefs5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_g1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_g1b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_g2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_g5a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_g5b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g5c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_g5d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_g5d2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_g5d3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ok.Lib_handle_f_g5d4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_g6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ou.Lib_handle_f_g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_g9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o0.Lib_handle_f_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf. End VNP.
Module PGP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_tess_polygon_pf. End PGP.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.
Module AR. Include Lib_handle_f_arith. End AR.

Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 512 < 2 ^ 40. Proof. lia. Qed.

Definition VM (e c : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S8Sa2S98Z40S8Sa5Ve;Vc;A3A2S6Vpos;A1A3").
Lemma VR_VM : ltac2:(tb__ "0|0|
S2S0S26S2SacR2R1A2S100S9bR2R1A3A3Fpos;Fc;"). Proof. reflexivity. Qed.
Lemma VL_VM : ltac2:(tb__ "0|0|
S0S26S2SaaR1A1S100S16cS124R1A3A3Fpos;"). Proof. reflexivity. Qed.
Lemma VM_val : ltac2:(tb__ "0|2|
S3S2S2S0S27S53S48R4R2A2S48R4R3A2M0A2S53G0S55Z2Z28A2A2A2S27S53Z0R2A2S58R2Z40M1A2A2S26S0S48R6S100R5R4R3A3A2S54S57G1S59S48R6R5A2S48R6R4A2A2A2R3A2A3F_;F_;Fa;Fc;Fe;Frho;").
Proof.
  intros rho e c a [Hce He] Ha. pose proof (uval_range rho c) as Rc. pose proof (uval_range rho e) as Re.
  assert (ES : uval rho (SAlu ALU_SUB e c) = uval rho e - uval rho c).
  { destruct (U_sub_q rho e c) as [k Hk]. unfold U in Hk. unfold uval in *.
    pose proof (bv_urange (eval rho (SAlu ALU_SUB e c))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia. }
  assert (EM : uval rho (kb 64 (SAlu ALU_SUB e c)) = 64 * (uval rho e - uval rho c)).
  { unfold kb. rewrite uval_mul_lit by lia. rewrite ES. reflexivity. }
  unfold VM. rewrite uval_add_litZ by (rewrite ?EM; lia). rewrite EM. lia.
Qed.

Lemma vrF_bound : ltac2:(tb__ "0|1|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S145R2R3A2S31A3S27S53S48R5R3A2S48R5S9bA2M0A2S53G0S55Z2Z28A2A2A2F_;F_;Fq;FF;Frho;").
Proof.
  intros rho F q HF HV. unfold vrF in HV. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F2, F3. unfold two26 in F3. rewrite uval_lit in F3 by lia.
  assert (F1 : uval rho q <= uval rho tE).
  { apply orb_prop in H1 as [H1|H1]; pose proof (holds_mem _ _ _ HF H1) as F1; [rewrite h_ule in F1 | rewrite h_ult in F1]; lia. }
  lia.
Qed.

Lemma uval_add_neglit : ltac2:(tb__ "0|0|
S3S2S0S58R1Z0A2S53S5aR2A1S48R4R3A2A2S53S5aS55Z2Z3fA2A1R3A2S26S0S48R6S8Sa2R5S6R4A1A3A2S54S48R6R5A2R4A2A3F_;F_;F_;Fk;Fa;Frho;").
Proof.
  intros rho a k Hk Ha Hk2. unfold uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho a)) as R. unfold M64v in *.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma vlF_bound : ltac2:(tb__ "0|1|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S131R2A1S31A3S27S53S48R4S124A2S48R4S16cA2M0A2S53G0S55Z2Z28A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF HV. unfold vlF in HV.
  apply andb_prop in HV as [HV H4]. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  rewrite h_ult in F1. rewrite h_ule in F2, F4. rewrite uval_lit in F4 by lia.
  cbn [holds eval branch_taken] in F3. unfold bv_ltu in F3. rewrite lit_unsigned in F3 by lia. apply Z.ltb_lt in F3. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F3.
  unfold am2 in F2. rewrite uval_add_neglit in F2 by lia. lia.
Qed.

Lemma uval_sub_nw : ltac2:(tb__ "0|0|
S3S2S2S53S48R3R1A2S48R3R2A2A2S26S0S48R4S8Sa5R3R2A3A2S59S48R4R3A2S48R4R2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. pose proof (uval_range rho a) as Ra. pose proof (uval_range rho b) as Rb.
  destruct (U_sub_q rho a b) as [k Hk]. unfold U in Hk. unfold uval in *.
  pose proof (bv_urange (eval rho (SAlu ALU_SUB a b))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia.
Qed.
Lemma uval_kb : ltac2:(tb__ "0|1|
S3S0S2S27S53Z0R2A2S58R2S55Z2M0Z20A2A2A2S58S57R3S48R4R2A2A2S55G0Z40A2A2S26S0S48R5S98R4R3A2A2S57R4S48R5R3A2A2A3F_;F_;Fk;Fe;Frho;").
Proof. intros rho e k He H. unfold kb. pose proof (uval_range rho k). apply uval_mul_lit; lia. Qed.
Lemma uval_mulc : ltac2:(tb__ "0|1|
S3S2S0S27S53Z0R1A2S58R1S55Z2M0Z20A2A2A2S58S57R2S48R4R3A2A2S55G0Z40A2A2S26S0S48R5S13Sa3R4S6R3A1A3A2S57R3S48R5R4A2A2A3F_;F_;Fe;Fc;Frho;").
Proof. intros rho c e He H. rewrite uval_mul_comm. apply uval_mul_lit; lia. Qed.
Ltac hfact HF H f := pose proof (holds_mem _ _ f HF ltac:(assumption)) as H.

Lemma co_need_ok : ltac2:(tb__ "0|0|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S136R2A1S31A3S7cS4S7R4A1S95S82A1A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold coF in C.
  apply andb_prop in C as [C H7]. apply andb_prop in C as [C H6]. apply andb_prop in C as [C H5]. apply andb_prop in C as [C H4].
  apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6. pose proof (holds_mem _ _ _ HF H7) as F7.
  assert (F4 : uval rho pT0 <= uval rho pQ).
  { apply orb_prop in H4 as [H4|H4]; pose proof (holds_mem _ _ _ HF H4) as F4; [rewrite h_ule in F4 | rewrite h_ult in F4]; lia. }
  rewrite h_ule in F2, F3, F5, F6, F7. unfold B32 in F2. unfold two26 in F7. rewrite uval_lit in F2 by lia. rewrite uval_lit in F7 by lia.
  pose proof (uval_range rho co_n) as R1. pose proof (uval_range rho tI) as R2. pose proof (uval_range rho pQ) as R3.
  unfold room_r in F1. rewrite h_ule in F1. change (1 * 12) with 12 in F1.
  assert (E1 : uval rho (kb 12 co_n) = 12 * uval rho co_n) by (apply uval_kb; lia).
  assert (E2 : uval rho (kb 12 tE) = 12 * uval rho tE) by (apply uval_kb; lia).
  assert (E3 : uval rho (kb 12 tI) = 12 * uval rho tI) by (apply uval_kb; lia).
  assert (E4 : uval rho (SLit (B_EW - 12)) = B_EW - 12) by (apply uval_lit; unfold B_EW; lia).
  rewrite !uval_add_small in F1 by (rewrite ?E1, ?E2, ?E3, ?E4; unfold B_EW; lia). rewrite E1, E2, E3, E4 in F1.
  assert (E5 : uval rho (SAlu ALU_SUB pQ tI) = uval rho pQ - uval rho tI) by (apply uval_sub_nw; lia).
  assert (E6 : uval rho (NCO pQ) = uval rho co_n + (uval rho pQ - uval rho tI)) by (unfold NCO; rewrite uval_add_small by (rewrite E5; lia); rewrite E5; lia).
  unfold co_need. constructor; [|constructor]. rewrite h_ule. rewrite uval_kb by (rewrite ?E6; lia). rewrite E6, uval_lit by (unfold B_EW; lia). unfold B_EW in *. lia.
Qed.

Lemma pc_need_ok : ltac2:(tb__ "0|0|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S33SbaS4SbScS82S9bA2A1R2A3SbaS4SbScS9bS9eA2A1R2A3A2S31A3S7cS4S7R4A1S1abS96S82A2A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. apply andb_prop in C as [H1 H2]. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. rewrite h_ule in F1, F2.
  unfold pc_need. constructor; [|constructor]. rewrite h_ule.
  assert (E : uval rho (SAlu ALU_ADD pT0 (SAlu ALU_SUB pQ pT0)) = uval rho pQ).
  { unfold uval. cbn [eval]. rewrite add_val, sub_val, Zplus_mod_idemp_r.
    pose proof (bv_urange (eval rho pQ)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    replace (bv_unsigned (eval rho pT0) + (bv_unsigned (eval rho pQ) - bv_unsigned (eval rho pT0))) with (bv_unsigned (eval rho pQ)) by lia.
    apply Z.mod_small. lia. }
  rewrite E. lia.
Qed.

Lemma xslot_val : ltac2:(tb__ "0|1|
S3S2S2S26S0S48R3S3bS2S2S1aaR2R1A2A3A2S56S54S48R3S98ZcM0R1A2A2G0A2S55Z2Z40A2A2A3Fc;Fd;Frho;").
Proof.
  intros rho d c. unfold xslot, slot. cbn [snd]. unfold uval. cbn [eval]. rewrite sub_val, !add_val.
  rewrite lit_unsigned by lia. rewrite Zplus_mod_idemp_l, Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma xslot_len : ltac2:(tb__ "0|2|
S3S2dS4A1S2S2S2S7cS4S7R5A1R4A3S26S30S144R3R2R5A3S31A3S29S53S54S48R7S3bS2S2S1aaR5R4A2A3A2M0Z8A2S48R7S98ZcR3A2A2M1A2S26S0G0G1A3A2F_;F_;Fk;Fc;Fd;FF;Frho;").
Proof.
  intros rho F d c k HF C. unfold slotF in C. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. unfold B32 in F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho k) as Rk. pose proof (uval_range rho d) as Rd.
  assert (Ek : uval rho (kb 12 k) = 12 * uval rho k) by (apply uval_kb; lia).
  assert (Ec : uval rho (kb 12 c) = 12 * uval rho c) by (apply uval_kb; lia).
  rewrite uval_add_litZ in F1 by (rewrite ?Ec; lia). rewrite Ec, Ek in F1.
  assert (El : uval rho (snd (xslot d c)) = 12 * uval rho c + 12).
  { rewrite xslot_val, Ec. apply Z.mod_small. lia. }
  rewrite El, Ek. lia.
Qed.

Lemma vr_need_core : ltac2:(tb__ "0|0|
S3S0S2S2S27S58Z0R3A2S53R3ZcA2A2S53S48R5R3A2S48R5R2A2A2S53S57R5S48R6R3A2A2SceA2S7cS4S7R7A1S107R6R5R4A3A3F_;F_;F_;Fn;Fw;Fe;Frho;").
Proof.
  intros rho e w n He Hwn Hn. pose proof (uval_range rho w) as Rw. unfold B_EW in Hn.
  assert (Ew : uval rho (kb e w) = e * uval rho w) by (apply uval_kb; nia).
  assert (En : uval rho (kb e n) = e * uval rho n) by (apply uval_kb; nia).
  unfold vr_need. repeat constructor; rewrite h_ule; rewrite ?Ew, ?En; try (rewrite uval_lit by (unfold B_EW, two48; lia)); unfold B_EW, two48; nia.
Qed.
Tactic Notation "rdF" hyp(HF) hyp(C) ident(H) := let X := fresh in apply andb_prop in C as [C X]; pose proof (holds_mem _ _ _ HF X) as H; clear X.

Lemma roomF_vals : ltac2:(tb__ "0|6|
S3S2dS4A1S0S0S0S2S2S7cS4S7R7A1R6A3S26S30S142R6R5R4R3R2R7A6S31A3S27S58Z0M0R7A2M1S53R7ZcA2A2S27G1S53R7Z3A2A2S27S53G0R7A2S53R7Z40A2A2S53S48RcS81A2S55Z2M2Z20A2A2S27S53S48RdR8A2S48RdR7A2M3A2S27S53G3SccA2S27S53S54S57RbG3A2S57S57RaRbA2S59S48RdS9bA2M4S48RdSa1A2M5A2A2A2S59SceR9A2A2S27S53S54S48RdS81A2G5A2G4A2S53G4S55G2Z1aA2A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fn;Fc;Fsl;Fr;Fe;FF;Frho;").
Proof.
  intros rho F e r sl c n HF C He Hr Hsl HA. unfold roomF in C.
  rdF HF C F7. rdF HF C F6. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F5, F6, F7. unfold B32 in F2. unfold two26 in F7. rewrite uval_lit in F2 by lia. rewrite uval_lit in F7 by lia.
  unfold arity_fact in F4. rewrite h_ule in F4. pose proof (uval_range rho tI) as RI. pose proof (uval_range rho pA) as RA. pose proof (uval_range rho n) as Rn.
  rewrite uval_add_small in F4 by lia.
  unfold room_r in F3. rewrite h_ule in F3.
  assert (Hre : 0 < r * e <= 36) by nia. assert (HtE : uval rho tE <= 2 ^ 26) by lia. assert (HtI : uval rho tI <= 2 ^ 26) by lia.
  set (re := r * e) in *.
  assert (E1 : uval rho (kb e n) = e * uval rho n) by (apply uval_kb; nia).
  assert (E2 : uval rho (kb re tE) = re * uval rho tE) by (apply uval_kb; nia).
  assert (E3 : uval rho (kb re tI) = re * uval rho tI) by (apply uval_kb; nia).
  assert (E4 : uval rho (SLit (B_EW - sl)) = B_EW - sl) by (apply uval_lit; unfold B_EW; lia).
  assert (B1 : e * uval rho n <= 2 ^ 36) by nia. assert (B2 : re * uval rho tE <= 2 ^ 32) by nia. assert (B3 : re * uval rho tI <= 2 ^ 32) by nia.
  rewrite !uval_add_small in F3 by (rewrite ?E1, ?E2, ?E3, ?E4; unfold B_EW; lia). rewrite E1, E2, E3, E4 in F3.
  unfold B32, B_EW in *. repeat split; nia.
Qed.
Lemma vr_mi3_ok : ltac2:(tb__ "0|1|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S132ZcM0Z3Z24S86S8cR2A6S31A3S7cS4S7R4A1S107G0S8Sa2S86S81A3S10bS81A1A3A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold vr3F in C. rdF HF C FA. cbn [holds eval branch_taken] in FA. unfold bv_ltu, bv_eqb in FA. apply Z.eqb_eq in FA. rewrite lit_unsigned in FA by lia.
  assert (A3 : uval rho pA = 3) by exact FA.
  destruct (roomF_vals rho F 12 3 36 mi_c mi_n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho mi_c) as Rc.
  assert (EW : uval rho (SAlu ALU_ADD mi_c pA) = uval rho mi_c + 3) by (rewrite uval_add_small by (unfold B32 in *; lia); lia).
  assert (EN : uval rho (NMI pA) = uval rho mi_n + 9) by (unfold NMI; rewrite uval_add_small by (rewrite uval_kb by lia; unfold B32 in *; lia); rewrite uval_kb by lia; lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.
Lemma vr_fv3_ok : ltac2:(tb__ "0|2|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30S132Z4M0Z1M1Z8R3R2R4A6S31A3S7cS4S7R6A1S107G0S8Sa2R4S6G1A1A3S8Sa2R3S81A3A3A3F_;F_;Fn;Fc;FF;Frho;").
Proof.
  intros rho F c n HF C. unfold vr3F in C. rdF HF C FA. cbn [holds eval branch_taken] in FA. unfold bv_ltu, bv_eqb in FA. apply Z.eqb_eq in FA. rewrite lit_unsigned in FA by lia.
  assert (A3 : uval rho pA = 3) by exact FA.
  destruct (roomF_vals rho F 4 1 8 c n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho c) as Rc.
  assert (EW : uval rho (SAlu ALU_ADD c (SLit 1)) = uval rho c + 1) by (apply uval_add_litZ; unfold B32 in *; lia).
  assert (EN : uval rho (SAlu ALU_ADD n pA) = uval rho n + 3) by (rewrite uval_add_small by (unfold B32 in *; lia); lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.

Lemma loop_vals : ltac2:(tb__ "0|4|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S33S33S33SbaS4SbS1aS124S16cA2A1R2A3SbaS4SbScS16cS84A2A1R2A3A2SbaS4SbS18Sa6S6Z2M0A1S81A3A1R2A3A2SbaS4SbScS81S6S55G0Z14A2M1A1A2A1R2A3A2S31A3S27S53S54S48R4S124A2Z3M2A2S48R4S81A2M3A2S27S53G2G3A2S53G3G1A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ult in F1. rewrite h_ule in F2, F4. rewrite uval_lit in F4 by lia.
  cbn [holds eval branch_taken] in F3. unfold bv_ltu in F3. rewrite lit_unsigned in F3 by lia. apply Z.ltb_lt in F3. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F3.
  unfold am2 in F2. rewrite uval_add_neglit in F2 by lia. lia.
Qed.
Lemma vr_mi4_ok : ltac2:(tb__ "0|2|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S133ZcM0Z3M1Z24S86S8cR2A6S31A3S7cS4S7R4A1S107G0S8Sa2S129S124A1S6G1A1A3S10bS81A1A3A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold vrLF in C.
  apply andb_prop in C as [C L4]. apply andb_prop in C as [C L3]. apply andb_prop in C as [C L2]. apply andb_prop in C as [C L1].
  destruct (loop_vals rho F HF ltac:(rewrite L1, L2, L3, L4; reflexivity)) as [W1 W2].
  destruct (roomF_vals rho F 12 3 36 mi_c mi_n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho mi_c) as Rc. pose proof (uval_range rho pL) as RL.
  assert (EkL : uval rho (kb 3 pL) = 3 * uval rho pL) by (apply uval_kb; lia).
  assert (EkA : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
  assert (EC : uval rho (cMI pL) = uval rho mi_c + 3 * uval rho pL) by (unfold cMI; rewrite uval_add_small by (rewrite EkL; unfold B32 in *; lia); rewrite EkL; lia).
  assert (EW : uval rho (SAlu ALU_ADD (cMI pL) (SLit 3)) = uval rho mi_c + 3 * uval rho pL + 3) by (rewrite uval_add_litZ by (rewrite ?EC; unfold B32 in *; lia); rewrite EC; lia).
  assert (EN : uval rho (NMI pA) = uval rho mi_n + 3 * uval rho pA) by (unfold NMI; rewrite uval_add_small by (rewrite EkA; unfold B32 in *; lia); rewrite EkA; lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.
Lemma vr_fv4_ok : ltac2:(tb__ "0|2|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30S133Z4M0Z1M1Z8R3R2R4A6S31A3S7cS4S7R6A1S107G0S8Sa2S8Sa2R4S124A3S6G1A1A3S8Sa2R3S81A3A3A3F_;F_;Fn;Fc;FF;Frho;").
Proof.
  intros rho F c n HF C. unfold vrLF in C.
  apply andb_prop in C as [C L4]. apply andb_prop in C as [C L3]. apply andb_prop in C as [C L2]. apply andb_prop in C as [C L1].
  destruct (loop_vals rho F HF ltac:(rewrite L1, L2, L3, L4; reflexivity)) as [W1 W2].
  destruct (roomF_vals rho F 4 1 8 c n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho pL) as RL.
  assert (EC : uval rho (SAlu ALU_ADD c pL) = uval rho c + uval rho pL) by (apply uval_add_small; unfold B32 in *; lia).
  assert (EW : uval rho (SAlu ALU_ADD (SAlu ALU_ADD c pL) (SLit 1)) = uval rho c + uval rho pL + 1) by (rewrite uval_add_litZ by (rewrite ?EC; unfold B32 in *; lia); rewrite EC; lia).
  assert (EN : uval rho (SAlu ALU_ADD n pA) = uval rho n + uval rho pA) by (rewrite uval_add_small by (unfold B32 in *; lia); lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.

Lemma triA_vals : ltac2:(tb__ "0|1|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S12eR2A1S31A3S27S53Z4S48R4S81A2M0A2S53G0S55Z2Z14A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold triAF in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  cbn [holds eval branch_taken] in F1. unfold bv_eqb in F1.
  assert (NE : uval rho pA <> 3).
  { intros E3. apply F1. apply Z.eqb_eq. rewrite lit_unsigned by lia. exact E3. }
  lia.
Qed.
Lemma ts_need_ok : ltac2:(tb__ "0|0|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S12eR2A1S31A3S7cS4S7R4A1SfeA3F_;F_;FF;Frho;").
Proof. intros rho F HF C. exact (AR.need_facts_ok rho (triA_vals rho F HF C)). Qed.

Lemma k_nz_w : ltac2:(tb__ "0|1|
S3S2S2S7R3ScR2R1A2A2S7R4ScR2S6SccA1A2A2S53Z1S48R5R4A2A2S27S53S48R6R4A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;F_;Fk;Fw;Frho;").
Proof. intros rho w k H1 H2 Hw. rewrite h_ule in H1, H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. Qed.
Lemma k_nz_3 : ltac2:(tb__ "0|1|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30S13aR3R2R4A3S31A3S27S53S48R6R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;Fa;FF;Frho;").
Proof.
  intros rho F a k HF C. unfold live3F in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  cbn [holds eval branch_taken] in F1. unfold bv_eqb in F1. apply Z.eqb_eq in F1. rewrite lit_unsigned in F1 by lia.
  apply (k_nz_w rho a k F2 F3). unfold uval. rewrite F1. lia.
Qed.
Lemma uval_sll1 : ltac2:(tb__ "0|1|
S3S2S58S48R2R1A2S55Z2M0Z3eA2A2S26S0S48R3S8Sa7R2S6Z1A1A3A2S57G0S48R3R2A2A2A3F_;Fa;Frho;").
Proof.
  intros rho a Ha. pose proof (uval_range rho a). unfold uval in *. cbn [eval]. rewrite sll_val. change (1 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2. rewrite Z.mod_small by lia. lia.
Qed.
Lemma k_nz_tri : ltac2:(tb__ "0|1|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S13eR2R3A2S31A3S27S53S48R5R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveTri in C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  assert (E2 : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
  apply (k_nz_w rho _ k F1 F4). rewrite uval_add_small by (rewrite uval_sll1 by (rewrite E2; lia); rewrite E2; lia). rewrite uval_sll1 by (rewrite E2; lia). rewrite E2. lia.
Qed.
Lemma k_nz_rp : ltac2:(tb__ "0|1|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S13dR2R3A2S31A3S27S53S48R5R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveRp in C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  apply (k_nz_w rho _ k F1 F4). rewrite uval_add_small by (rewrite uval_sll1 by lia; lia). rewrite uval_sll1 by lia. lia.
Qed.
Lemma k_nz_ts : ltac2:(tb__ "0|1|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S13fR2R3A2S31A3S27S53S48R5R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveTs in C. rdF HF C F3. apply andb_prop in C as [C CT]. pose proof (holds_mem _ _ _ HF C) as F1.
  pose proof (triA_vals rho F HF CT) as HA.
  apply (k_nz_w rho _ k F1 F3). pose proof (AR.U_needA rho HA) as N. unfold uval. unfold AR.needA, AR.M16, AR.M32, AR.pA in N. unfold needA, M16, M32, pA.
  rewrite N. unfold uval, pA in HA. cbn [eval] in HA. pose proof (Z.mod_pos_bound (8 * bv_unsigned (rw rho 418) + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound ((bv_unsigned (rw rho 418) + 7) / 8 + 15) 16 ltac:(lia)).
  pose proof (Z.div_pos (bv_unsigned (rw rho 418) + 7) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma g_need_ok : ltac2:(tb__ "0|2|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S138R3A1S31A3S58S48R5R3A2S48R5S81A2A2S7cS4S7R6A1S32S4ScS8Sa2S8Sa2S88S13Sa3R4S6ZcM0A1M1A3A3G1A3S8Sa2S88S98G0S89A2A3A2S34S4A1A3A3F_;F_;F_;Fm;FF;Frho;").
Proof.
  intros rho F m HF C Hm. unfold gF in C. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F3, F4, F5. unfold two47, RA.two47 in F1. unfold B32 in F2, F3. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  rewrite uval_lit in F3 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho m) as Rm. pose proof (uval_range rho pDco) as Rd.
  assert (EK : uval rho (kb 12 pKco) = 12 * uval rho pKco) by (apply uval_kb; lia).
  assert (EA : uval rho (kb 12 pA) = 12 * uval rho pA) by (apply uval_kb; lia). rewrite EK, EA in F4.
  assert (EM : uval rho (SMd M_MUL m (SLit 12)) = 12 * uval rho m) by (apply uval_mulc; lia).
  assert (E1 : uval rho (SAlu ALU_ADD pDco (SMd M_MUL m (SLit 12))) = uval rho pDco + 12 * uval rho m) by (rewrite uval_add_small by (rewrite EM; lia); rewrite EM; lia).
  assert (E2 : uval rho (SAlu ALU_ADD (SAlu ALU_ADD pDco (SMd M_MUL m (SLit 12))) (SLit 12)) = uval rho pDco + 12 * uval rho m + 12) by (rewrite uval_add_litZ by (rewrite ?E1; lia); rewrite E1; lia).
  assert (E3 : uval rho (SAlu ALU_ADD pDco (kb 12 pKco)) = uval rho pDco + 12 * uval rho pKco) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
  constructor; [|constructor]. rewrite h_ule. rewrite E2, E3. lia.
Qed.

Section TSX.
Variable rho : valuation.
Let a := uval rho pA.
Let d := uval rho pDts.
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Hypothesis Hd : d <= 2 ^ 47.
Let x16 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|1|
S59S54S57Z4Va;A2ZfA2M0S56G0Z10A2A2").
Let r8 := (a + 7) / 8.
Lemma dts_range : 0 <= d. Proof using. pose proof (uval_range rho pDts). subst d. lia. Qed.
Lemma V_o16A : ltac2:(tb__ "0|0|
S26S0S48Vrho;S148A2S57Z10Va;A2A3"). Proof using Ha. exact (AR.U_o16A rho Ha). Qed.
Lemma V_o4A : ltac2:(tb__ "0|0|
S26S0S48Vrho;S147A2S57Z4Va;A2A3"). Proof using Ha. exact (AR.U_o4A rho Ha). Qed.
Lemma V_a16 : ltac2:(tb__ "0|0|
S26S0S48Vrho;S152A2Vx16;A3"). Proof using Ha. exact (AR.U_a16 rho Ha). Qed.
Lemma V_orfx : ltac2:(tb__ "0|0|
S26S0S48Vrho;S149A2Vr8;A3"). Proof using Ha. exact (AR.U_orfx rho Ha). Qed.
Lemma V_oNXTe : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14dA2S54S57Z10Va;A2S57Z4Va;A2A2A3"). Proof using Ha. exact (AR.U_oNXTe rho Ha). Qed.
Lemma V_oPRV : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14eA2S54S57Z10Va;A2Vx16;A2A3"). Proof using Ha. exact (AR.U_oPRV rho Ha). Qed.
Lemma V_oPRVe : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14fA2S54S54S57Z10Va;A2Vx16;A2S57Z4Va;A2A2A3"). Proof using Ha. exact (AR.U_oPRVe rho Ha). Qed.
Lemma V_oRFX : ltac2:(tb__ "0|0|
S26S0S48Vrho;S150A2S54S54S57Z10Va;A2Vx16;A2Vx16;A2A3"). Proof using Ha. exact (AR.U_oRFX rho Ha). Qed.
Lemma V_oRFXe : ltac2:(tb__ "0|0|
S26S0S48Vrho;S151A2S54S54S54S57Z10Va;A2Vx16;A2Vx16;A2Vr8;A2A3"). Proof using Ha. exact (AR.U_oRFXe rho Ha). Qed.
Lemma V_x16 : ltac2:(tb__ "0|1|
S27S27S53S57Z4Va;A2M0Vx16;A2S53Vx16;S54G0ZfA2A2A2S26S0S56Vx16;Z10A2Z0A3A2").
Proof using Ha. pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)). pose proof (Z.div_mod (4 * a + 15) 16 ltac:(lia)). subst x16. split; [lia|].
  replace (4 * a + 15 - (4 * a + 15) mod 16) with (16 * ((4 * a + 15) / 16)) by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma V_r8 : ltac2:(tb__ "0|0|
S27S53Z0Vr8;A2S53Vr8;S54Va;Z7A2A2A2"). Proof using Ha. subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.
Lemma V_pNXT : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14aA2S54Vd;S57Z10Va;A2A2A3").
Proof using Ha Hd. pose proof dts_range. unfold AR.pNXT'. rewrite uval_add_small by (change (uval rho (SVar AR.vDTS)) with d; rewrite V_o16A; lia). change (uval rho (SVar AR.vDTS)) with d. rewrite V_o16A. lia. Qed.
Lemma V_pPRV : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14bA2S54S54Vd;S57Z10Va;A2A2Vx16;A2A3").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. unfold AR.pPRV'. rewrite uval_add_small by (rewrite V_pNXT, V_a16; lia). rewrite V_pNXT, V_a16. lia. Qed.
Lemma V_pRFX : ltac2:(tb__ "0|0|
S26S0S48Vrho;S14cA2S54S54S54Vd;S57Z10Va;A2A2Vx16;A2Vx16;A2A3").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. unfold AR.pRFX'. rewrite uval_add_small by (rewrite V_pPRV, V_a16; lia). rewrite V_pPRV, V_a16. lia. Qed.
Lemma V_needA : ltac2:(tb__ "0|3|
S26S0S48Vrho;Sf7A2S54S54S59S54S57Z8Va;A2Z1eA2M0S56G0Z20A2A2S57Z10M1Va;A2A2S59S54Vr8;ZfA2M2S56G2G1A2A2A2A3").
Proof using Ha. exact (AR.U_needA rho Ha). Qed.
Lemma soffU : ltac2:(tb__ "0|0|
S2S58S48Vrho;R1A2S55Z2Z3fA2A2S26S0SfVrho;R2A2S48Vrho;R2A2A3F_;Fe;").
Proof using. intros e He. apply soff_smallu. exact He. Qed.

Lemma nxt_eqs_f : ltac2:(tb__ "0|1|
S27S26S0S54S48Vrho;S14aA2M0SfVrho;S6Z0A1A2A2S54Vd;SfVrho;S148A2A2A3S26S0S54G0SfVrho;S147A2A2S54Vd;SfVrho;S14dA2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. rewrite V_pNXT, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_o16A, ?V_o4A, ?V_oNXTe; lia). rewrite V_o16A, V_o4A, V_oNXTe. lia. Qed.
Lemma prv_eqs_f : ltac2:(tb__ "0|1|
S27S26S0S54S48Vrho;S14bA2M0SfVrho;S6Z0A1A2A2S54Vd;SfVrho;S14eA2A2A3S26S0S54G0SfVrho;S147A2A2S54Vd;SfVrho;S14fA2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. rewrite V_pPRV, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_oPRV, ?V_o4A, ?V_oPRVe; lia). rewrite V_oPRV, V_o4A, V_oPRVe. lia. Qed.
Lemma rfx_eqs_f : ltac2:(tb__ "0|1|
S27S26S0S54S48Vrho;S14cA2M0SfVrho;S6Z0A1A2A2S54Vd;SfVrho;S150A2A2A3S26S0S54G0SfVrho;S149A2A2S54Vd;SfVrho;S151A2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. pose proof V_r8. rewrite V_pRFX, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_oRFX, ?V_orfx, ?V_oRFXe; lia). rewrite V_oRFX, V_orfx, V_oRFXe. lia. Qed.
End TSX.

Lemma xr_ok_subrange : ltac2:(tb__ "0|2|
S3S2dS5A1S0S2S2S2S2S0S0S26S0S48R9R4A2S54S48R9R6A2R2A2A3S53Z0M0R3A2S26S0S56S54S48RbR8A2R4A2Z8M1A2G0A3S53S54R5S48RcR6A2A2R4A2S53R5S48RdR9A2A2S29S26S0S56S54S48ReRbA2R6A2G1A2G0A3S26S0S54R7S48ReR8A2A2S48ReRaA2A3A2S41RfReRdS2eS2S2RcRbA4A4S41R10RfReS2eS2S2RbRaA4A4F_;F_;F_;F_;F_;F_;F_;FM;Fo;Fl';Fb';Fl;Fb;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off b l b' l' o M Eb Ho Hal HM1 HM2 HM (HB8 & HBL & Hall). unfold xr_ok. cbn [fst snd] in *. unfold uval in *.
  pose proof (bv_urange (eval rho l')) as Rl'. change (bv_modulus 64) with (2 ^ 64) in Rl'.
  rewrite Eb. split; [exact Hal|]. split; [lia|]. intros x Hx.
  destruct (Hall x ltac:(lia)) as (G1 & G2 & G3 & v & Gv & Gd). split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. exists v. split; [exact Gv|].
  destruct Gd as [Gd|[Gv2 Ga]]; [left; exact Gd|]. destruct HM as [HM|HM].
  - exfalso. assert (x / 8 < (bv_unsigned (eval rho b) + M) / 8).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite <- (Z_div_exact_2 (bv_unsigned (eval rho b) + M) 8) by lia. lia. }
    pose proof (Z.div_le_mono (bv_unsigned (eval rho b) + M) (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) 8 ltac:(lia) ltac:(lia)). lia.
  - right. replace (bv_unsigned (eval rho b) + o + bv_unsigned (eval rho l')) with (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) by lia. split; [exact Gv2 | exact Ga].
Qed.
Lemma publish_sub_imp : ltac2:(tb__ "0|7|
S77S3dS2S2S2S2S3S2dS7aQ40A1A1SbeS26S30SbaS2fS2S2A2M0S177S2eS2S2R7R6A4A1S3fR8A1A3S31A3S26S30S44SaS3eR9A1A1S2eS2S2R6R5A4A2S31A3S7cS4S7R5A1S9S3eRaA1A1A3S26S0S56S48R6RaA2Z8M1A2Z0M2A3S28S0S0S28S0S0S27S26S0S48R9RbA2S54S48R9RdA2M3R2A2M4A3S27S53G2R2A2S27S26S0S56G4G1A2G2A3S27S53S54R2S48R9RaA2A2M5R1A2S27S53R1S48R9RcA2M6A2S29S26S0S56S54G3R1A2G1A2G2A3S26S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;S76S5bRcRbR6R5R4A6S76S5bRdS171RcS32G0S2eS2S2R9R8A4S3fRcA1A3A2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fl';Fb';Fl;Fb;FA;FJ;").
Proof.
  intros J A b l b' l' rho tp w Hin Hb Hsem Hx. apply SPA_x_publish; [exact Hb | | exact Hx].
  pose proof Hx as [(Hsm & _ & _ & Hsh & _) _].
  apply existsb_exists in Hin as (r & Hr & Heq). unfold xr_eqb in Heq. apply andb_prop in Heq as [Q1 Q2]. apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2.
  destruct r as [rb rl]. cbn in Q1, Q2. subst rb rl.
  assert (HX : xr_ok rho (ss_objs (ax_S A)) (bv_unsigned (eval rho (ax_base A))) (b, l)) by (unfold shadow_ok in Hsh; exact (proj1 (Forall_forall _ _) Hsh _ Hr)).
  destruct (Hsem (smatchA_facts segs _ _ _ _ (proj1 Hx)) (proj1 HX)) as (o & M & E1 & E2 & E3 & E4 & E5 & E6).
  exact (xr_ok_subrange rho _ _ b l b' l' o M E1 E2 E3 E4 E5 E6 HX).
Qed.

Lemma reshape_gen : ltac2:(tb__ "0|3|
S77S3dS35S5S5S3S2dS7aQ40M0A1A1SbeS26S37S5A1SbcS5SeS3eR7A1A1R6A3S38S5R5A2A3S26S2dS11A1S21R5A1S34S11A1A3S26S14S1eR6A1SdA3S26S30S16S1eR8A1A1S31A3S26S30S17SaS3eRbA1A1R8A2S31A3S7cS4S7R8A1S9S3eRcA1A1A3S27S26S0S54S7bG0S12R9S20RaA1A2A2M1S23R9RaA2A2S54S7bG0S12R9S20RbA1A2A2M2S23R9RbA2A2A3S26S0S54G1S22R9RaA2A2S54G2S22R9RbA2A2A3A2F_;S76S5bReRdR9R8R7A6S76S5bRfS83ReRdRbA3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fo';Fo;Fi;FA;FJ;").
Proof. intros J A i o o' rho tp wd Hn Hc Hd Hw Hwf Hrg Hx. unfold reshapeA. exact (SPA_reshape segs _ rho A i o o' tp wd Hn Hc Hd Hw Hwf Hrg Hx). Qed.

Lemma tsx_vals : ltac2:(tb__ "0|2|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S33S12eR2A1SbaS4SbScSf8S6ScdA1A2A1R2A3A2S31A3S27S27S53Z4S48R4S81A2M0A2S53G0S55Z2M1Z14A2A2A2S53S48R4Sf8A2S55G1Z2fA2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. apply andb_prop in C as [C1 C2]. pose proof (holds_mem _ _ _ HF C2) as F2. rewrite h_ule in F2. unfold two47, RA.two47 in F2. rewrite uval_lit in F2 by lia.
  split; [exact (triA_vals rho F HF C1) | lia].
Qed.

Lemma mod8_add : ltac2:(tb__ "0|3|
S0S0S26S0S56R2Z8M0A2Z0M1A3M2G2S26S0S56S54R4R3A2G0A2G1A3F_;F_;Fn;FB;").
Proof. intros B n HB Hn. rewrite Z.add_mod, HB, Hn by lia. reflexivity. Qed.
Lemma mod8_of16 : ltac2:(tb__ "0|1|
S0S26S0S56R1Z10A2Z0M0A3S26S0S56R2Z8A2G0A3F_;Fn;").
Proof. intros n H. pose proof (Z.div_mod n 16 ltac:(lia)). rewrite H in H0. replace n with ((n / 16 * 2) * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod8_mul8 : ltac2:(tb__ "0|1|
S0S26S0S56S57Z8M0R1A2G0A2Z0A3Fk;"). Proof. intros k. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma mod16_mul16 : ltac2:(tb__ "0|1|
S0S26S0S56S57Z10M0R1A2G0A2Z0A3Fk;"). Proof. intros k. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Definition x16f (a : Z) : Z := ltac2:(tb__ "0|1|
S59S54S57Z4Va;A2ZfA2M0S56G0Z10A2A2").
Definition r8f (a : Z) : Z := (a + 7) / 8.
Section TSX2.
Variable rho : valuation.
Let a := uval rho pA.
Let d := uval rho pDts.
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Hypothesis Hd : d <= 2 ^ 47.

Lemma xsub_pts : ltac2:(tb__ "0|7|
S53S48Vrho;S98Z3S81A2A2S48Vrho;Sf9A2M0A2S53G0SccA2S26S0S56S48Vrho;SfdA2M1Z8M2A2Z0M3A3S28S0S0S28S0S0S27S26S0G1S54G1R2A2M4A3S27S53G3R2A2S27S26S0S56G4G2A2G3A3S27S53S54R2S48Vrho;S13Sa3S81S6ZcA1A3A2A2M5R1A2S27S53R1S48Vrho;S98Z4Sf9A2A2M6A2S29S26S0S56S54G1R1A2G2A2G3A3S26S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;F_;").
Proof using Ha.
  intros H3 HK HB8. unfold B32 in HK. rewrite uval_kb in H3 by (subst a; lia). change (uval rho pA) with a in H3.
  rewrite uval_mulc by (subst a; lia). rewrite uval_kb by lia. change (uval rho pA) with a.
  assert (Z0 : (uval rho pDrp + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  destruct (Z.eq_dec (3 * a) (uval rho pKrp)) as [E|NE].
  - exists 0, (12 * a). repeat split; first [lia | exact Z0 | right; lia].
  - destruct (Z.Even_or_Odd a) as [[k Hk]|[k Hk]].
    + assert (M8 : (uval rho pDrp + 12 * a) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * a) with (8 * (3 * k)) by lia; apply mod8_mul8).
      exists 0, (12 * a). repeat split; first [lia | exact Z0 | left; exact M8].
    + assert (M8 : (uval rho pDrp + (12 * a + 4)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * a + 4) with (8 * (3 * k + 2)) by lia; apply mod8_mul8).
      exists 0, (12 * a + 4). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.

Lemma xsub_out : ltac2:(tb__ "0|7|
S53S48Vrho;S98Z3S84A2A2S48Vrho;S185A2M0A2S53G0SccA2S26S0S56S48Vrho;S189A2M1Z8M2A2Z0M3A3S28S0S0S28S0S0S27S26S0G1S54G1R2A2M4A3S27S53G3R2A2S27S26S0S56G4G2A2G3A3S27S53S54R2S48Vrho;S13Sa3S84S6ZcA1A3A2A2M5R1A2S27S53R1S48Vrho;S98Z4S185A2A2M6A2S29S26S0S56S54G1R1A2G2A2G3A3S26S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;F_;").
Proof using Ha.
  intros H3 HK HB8. unfold B32 in HK.
  assert (E2 : uval rho am2 = a - 2) by (unfold am2; subst a; apply uval_add_neglit; lia).
  rewrite uval_kb in H3 by (rewrite ?E2; lia). rewrite E2 in H3. rewrite uval_mulc by (rewrite ?E2; lia). rewrite uval_kb by lia. rewrite E2.
  assert (Z0 : (uval rho pDtr + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  destruct (Z.eq_dec (3 * (a - 2)) (uval rho pKtr)) as [E|NE].
  - exists 0, (12 * (a - 2)). repeat split; first [lia | exact Z0 | right; lia].
  - destruct (Z.Even_or_Odd a) as [[k Hk]|[k Hk]].
    + assert (M8 : (uval rho pDtr + 12 * (a - 2)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * (a - 2)) with (8 * (3 * k - 3)) by lia; apply mod8_mul8).
      exists 0, (12 * (a - 2)). repeat split; first [lia | exact Z0 | left; exact M8].
    + assert (M8 : (uval rho pDtr + (12 * (a - 2) + 4)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * (a - 2) + 4) with (8 * (3 * k - 1)) by lia; apply mod8_mul8).
      exists 0, (12 * (a - 2) + 4). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.

Lemma needA_facts : ltac2:(tb__ "0|5|
S53S48Vrho;Sf7A2M0S48Vrho;Sf6A2A2S27S53S54S54S54S57Z10M1Va;A2S103Va;A1M2A2G2A2S102Va;A1M3A2G0A2S27S26S0S56G0G1A2Z0M4A3S27S53S57Z4Va;A2G2A2S27S26S0S56G2G1A2G4A3S53G4G3A2A2A2A2A2F_;").
Proof using Ha.
  intros HN. unfold x16f, r8f in *. pose proof (V_needA rho Ha) as N. change (uval rho pA) with a in N.
  pose proof (V_x16 rho Ha) as [X1 X2]. change (uval rho pA) with a in X1, X2.
  pose proof (V_r8 rho Ha) as R. change (uval rho pA) with a in R.
  pose proof (AR.ts_arith a (uval rho needA) Ha) as T. cbv zeta in T. specialize (T ltac:(rewrite N; lia)).
  destruct T as (A1 & A2 & [A3a A3b] & A4 & A5 & A6 & A7).
  split; [lia|]. split; [|split; [lia | split; [exact X2 | lia]]].
  rewrite N. pose proof (Z.mod_pos_bound (8 * a + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound ((a + 7) / 8 + 15) 16 ltac:(lia)).
  pose proof (Z.div_mod (8 * a + 30) 32 ltac:(lia)). pose proof (Z.div_mod ((a + 7) / 8 + 15) 16 ltac:(lia)).
  replace (8 * a + 30 - (8 * a + 30) mod 32 + 16 * a + ((a + 7) / 8 + 15 - ((a + 7) / 8 + 15) mod 16)) with (16 * (2 * ((8 * a + 30) / 32) + a + ((a + 7) / 8 + 15) / 16)) by lia.
  apply mod16_mul16.
Qed.
Lemma mod8_16a : ltac2:(tb__ "0|2|
S0S0S26S0S56R2Z8M0A2Z0M1A3S26S0S56S54R3S57Z10R2A2A2G0A2G1A3F_;Fx;FB;").
Proof. intros B x HB. apply mod8_add; [exact HB|]. replace (16 * x) with (8 * (2 * x)) by lia. apply mod8_mul8. Qed.
Lemma xsub_p2d : ltac2:(tb__ "0|6|
S53S48Vrho;Sf7A2S48Vrho;Sf6A2A2S26S0S56S48Vrho;Sf8A2M0Z8M1A2Z0M2A3S28S0S0S28S0S0S27S26S0G0S54G0R2A2M3A3S27S53G2R2A2S27S26S0S56G3G1A2G2A3S27S53S54R2S48Vrho;S148A2A2M4R1A2S27S53R1S48Vrho;S98Z1Sf6A2A2M5A2S29S26S0S56S54G0R1A2G1A2G2A3S26S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_o16A rho Ha). change (uval rho pA) with a.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia.
  assert (Z0 : (uval rho pDts + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  pose proof (mod8_16a _ a HB8) as M8.
  exists 0, (16 * a). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.
Lemma xsub_nxt : ltac2:(tb__ "0|6|
S53S48Vrho;Sf7A2S48Vrho;Sf6A2A2S26S0S56S48Vrho;Sf8A2M0Z8M1A2Z0M2A3S28S0S0S28S0S0S27S26S0S48Vrho;S14aA2S54G0R2A2M3A3S27S53G2R2A2S27S26S0S56G3G1A2G2A3S27S53S54R2S48Vrho;S147A2A2M4R1A2S27S53R1S48Vrho;S98Z1Sf6A2A2M5A2S29S26S0S56S54G0R1A2G1A2G2A3S26S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pNXT rho Ha Hd), (V_o4A rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *.
  pose proof (mod8_16a _ a HB8) as M1. assert (M2 : (d + (16 * a + x)) mod 8 = 0) by (rewrite Z.add_assoc; apply mod8_add; [exact M1 | exact (mod8_of16 _ N4)]).
  exists (16 * a), (16 * a + x). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
Lemma xsub_prv : ltac2:(tb__ "0|6|
S53S48Vrho;Sf7A2S48Vrho;Sf6A2A2S26S0S56S48Vrho;Sf8A2M0Z8M1A2Z0M2A3S28S0S0S28S0S0S27S26S0S48Vrho;S14bA2S54G0R2A2M3A3S27S53G2R2A2S27S26S0S56G3G1A2G2A3S27S53S54R2S48Vrho;S147A2A2M4R1A2S27S53R1S48Vrho;S98Z1Sf6A2A2M5A2S29S26S0S56S54G0R1A2G1A2G2A3S26S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pPRV rho Ha Hd), (V_o4A rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *.
  pose proof (mod8_16a _ a HB8) as M0.
  assert (M1 : (d + (16 * a + x)) mod 8 = 0) by (rewrite Z.add_assoc; apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)]).
  assert (M2 : (d + (16 * a + x + x)) mod 8 = 0) by (rewrite !Z.add_assoc; apply mod8_add; [apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)] | exact (mod8_of16 _ N4)]).
  exists (16 * a + x), (16 * a + x + x). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
Lemma xsub_rfx : ltac2:(tb__ "0|6|
S53S48Vrho;Sf7A2S48Vrho;Sf6A2A2S26S0S56S48Vrho;Sf8A2M0Z8M1A2Z0M2A3S28S0S0S28S0S0S27S26S0S48Vrho;S14cA2S54G0R2A2M3A3S27S53G2R2A2S27S26S0S56G3G1A2G2A3S27S53S54R2S48Vrho;S149A2A2M4R1A2S27S53R1S48Vrho;S98Z1Sf6A2A2M5A2S29S26S0S56S54G0R1A2G1A2G2A3S26S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pRFX rho Ha Hd), (V_orfx rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *. set (r := (a + 7) / 8) in *.
  pose proof (mod8_16a _ a HB8) as M0.
  assert (M1 : (d + (16 * a + x + x)) mod 8 = 0) by (rewrite !Z.add_assoc; apply mod8_add; [apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)] | exact (mod8_of16 _ N4)]).
  assert (M2 : (d + uval rho needA) mod 8 = 0) by (apply mod8_add; [exact HB8 | exact (mod8_of16 _ N2)]).
  exists (16 * a + x + x), (uval rho needA). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
End TSX2.

Lemma pg_vals : ltac2:(tb__ "0|5|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S19eR2A1S31A3S27S27S53Z4S48R4S81A2M0A2S53G0S55Z2M1Z14A2A2A2S27S53S48R4Sf8A2S55G1Z2fA2A2S27S53S48R4S98Z3M2S81A2A2S48R4Sf9A2M3A2S27S53G3SccA2S27S53S48R4S98G2S84A2A2S48R4S185A2M4A2S27S53G4SccA2S53S48R4Sf7A2S48R4Sf6A2A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold pgF in C. rdF HF C F7. rdF HF C F6. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2.
  pose proof (triA_vals rho F HF C) as HA. rewrite h_ule in F2, F3, F4, F5, F6, F7. unfold two47, RA.two47 in F2. unfold B32 in F4, F6 |- *.
  rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. rewrite uval_lit in F6 by lia. repeat split; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sd0S3S2dS7aQ40A1A1ScaOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S160S5bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S1b9VCST;R1A2S27S53Z0R2A2S58R2S154A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S1b9VXGL;R1A2S27S53Z0R2A2S58R2S154A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2dS2fS2fS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 6 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S70VAInv;VCST;VXGL;VKc;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60Vnd;Aa").
Definition Posts_hfJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S32S2fS3dSc2A2M0S2eS3dSc2S193S123S197A1A4S32G0S2eS3dSc2S194S123S198A1A4S34G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S6fVAInv;VCST;VXGL;S97VKc;Vrho0;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2fS3dS5cA2S170Fn;") := ltac2:(tb__ "0|0|
S74VAInv;VCST;VXGL;S97VKc;Vrho0;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sc3S5bS97Vrho0;Vtp0;S122A5").

Let siteP : ltac2:(tb__ "0|0|
Sd0S3S2dS4A1S2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S37S35A1S2dS5A1S3S2dS7aQ40A1A1ScaVAInv;RaR3R2R1A4S7cS4S7RaA1R9A3S26S30S12aSddRaA2S31A3Sd3S97Vrho0;RcA3Sb8VCST;VFB;VFF;Vrho0;A4S66Vrho0;RfA2S112RfSd2Sd1R10A1A1A2S6aVFB;R11A2S6bVFF;R12A2S63VFB;R13R12R10A4S111R13R11A2S110R14R12A2S67VFF;R16R15R12A4S26S30S18dR15R14R13R12S117R11A6S31A3S183VCST;R18S39S0A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S11eVAInv;VCST;VALA;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddS101Ac").
Let siteF : ltac2:(tb__ "0|0|
Sd0S3S2dS4A1S2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S2dS5A1S3S2dS7aQ40A1A1ScaVAInv;R9R3R2R1A4S7cS4S7R9A1R8A3S26S30S12aSddR9A2S31A3Sd3S97Vrho0;RbA3Sb8VCST;VFB;VFF;Vrho0;A4S66Vrho0;ReA2S112ReSd2Sd1RfA1A1A2S63VFB;R10RfRdA4S111R10ReA2S110R11RfA2S67VFF;R13R12RfA4S26S30Se7R12R11R10S39S35A1S117RfA6S31A3S1cbVCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S11cVAInv;VCST;VALA;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddS101Ac").
Let siteH : ltac2:(tb__ "0|1|
Sd0S3S2dS4A1S2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S2dS5A1S3S2dS7aQ40A1A1ScaVAInv;R9R3R2R1A4S7cS4S7R9A1R8A3S26S30S12aSddR9A2S31A3Sd3S97Vrho0;RbA3Sb8VCST;VFB;VFF;Vrho0;A4S66Vrho0;ReA2S112ReSd2Sd1RfA1A1A2S63VFB;R10RfRdA4S111R10ReA2S110R11RfA2S67VFF;R13R12RfA4S26S30Se7R12R11R10S39S35A1S117RfA6S31A3S5S0SbbS5R2R12A3S27S53S3aS0S0S1fR17R3A2M0A3R2A2S58R2S3bS0S0G0A3A2A2S29S175VCST;Vrho0;S113VFB;R18R16A3S172VFF;R18R15A3R3A5S29S27S53Z0R3A2S58R3S154A2A2S182R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S11dVAInv;VCST;VALA;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddS101Ac").
Let siteX : ltac2:(tb__ "0|4|
Sd0S3S2dS4A1S2dS2fS2S2A2A1M0S2dS2fS2fS2S0A2S2A2M1A1M2S37S35A1M3S2dS5A1G0S3S2dS7aQ40A1A1ScaVAInv;RbR3R2R1A4S7cS4S7RbA1RaA3S26S30S12aSddRbA2S31A3Sd3S97Vrho0;RdA3Sb8VCST;VFB;VFF;Vrho0;A4S66Vrho0;R10A2S112R10Sd2Sd1R11A1A1A2S6aVFB;R12A2S6bVFF;R13A2S63VFB;R14R13R11A4S111R14R12A2S110R15R13A2S67VFF;R17R16R13A4S26S30Se6VXGL;R16R15R14R13R12S118R11A8S31A3S27S17cVCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S35S116G1R1R16A3Li;R15X37x2R12A9S27S180VCST;VXGL;R19S39S0A1R18R12A6S1ccR18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S11fVAInv;VCST;VXGL;VALA;VHCST;VHXGL;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddS101Af").
Let site_pure : ltac2:(tb__ "0|2|
S3dSdeS2dS5A1S3S2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S2dS49A1S26S30S12aSddS9S3eR7A1A1A2S31A3S26S30S18dS9S3eR8A1A1R4R3S39S35A1M0S117R6A6S31A3S26S30Se6VXGL;S9S3eR9A1M1A1R5R4G0SeG1A1S118S3fR9A1A8S31A3S184VAInv;VCST;VXGL;S97Vrho0;Sb8VCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S5fR6R5R4S5eA4S39S0A1Sd0SebS2cL_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
S120VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddS101Af").
Let payA_same : ltac2:(tb__ "0|1|
S2dS4A1S2dS49A1S26S30S4bR1A1S31A3S17fS97Vrho0;Sb8VCST;VFB;VFF;A3R3S6Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
S11bS97Vrho0;Sb8VCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S1S1S5cS3S18fS97R3A2S26S30S64R4R3A2S31A3S79S5bR6S73VAInv;VCST;VXGL;S97VKc;Vrho0;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S11aVAInv;VCST;VXGL;VALA;S97VKc;VHKc;VFB;VFF;VBX;Vrho0;Sb8VCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S3S5S0S2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S12bSddR5A2Sd3S97Vrho0;R6A3Sb8VCST;VFB;VFF;Vrho0;A4S26S30S117R7A1S31A3S27S53S3aS0S0S1fR9R8A2M0A3R7A2S58R7S3bS0S0G0A3A2A2S175VCST;Vrho0;S113VFB;RaR7A3S172VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
S119VCST;S97S121VFB;VFF;Vrho0;Sb8VCST;VFB;VFF;A3Sb9VCST;VFB;VFF;A3SddA9").

Lemma P0_now : ltac2:(tb__ "0|4|
S3Sd3S97Vrho0;R1A3Sb8VCST;VFB;VFF;Vrho0;A4S27S0S27S53S48R4Sa0A2M0R1A2S58R1S54G0S48R4S9eA2A2A2A2S175VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S27S1b8VFF;S48R3S1bdA2Z518A3S27S1b8VFF;S48R3S1bcA2Z30A3S27S26S35S17dZ3S7dS2fS2fS0S0A2M1S0A2G1S3aG1S0A2VFF;A4M2A2U0M3A3S26S35S17dZ6G2A2G3A3A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hf CST FB FF) (P0_hf_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as (_ & D & E). auto 6.
Qed.

Lemma tvz_in : ltac2:(tb__ "0|2|
S3S2dS2fS2S2A2M0A1S2S0S2S110R5R4A2SbbG0S2eS2S2R4S98R3R2A2A4R5A3S27S58Z0M1R4A2S53R4ZcA2A2S53S48R8R4A2SccA2S2aS26S0S48R9R5A2G1A3A1S2aS26S0S48RaR8A2G1A3A1F_;F_;F_;F_;F_;Fk;Fe;Fd;Ftv;Frho;").
Proof.
  intros rho tv d e k HZ Hin He HK Hk Hd. pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X.
  unfold uval in Hd, Hk, HK. specialize (X ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E12. unfold uval, kb in E12. unfold kb in X. rewrite E12 in X. nia.
Qed.

Lemma foff_rng : ltac2:(tb__ "0|0|
S3S2dS4A1S0S7cS4S7R3A1R2A3S26S30S12cR3A1S31A3S27S53Z0R3A2S53R3Z200A2A2S26S0S48R6S8Sa2S9aS6R4A1A3A2S54S48R6S9aA2R4A2A3F_;F_;F_;Foff;FF;Fr;").
Proof. intros r F off HF HFR Ho. unfold hF. apply (frame_off_rng hG 160 512 off r F sz_rng Ho HF HFR). Qed.

Lemma slot_rng : ltac2:(tb__ "0|1|
S3S2dS4A1S2S2S0S27S53Z0R1A2S53R1Z40A2A2S7cS4S7R6A1R5A3S26S30SbaS4SbScR5S6Z800000000000A1A2A1R6A3S31A3S26S30SbaS4SbScR5S6SccA1A2A1R7A3S31A3S27S26S0S48R9S8Sa2R7R6A3A2S54S48R9R7A2S48R9R6A2M0A2A3S27S26S0SfR9R6A2G0A3S26S0SfR9S8Sa2R6S6R5A1A3A2S54G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm;Fd;FF;Fr;").
Proof.
  intros r F d cm w Hw HF Hd Hs.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S2dS7aQ40A1A1SbfF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S77S3dS3S2dS7aQ40A1A1SbfS7cS4S7R3A1S9S3eR4A1A1A3VTR;S76S5bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SbfSbfSbfSbeR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SbfOSbfSbeR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
SbfSbfSbfSbeR3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S77S77S3dS3dSdeS2dS5A1M0S2dS2fS3dSc2A2M1A1S2dS2fS2S2A2M2A1SbfS3S2dS7aQ40A1A1M3G2SbbG2R1R5A3SbbG2R2S3fRbA1A3F_;Fr;S26S37G0A1Sc4RaR9R8A3S38G0R7A2A3S26S30Sc6RbRaR9R8S7dG1S3dS3aS3dSc2A2R7A4A5S31A3S3G3VTR;S76S5bRfRdR2R1A5Sc3S5bSaS3eRdA1A1R2R1RaA5A2Ftp1;Frho1;S2dScbA1M4SebScaS78S5bR9R8R10S2eG4SdbR3SdcR2R1A2A4A5R13RaR9R4R2A4R13SdfSe0RbRfSffR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S3dSc2G4SebScaS3G3G4SebScaSbbG1S2eS3dSc2RaR9A4R14A3S78S5bR12R11R19S2eG4SdbR9SdcR8R7A2A4A5R1cR13R12RaR8A4Sd3SaS3eR1aA1A1SdfSe0R14R18SffR9R13RaA3A3R19A2R8A3S78S5bR9R8ReS2eG4SdbR7SdcR6R5A2A4A5ReSdfSe0R16R1aSffRbR15RcA3A3R1bA2R15RaR9R8R6A6S27S1c9R17SffRcR16RdA3R1bR1cR1dR10R1eR19RbA9S3Sd4R18SffRdR17ReA3R1cR1dS3eR1eA1S3eR1fA1S3eR11A1R1RcA9VTR;S76S5bSc8R11SdfSe0R19R1dSffReR18RfA3A3R1eA2R18RdRcA5S1caR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S76S5bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRESN : ltac2:(tb__ "0|1|
S2dS2fS0S0A2M0A1S2dS2fG0S0A2A1S4dS3S2dS7aQ40A1A1S4cZ3R3A2VTR;S76S5bS65VAInv;VCST;VXGL;VKc;S1a7R6R5A2R6R5R4S60Sf0AaSecR3R2A5Sc3S5bSdaR3R2S173VAInv;VCST;VXGL;VKc;S1a7S60S91R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Definition PD_pg : list (axst * ndesc) := ltac2:(tb__ "0|1|
S32S2fS3dS5cA2M0S2eS3dS5cS1beS16bA4S32G0S2eS3dS5cS1bfS16bA4S34G0A1A3A3").
Hypothesis CPG : ltac2:(tb__ "0|1|
S2dS2fS0S0A2M0A1S2dS2fG0S0A2A1S4dS3S2dS7aQ40A1A1S4cZ5R3A2VTR;S76S5bS65VAInv;VCST;VXGL;VKc;S153R6R5A2R6R5R4S60S16bAaS1c0R3R2A5Sc3S5bSdaR3R2S173VAInv;VCST;VXGL;VKc;S153S60S1c1R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CSM : ltac2:(tb__ "0|2|
Sd0S3S2dS7aQ40A1A1VTR;S76S5bS15dVAInv;Z3M0R3VKc;A4S93R2R1A5Sc3S5bSdaR2R1S32S2fS3dSc2A2M1S2eS3dSc2S90S15aVAInv;VCST;VXGL;G0R3VKc;A6A4S34G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMSET : ltac2:(tb__ "0|1|
Sd0S3S2dS7aQ40A1A1VTR;S76S5bS15cVAInv;R3VKc;A3S92R2R1A5Sc3S5bSdaR2R1S32S2fS3dSc2A2M0S2eS3dSc2S8fS157VAInv;VCST;VXGL;R3VKc;A5A4S34G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
Sd0S3S2dS7aQ40A1A1VTR;S76S5bS15bVAInv;R3VKc;A3S10fR2R1A5Sc3S5bSdaR2R1S32S2fS3dSc2A2M0S2eS3dSc2S10eS157VAInv;VCST;VXGL;R3VKc;A5A4M1S32G0G1S34G0A1A3A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF5 : ltac2:(tb__ "0|1|
Sd0S3S2dS7aQ40A1A1VTR;S76S5bS159VAInv;R3VKc;A3S19aR2R1A5Sc3S5bSdaR2R1S32S2fS3dSc2A2M0S2eS3dSc2S199S157VAInv;VCST;VXGL;R3VKc;A5A4S34G0A1A3A5A2Ftp1;Frho1;FAi;").

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S3dSdeS2dS5A1M0S3S2dS7aQ40A1A1S5cSbfS26S37G0A1Sc4R7VPre;R6A3S38G0R5A2A3S26S30Sc9R8VPre;R7R6S7dS40S3dS43VPosts;A4A5S31A3S26S30S18eS97SaS3eR9A1A1A2S31A3S26S30S64SaS3eRaA1A1R5A2S31A3S26S30SbdS4S25SaS3eRbA1M1A1A1S9G1A1A3S31A3S40S3SbbS40R2VPosts;A3S1dSaS3eRfA1A1RcR2A3VTR;S76S5bVJAv;RbA1S16fS9S3eR10A1A1Sc7RfVPre;S43R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S76S5bVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_pc : pure_rule Pre_pc Posts_pc.
Hypothesis CALL_da : pure_rule Pre_da Posts_da.
Hypothesis CALL_bw : pure_rule Pre_bw Posts_bwH.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S3dS5cS2fS0S2A2M0S3S2dS7aQ40A1A1M1S0G1SbbS2fS2fS3dS5cA2M2G0A2S2eG2G0S2eS3dS5cR7R6A4R5A4S169A3S27S53Z0S5dS2eG2G0S2eS3dS5cR8R7A4R6A4R5A2M3A2S58G3R3A2A2VTR;S76S5bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S3dS5cS3S2dS7aQ40A1A1M0S0G0SbbS2fS3dSc2A2S2eS3dSc2R6S123R5A1A4S122A3VTR;S76S5bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Ltac peel H n := apply andb_prop in H as [H n].
Tactic Notation "innth" integer(n) := cbn [In cutsF2 exitsF2 Posts_hfJ PD_vn PD_pg]; do n right; left; reflexivity.

Lemma emeas_z0 : ltac2:(tb__ "0|0|
S3dS5cS0S3S26S0S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cR4R3A4S2eS0S2R2Sa8A4A4R1A2S57R2S55Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA, z0. cbn [eda_rank eda_var fst snd eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S3dS5cS0S2S3S3S2S26S7aQ40A1S12R2R1A2S12R3R1A2A3Fe;S26S0S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cR7R6A4S2eS0S2R5R4A4A4M0R2A2S5dG0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.
Lemma emeas_lb : ltac2:(tb__ "0|0|
S3dS5cS0S2S3S53Z0R3A2S53S57R4S55Z2Z40A2A2S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cR6R5A4S2eS0S2R4R3A4A4R2A2A2F_;Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho v)). lia. Qed.
Lemma emeas_ub : ltac2:(tb__ "0|0|
S3dS5cS0S2S3S58S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cR5R4A4S2eS0S2R3R2A4A4R1A2S57S54R3Z1A2S55Z2Z40A2A2A2Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho v)). change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.

Lemma VM_meas : ltac2:(tb__ "0|7|
S3dS3dS5cS5cS0S2S2S0S0S3S3S53Z0M0R7A2S27S53S48R3R6A2S48R3R7A2M1A2S53G1S55Z2Z28A2A2A2S26S7aQ40A1M2S12R3R8A2S12R4R8A2M3A3S26G2G3S12R5R8A2A3S53G0R8A2S58R9R8A2S58R9Z40A2S27S53G0S5dS2eS2fS3dS5cA2M4S2fS0S2A2M5S2eS3dS5cR11RfA4S2eS0S2ReS100RdRcRbA3A4A4R8A2M6A2S58G6S5dS2eG4G5S2eS3dS5cR12R10A4S2eS0S2ReS100RdRcRaA3A4A4R9A2A2A2F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' Hrk Hb He Hc Ha Hab Hb64. unfold emeasA. cbn [eda_rank eda_var fst snd].
  assert (EQ : uval rho' (VM e c a) = uval rho (VM e c a)) by (unfold uval, VM, kb; cbn [eval]; rewrite He, Hc; reflexivity).
  pose proof (VM_val rho e c a Hb ltac:(lia)) as V1. pose proof (VM_val rho e c b Hb ltac:(lia)) as V2. unfold uval in EQ, V1, V2.
  pose proof (bv_urange (eval rho' (VM e c a))). rewrite EQ, V1, V2. lia.
Qed.

Lemma VM_meas_sub : ltac2:(tb__ "0|5|
S3dS3dS5cS5cS0S2S2S0S0S3S3SdeS1S53Z0M0R9A2S27S53S48R5R8A2S48R5R9A2M1A2S53G1S55Z2Z28A2A2A2Sd3R3R6R5A3S26S30S1bR4RbA2S31A3S26S30S1bR5RbA2S31A3S26S30S15Se2R7RdA2RdA2S31A3S26S30S15Se2R8RdA2RdA2S31A3S53G0RdA2S58ReRdA2S58ReZ40A2S27S53G0S5dS2eS2fS3dS5cA2M2S2fS0S2A2M3S2eS3dS5cR16R14A4S2eS0S2R13S100R12R11R10A3A4A4SdfRdRcA2A2M4A2S58G4S5dS2eG2G3S2eS3dS5cR17R15A4S2eS0S2R13S100R12R11RfA3A4A4ReA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fs;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' s n Hrk Hb Hag Hbe Hbc Hse Hsc Ha Hab Hb64.
  apply sv_eqb_sound in Hse. apply sv_eqb_sound in Hsc.
  apply (VM_meas X T ndX ndT rk e c a b rho (rho_sub rho' s) Hrk Hb); [| |exact Ha|exact Hab|exact Hb64].
  - rewrite <- eval_subst, Hse. symmetry. exact (eval_agree_vals n rho rho' e Hag Hbe).
  - rewrite <- eval_subst, Hsc. symmetry. exact (eval_agree_vals n rho rho' c Hag Hbc).
Qed.

Lemma VM_meas_ag : ltac2:(tb__ "0|5|
S3dS3dS5cS5cS0S2S2S0S0S3S3S1S53Z0M0R8A2S27S53S48R4R7A2S48R4R8A2M1A2S53G1S55Z2Z28A2A2A2Sd3R3R5R4A3S26S30S1bR4RaA2S31A3S26S30S1bR5RaA2S31A3S53G0RaA2S58RbRaA2S58RbZ40A2S27S53G0S5dS2eS2fS3dS5cA2M2S2fS0S2A2M3S2eS3dS5cR13R11A4S2eS0S2R10S100RfReRdA3A4A4RaA2M4A2S58G4S5dS2eG2G3S2eS3dS5cR14R12A4S2eS0S2R10S100RfReRcA3A4A4RbA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fn;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' n Hrk Hb Hag Hbe Hbc Ha Hab Hb64.
  apply (VM_meas X T ndX ndT rk e c a b rho rho' Hrk Hb); [| |exact Ha|exact Hab|exact Hb64].
  - symmetry. exact (eval_agree_vals n rho rho' e Hag Hbe).
  - symmetry. exact (eval_agree_vals n rho rho' c Hag Hbc).
Qed.

Lemma BUD_transfer_eq : ltac2:(tb__ "0|1|
SdeS2dS49A1M0G0S2fS0S0A2S0S0S0S3S26G0S4aR8R7A2R6A3S4eR7R6R5R4R3R2A6S4eR9R7R6R5R4SdfR3RaA2A6F_;F_;Frho;FKf;FKm;FV;FBXv;Fbfrom;Fbto;Fs;").
Proof.
  intros s bto bfrom BXv V Km Kf rho E H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). subst bfrom.
  rewrite bsumV_subst in B1. rewrite bsumK_subst in B2. rewrite bd_wpos_subst in Hw. apply bd_nn_subst in Hn.
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.
Lemma JAi_transfer_eq : ltac2:(tb__ "0|1|
SdeS1S5cS5cSd0S0S3S3S2dS7aQ40A1A1S2dScbA1ScaS26S30Se3RbS97A2S31A3S18fS97RbA2S26S30S64RcRbA2S31A3S26S30S115ReS61RcA1S61RbA1A3S31A3S26S30S6eRfS69RdA1S69RcA1A3S31A3S26S2dS49A1S4aR10S62RdA1A2S62ReA1A3S26S72S6dR11S68ReA1A2S68RfA1A3S1dR11RcRbA3S6cVAInv;VCST;VXGL;S97VKc;Vrho0;Sb8VCST;VFB;VFF;A3M0VFB;VFF;VBX;S60R11RfReRdRbRaR9A12S6cVAInv;VCST;VXGL;S97VKc;Vrho0;G0VFB;VFF;VBX;S60R11R10RfSdfRdR14A2RcRbRaA12F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fndj;Fndi;Fn;Fs;").
Proof.
  intros s n ndi ndj Ai kc rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  pose proof (rho_sub_agree s NPH rho' H1) as Hids.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [|split; [exact Hk|split; [|split; [exact HT|split; [exact HB|split; [exact HFF|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [|split; [|split; [exact HPA|split; [exact HCK|]]]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact H2|exact Hav']|].
    apply agree_below_vals. exact Hids.
  - eapply (law_vars _ _ _ ALA); [exact HM|]. apply functional_extensionality. exact Hrm.
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - eapply fr_sub_eqb_sound; [exact H6|]. eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR].
  - eapply keptFA_eq_r; [exact HK | exact Hrm].
  - eapply XA_subst; [exact M1 |]. rewrite Ham. eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA].
  - rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer_eq; [exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
  - eapply capN_map; [exact M1|]. exact (capN_agree n BX Ai rho rho' _ Hav' Hbt HCN).
Qed.
Lemma SPA_entails_JA_eq : ltac2:(tb__ "0|1|
S3dS3dSdeS5cS5cS3S2dS7aQ40A1A1SbeS26S30S46R8R7R6A3S31A3S26S30Se3R7S97A2S31A3S26S30S18eS97SaS3eRaA1A1A2S31A3S26S30S64SaS3eRbA1A1R8A2S31A3S26S30S115RaS61R9A1S61R8A1A3S31A3S26S30S6eRbS69RaA1S69R9A1A3S31A3S26S2dS49A1S4aRcS62RaA1A2S62RbA1A3S26S30S71S6dRdS68RbA1A2S68RcA1A2S31A3S76S5bVJAv;RdA1M0R10RbRaR9A6S76S5bG0R10SdfRcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj rho tp w He Hid Hnp Hnb Htv Hfr Hbd Ham [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ |- *. destruct HJ as (Ai & kc & HJ). exists Ai, kc.
  exact (JAi_transfer_eq s (ss_next (ax_S L)) ndi ndj Ai kc rho rho tp tr md Hid Hnp Hnb Htv Hfr Hbd Ham (agree_below_refl _ _) HJ).
Qed.

Lemma forallb_firstn : forall {A} (f : A -> bool) n (l : list A), forallb f l = true -> forallb f (firstn n l) = true.
Proof.
  intros A f n. induction n as [|n IH]; intros [|x l] H; cbn in *; try reflexivity.
  apply andb_prop in H as [H1 H2]. rewrite H1, (IH l H2). reflexivity.
Qed.
Lemma bsum_firstn : ltac2:(tb__ "0|1|
S2dS49A1S35S3S26S30S4bR3A1S31A3S4fR4R2A2S27S53S51S7eS49R4R5A3M0R3A2S51R5R3A2A2S27S53S50G0R3A2S50R5R3A2A2S4fG0R3A2A2A2F_;F_;Frho;Fn;Fb;").
Proof.
  intros b. induction b as [|it r IH]; intros [|n] rho Hw Hn; cbn.
  - repeat split; try lia. constructor.
  - repeat split; try lia. constructor.
  - pose proof (bsum_nonneg (it :: r) rho Hw Hn) as [N1 N2]. cbn in N1, N2. repeat split; try lia. constructor.
  - unfold bd_wpos in Hw. cbn in Hw. apply andb_prop in Hw as [Hi Hw]. apply andb_prop in Hi as [Hv Hk]. apply Z.leb_le in Hv. apply Z.leb_le in Hk.
    inversion Hn as [|x l Hit Hr]; subst.
    destruct (IH n rho Hw Hr) as (I1 & I2 & I3). repeat split; try nia. constructor; [exact Hit | exact I3].
Qed.
Lemma payA_firstn : ltac2:(tb__ "0|1|
S2dS4A1S2dS49A1S35S26S30S4bR2A1S31A3S17fS97Vrho0;Sb8VCST;VFB;VFF;A3R4S6Z0M0A1G0R3S7eS49R2R3A3A8F_;Fn;Fb;Ffacts;").
Proof.
  intros facts b n Hw. split; [exact (forallb_firstn _ n b Hw)|]. split; [lia|].
  intros rho _ _ _ Hn. destruct (bsum_firstn b n rho Hw Hn) as (I1 & I2 & I3). unfold pay_sem. rewrite uval_lit by lia. split; [lia|]. split; [lia | exact I3].
Qed.
Lemma drop_imp : ltac2:(tb__ "0|0|
S3dS2dS2fS2S2A2A1S2dS2fS2fS2S0A2S2A2A1S2dS49A1S35S3S2dS7aQ40A1A1SbeS26S30S4bR5A1S31A3S76S5bVJAv;S5fR8R7R6S5eA4A1R9R4R3R2A6S76S5bVJAv;S5fR9R8S7eS49R6R7A3S5eA4A1RaR5R4R3A6F_;F_;Fw;Ftp;Frho;Fn;Fbd;Ffr;Ftv;FA;").
Proof.
  intros A tv fr bd n rho tp w Hw Hx.
  exact (JA_repay segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv fr bd (firstn n bd) ANone A rho tp w (payA_firstn _ bd n Hw) Hx).
Qed.

Lemma live_holds : ltac2:(tb__ "0|1|
S5cS3S2dS7aQ40A1A1S2dScbA1ScaS2S0S2VJAv;R8R7R6R5R4A5SbbS2fS2S2A2S2eS2S2R4S98R3R2A2A4S61R9A1A3S27S58Z0M0R4A2S53R4ZcA2A2S53S48RaR4A2SccA2S2aS26S0S48RbR5A2G0A3A1S7RcScS6S154A1R8A2A2F_;F_;F_;F_;F_;Fk;Fe;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d e k HJ Hin He HK Hk.
  assert (TNZ : tnz rho (d, kb e k)).
  { destruct HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ) & _). unfold tnz. cbn [fst]. exact (tvz_in rho _ d e k HZ Hin He HK Hk). }
  pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (d, kb e k) eq_refl HJ Hin TNZ) as TF.
  apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
Qed.

Lemma k_nz_lit : ltac2:(tb__ "0|2|
S3S2dS4A1S2S0S2S7cS4S7R5A1R4A3S27S58Z0M0R3A2S58R3S55Z2Z20A2A2A2S26S30S13bR5R4R3R6A4S31A3S27S53S48R8R4A2M1SccA2S2aS26S0G1G0A3A1A2F_;F_;F_;Fk;Fc;Fx;FF;Frho;").
Proof.
  intros rho F x c k HF Hc C. unfold liveF in C. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. rewrite h_ule in F1, F2. unfold B32 in *. rewrite uval_lit in F2 by lia.
  assert (F3 : uval rho x <= 2 ^ 32) by (apply orb_prop in H3 as [H3|H3]; pose proof (holds_mem _ _ _ HF H3) as F3; rewrite h_ule in F3; [rewrite uval_lit in F3 by lia|]; lia).
  pose proof (uval_range rho x) as Rx. rewrite uval_add_litZ in F1 by lia. lia.
Qed.

Lemma k_nz_a : ltac2:(tb__ "0|1|
S3S2dS4A1S2S2S2S7cS4S7R5A1R4A3S26S30S13cR4R3R2R5A4S31A3S27S53S48R7R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;Fa;Fx;FF;Frho;").
Proof.
  intros rho F x a k HF C. unfold liveFa in C. apply andb_prop in C as [C H4]. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H3) as F3. rewrite h_ule in F1, F3. unfold B32 in *. rewrite uval_lit in F3 by lia.
  pose proof (holds_mem _ _ _ HF H2) as F2. cbn [holds eval branch_taken] in F2. unfold bv_eqb in F2. apply Z.eqb_eq in F2. rewrite lit_unsigned in F2 by lia.
  assert (A3 : uval rho a = 3) by exact F2.
  assert (F4 : uval rho x <= 2 ^ 32) by (apply orb_prop in H4 as [H4|H4]; pose proof (holds_mem _ _ _ HF H4) as F4; rewrite h_ule in F4; [rewrite uval_lit in F4 by lia|]; lia).
  pose proof (uval_range rho x) as Rx. rewrite uval_add_small in F1 by lia. lia.
Qed.

Lemma xff_imp : ltac2:(tb__ "0|0|
S77S3dS3dS3dS2dS18aA1S2dS4A1S3S2dS7aQ40A1A1SbeS26S37S3dA1S18bR8R5A2S38S3dR7A2A3S26S3dS16fR5R8A2R7A3S26S30S134R9R6A2S31A3S2dScbA1ScaReR8R7R2R1A4S7cS4S7R9A1S9S3eRdA1A1A3S7cS4S7RaA1RbA3F_;F_;Fmd;Ftr;S76S5bRdRcR7R6R5A6S76S5bReRbR8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho;FF;Fxf;FT2;FT1;FT0;FJ;").
Proof.
  intros J T0 T1 T2 xf F rho tp w HT1 HT2 Hb HF Hw. rewrite <- HT2. unfold xff_chk in Hb.
  change (ax_add_facts F T1) with (ax_with_facts T1 (F ++ ss_facts (ax_S T1))).
  apply (SPA_refacts_JA segs); [| exact Hb | intros tr md HJ HF1; apply Forall_app; split; [exact (HF tr md HJ HF1) | exact HF1]].
  exact (SPA_axforms segs _ xf rho T0 T1 tp w HT1 Hw).
Qed.

Lemma facts_imp : ltac2:(tb__ "0|0|
S77S3dS3dS2dS4A1S3S2dS7aQ40A1A1SbeS26S3dS16fR4R6A2R5A3S26S30S134R7R5A2S31A3S2dScbA1ScaRbR7R6R2R1A4S7cS4S7R8A1S9S3eRbA1A1A3S7cS4S7R9A1RaA3F_;F_;Fmd;Ftr;S76S5bRaR9R6R5R4A6S76S5bRbR9R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;FF;FT2;FT1;FJ;").
Proof.
  intros J T1 T2 F rho tp w HT2 Hb HF Hw. rewrite <- HT2. unfold xff_chk in Hb.
  change (ax_add_facts F T1) with (ax_with_facts T1 (F ++ ss_facts (ax_S T1))).
  apply (SPA_refacts_JA segs); [exact Hw | exact Hb | intros tr md HJ HF1; apply Forall_app; split; [exact (HF tr md HJ HF1) | exact HF1]].
Qed.

Lemma slot_rng2 : ltac2:(tb__ "0|1|
S3S2S2S2S0S27S53Z0R1A2S53R1Z40A2A2S26S0S48R6R3A2S48R6R4A2A3S53S48R7R6A2Z800000000000A2S53S48R8R6A2S55Z2Z28A2A2S27S26S0S48R9S8Sa2R8R6A3A2S54S48R9R8A2S48R9R7A2M0A2A3S27S26S0SfR9R7A2G0A3S26S0SfR9S8Sa2R7S6R5A1A3A2S54G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm';Fcm;Fd;Fr;").
Proof.
  intros r d cm cm' w Hw Hc Hd Hs. pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [rewrite uval_add_small by lia; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.
Lemma reshape_fwd : ltac2:(tb__ "0|3|
S77S3dS35S2S2S2S0S14S3S2dS7aQ40A1A1SbeS26S37S5A1SbcS5SeS3eRaA1A1R9A3S38S5S10R8R7S8Sa2R7S6R5A1A3S34S11A1M0R4A5A2A3S26S30S16R5A1S31A3S26S30S17SaS3eRcA1A1S10S8Sa2RaR8A3S6Z0M1A1M2S6R7A1G0SdA5A2S31A3S27S53G1R8A2S53R8Z40A2A2S3S26S0S48R1RbA2S48R1RcA2A3Fr;S7cS4S7R8A1S9S3eRfA1A1A3S27S53S48R9ReA2Z800000000000A2S53S48R9RdA2S55Z2Z28A2A2A2F_;S76S5bR11R10R9R8R7A6S76S5bR12S83R11R10S10S8Sa2RfRdA3G2S6RcA1G0SdA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fw;Fcm';Fcm;Fd;Fi;FA;FJ;").
Proof.
  intros J A i d cm cm' w dfl rho tp wd Hn Hdw Hwf Hw Hc Hb Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. destruct (Hb HF) as [Bd Bc]. destruct (slot_rng2 rho d cm cm' w Hw (Hc rho) Bd Bc) as (A1 & A2 & A3).
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
  change (bv_unsigned (eval rho (SAlu ALU_ADD d cm'))) with (uval rho (SAlu ALU_ADD d cm')). rewrite A1. unfold uval. lia.
Qed.
Lemma reshape_bwd : ltac2:(tb__ "0|2|
S77S3dS35S2S2S2S0S14S3S2dS7aQ40A1A1SbeS26S37S5A1SbcS5SeS3eRaA1A1R9A3S38S5S10S8Sa2R8R6A3S6Z0M0A1S6R5A1S34S11A1M1R4A5A2A3S26S30S16R5A1S31A3S26S30S17SaS3eRcA1A1S10RaR9S8Sa2R9S6R7A1A3G1SdA5A2S31A3S27S53G0R8A2S53R8Z40A2A2S3S26S0S48R1RbA2S48R1RcA2A3Fr;S7cS4S7R8A1S9S3eRfA1A1A3S27S53S48R9ReA2Z800000000000A2S53S48R9RdA2S55Z2Z28A2A2A2F_;S76S5bR11R10R9R8R7A6S76S5bR12S83R11R10S10RfReS8Sa2ReS6RcA1A3G1SdA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fw;Fcm';Fcm;Fd;Fi;FA;FJ;").
Proof.
  intros J A i d cm cm' w dfl rho tp wd Hn Hdw Hwf Hw Hc Hb Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. destruct (Hb HF) as [Bd Bc]. destruct (slot_rng2 rho d cm cm' w Hw (Hc rho) Bd Bc) as (A1 & A2 & A3).
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
  change (bv_unsigned (eval rho (SAlu ALU_ADD d cm'))) with (uval rho (SAlu ALU_ADD d cm')). rewrite A1. unfold uval. lia.
Qed.

Lemma rs_bnd_lit : ltac2:(tb__ "0|0|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30S143R3R2R4A3S31A3S27S53S48R6R4A2Z800000000000A2S53S48R6R3A2S55Z2Z28A2A2A2F_;F_;Fcm;Fd;FF;Frho;").
Proof.
  intros rho F d cm HF C. unfold rsF in C. apply andb_prop in C as [H1 H2]. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia. lia.
Qed.
Lemma rs_bnd_kb : ltac2:(tb__ "0|1|
S3S2dS4A1S2S0S2S2S7cS4S7R6A1R5A3S27S58Z0R4A2S53R4ZcA2A2S26S30S130R6R4R3R7A4S31A3S27S53S48R9R7A2Z800000000000A2S27S53S48R9S98R6R5A2A2M0S55Z2Z28A2A2S26S0S48R9S13Sa3R5S6R6A1A3A2G0A3A2A2F_;F_;F_;Fk;Fc;Fe;Fd;FF;Frho;").
Proof.
  intros rho F d e c k HF He C. unfold rsFk in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F3. unfold B32 in F3. rewrite uval_lit in F1 by lia. rewrite uval_lit in F3 by lia. pose proof (uval_range rho c) as Rc.
  assert (E1 : uval rho (kb e c) = e * uval rho c) by (apply uval_kb; nia).
  assert (E2 : uval rho (SMd M_MUL c (SLit e)) = e * uval rho c) by (apply uval_mulc; nia).
  rewrite E1, E2. nia.
Qed.
Lemma uval_sext32 : ltac2:(tb__ "0|0|
S3S2S26S0S48R2S19S3cQ20R1A3A2S56S48R2R1A2S55Z2Z20A2A2A3Fe;Frho;").
Proof. intros rho e. unfold uval. cbn [eval]. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. reflexivity. Qed.
Lemma rs_bnd_gz : ltac2:(tb__ "0|0|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30SbaS4SbScR3S6ScdA1A2A1R4A3S31A3S27S53S48R6R4A2Z800000000000A2S53S48R6S13Sa3S19S3cQ20R3A3S6ZcA1A3A2S55Z2Z28A2A2A2F_;F_;Fe0;Fd;FF;Frho;").
Proof.
  intros rho F d e0 HF H1. pose proof (holds_mem _ _ _ HF H1) as F1. rewrite h_ule in F1. unfold two47, RA.two47 in F1. rewrite uval_lit in F1 by lia.
  pose proof (uval_range rho e0). pose proof (Z.mod_pos_bound (uval rho e0) (2 ^ 32) ltac:(lia)).
  rewrite uval_mulc by (rewrite ?uval_sext32; lia). rewrite uval_sext32. lia.
Qed.
Lemma rs_bnd_gv : ltac2:(tb__ "0|1|
S3S2dS4A1S2S2S7cS4S7R4A1R3A3S26S30S33S33SbaS4SbScR3S6ScdA1A2A1R4A3SbaS4SbS1aR2S81A2A1R4A3A2SbaS4SbScS81S6S55Z2M0Z14A2A1A2A1R4A3A2S31A3S27S53S48R6R4A2Z800000000000A2S53S48R6S13Sa3R3S6ZcA1A3A2S55G0Z28A2A2A2F_;F_;Fv;Fd;FF;Frho;").
Proof.
  intros rho F d v HF C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F3. rewrite h_ult in F2. unfold two47, RA.two47 in F1. rewrite uval_lit in F1 by lia. rewrite uval_lit in F3 by lia.
  rewrite uval_mulc by lia. lia.
Qed.
Lemma rs_bnd_mc : ltac2:(tb__ "0|0|
S3S2dS4A1S2S0S2S2S7cS4S7R6A1R5A3S27S58Z0R4A2S53R4ZcA2A2S26S30S130R6R4R3R7A4S31A3S27S53S48R9R7A2Z800000000000A2S53S48R9S13Sa3R5S6R6A1A3A2S55Z2Z28A2A2A2F_;F_;F_;Fk;Fc;Fe;Fd;FF;Frho;").
Proof. intros rho F d e c k HF He C. destruct (rs_bnd_kb rho F d e c k HF He C) as (A1 & A2 & A3). rewrite A3. split; assumption. Qed.
Lemma uval_mulc_kb : ltac2:(tb__ "0|0|
S3S2S0S26S0S48R3S13Sa3R2S6R1A1A3A2S48R3S98R1R2A2A2A3Fe;Fc;Fr;").
Proof. intros. unfold kb. apply uval_mul_comm. Qed.
Lemma sext_lt : ltac2:(tb__ "0|0|
S3S2S2S7R3S1aR2R1A2A2S58S48R4S19S3cQ20R3A3A2S48R4R2A2A2F_;Fb;Fv;Frho;").
Proof. intros rho v b H. rewrite h_ult in H. rewrite uval_sext32. pose proof (uval_range rho v). pose proof (Z.mod_le (uval rho v) (2 ^ 32) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma reshape_ffwd : ltac2:(tb__ "0|3|
S77S3dS35S0S0S14S3S2dS7aQ40A1A1SbeS26S37S5A1SbcS5SeS3eR8A1A1R7A3S38S5S10S9aS6R6A1S6R5A1S34S11A1M0R4A5A2A3S26S30S16R5A1S31A3S26S30S17SaS3eRaA1A1S10S8Sa2S9aS6R8A1A3S6Z0M1A1M2S6S59R7R8A2A1G0SdA5A2S31A3S27S53G1R9A2S53R9R8A2A2S53R9Z200A2S26S30S12cS9S3eRdA1A1A1S31A3S76S5bRfReR9R8R7A6S76S5bR10S83RfReS10S8Sa2S9aS6RdA1A3G2S6S59RcRdA2A1G0SdA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.

Lemma reshape_ffwd_c : ltac2:(tb__ "0|3|
S77S3dS35S0S0S2dS11A1S14S3S2dS7aQ40A1A1SbeS26S37S5A1SbcS5SeS3eR9A1A1R8A3S38S5S10S9aS6R7A1S6R6A1R5R4A5A2A3S26S30S16R5A1S31A3S26S30S17SaS3eRbA1A1S10S8Sa2S9aS6R9A1A3S6Z0M0A1M1S6S59R8R9A2A1S34S11A1M2SdA5A2S31A3S27S53G0RaA2S53RaR9A2A2S53RaZ200A2S26S30S12cS9S3eReA1A1A1S31A3S76S5bR10RfR9R8R7A6S76S5bR11S83R10RfS10S8Sa2S9aS6ReA1A3G1S6S59RdReA2A1G2SdA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fcs;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b cs dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.
Lemma reshape_fbwd : ltac2:(tb__ "0|2|
S77S3dS35S0S0S14S3S2dS7aQ40A1A1SbeS26S37S5A1SbcS5SeS3eR8A1A1R7A3S38S5S10S8Sa2S9aS6R6A1A3S6Z0M0A1S6S59R5R6A2A1S34S11A1M1R4A5A2A3S26S30S16R5A1S31A3S26S30S17SaS3eRaA1A1S10S9aS6R8A1S6R7A1G1SdA5A2S31A3S27S53G0R9A2S53R9R8A2A2S53R9Z200A2S26S30S12cS9S3eRdA1A1A1S31A3S76S5bRfReR9R8R7A6S76S5bR10S83RfReS10S9aS6RdA1S6RcA1G1SdA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.

Lemma xr_ok_prefix : ltac2:(tb__ "0|2|
S3S2dS5A1S0S2S2S2S2S26S7aQ40A1S12R7R2A2S12R7R4A2A3S29S53S54S48R8R2A2M0Z8A2S48R8R4A2M1A2S26S0G0G1A3A2S41R9R8R7S2eS2S2R6R5A4A4S41RaR9R8S2eS2S2R5R4A4A4F_;F_;F_;Fl';Fb';Fl;Fb;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off b l b' l' Eb Hl (HB8 & HBL & Hall). unfold xr_ok. cbn [fst snd] in *. rewrite Eb. unfold uval in Hl.
  pose proof (bv_urange (eval rho l')) as Rl'. change (bv_modulus 64) with (2 ^ 64) in Rl'.
  split; [exact HB8|]. split; [lia|]. intros a Ha.
  destruct (Hall a ltac:(lia)) as (G1 & G2 & G3 & v & Gv & Gd). split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. exists v. split; [exact Gv|].
  destruct Gd as [Gd|[Gv2 Ga]]; [left; exact Gd|]. destruct Hl as [Hl|Hl].
  - exfalso. pose proof (Z.mul_div_le (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) 8 ltac:(lia)).
    pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). nia.
  - right. rewrite Hl. split; [exact Gv2 | exact Ga].
Qed.
Lemma publish_prefix_imp : ltac2:(tb__ "0|4|
S77S3dS2S2S2S2S3S2dS7aQ40A1M0A1SbeS26S30SbaS2fS2S2A2M1S177S2eS2S2R7R6A4A1S3fR8A1A3S31A3S26S30S44SaS3eR9A1A1S2eS2S2R6R5A4A2S31A3S7cS4S7R5A1S9S3eRaA1A1A3S27S26G0S12R6R8A2S12R6RaA2A3S29S53S54S48R6R7A2M2Z8A2S48R6R9A2M3A2S26S0G2G3A3A2A2F_;S76S5bRcRbR6R5R4A6S76S5bRdS171RcS32G1S2eS2S2R9R8A4S3fRcA1A3A2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fl';Fb';Fl;Fb;FA;FJ;").
Proof.
  intros J A b l b' l' rho tp w Hin Hb Hsem Hx. apply SPA_x_publish; [exact Hb | | exact Hx].
  pose proof Hx as [(Hsm & _ & _ & Hsh & _) _]. destruct (Hsem (smatchA_facts segs _ _ _ _ (proj1 Hx))) as [E1 E2].
  apply existsb_exists in Hin as (r & Hr & Heq). unfold xr_eqb in Heq. apply andb_prop in Heq as [Q1 Q2]. apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2.
  destruct r as [rb rl]. cbn in Q1, Q2. subst rb rl.
  apply (xr_ok_prefix rho _ _ b l b' l' E1 E2). unfold shadow_ok in Hsh. exact (proj1 (Forall_forall _ _) Hsh _ Hr).
Qed.
Lemma subX_imp : ltac2:(tb__ "0|0|
S77S3dS3dS2dS2fS2S2A2A1S3S2dS7aQ40A1A1SbeS26S3dS171R6R4A2R5A3S26S30S176R5S3fR7A1A2S31A3S76S5bR9R8R5R4R3A6S76S5bRaR8R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FX';FB;FA;FJ;").
Proof. intros J A B X' rho tp w HB Hi Hx. rewrite <- HB. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ Hi) | exact Hx]. Qed.

Lemma reopen_imp : ltac2:(tb__ "0|1|
S3dS2dS2fS2S2A2A1M0G0S2dS49A1S0S0S3S2dS7aQ40A1A1SbeS26S30S141VXGL;R9R8R7R5R4A6S31A3S76S5bVJAv;S5fR8S80R7S5eA4A1RaR4R3R2A6S76S5bVJAv;S5fR9S80R8S5eA4A1Se8RbRaS99R7R6A5R5R4R3A6F_;F_;Fw;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 rho tp w CK Hw.
  unfold reopen_chk in CK. peel CK HXL. peel CK HRO. peel CK HB. peel CK Hwf. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma carve_imp : ltac2:(tb__ "0|1|
S3dS2dS5A1M0S5S0S0S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1SbeS26G0SeS3eRaA1A1S36S5R9S32S5R8S34S5A1A3A3A3S26S5R9Se4S99R8R7S21R9A1S1eR9A1A5A3S53Z0R9A2S27S53RaR9A2S53R9Z40A2A2S26S30S19fVXGL;ReRdR9A4S31A3S76S5bVJAv;S5fRaS80R9S5eA4A1RfR8R7R6A6S76S5bVJAv;S5fRbS80RaS5eA4A1Se9R10PaaA2R9R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fbd;Ftv;Fk2;Fk1;Fsh;Fobjs;FA;").
Proof.
  intros A objs sh k1 k2 tv bd rho tp w Ho Hsh Hk1 Hk2 CK Hw.
  unfold carve_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwf. rename CK into Hbase. apply sv_eqb_sound in Hbase.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive A rho tp w eq_refl ltac:(lia) Hbase Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - intros o a Hoi Hr. rewrite Ho in Hoi. apply in_app_or in Hoi as [Hoi|[<-|[]]].
    + exact (siteH Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Hoi Hr).
    + right. right. rewrite Hsh in Hr. exact (shobj_range_hse hG 160 512 k1 k2 rho _ a sz_rng Hk1 ltac:(change (512 / 8) with 64; lia) HF HFRF Hr).
  - exact (proj2 (proj2 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
Qed.

Lemma k_nz_L : ltac2:(tb__ "0|1|
S3S2dS4A1S2S7cS4S7R3A1R2A3S26S30S1a0R2R3A2S31A3S27S53S48R5R3A2M0SccA2S2aS26S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveLF in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  apply (k_nz_w rho pA k F1 F3). lia.
Qed.

Lemma release_imp : ltac2:(tb__ "0|3|
S3dS2dS5A1M0S0S0S2dS11A1S14S2dS2fS0S0A2A1S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1S2dScbA1M1SebScaS26S30S12dReRdRcRbRaR9R8R7R6A9S31A3S26G0SeS3eRfA1A1S36S5ReS32S5Se4S99RdRcRbRaA5S34S5A1M2A3A3A3S76S5bVJAv;S5fR9S80R8S5eA4A1R10R7R6S2eG1SdbR5SdcR4R3A2A4A6S76S5bVJAv;S5fRaS80R9S5eA4A1Se5R11R10Pa0RbA4Se0R8S32S5Se4S99RfReRdRcA5G2A3SffR4R7R5A3A3R7S2eG1SdbR6SdcR5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;FL;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d L tv bd rho tp tr ms md CK Ho Hw.
  unfold release_chk in CK. peel CK HRO. peel CK HB. peel CK Hnb. peel CK HL. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs L rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe HL Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hf objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.

Lemma release0_imp : ltac2:(tb__ "0|3|
S3dS2dS5A1M0S0S0S2dS11A1S14S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1S2dScbA1M1SebScaS26S30S1a2RdRbRaR8A4S31A3S26G0SeS3eReA1A1S36S5RdS32S5Se4S99RcRbRaR9A5S34S5A1M2A3A3A3S76S5bVJAv;S5fR9S80R8S5eA4A1RfR7R6S2eG1SdbR5SdcR4R3A2A4A6S76S5bVJAv;S5fRaS80R9S5eA4A1Se5R10RfPa0S34S2fS0S0A2A1A4Se0R8S32S5Se4S99ReRdRcRbA5G2A3SffR4R7R5A3A3R7S2eG1SdbR6SdcR5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d tv bd rho tp tr ms md CK Ho Hw.
  unfold release0_chk in CK. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. rename CK into Hk1.
  apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  exact (JA_shadow_release0 segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs rho tp tr ms md
           eq_refl ltac:(lia) Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe Hw).
Qed.

Lemma is_shx_out : ltac2:(tb__ "0|2|
S3S2dS4A1S5S0S0S0S7cS4S7R6A1R5A3S26S30S12cR6A1S31A3S26S30S1a3R5R4R6A3S31A3S53Z0R6A2S53R7R6A2S53R7Z40A2S27S53S3aS0S0S1fRcRaA2M0A3R7A2S58R7S3bS0S0G0A3A2A2S2aS27S53S54S156S48RdS9aA2A1M1RaA2R8A2S58R8S54G1R9A2A2A2A1F_;F_;F_;F_;F_;F_;F_;Fa;Fk2;Fk1;Fo;FF;Frho;").
Proof.
  intros rho F o k1 k2 a HF HFR HS Hk1 Hk2 Hk3 Hr Ha. pose proof (framez_of hG 160 512 rho F sz_rng HF HFR) as [G1 G2 G3].
  unfold is_shx in HS. destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in HS.
  destruct b as [ | g | | | | | | ]; try discriminate. destruct lo as [lo| | | | | | | ]; try discriminate. destruct hi as [hi| | | | | | | ]; try discriminate.
  peel HS Hd. peel HS H4. peel HS H3. peel HS H2. apply Pos.eqb_eq in HS. subst g.
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  unfold SHADOW_OFF in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar hG))) with (uval rho (SVar hG)) in Hr. rewrite G1 in Hr. unfold hF, Sh, SHADOW_OFF in Ha.
  apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
Lemma reopenS_imp : ltac2:(tb__ "0|1|
S3dS2dS2fS2S2A2A1M0G0S2dS49A1S0S0S3S2dS7aQ40A1A1SbeS26S30S1a4VXGL;R9R8R7R5R4A6S31A3S76S5bVJAv;S5fR8S80R7S5eA4A1RaR4R3R2A6S76S5bVJAv;S5fR9S80R8S5eA4A1Se8RbRaS99R7R6A5R5R4R3A6F_;F_;Fw;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 rho tp w CK Hw.
  unfold reopenS_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwf. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_reopenS segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - intros o a Hoi Hr. destruct (is_shx k1 k2 o) eqn:ES.
    + right. exact (is_shx_out rho _ o k1 k2 a HF HFRF ES Hk1 Hk2 Hk3 Hr).
    + left. refine (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a _ Hr).
      apply filter_In. split; [exact Hoi | rewrite ES; reflexivity].
  - intros r y Hr Hy. destruct (xloc_ok k1 k2 r) eqn:EL.
    + right. unfold xloc_ok in EL. destruct r as [ra rl]. destruct ra as [ | | op ra1 ra2 | | | | | ]; try discriminate. destruct op; try discriminate.
      destruct ra1 as [ | p0 | | | | | | ]; try discriminate. destruct ra2 as [off| | | | | | | ]; try discriminate. destruct rl as [len| | | | | | | ]; try discriminate.
      peel EL Hwc. peel EL H3. peel EL H2. peel EL H1. apply Pos.eqb_eq in EL. subst p0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
      exists off, len. change (fs_frame_size 3) with 512. repeat split; try assumption; reflexivity.
    + left. refine (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y _ Hy).
      apply filter_In. split; [exact Hr | rewrite EL; reflexivity].
Qed.

Lemma releaseP_imp : ltac2:(tb__ "0|3|
S3dS2dS5A1M0S0S0S2dS11A1S14S2dS2fS0S0A2A1S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1S2dScbA1M1SebScaS26S30S1a5ReRdRcRbRaR9R8R7R6A9S31A3S26G0SeS3eRfA1A1S36S5ReS32S5Se4S99RdRcRbRaA5S34S5A1M2A3A3A3S76S5bVJAv;S5fR9S80R8S5eA4A1R10R7R6S2eG1SdbR5SdcR4R3A2A4A6S76S5bVJAv;S5fRaS80R9S5eA4A1Se5R11R10Pa0RbA4Se0R8S32S5Se4S99RfReRdRcA5G2A3SffR4R7R5A3A3R7S2eG1SdbR6SdcR5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;FL;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d L tv bd rho tp tr ms md CK Ho Hw.
  unfold releaseP_chk in CK. peel CK HRO. peel CK HB. peel CK Hnb. peel CK HL. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_releaseP segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs L rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe HL Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hf objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.
Lemma reopenC_imp : ltac2:(tb__ "0|1|
S3dS2dS2fS2S2A2A1M0G0S2dS49A1S0S0S0S0S3S2dS7aQ40A1A1SbeS26S30S1a6VXGL;RbRaR9R7R6R5R4A8S31A3S76S5bVJAv;S5fRaS80R9S5eA4A1RcR4R3R2A6S28S0S0S27S29S26S0R1Z0A3S26S0R1S56S54R8R7A2Z8A2A3A2S76S5bVJAv;S5fRcS80RbS5eA4A1S1c6ReRdS99RaR9S1c5R8R7R1A3A6R6R5R4A6A2LbL;A2F_;F_;Fw;Ftp;Frho;Flen;Foff;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 off len rho tp w CK Hw.
  unfold reopenC_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwfm. peel CK Hwf0. peel CK Hq2. peel CK Hq1. peel CK Hols. peel CK Hm1.
  peel CK Hl1. peel CK Ho8. peel CK Ho0. peel CK HiL. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3. apply Z.leb_le in Ho0. apply Z.eqb_eq in Ho8.
  apply Z.leb_le in Hl1. apply Z.leb_le in Hm1. apply Z.leb_le in Hols. apply Z.leb_le in Hq1. apply Z.ltb_lt in Hq2.
  apply (JA_shadow_reopen_cells segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 off len A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) (xrs_inclb_sound _ _ HiL _ (or_introl eq_refl)) Ho0 Ho8 Hl1 Hm1
           ltac:(change (fs_frame_size 3) with 512; exact Hols) Hq1 Hq2); [| |exact Hw].
  - intros bL [->| ->]; assumption.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + intros o a Hoi Hr. destruct (is_shx k1 k2 o) eqn:ES.
      * right. exact (is_shx_out rho _ o k1 k2 a HF HFRF ES Hk1 Hk2 Hk3 Hr).
      * left. refine (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a _ Hr).
        apply filter_In. split; [exact Hoi | rewrite ES; reflexivity].
    + intros r y Hr Hy. destruct (xloc_ok k1 k2 r) eqn:EL.
      * right. unfold xloc_ok in EL. destruct r as [ra rl]. destruct ra as [ | | op ra1 ra2 | | | | | ]; try discriminate. destruct op; try discriminate.
        destruct ra1 as [ | p0 | | | | | | ]; try discriminate. destruct ra2 as [off'| | | | | | | ]; try discriminate. destruct rl as [len'| | | | | | | ]; try discriminate.
        peel EL Hwc. peel EL H3. peel EL H2. peel EL H1. apply Pos.eqb_eq in EL. subst p0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
        exists off', len'. change (fs_frame_size 3) with 512. repeat split; try assumption; reflexivity.
      * left. refine (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y _ Hy).
        apply filter_In. split; [exact Hr | rewrite EL; reflexivity].
Qed.

Lemma facts_sub_holds : ltac2:(tb__ "0|1|
S3S2dS4A1M0G0S26S30S166R2R1A2S31A3S7cS4S7R4A1R2A3S7cS4S7R5A1R4A3F_;F_;FG;FF;Frho;").
Proof.
  intros rho F G H HG. apply Forall_forall. intros p Hp. exact (holds_mem rho G p HG (proj1 (forallb_forall _ _) H p Hp)).
Qed.

Lemma TR_absorb : ltac2:(tb__ "0|3|
SbfS3dS5cS3S2dS7aQ40A1M0A1SbfS2dScbA1M1SebScaR9S2eG1SdbR3SdcR2R1A2A4A1S28S3S3S27S2S26G0S12R2R1A2M2S12R9R1A2A3Fe;S76S5bVJAv;R9A1RaR1R7S2eG1SdbR5SdcR4R3A2A4A6A2Lrho';A2F_;Fmd;Fms;Ftr;S3S2S26G0G2S12R6R1A2A3Fe;VTR;S76S5bVJAv;R7A1R8R2R5A5R4A2F_;Frho';VTR;R8R3A2F_;F_;FQ';Ftp;Frho;Fnd;FS;FP;").
Proof.
  intros P S nd rho tp Q' HP HS.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv nd) S rho' tp w') w)).
  { intros [tr [ms md]] Hw. destruct (HP tr ms md Hw) as (rho' & HE & Hw'). exists rho'. split; [exact HE | exact Hw']. }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. exact (HS rho' HE).
Qed.

Lemma land_imp : ltac2:(tb__ "0|2|
S3dS3dSdeS2dS2fS2S2A2A1M0G0S2dS49A1M1G1G0G1S3S2dS7aQ40A1A1SbeS26S30S139RcRbRaR9R8R7R6R5A8S31A3S26G1S4aRbR5A2R7A3S76S5bVJAv;S5fRbS80R9S5eA4A1ReR5R4R3A6S76S5bVJAv;S5fR8S80R7S5eA4A1ReSdfR6RdA2R5R4A6F_;F_;F_;Fw;Ftp;Frho;FbdC;FtvC;Fbd2;Fbd1;Ftv2;Ftv1;Fs;FC;FL;").
Proof.
  intros L C s tv1 tv2 bd1 bd2 tvC bdC rho tp w CK Hbd Hw.
  unfold land_chk in CK. peel CK Hfr. peel CK Htv. peel CK Hnb. peel CK Hnp. peel CK Hid. peel CK He. peel CK Hbp. rename CK into Htp.
  apply (SPA_entails_JA_eq L C s (NDA tv2 fr_hf bd2 ANone) (NDA tvC fr_hf bdC ANone) rho tp w He Hid Hnp Hnb Htv Hfr Hbd eq_refl).
  apply (SPA_bd_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv2 fr_hf bd1 bd2 ANone L rho tp w Hbp).
  exact (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv1 tv2 fr_hf bd1 ANone L rho tp w Htp Hw).
Qed.

Lemma tvx_app_l : ltac2:(tb__ "0|2|
Sd0S3S2dS2fS2S2A2M0A1M1G1S63VFB;R4R3S36G0R2R1A3A4S111R4S36G0R3R2A3A2S110R5S36G0R4R3A3A2S27S63VFB;R7R6R5A4S27S111R6R5A2S110R6R5A2A2A2F_;F_;F_;Fl2;Fl1;Frho;FAi;").
Proof.
  intros Ai rho l1 l2 HN HD HZ. unfold tvinA, tvz in *. apply Forall_app in HN as [HN _]. apply Forall_app in HZ as [HZ _].
  split; [exact HN|]. split; [exact (tvd_app_l rho l1 l2 HD) | exact HZ].
Qed.

Lemma X_pureT : ltac2:(tb__ "0|1|
S3dS3dS3dS3dS5cSdeS2dS5A1M0S3S2dS7aQ40A1A1SbfS1c4RaS32S40S47R9S1c7A2S34S40A1A3A2S26S37G0A1Sc4R9RbR6A3S38G0R5A2A3S26S30S140RcRbRaR8R7R6A6S31A3S26S3dS16fS9S3eRbA1A1Sc7R8RdRcRbR7A5A2RaA3S3S1dSaS3eRdA1A1R8R1A3VTR;S76S5bVJAv;RcA1RdR2R8A5R7A2F_;Frho';VTR;S76S5bVJAv;RbA1RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fnd;FT0;FE;FP;FPre;").
Proof.
  intros Pre P E T0 nd s R rho tp Q' CALL He CK HT0 HK.
  unfold pure_chk in CK. peel CK Hfb. peel CK Hnb. peel CK Hnf. rename CK into Hchk.
  apply (CALL E s R rho tp nd _ He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [In] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite HT0. exact (HK rho' Hag).
Qed.

Lemma X_purecT : ltac2:(tb__ "0|3|
Sd0S3OF_;F_;S3dS2dS3dA1S3dS2dS2fS2S2A2A1S2dS49A1SdeS2dS5A1M0S3S2dS7aQ40A1A1M1SbfSd0S3G1VTR;S76S5bS3G1S2dScbA1M2ScaS27S159VAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5Sc3S5bSdaR2R1S7dS3dS2fS3dSc2A2S3dS2eS3dSc2R1S157VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;Sd0G2SebScaS78S5bR8R7RdS2eG2SdbR3SdcR2R1A2A4A5VAInv;R5R9R8R2A4S180VCST;VXGL;R6S39S0A1RaS3fRfA1A6R13R7SdfSe0RbRcSffR4RaR5A3A3RdA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S26S1SaS3eRcA1A1SdaA3S26S2S42RdA1S6S155A1A3S26S37G0A1Sc4RcReR9A3S38G0R8A2A3S26S30S12fVXGL;RfReRdRcRbRaR9A8S31A3S3dS3G1SbbS3dR3R12A3Sd3SaS3eR12A1A1RdR3A3S7cS4S7ReA1S9S3eR13A1A1A3VTR;S76S5bVJAv;S5fR13S80R12S5eA4A1S17eR16R14R11R10R6A5R5R4A5RdA2F_;F_;F_;Ftp';Frho';FL;VTR;S76S5bVJAv;S5fReS80RdS5eA4A1RfRaR9A5R8A2F_;F_;F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fbd;Ftv;FE;FLs;FPre;FXP;").
Proof.
  intros XP Pre Ls E tv bd s R rho tp Q' CALLEE HXP HNF HbP He CK HK.
  unfold purec_chk in CK. peel CK HX. peel CK HR. peel CK HB. peel CK Hshape. peel CK Hwp. peel CK Hnb. peel CK Hnf. peel CK Htp. rename CK into Hchk.
  apply TR_facts. intros HF.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP Pre Ls E s R rho tp (NDA tv fr_hf bd ANone) bd Q' CALLEE HNF HbP He Hchk Htp Hnf Hnb).
  - destruct (nd_below_split _ _ Hnb) as (_ & _ & Hbb & _). exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - exact Hshape.
  - exact (site_pure E s R rho tv fr_hf bd HB HR HX).
  - exact HXP.
  - intros L rho' tp' HL Hag. cbn [nd_tv nd_fr nd_am]. exact (HK L rho' tp' HL Hag HF).
Qed.

Lemma X_purecT0 : ltac2:(tb__ "0|2|
S3dS2dS3dA1S3dS2dS2fS2S2A2A1S2dS49A1SdeS2dS5A1M0S3S2dS7aQ40A1A1M1SbfSd0S3G1VTR;S76S5bS159VAInv;R3VKc;A3RdR2R1A5Sc3S5bSdaR2R1S7dS3dS2fS3dSc2A2S3dS2eS3dSc2R1S157VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S26S1SaS3eRbA1A1SdaA3S26S2S42RcA1S6S155A1A3S26S37G0A1Sc4RbRdR8A3S38G0R7A2A3S26S30S12fVXGL;ReRdRcRbRaR9R8A8S31A3S3dS3G1SbbS3dR3R11A3Sd3SaS3eR11A1A1RcR3A3S7cS4S7RdA1S9S3eR12A1A1A3VTR;S76S5bVJAv;S5fR12S80R11S5eA4A1S17eR15R13R10RfR6A5R5R4A5RcA2F_;F_;F_;Ftp';Frho';FL;VTR;S76S5bVJAv;S5fRdS80RcS5eA4A1ReR9R8A5R7A2F_;F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fbd;Ftv;FE;FLs;FPre;").
Proof.
  intros Pre Ls E tv bd s R rho tp Q' CALLEE HNF HbP He CK HK.
  unfold purec_chk in CK. peel CK HX. peel CK HR. peel CK HB. peel CK Hshape. peel CK Hwp. peel CK Hnb. peel CK Hnf. peel CK Htp. rename CK into Hchk.
  apply TR_facts. intros HF.
  apply (purec_callT_ag segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre Ls E s R rho tp (NDA tv fr_hf bd ANone) bd Q' CALLEE HNF HbP He Hchk Htp Hnf Hnb).
  - destruct (nd_below_split _ _ Hnb) as (_ & _ & Hbb & _). exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - exact Hshape.
  - exact (site_pure E s R rho tv fr_hf bd HB HR HX).
  - intros L rho' tp' HL Hag. cbn [nd_tv nd_fr nd_am]. exact (HK L rho' tp' HL Hag HF).
Qed.

Lemma X_VR : ltac2:(tb__ "0|8|
S3dS2dS2fS2S2A2M0A1M1S2S2S0S0S2dS49A1M2G2SdeS2dS5A1M3G1S3S2dS7aQ40A1A1M4SbfS3dS3dS3dS2S2G2G2S26S30S146VXGL;R15R14R13R12R11R10RfReRdRcRbAcS31A3S26S37G3A1Sc4R16SecReA3S38G3RdA2A3S26S3dS174SecR17RfReSeeRdA6R9A3S26G1S114Sc5R10SecSeeR18A4Sf1A2S32G0S2eS2S2R16S98R14R15A2A4S34G0A1M5A3A3S26G2S4aSc5R11SecSeeR19A4S62Sf0A1A2R6A3S26S3dS174SecR1aR12R11SefR10A6RbA3S26G1S114Sc5R13SecSefR1bA4Sf1A2S32G0S2eS2S2R19S98R17R18A2A4G5A3A3S26S3dS174SecR1cR14R13SedR12A6RcA3S26G1S114Sc5R15SecSedR1dA4Sf3A2S32G0S2eS2S2RcS98R19RbA2A4G5A3A3S26G2S4aSc5R16SecSedR1eA4Sf2Sf5Sf4A2A2RaA3S3G4Sd3SaS3eR21A1A1R16R2A3S7cS4S7R17A1S9S3eR22A1M6A1A3VTR;S76S5bVJAv;S5fS36G0R22S32G0S2eS2S2R21S98R1fR20A2A4G5A3A3S80S36S49R10R1cA3S5eA4A1R15R4R3A5R16A2F_;F_;Ftp';Frho';S3G4Sd3SaG6A1R17R2A3S7cS4S7R18A1S9S3eR23A1M7A1A3VTR;S76S5bVJAv;S5fS36G0R23S32G0S2eS2S2R22S98R20R21A2A4G5A3A3S80R1dS5eA4A1R15R4R3A5R17A2F_;F_;Ftp';Frho';S3G4Sd3SaG7A1R18R2A3S7cS4S7R19A1S9S3eR24A1A1A3VTR;S76S5bVJAv;S5fS36G0R24S32G0S2eS2S2R14S98R21R13A2A4G5A3A3S80S36S49R11R1eA3S5eA4A1R15R4R3A5R18A2F_;F_;Ftp';Frho';VTR;S76S5bVJAv;S5fS36G0R21S32G0S2eS2S2R20S98R1eR1fA2A4G5A3A3S80R1cS5eA4A1R22R17R16A5R15A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FbdG;FbdK;FkG;FdG;FTG;FTF;FTK;FQ';Ftp;Frho;FXk;FR;Fs;Fbrest;Fbd;Foff;Fe;Fk;Fd;Fkept;FE;").
Proof.
  intros E kept d k e off bd brest s R Xk rho tp Q' TK TF TG dG kG bdK bdG C He HTK HiK HbK HTF HiF HTG HiG HbG KK KF KG.
  unfold vr_chk in C. peel C Hoff2. peel C Hoff1. peel C Hs12. peel C Hs14. peel C Hs15. peel C Hs17. peel C HkB. peel C He2. peel C He1.
  peel C HX. peel C HR. peel C HB. peel C Hpd. peel C Hwp. peel C Hperm. peel C Htvs. peel C Hbb. peel C Hnb. peel C Hnp. peel C Hdom. peel C Hta. peel C Hchk. rename C into HXk.
  apply sv_eqb_sound in Hs12. apply sv_eqb_sound in Hs14. apply sv_eqb_sound in Hs15. apply sv_eqb_sound in Hs17.
  apply Z.leb_le in Hoff1. apply Z.leb_le in Hoff2. apply Z.ltb_lt in He1. apply Z.leb_le in He2.
  eapply TR_pre; [intros w Hw; exact (SPA_bd_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ fr_hf bd _ ANone E rho tp w Hperm Hw)|].
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E s R Xk rho tp kept [(d, kb e k)] fr_hf (bd_subst s (nd_bd VN.nd0) ++ brest) brest ANone Q' HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs eq_refl).
  - apply payA_same. exact Hwp.
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK'.
    destruct (tvx_app_l Ai rho kept _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (P0_now rho Hav HP0) as (_ & Hb & Hal & _).
    pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop].
    split; [|split].
    + intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ kept fr_hf None extraOH R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK') HN1 HD1 HZ1 HFR HR);
        [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
    + exact (proj1 (siteX Ai rho _ kept fr_hf None (ss_objs (ax_S E)) Xk rho1 tp1 md1 HM HF HB Hav HP0 HT HTK' HBf HFF HN1 HD1 HZ1 HFR HX)).
    + unfold VNP.P0_vr. rewrite !rw_call', Hs17, Hs15, Hs14, Hs12.
      change (bv_unsigned (eval rho k)) with (uval rho k). change (bv_unsigned (eval rho d)) with (uval rho d).
      change (bv_unsigned (eval rho vAL)) with (uval rho vAL). change (bv_unsigned (eval rho (xbo off))) with (uval rho (xbo off)).
      split; [|split].
      * pose proof (holds_mem _ _ (SPUle k (SLit B32)) HF HkB) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
        intros HK. apply (tvz_in rho _ d e k HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32; lia | exact HK].
      * destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
        assert (EO : uval rho (xbo off) = uval rho vb + off) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
        rewrite EO. unfold uval in H1, H2 |- *. lia.
      * destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2 |- *. lia.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    + rewrite HTK, HiK. change (nd_bd VN.nd0) with (VN.bdP VN.vN VN.vK) in HbK. cbn [nd_bd VN.nd0 ND] . rewrite HbK. exact (KK rho' tp' Hag HF).
    + rewrite HTF, HiF. cbn [bd_subst map app]. exact (KF rho' tp' Hag HF).
    + rewrite HTG, HiG, HbG. exact (KG rho' tp' Hag HF).
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0S53S57Z62S55Z2Z40A2A2R2A2VTR;S76S5bVJAv;S87A1S8eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  pose proof (sm_chk XGL) as C. peel C Hs12. peel C HX. peel C HR. peel C HB. peel C HpF. peel C HvF. peel C HpR. peel C HvR. peel C Hwp. peel C Hnb. peel C Hnp. peel C Hta. rename C into Hchk.
  apply sv_eqb_sound in HvF. apply sv_eqb_sound in HvR. apply sv_eqb_sound in Hs12.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           3 E_sm0 s_sm R_sm rho tp nd0 160 170 (FAM b tp0) CSM ltac:(lia) R_sm_eq Hchk Hta Hnp Hnb Hwp HvR HpR HvF HpF (fun A A' _ => I)).
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & HC0 & _).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ tv0 [] None R_sm rho1 tp1 md1 HM HF' HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR).
    + exact (proj1 (proj2 (siteX Ai rho _ tv0 [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))).
    + split; [rewrite Hs12; rewrite uval_lit by lia; change (fs_frame_size 3) with 512; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. pose proof T_sm_eq as ET. unfold Pre_sm, L_sm in ET. cbn [nd_tv nd_fr nd_bd nd_am nd0 ND]. rewrite ET. clear ET.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect (sel_last T_sm 3)] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    pose proof (sm1_chk XGL) as C. peel C Hlt. peel C Hal. peel C HX1. peel C HB1. peel C Hnb1. peel C Hnp1. rename C into Hwf1.
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
                  tv0 fr_hf (bd_hf tI mi_n mi_k fv_n fv_k mm_n mm_k sg_n sg_k co_n co_k rp_n rp_k tr_n tr_k ts_n ts_k) ANone 0%nat 160 3 170
                  T_sm1 objs_sm1 X_hf0 [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X Hwf1 Hnp1 Hnb1) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
        exact (proj1 (siteX Ai rho' _ tv0 fr_hf (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hf0 ++ []) rho1 tp1 md1 HM HF2 HB1 Hav HP0 HT HTK HBf HFF HN HDt HZt HFR HX1)).
      - exists rho2. rewrite app_nil_r in Hw2. change (fs_frame_size 3) with 512 in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        exact (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w Hal ltac:(lia) Hlt Hw2). }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma XH_X_pro : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0S53S57Z5eS55Z2Z40A2A2R2A2VTR;S76S5bVJAv;Sb7A1S94R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_absorb _ C_pre ndP rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 0 64 cells_pro DZero] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- C_pre_eq. exact (release_imp X_pro objs_pro 0 64 cells_pro DZero [] tv0 _ rho tp tr ms md pro_chk X_pro_objs Hw). }
  intros rho' HE. apply (REENTER C_pre ndP (92, z0)); [innth 2 | rewrite emeas_z0; lia].
Qed.

Lemma XH_E_co : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb0A1S8aR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS8aSb0A4S2eS0S2Z50SacS82Z3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 co_vrF) as VB.
  pose proof co_meas as CM. peel CM MbQ. peel CM MbE. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.

  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_co ++ [(pDco, kb 12 pKco)]) fr_hf (bd_loop pQ pKco) ANone)) E_co rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_co rho tp w co_tvp).
    apply (xff_imp _ E_co0 E_co1 E_co (xf_vr 19 720) (co_need pQ) rho tp w E_co1_eq E_co_eq2 co_xff); [|exact Hw].
    intros tr md _ HF1. exact (co_need_ok rho _ HF1 co_coF). }
  apply (X_VR E_co kept_co pDco pKco 12 720 (bd_loop pQ pKco) brest_co s_co R_co (Xkeep pDco) rho tp _ T_cok0 T_cof0 T_cog0 (SVar 520) (SVar 521) bdK_co bdG_co
           (co_chk XGL) R_co_eq T_cok0_eq co_iK co_bK T_cof0_eq co_iF T_cog0_eq co_iG co_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_co ndR (80, VR pQ 58) (rho_sub rho' s_cok)); [innth 7 |
      rewrite !VR_VM; exact (VM_meas_sub E_co0 JR_co ndJ ndR 80 tE pQ 58 59 rho rho' s_cok _ ltac:(lia) VB Hag MbE MbQ Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. unfold ndR, ndL. apply (land_imp T_coks JR_co s_cok _ tv2_cok _ bd2_cok _ _ rho' tp' w cok_land cok_bd).
    apply (xff_imp _ T_cok0 T_cok T_coks xf_back [SPUle (SLit IMG_HI) pDco] rho' tp' w T_cok_eq eq_refl cok_xff); [|exact Hw].
    intros tr md HJ HF1. destruct (k_nz_lit rho' _ pA 1 pKco HF1 ltac:(lia) cok_live) as [K1 K2].
    constructor; [|constructor]. exact (live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) K1 K2).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_co ndFc (30, z0) (rho_sub rho' s_cof)); [innth 8 | rewrite emeas_z0; pose proof (emeas_lb E_co0 ndJ 80 (VR pQ 59) rho); lia]].
    intros w Hw. unfold ndFc. apply (land_imp T_cof JF_co s_cof _ tv2_cof _ (firstn 1 brest_co) _ _ rho' tp' w cof_land cof_bd).
    apply (drop_imp T_cof _ fr_hf brest_co 1 rho' tp' w cof_wp). exact (SPA_axforms segs _ xf_back rho' T_cof0 T_cof tp' w T_cof_eq Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_co ndR (80, VR pQ 58) (rho_sub rho' s_cog)); [innth 7 |
      rewrite !VR_VM; exact (VM_meas_sub E_co0 JR_co ndJ ndR 80 tE pQ 58 59 rho rho' s_cog _ ltac:(lia) VB Hag MbE MbQ Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. unfold ndR, ndL. apply (land_imp T_cog JR_co s_cog _ tv2_cog _ bd2_cog _ _ rho' tp' w cog_land cog_bd).
    exact (SPA_axforms segs _ xf_back rho' T_cog0 T_cog tp' w T_cog_eq Hw).
Qed.

Lemma XH_E_pc : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S85A1S1a9R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1a9S85A4S2eS0S2Z50SacS82Z37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 pc_vrF) as VB. pose proof pc_meas as CM. peel CM MbQ. rename CM into MbE.
  eapply TR_pre with (P := SPA segs (JAv ndR) E_pc rho tp).
  { intros w Hw. apply (facts_imp _ _ E_pc (pc_need pT0 pQ) rho tp w E_pc_eq3 pc_xff); [intros tr md _ HF1; exact (pc_need_ok rho _ HF1 pc_pcF)|].
    apply (publish_prefix_imp _ E_pc2 pD2 (kb 12 pK2) pD2 _ rho tp w pc_xin pc_xb); [intros HF1; split; [reflexivity | exact (xslot_len rho _ pD2 pA pK2 HF1 pc_slotF)]|].
    rewrite <- E_pc2_eq. apply (reshape_fwd _ E_pc1 34 pD2 (kb 12 pA) (kb 12 pA) 12 DUnknown rho tp w pc_o34 eq_refl pc_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho _ _ _ HF pc_rs)).
    exact (SPA_axforms segs _ xf_pc rho E_pc0 E_pc1 tp w E_pc1_eq Hw). }
  apply (X_pureT Pre_pc P_ret E_pc T_pc0 ndR s_pc R_pc rho tp _ CALL_pc R_pc_eq pc_chk T_pc0_eq).
  intros rho' Hag. pose proof (agree_below_vals _ _ _ Hag) as Hag'.
  eapply TR_pre; [|apply (REENTER T_pc ndR (80, VR pQ 54) rho'); [innth 10 |
    rewrite !VR_VM; exact (VM_meas_ag E_pc0 T_pc ndR ndR 80 tE pQ 54 55 rho rho' _ ltac:(lia) VB Hag' MbE MbQ ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. apply (subX_imp _ T_pc2 T_pc (X_body pD2 pK2) rho' tp w T_pc_eq2 pc_xsub).
  apply (SPA_axforms segs _ _ rho' T_pc1 T_pc2 tp w T_pc2_eq). rewrite <- T_pc1_eq.
  apply (reshape_bwd _ T_pc0 2 pD2 (kb 12 pA) (kb 12 pA) 12 DUnknown rho' tp w tpc_o2 eq_refl tpc_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho' _ _ _ HF tpc_rs)). exact Hw.
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S85A1S1a8R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1a8S85A4S2eS0S2Z50SacS82Z35A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 da_vrF) as VB. pose proof da_meas as CM. peel CM MbQ. rename CM into MbE.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pureT Pre_da P_da E_da T_da0 ndR s_da R_da rho tp _ CALL_da R_da_eq da_chk T_da0_eq).
  intros rho' Hag. pose proof (agree_below_vals _ _ _ Hag) as Hag'.
  eapply TR_pre; [|apply (REENTER T_da ndR (80, VR pQ 52) rho'); [innth 11 |
    rewrite !VR_VM; exact (VM_meas_ag E_da0 T_da ndR ndR 80 tE pQ 52 53 rho rho' _ ltac:(lia) VB Hag' MbE MbQ ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. apply (subX_imp _ T_da2 T_da (X_body pD2 pK2) rho' tp w T_da_eq2 da_xsub). exact (SPA_axforms segs _ _ rho' T_da0 T_da2 tp w T_da2_eq Hw).
Qed.
Lemma XH_E_dg : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0S53S57Z45S55Z2Z40A2A2R2A2VTR;S76S5bVJAv;S105A1S10dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_dg0 E_dg tp w E_dg_eq Hw)|].
  apply (X_pureT Pre_da P_da E_dg T_dg0 ndXA s_dg R_dg rho tp _ CALL_da R_dg_eq dg_chk T_dg0_eq).
  intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_dg ndXA (68, z0) rho'); [innth 13 | rewrite emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_dg2 T_dg (X_body pDco pKco) rho' tp w T_dg_eq2 dg_xsub). exact (SPA_axforms segs _ _ rho' T_dg0 T_dg2 tp w T_dg2_eq Hw).
Qed.

Lemma XH_E_mi0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S105A1S109R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS109S105A4S2eS0S2Z41Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mi ++ [(mi_d, (kb 12 mi_k))]) fr_hf (nd_bd ndXA) ANone)) E_mi rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mi rho tp w mi_tvp).
    apply (xff_imp _ E_mi0 E_mi1x E_mi (xf_vr 15 496) (vr_need 12 (SAlu ALU_ADD mi_c pA) (NMI pA)) rho tp w E_mi1x_eq E_mi_eq2 mi_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_mi3_ok rho _ HF1 mi_needF). }
  apply (X_VR E_mi kept_mi mi_d mi_k 12 496 (nd_bd ndXA) brest_mi s_mi R_mi (XkeepF mi_d (X_body pDco pKco)) rho tp _ T_mik0 T_mif0 T_mig0 (SVar 520) (SVar 521) bdK_mi bdG_mi
           (mi_chk XGL) R_mi_eq T_mik0_ta mi_iK mi_bK T_mif0_ta mi_iF T_mig0_ta mi_iG mi_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi ndMI (64, z0) (rho_sub rho' s_mik)); [innth 15 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_miks (ax_X T_miks) hG 4 5) JR_mi s_mik (kept_mi ++ [(mi_d, (kb 12 mi_k))]) tv2_mik (bdK_mi ++ brest_mi) bd2_mik _ _ rho' tp' w mik_land mik_bd).
    apply (reopen_imp T_miks (ax_X T_miks) (kept_mi ++ [(mi_d, (kb 12 mi_k))]) _ 4 5 rho' tp' w (mik_ro0 XGL)).
    apply (xff_imp _ T_mik0 T_mik T_miks (xf_backV 14 28 496) [SPUle (SLit IMG_HI) mi_d; co_live] rho' tp' w T_mik_ap T_miks_eq2 mik_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_a rho' _ mi_c pA mi_k HF1 mik_live in live_holds _ rho' tp' tr md mi_d 12 mi_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mik_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor]].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mi ndMIf (20, z0) (rho_sub rho' s_mif)); [innth 16 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mifs JF_mi s_mif (kept_mi ++ [(mi_d, (kb 12 mi_k))]) tv2_mif (firstn 1 brest_mi) (firstn 1 brest_mi) _ _ rho' tp' w mif_land mif_bd).
    apply (drop_imp _ _ fr_hf brest_mi 1 rho' tp' w mif_wp).
    apply (xff_imp _ T_mif0 T_mif T_mifs (xf_backV 14 28 496) [co_live] rho' tp' w T_mif_ap T_mifs_eq2 mif_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mif_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi ndMI (64, z0) (rho_sub rho' s_mig)); [innth 15 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_migs (ax_X T_migs) hG 4 5) JR_mi s_mig (kept_mi ++ [(SVar 520, (kb 12 (SVar 521)))]) tv2_mig (bdG_mi ++ brest_mi) bd2_mig _ _ rho' tp' w mig_land mig_bd).
    apply (reopen_imp T_migs (ax_X T_migs) (kept_mi ++ [(SVar 520, (kb 12 (SVar 521)))]) _ 4 5 rho' tp' w (mig_ro0 XGL)).
    apply (xff_imp _ T_mig0 T_mig T_migs (xf_backV 14 28 496) [co_live] rho' tp' w T_mig_ap T_migs_eq2 mig_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mig_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
Qed.

Lemma XH_E_fv0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb5A1S108R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS108Sb5A4S2eS0S2Z3bSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (TR_absorb _ E_fv1 ndMI rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 4 5 cells_fv DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_fv1_eq. exact (release_imp E_fv0 objs_fv0 4 5 cells_fv DUnknown [(32, 4)] _ _ rho tp tr ms md fv_rel fv_robjs Hw). }
  intros rho1 HE1.
  change (JAv ndMI) with (JAv (NDA (nd_tv ndMI) fr_hf (nd_bd ndMI) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_fv ++ [(fv_d, (kb 4 fv_k))]) fr_hf (nd_bd ndMI) ANone)) E_fv rho1 tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_fv rho1 tp w fv_tvp).
    apply (xff_imp _ E_fv1 E_fv1x E_fv (xf_vr 16 528) (vr_need 4 (SAlu ALU_ADD fv_c (SLit 1)) (NFV pA)) rho1 tp w E_fv1x_eq E_fv_eq2 fv_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho1 _ fv_c fv_n HF1 fv_needF). }
  apply (X_VR E_fv kept_fv fv_d fv_k 4 528 (nd_bd ndMI) brest_fv s_fv R_fv (XkeepF fv_d XF1) rho1 tp _ T_fvk0 T_fvf0 T_fvg0 (SVar 520) (SVar 521) bdK_fv bdG_fv
           (fv_chk XGL) R_fv_eq T_fvk0_ta fv_iK fv_bK T_fvf0_ta fv_iF T_fvg0_ta fv_iG fv_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv ndFV (58, z0) (rho_sub rho' s_fvk)); [innth 19 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_fvks JR_fv s_fvk (kept_fv ++ [(fv_d, (kb 4 fv_k))]) tv2_fvk (bdK_fv ++ brest_fv) bd2_fvk _ _ rho' tp' w fvk_land fvk_bd).
    apply (xff_imp _ T_fvk0 T_fvk T_fvks (xf_backV 15 29 528) [SPUle (SLit IMG_HI) fv_d] rho' tp' w T_fvk_ap T_fvks_eq2 fvk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ fv_c 1 fv_k HF1 ltac:(lia) fvk_live in live_holds _ rho' tp' tr md fv_d 4 fv_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_fv ndFVf (20, z0) (rho_sub rho' s_fvf)); [innth 20 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k) hG 4 5) JF_fv s_fvf (kept_fv ++ [(fv_d, (kb 4 fv_k))]) tv2_fvf (firstn 1 brest_fv) (firstn 1 brest_fv) _ _ rho' tp' w fvf_land fvf_bd).
    apply (drop_imp _ _ fr_hf brest_fv 1 rho' tp' w fvf_wp).
    apply (reopen_imp T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k) (kept_fv ++ [(fv_d, (kb 4 fv_k))]) _ 4 5 rho' tp' w (fvf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fvf0 T_fvf tp' w T_fvf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv ndFV (58, z0) (rho_sub rho' s_fvg)); [innth 19 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_fvg JR_fv s_fvg (kept_fv ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_fvg (bdG_fv ++ brest_fv) bd2_fvg _ _ rho' tp' w fvg_land fvg_bd).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fvg0 T_fvg tp' w T_fvg_ap Hw).
Qed.

Lemma XH_E_mm0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SafA1S10aR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS10aSafA4S2eS0S2Z37Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndFV) with (JAv (NDA (nd_tv ndFV) fr_hf (nd_bd ndFV) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mm ++ [(mm_d, (kb 4 mm_k))]) fr_hf (nd_bd ndFV) ANone)) E_mm rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mm rho tp w mm_tvp).
    apply (xff_imp _ E_mm0 E_mm1x E_mm (xf_vr 17 560) (vr_need 4 (SAlu ALU_ADD mm_c (SLit 1)) (NMM pA)) rho tp w E_mm1x_eq E_mm_eq2 mm_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho _ mm_c mm_n HF1 mm_needF). }
  apply (X_VR E_mm kept_mm mm_d mm_k 4 560 (nd_bd ndFV) brest_mm s_mm R_mm (XkeepF mm_d (XFV pDfv pKfv)) rho tp _ T_mmk0 T_mmf0 T_mmg0 (SVar 788) (SVar 789) bdK_mm bdG_mm
           (mm_chk XGL) R_mm_eq T_mmk0_ta mm_iK mm_bK T_mmf0_ta mm_iF T_mmg0_ta mm_iG mm_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm ndMM (54, z0) (rho_sub rho' s_mmk)); [innth 22 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mmks JR_mm s_mmk (kept_mm ++ [(mm_d, (kb 4 mm_k))]) tv2_mmk (bdK_mm ++ brest_mm) bd2_mmk _ _ rho' tp' w mmk_land mmk_bd).
    apply (xff_imp _ T_mmk0 T_mmk T_mmks (xf_backV 16 30 560) [SPUle (SLit IMG_HI) mm_d] rho' tp' w T_mmk_ap T_mmks_eq2 mmk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ mm_c 1 mm_k HF1 ltac:(lia) mmk_live in live_holds _ rho' tp' tr md mm_d 4 mm_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mm ndMMf (20, z0) (rho_sub rho' s_mmf)); [innth 23 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_mmf (XMM mm_d mm_k) hG 4 5) JF_mm s_mmf (kept_mm ++ [(mm_d, (kb 4 mm_k))]) tv2_mmf (firstn 1 brest_mm) (firstn 1 brest_mm) _ _ rho' tp' w mmf_land mmf_bd).
    apply (drop_imp _ _ fr_hf brest_mm 1 rho' tp' w mmf_wp).
    apply (reopen_imp T_mmf (XMM mm_d mm_k) (kept_mm ++ [(mm_d, (kb 4 mm_k))]) _ 4 5 rho' tp' w (mmf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mmf0 T_mmf tp' w T_mmf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm ndMM (54, z0) (rho_sub rho' s_mmg)); [innth 22 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mmg JR_mm s_mmg (kept_mm ++ [(SVar 788, (kb 4 (SVar 789)))]) tv2_mmg (bdG_mm ++ brest_mm) bd2_mmg _ _ rho' tp' w mmg_land mmg_bd).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mmg0 T_mmg tp' w T_mmg_ap Hw).
Qed.

Lemma XH_E_sg0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb6A1S1afR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1afSb6A4S2eS0S2Z35Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndMM) with (JAv (NDA (nd_tv ndMM) fr_hf (nd_bd ndMM) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_sg ++ [(sg_d, (kb 4 sg_k))]) fr_hf (nd_bd ndMM) ANone)) E_sg rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_sg rho tp w sg_tvp).
    apply (xff_imp _ E_sg0 E_sg1x E_sg (xf_vr 18 592) (vr_need 4 (SAlu ALU_ADD sg_c (SLit 1)) (NSG pA)) rho tp w E_sg1x_eq E_sg_eq2 sg_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho _ sg_c sg_n HF1 sg_needF). }
  apply (X_VR E_sg kept_sg sg_d sg_k 4 592 (nd_bd ndMM) brest_sg s_sg R_sg (XkeepF sg_d (XMM pDmm pKmm)) rho tp _ T_sgk0 T_sgf0 T_sgg0 (SVar 656) (SVar 657) bdK_sg bdG_sg
           (sg_chk XGL) R_sg_eq T_sgk0_ta sg_iK sg_bK T_sgf0_ta sg_iF T_sgg0_ta sg_iG sg_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg ndSG (52, z0) (rho_sub rho' s_sgk)); [innth 24 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgks (XnoL T_sgks) hG 4 5) JR_sg s_sgk (kept_sg ++ [(sg_d, (kb 4 sg_k))]) tv2_sgk (bdK_sg ++ brest_sg) bd2_sgk _ _ rho' tp' w sgk_land sgk_bd).
    apply (reopen_imp T_sgks (XnoL T_sgks) (kept_sg ++ [(sg_d, (kb 4 sg_k))]) _ 4 5 rho' tp' w (sgk_ro0 XGL)).
    apply (xff_imp _ T_sgk0 T_sgk T_sgks (xf_backV 17 31 592) [SPUle (SLit IMG_HI) sg_d] rho' tp' w T_sgk_ap T_sgks_eq2 sgk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ sg_c 1 sg_k HF1 ltac:(lia) sgk_live in live_holds _ rho' tp' tr md sg_d 4 sg_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_sg ndSGf (20, z0) (rho_sub rho' s_sgf)); [innth 25 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgf (XnoL T_sgf) hG 4 5) JF_sg s_sgf (kept_sg ++ [(sg_d, (kb 4 sg_k))]) tv2_sgf (firstn 1 brest_sg) (firstn 1 brest_sg) _ _ rho' tp' w sgf_land sgf_bd).
    apply (drop_imp _ _ fr_hf brest_sg 1 rho' tp' w sgf_wp).
    apply (reopen_imp T_sgf (XnoL T_sgf) (kept_sg ++ [(sg_d, (kb 4 sg_k))]) _ 4 5 rho' tp' w (sgf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sgf0 T_sgf tp' w T_sgf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg ndSG (52, z0) (rho_sub rho' s_sgg)); [innth 24 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgg (XnoL T_sgg) hG 4 5) JR_sg s_sgg (kept_sg ++ [(SVar 656, (kb 4 (SVar 657)))]) tv2_sgg (bdG_sg ++ brest_sg) bd2_sgg _ _ rho' tp' w sgg_land sgg_bd).
    apply (reopen_imp T_sgg (XnoL T_sgg) (kept_sg ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 4 5 rho' tp' w (sgg_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sgg0 T_sgg tp' w T_sgg_ap Hw).
Qed.

Lemma XH_E_trg0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S105A1S188R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS188S105A4S2eS0S2Z3fSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_trg ++ [(tr_d, (kb 4 tr_k))]) fr_hf (nd_bd ndXA) ANone)) E_trg rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_trg rho tp w trg_tvp).
    rewrite <- E_trg_eq2. exact (SPA_axforms segs _ (xf_vr 21 784) rho E_trg0 E_trg1x tp w E_trg1x_eq Hw). }
  apply (X_VR E_trg kept_trg tr_d tr_k 4 784 (nd_bd ndXA) brest_trg s_trg R_trg (XkeepF tr_d (X_body pDco pKco)) rho tp _ T_trgk0 T_trgf0 T_trgg0 (SVar 520) (SVar 521) bdK_trg bdG_trg
           (trg_chk XGL) R_trg_eq T_trgk0_ta trg_iK trg_bK T_trgf0_ta trg_iF T_trgg0_ta trg_iG trg_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trg ndTR (62, z0) (rho_sub rho' s_trgk)); [innth 29 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgk JR_trg s_trgk (kept_trg ++ [(tr_d, (kb 4 tr_k))]) tv2_trgk (bdK_trg ++ brest_trg) bd2_trgk _ _ rho' tp' w trgk_land trgk_bd).
    apply (xff_imp _ T_trgk0 T_trgk1 T_trgk (xf_backV 20 34 784) [SPUle (SLit IMG_HI) tr_d] rho' tp' w T_trgk1_ap T_trgk_eq2 trgk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_tri rho' _ tr_k HF1 trgk_live in live_holds _ rho' tp' tr md tr_d 4 tr_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_trg ndTRf (20, z0) (rho_sub rho' s_trgf)); [innth 30 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgf JF_trg s_trgf (kept_trg ++ [(tr_d, (kb 4 tr_k))]) tv2_trgf (firstn 1 brest_trg) (firstn 1 brest_trg) _ _ rho' tp' w trgf_land trgf_bd).
    apply (drop_imp _ _ fr_hf brest_trg 1 rho' tp' w trgf_wp).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trgf0 T_trgf tp' w T_trgf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trg ndTR (62, z0) (rho_sub rho' s_trgg)); [innth 29 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgg JR_trg s_trgg (kept_trg ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_trgg (bdG_trg ++ brest_trg) bd2_trgg _ _ rho' tp' w trgg_land trgg_bd).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trgg0 T_trgg tp' w T_trgg_ap Hw).
Qed.

Lemma XH_E_trb0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S105A1S187R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS187S105A4S2eS0S2Z3fSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_trb ++ [(tr_d, (kb 4 tr_k))]) fr_hf (nd_bd ndXA) ANone)) E_trb rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_trb rho tp w trb_tvp).
    rewrite <- E_trb_eq2. exact (SPA_axforms segs _ (xf_vr 21 784) rho E_trb0 E_trb1x tp w E_trb1x_eq Hw). }
  apply (X_VR E_trb kept_trb tr_d tr_k 4 784 (nd_bd ndXA) brest_trb s_trb R_trb (XkeepF tr_d (X_body pDco pKco)) rho tp _ T_trbk0 T_trbf0 T_trbg0 (SVar 520) (SVar 521) bdK_trb bdG_trb
           (trb_chk XGL) R_trb_eq T_trbk0_ta trb_iK trb_bK T_trbf0_ta trb_iF T_trbg0_ta trb_iG trb_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trb ndTR (62, z0) (rho_sub rho' s_trbk)); [innth 31 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbk JR_trb s_trbk (kept_trb ++ [(tr_d, (kb 4 tr_k))]) tv2_trbk (bdK_trb ++ brest_trb) bd2_trbk _ _ rho' tp' w trbk_land trbk_bd).
    apply (xff_imp _ T_trbk0 T_trbk1 T_trbk (xf_backV 20 34 784) [SPUle (SLit IMG_HI) tr_d] rho' tp' w T_trbk1_ap T_trbk_eq2 trbk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_tri rho' _ tr_k HF1 trbk_live in live_holds _ rho' tp' tr md tr_d 4 tr_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_trb ndTRf (20, z0) (rho_sub rho' s_trbf)); [innth 32 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbf JF_trb s_trbf (kept_trb ++ [(tr_d, (kb 4 tr_k))]) tv2_trbf (firstn 1 brest_trb) (firstn 1 brest_trb) _ _ rho' tp' w trbf_land trbf_bd).
    apply (drop_imp _ _ fr_hf brest_trb 1 rho' tp' w trbf_wp).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trbf0 T_trbf tp' w T_trbf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trb ndTR (62, z0) (rho_sub rho' s_trbg)); [innth 31 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbg JR_trb s_trbg (kept_trb ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_trbg (bdG_trb ++ brest_trb) bd2_trbg _ _ rho' tp' w trbg_land trbg_bd).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trbg0 T_trbg tp' w T_trbg_ap Hw).
Qed.

Lemma XH_E_rp0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SadA1SfaR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cSfaSadA4S2eS0S2Z3dSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndTR) with (JAv (NDA (nd_tv ndTR) fr_hf (nd_bd ndTR) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_rp ++ [(rp_d, (kb 4 rp_k))]) fr_hf (nd_bd ndTR) ANone)) E_rp rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_rp rho tp w rp_tvp).
    rewrite <- E_rp_eq2. exact (SPA_axforms segs _ (xf_vr 20 752) rho E_rp0 E_rp1x tp w E_rp1x_eq Hw). }
  apply (X_VR E_rp kept_rp rp_d rp_k 4 752 (nd_bd ndTR) brest_rp s_rp R_rp (XkeepF rp_d (XTR pDtr pKtr)) rho tp _ T_rpk0 T_rpf0 T_rpg0 (SVar 520) (SVar 521) bdK_rp bdG_rp
           (rp_chk XGL) R_rp_eq T_rpk0_ta rp_iK rp_bK T_rpf0_ta rp_iF T_rpg0_ta rp_iG rp_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_rp ndRP (60, z0) (rho_sub rho' s_rpk)); [innth 35 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpk JR_rp s_rpk (kept_rp ++ [(rp_d, (kb 4 rp_k))]) tv2_rpk (bdK_rp ++ brest_rp) bd2_rpk _ _ rho' tp' w rpk_land rpk_bd).
    apply (xff_imp _ T_rpk0 T_rpk1 T_rpk (xf_backV 19 33 752) [SPUle (SLit IMG_HI) rp_d] rho' tp' w T_rpk1_ap T_rpk_eq2 rpk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_rp rho' _ rp_k HF1 rpk_live in live_holds _ rho' tp' tr md rp_d 4 rp_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_rp ndRPf (20, z0) (rho_sub rho' s_rpf)); [innth 36 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpf JF_rp s_rpf (kept_rp ++ [(rp_d, (kb 4 rp_k))]) tv2_rpf (firstn 1 brest_rp) (firstn 1 brest_rp) _ _ rho' tp' w rpf_land rpf_bd).
    apply (drop_imp _ _ fr_hf brest_rp 1 rho' tp' w rpf_wp).
    exact (SPA_axforms segs _ (xf_backV 19 33 752) rho' T_rpf0 T_rpf tp' w T_rpf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_rp ndRP (60, z0) (rho_sub rho' s_rpg)); [innth 35 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpg JR_rp s_rpg (kept_rp ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_rpg (bdG_rp ++ brest_rp) bd2_rpg _ _ rho' tp' w rpg_land rpg_bd).
    exact (SPA_axforms segs _ (xf_backV 19 33 752) rho' T_rpg0 T_rpg tp' w T_rpg_ap Hw).
Qed.

Lemma XH_E_ts0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SaeA1SfbR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cSfbSaeA4S2eS0S2Z37Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndRP) with (JAv (NDA (nd_tv ndRP) fr_hf (nd_bd ndRP) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_ts ++ [(ts_d, (kb 1 ts_k))]) fr_hf (nd_bd ndRP) ANone)) E_ts rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_ts rho tp w ts_tvp).
    apply (xff_imp _ E_ts0 E_ts1x E_ts (xf_vr 22 816) need_facts rho tp w E_ts1x_eq E_ts_eq2 ts_xff); [|exact Hw].
    intros tr md _ HF1. exact (ts_need_ok rho _ HF1 ts_needF). }
  apply (X_VR E_ts kept_ts ts_d ts_k 1 816 (nd_bd ndRP) brest_ts s_ts R_ts (XkeepF ts_d (XRT pDrp pKrp ts_d ts_k)) rho tp _ T_tsk0 T_tsf0 T_tsg0 (SVar 520) (SVar 521) bdK_ts bdG_ts
           (ts_chk XGL) R_ts_eq T_tsk0_ta ts_iK ts_bK T_tsf0_ta ts_iF T_tsg0_ta ts_iG ts_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_ts ndTS (54, z0) (rho_sub rho' s_tsk)); [innth 41 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_tsk (ax_X T_tsk) hG 6 23) JR_ts s_tsk (kept_ts ++ [(ts_d, (kb 1 ts_k))]) tv2_tsk (bdK_ts ++ brest_ts) bd2_tsk _ _ rho' tp' w tsk_land tsk_bd).
    apply (reopen_imp T_tsk (ax_X T_tsk) (kept_ts ++ [(ts_d, (kb 1 ts_k))]) _ 6 23 rho' tp' w (tsk_ro0 XGL)).
    apply (xff_imp _ T_tsk0 T_tsk1 T_tsk (xf_backV 21 35 816) [SPUle (SLit IMG_HI) ts_d] rho' tp' w T_tsk1_ap T_tsk_eq2 tsk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_ts rho' _ ts_k HF1 tsk_live in live_holds _ rho' tp' tr md ts_d 1 ts_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_ts ndTSf (20, z0) (rho_sub rho' s_tsf)); [innth 42 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_tsf JF_ts s_tsf (kept_ts ++ [(ts_d, (kb 1 ts_k))]) tv2_tsf (firstn 1 brest_ts) (firstn 1 brest_ts) _ _ rho' tp' w tsf_land tsf_bd).
    apply (drop_imp _ _ fr_hf brest_ts 1 rho' tp' w tsf_wp).
    exact (SPA_axforms segs _ (xf_backV 21 35 816) rho' T_tsf0 T_tsf tp' w T_tsf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_ts ndTS (54, z0) (rho_sub rho' s_tsg)); [innth 41 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_tsg (ax_X T_tsg) hG 6 23) JR_ts s_tsg (kept_ts ++ [(SVar 520, (kb 1 (SVar 521)))]) tv2_tsg (bdG_ts ++ brest_ts) bd2_tsg _ _ rho' tp' w tsg_land tsg_bd).
    apply (reopen_imp T_tsg (ax_X T_tsg) (kept_ts ++ [(SVar 520, (kb 1 (SVar 521)))]) _ 6 23 rho' tp' w (tsg_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 21 35 816) rho' T_tsg0 T_tsg tp' w T_tsg_ap Hw).
Qed.

Lemma XH_E_tdg0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SadA1S186R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS186SadA4S2eS0S2Z3dSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_tdg0 E_tdg tp w E_tdg_eq Hw)|].
  apply (X_pureT Pre_da P_da E_tdg T_tdg0 ndTR s_tdg R_tdg rho tp _ CALL_da R_tdg_eq tdg_chk T_tdg0_eq). intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_tdg ndTR (60, z0) rho'); [innth 33 | rewrite !emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_tdg2 T_tdg (XTR pDtr pKtr) rho' tp w T_tdg_eq2 tdg_xsub). exact (SPA_axforms segs _ _ rho' T_tdg0 T_tdg2 tp w T_tdg2_eq Hw).
Qed.
Lemma XH_E_wdg0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SabA1S16dR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS16dSabA4S2eS0S2Z31Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_wdg0 E_wdg tp w E_wdg_eq Hw)|].
  apply (X_pureT Pre_bw P_bwH E_wdg T_wdg0 ndTS s_wdg R_wdg rho tp _ CALL_bw R_wdg_eq wdg_chk T_wdg0_eq). intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_wdg ndTS (48, z0) rho'); [innth 46 | rewrite !emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_wdg2 T_wdg XT rho' tp w T_wdg_eq2 wdg_xsub). exact (SPA_axforms segs _ _ rho' T_wdg0 T_wdg2 tp w T_wdg2_eq Hw).
Qed.

Lemma XH_XJ : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb1A1S16eR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS16eSb1A4S2eS0S2Z2fSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndJN) with (JAv (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone)).
  apply (TR_absorb _ XJ1 (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 20 23 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- XJ1_eq. exact (release0_imp XJ objs_XJ 20 23 [] DUnknown _ _ rho tp tr ms md XJ_rel XJ_objs Hw). }
  intros rho1 _.
  apply (TR_absorb _ J (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG 6 15 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- J_eq2. exact (release_imp XJ1 objs_J 6 15 [] DUnknown [] _ _ rho1 tp tr ms md XJ1_rel XJ1_objs Hw). }
  intros rho2 _. apply (REENTER J ndJN (46, z0)); [innth 47 | rewrite !emeas_z0; lia].
Qed.

Lemma XH_XLJ : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S128R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS128Sa9A4S2eS0S2Z2dSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  eapply TR_pre; [|apply (REENTER L14 ndLL (40, VL 60) rho); [innth 48 |
    rewrite emeas_z0; pose proof (emeas_ub L14 ndLL 40 (VL 60) rho); pose proof (emeas_lb L14 ndLL 40 (VL 60) rho ltac:(lia)); lia]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  rewrite <- L14_eq2. apply (reopenS_imp XLJ1 (ax_X XLJf) (nd_tv ndLL) _ 38 39 rho tp w (XLJ_ro1 XGL)).
  rewrite <- XLJ1_eq. apply (reopen_imp XLJf (ax_X XLJf) (nd_tv ndLL) _ 28 33 rho tp w (XLJ_ro0 XGL)).
  apply (facts_imp _ XLJ XLJf [co_live] rho tp w eq_refl XLJ_xff); [|exact Hw].
  intros tr md HJ HF1. destruct (k_nz_L rho _ pKco HF1 XLJ_live) as [K1 K2].
  constructor; [exact (live_holds _ rho tp tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) K1 K2) | constructor].
Qed.

Lemma X_arr1 : ltac2:(tb__ "0|7|
S3dS3dS2dS5A1M0S0S0S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1M1G1S0S0S35S26S30S12dRdRbRaR9S34S11A1M2SdS34S2fS0S0A2A1M3R8R7A9S31A3S26G0SeS3eReA1A1S36S5RcS32S5Se4S99RbRaG2SdA5S34S5A1A3A3A3S26S3dSe5RfRdPa0G3A4ReA3SbbS2fS2fS3dS5cA2M4S2fS0S2A2M5A2S2eG4G5S2eS3dS5cRfS5fRbS80RaS5eA4A4S2eS0S2R5Sa8A4A4S169A3S27S53Z0R6A2S58R6R7A2A2VTR;S76S5bVJAv;S5fRdS80RcS5eA4M6A1R12RbRaA5VFAM;S5dS2eG4G5S2eS3dS5cR12G6A4S2eS0S2R8Sa8A4A4RbA2R9A2A2F_;F_;F_;F_;F_;Fcut;FrkC;Frk;Ftp0;Ftp;Frho;Fbd;Ftv;Fk2;Fk1;Fobjs;FC;FA;").
Proof.
  intros A C objs k1 k2 tv bd rho tp tp0 rk rkC cut CK Ho HC Hin Hrk.
  apply (TR_absorb _ C (NDA tv fr_hf bd ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG k1 k2 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HC. exact (release_imp A objs k1 k2 [] DUnknown [] _ _ rho tp tr ms md CK Ho Hw). }
  intros rho1 _. apply (REENTER C (NDA tv fr_hf bd ANone) (rkC, z0)); [exact Hin | rewrite !emeas_z0; lia].
Qed.
Lemma X_arr2 : ltac2:(tb__ "0|9|
S3dS3dS3dS2dS5A1M0G0S0S0S0S0S2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1M1G1S0S0S26S30S1a2R10RbRaSdA4S31A3S26G0SeS3eR11A1A1S36S5ReS32S5Se4S99RcRbS34S11A1M2SdA5S34S5A1M3A3A3A3S26S3dSe5R12RfPa0M4S34S2fS0S0A2A1M5A4R11A3S26S30S12dR12RfRcRbG2SdG5RaR9A9S31A3S26G0SeS3eR13A1A1S36S5R10S32S5Se4S99RdRcG2SdA5G3A3A3A3S26S3dSe5R14R11G4G5A4R13A3SbbS2fS2fS3dS5cA2M6S2fS0S2A2M7A2S2eG6G7S2eS3dS5cR14S5fRdS80RcS5eA4A4S2eS0S2R7Sa8A4A4S169A3S27S53Z0R8A2S58R8R9A2A2VTR;S76S5bVJAv;S5fRfS80ReS5eA4M8A1R18RdRcA5VFAM;S5dS2eG6G7S2eS3dS5cR18G8A4S2eS0S2RaSa8A4A4RdA2RbA2A2F_;F_;F_;F_;F_;F_;F_;F_;FrkC;Frk;Ftp0;Ftp;Frho;Fbd;Ftv;Fk4;Fk3;Fk2;Fk1;Fobjs2;Fobjs1;FC;FB;FA;").
Proof.
  intros A B C objs1 objs2 k1 k2 k3 k4 tv bd rho tp tp0 rk rkC CK1 Ho1 HB CK2 Ho2 HC Hin Hrk.
  apply (TR_absorb _ B (NDA tv fr_hf bd ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG k1 k2 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HB. exact (release0_imp A objs1 k1 k2 [] DUnknown tv bd rho tp tr ms md CK1 Ho1 Hw). }
  intros rho1 HE1. rewrite <- (emeas_eq A (NDA tv fr_hf bd ANone) rk z0 rho rho1 HE1).
  apply (TR_absorb _ C (NDA tv fr_hf bd ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG k3 k4 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HC. exact (release_imp B objs2 k3 k4 [] DUnknown [] _ _ rho1 tp tr ms md CK2 Ho2 Hw). }
  intros rho2 _. apply (REENTER C (NDA tv fr_hf bd ANone) (rkC, z0)); [exact Hin | rewrite !emeas_z0; lia].
Qed.
Lemma XH_XEf42 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S104A1S195R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS195S104A4S2eS0S2Z10Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr1 XEf42 C_Ef2 objs_Ef42 4 5 tvQ _ rho tp tp0 16 14 62 XEf42_rel XEf42_objs XEf42_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEo42 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S106A1S196R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS196S106A4S2eS0S2Z10Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEo. apply (X_arr1 XEo42 C_Eo2 objs_Eo42 4 5 tvQ _ rho tp tp0 16 14 63 XEo42_rel XEo42_objs XEo42_eq2); [innth 63 | lia]. Qed.
Lemma XH_XEf6a : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S104A1S1acR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1acS104A4S2eS0S2Z10Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr2 XEf6a XEf6a1 C_Ef2 objs_Ef6a objs_Ef6a1 28 33 38 39 tvQ _ rho tp tp0 16 14 XEf6a_rel XEf6a_objs XEf6a1_eq XEf6a1_rel XEf6a1_objs XEf6a_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEf6b : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S104A1S1adR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1adS104A4S2eS0S2Z10Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr2 XEf6b XEf6b1 C_Ef2 objs_Ef6b objs_Ef6b1 38 39 28 33 tvQ _ rho tp tp0 16 14 XEf6b_rel XEf6b_objs XEf6b1_eq XEf6b1_rel XEf6b1_objs XEf6b_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEo6 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S106A1S1aeR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1aeS106A4S2eS0S2Z10Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEo. apply (X_arr2 XEo6 XEo61 C_Eo2 objs_Eo6 objs_Eo61 38 39 28 33 tvQ _ rho tp tp0 16 14 XEo6_rel XEo6_objs XEo61_eq XEo61_rel XEo61_objs XEo6_eq2); [innth 63 | lia]. Qed.

Lemma ccount_FFx3 : ltac2:(tb__ "0|3|
S3S0S2aS26S0R1Z3A3A1S26S35S17dR2S7dS2fS2fS0S0A2M0S0A2M1G0S3aG0S0A2M2S172VFF;R3S80A3A4A2S17dR2S7dG1G0G2VFF;A4A2A3F_;Fc;Frho;").
Proof.
  intros rho c Hc. unfold FFx, fr_hf. cbn [map app]. rewrite map_app. cbn [map fst frv snd]. unfold ccount. rewrite filter_app. cbn [List.filter].
  unfold is_cls at 2. cbn [snd]. replace (fs_frame_size 3 =? fs_frame_size c) with false.
  - cbn. rewrite app_nil_r. reflexivity.
  - symmetry. apply Z.eqb_neq. unfold fs_frame_size. intros E. destruct (Z.leb_spec 0 c) as [H0|H0].
    + rewrite !Z.shiftl_mul_pow2 in E by lia. assert (E2 : 2 ^ c = 2 ^ 3) by nia. apply Z.pow_inj_r in E2; lia.
    + rewrite (Z.shiftl_mul_pow2 64 3) in E by lia. rewrite (Z.shiftl_div_pow2 64 c) in E by lia.
      pose proof (Z.pow_pos_nonneg 2 (- c) ltac:(lia) ltac:(lia)) as HP.
      assert (HD : 64 / 2 ^ (- c) <= 64) by (apply Z.div_le_upper_bound; nia). change (2 ^ 3) with 8 in E. lia.
Qed.

Lemma pg_call_chkF_unf : pg_call_chkF XGL = ltac:(let t := eval unfold pg_call_chkF in (pg_call_chkF XGL) in exact t).
Proof. let t := eval unfold pg_call_chkF in (pg_call_chkF XGL) in exact (@eq_refl bool t). Qed.

Lemma CPGF : ltac2:(tb__ "0|1|
S2dS2fS0S0A2M0A1S2dS2fG0S0A2A1S4dS3S2dS7aQ40A1A1S4cZ5R3A2VTR;S76S5bS65VAInv;VCST;VXGL;VKc;S153R6R5A2R6R5R4S60S16bAaS164R3R2A5Sc3S5bSdaR3R2S173VAInv;VCST;VXGL;VKc;S153S60S163R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB0.
  pose proof Pre_pgS_chk as C. peel C HFb. peel C HFs. peel C HSs. rename C into HSb.
  apply (TR_pureP _ (Forall (holds rho1) F_pg)).
  { intros w Hw. exact (facts_sub_holds rho1 _ _ HFs (SPA_facts_hold segs _ rho1 Pre_pgF tp1 w Hw)). }
  intros HFp.
  apply (TR_post _ (LQPA segs NF rho1 tp1 (PostsC AInv CST XGL Kc PGP.P0_pg PTrue PD_pg FBc FFc BXc))).
  { intros w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
    assert (HFp' : Forall (holds rho') F_pg).
    { apply Forall_forall. intros p Hp. apply (proj1 (holds_agree_vals NF rho1 rho' p Hag (proj1 (forallb_forall _ _) HFb p Hp))).
      exact (proj1 (Forall_forall _ _) HFp p Hp). }
    pose proof P_F_below as PB. peel PB PBi.
    cbn [PostsC PD_pg map In fst snd] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    - exists P_invF, (JLA AInv CST XGL Kc (PGP.P0_pg FBc FFc) FBc FFc BXc PTrue PGC.nd0), rho', tp'.
      split; [left; reflexivity|]. split; [exact Hag|]. split; [|exact HJL].
      rewrite <- P_invF_eq.
      exact (proj1 (SPA_refacts segs (fun _ _ _ _ => True) rho' PG.P_inv _ tp' w (conj Hsm I) PBi (fun HF => proj2 (Forall_app _ _ _) (conj HFp' HF)))).
    - exists P_okF, (JLA AInv CST XGL Kc (PGP.P0_pg FBc FFc) FBc FFc BXc PTrue PGC.nd0), rho', tp'.
      split; [right; left; reflexivity|]. split; [exact Hag|]. split; [|exact HJL].
      rewrite <- P_okF_eq.
      exact (proj1 (SPA_refacts segs (fun _ _ _ _ => True) rho' PG.P_ok _ tp' w (conj Hsm I) PB (fun HF => proj2 (Forall_app _ _ _) (conj HFp' HF)))). }
  eapply TR_pre; [|exact (CPG FBc FFc BXc rho1 tp1 HB0)].
  intros w Hw. apply (SPA_axforms segs _ [AXMerge 3] rho1 Pre_pgS PG.Pre_pg tp1 w Pre_pg_merge).
  rewrite <- Pre_pgS_drop. apply (SPA_refacts segs _ rho1 Pre_pgF _ tp1 w Hw HSb). intros HF. exact (facts_sub_holds rho1 _ _ HSs HF).
Qed.

Lemma pg_F_ok : ltac2:(tb__ "0|0|
S3S2dS4A1S7cS4S7R2A1R1A3S26S30S19eR2A1S31A3S26S30S167R3A1S31A3S7cS4S7R5A1S165A3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF CP CE.
  destruct (pg_vals rho F HF CP) as (VA & VD & V3 & VK & VT3 & VKT & VN).
  unfold pgEF in CE. rdF HF CE FKts. rdF HF CE Fhf. rdF HF CE Ftr. rdF HF CE Frp. rdF HF CE Ftop. rdF HF CE Efr. rdF HF CE Ets. rdF HF CE Etr. pose proof (holds_mem _ _ _ HF CE) as Erp.
  rewrite h_ule in FKts, Fhf, Ftr, Frp, Ftop, Efr, Ets, Etr, Erp. unfold B32 in *.
  rewrite uval_lit in FKts by lia. rewrite uval_lit in Fhf by lia. rewrite uval_lit in Ftr by lia. rewrite uval_lit in Frp by lia. rewrite uval_lit in Ftop by lia.
  set (T := uval rho (SVar 30)) in *.
  pose proof (uval_range rho pDrp) as R1. pose proof (uval_range rho pDtr) as R2. pose proof (uval_range rho pDts) as R3. pose proof (uval_range rho hF) as R4.
  pose proof (uval_range rho pKrp) as R5. pose proof (uval_range rho pKtr) as R6. pose proof (uval_range rho pKts) as R7.
  assert (EKrp : uval rho (kb 4 pKrp) = 4 * uval rho pKrp) by (apply uval_kb; lia).
  assert (EKtr : uval rho (kb 4 pKtr) = 4 * uval rho pKtr) by (apply uval_kb; lia).
  assert (EKts : uval rho (kb 1 pKts) = uval rho pKts) by (rewrite uval_kb by lia; lia).
  rewrite uval_add_small in Erp by (rewrite EKrp; lia). rewrite uval_add_small in Etr by (rewrite EKtr; lia). rewrite uval_add_small in Ets by (rewrite EKts; lia).
  rewrite uval_add_litZ in Efr by lia. rewrite EKrp in Erp. rewrite EKtr in Etr. rewrite EKts in Ets.
  assert (E3a : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
  assert (Eam : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
  assert (E3t : uval rho (kb 3 am2) = 3 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_kb; rewrite ?Eam; lia).
  assert (E12a : uval rho (SMd M_MUL pA (SLit 12)) = 12 * uval rho pA) by (apply uval_mulc; lia).
  assert (E12t : uval rho (SMd M_MUL am2 (SLit 12)) = 12 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_mulc; rewrite ?Eam; lia).
  set (a := uval rho pA) in *. set (d := uval rho pDts) in *.
  pose proof (V_o16A rho VA) as O16. pose proof (V_o4A rho VA) as O4. pose proof (V_a16 rho VA) as A16. pose proof (V_orfx rho VA) as ORF.
  pose proof (V_pNXT rho VA VD) as PN. pose proof (V_pPRV rho VA VD) as PP. pose proof (V_pRFX rho VA VD) as PR. pose proof (V_needA rho VA) as NA.
  pose proof (V_x16 rho VA) as [X16 _]. pose proof (V_r8 rho VA) as R8.
  fold a in O16, O4, A16, ORF, PN, PP, PR, NA, X16, R8. fold d in PN, PP, PR.
  set (x16 := 4 * a + 15 - (4 * a + 15) mod 16) in *. set (r8 := (a + 7) / 8) in *.
  assert (NB : 16 * a + x16 + x16 + r8 <= uval rho needA).
  { rewrite NA. assert (E32 : (8 * a + 30) mod 32 = 2 * ((4 * a + 15) mod 16)) by (replace (8 * a + 30) with (2 * (4 * a + 15)) by lia; replace 32 with (2 * 16) by lia; apply Z.mul_mod_distr_l; lia).
    pose proof (Z.mod_pos_bound (r8 + 15) 16 ltac:(lia)). subst x16. lia. }
  subst x16 r8. subst a d.
  unfold F_pgC. change (SAlu ALU_ADD (SVar 350) (SAlu ALU_SLL (SVar 418) (SLit 4))) with AR.pNXT'.
  change (SAlu ALU_SLL (SVar 418) (SLit 4)) with AR.o16A. change (SAlu ALU_SLL (SVar 418) (SLit 2)) with AR.o4A.
  change (SAlu ALU_SRL (SAlu ALU_ADD (SVar 418) (SLit 7)) (SLit 3)) with AR.orfx.
  change (SAlu ALU_AND (SAlu ALU_ADD AR.o4A (SLit 15)) (SLit 18446744073709551600)) with AR.a16.
  change (SAlu ALU_ADD AR.pNXT' AR.a16) with AR.pPRV'. change (SAlu ALU_ADD AR.pPRV' AR.a16) with AR.pRFX'.
  change (SVar 160) with hF. change (SVar 346) with pDrp. change (SVar 343) with pDtr. change (SVar 350) with pDts. change (SVar 418) with pA.
  change (SAlu ALU_ADD pA (SLit (-2))) with am2.
  repeat (apply Forall_cons; [rewrite h_ule; rewrite ?(uval_lit rho 140737488355328) by lia; rewrite ?(uval_lit rho 1099511627776) by lia; rewrite ?(uval_lit rho 72) by lia|]); [..|constructor].
  all: try (rewrite uval_add_litZ by lia; lia).
  all: try (rewrite uval_add_small by (rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia); rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia).
  all: rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia.
Qed.

Lemma HIN_pg : ltac2:(tb__ "0|1|
S3SebSd0S3S2dS7aQ40A1A1ScaS7cS4S7R6A1S9S3eS161A1A1A3Sb8VCST;VFB;VFF;Vrho0;A4Sd3S97Vrho0;R8A3VAInv;R7R6R5R4A4S66Vrho0;R8A2S112RbSd2Sd1R9A1A1A2S6aVFB;RaA2S6bVFF;RbA2S63VFB;RcReS61SabA1M0A4S111RfG0A2S110R10G0A2S67VFF;RfR11S80A4S27S17aVCST;Vrho0;VFB;VFF;R12G0S80S162A8S27S17bVCST;VXGL;Vrho0;VFB;VFF;R12G0S80Sd7A9S153S113VFB;R12G0A3S172VFF;R12S80A3SdfSe0R12S162R11A3Sd6A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (_ & _ & _ & _ & HC6).
  pose proof (pg_chkF XGL) as C. rewrite pg_call_chkF_unf in C.
  peel C HP0F. peel C Hs18. peel C Hs17. peel C Hs16. peel C Hs15. peel C Hs14. peel C Hs13. peel C Hs12. peel C HX. peel C HR. peel C HB. clear C.
  apply sv_eqb_sound in Hs12. apply sv_eqb_sound in Hs13. apply sv_eqb_sound in Hs14. apply sv_eqb_sound in Hs15. apply sv_eqb_sound in Hs16. apply sv_eqb_sound in Hs17. apply sv_eqb_sound in Hs18.
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ.
  unfold pg0F in HP0F. peel HP0F Gtr. peel HP0F Grp. peel HP0F Lts. peel HP0F Ltr. peel HP0F Lrp. rename HP0F into HfF.
  pose proof (holds_mem _ _ _ HF Lrp) as Frp. pose proof (holds_mem _ _ _ HF Ltr) as Ftr. pose proof (holds_mem _ _ _ HF Lts) as Fts.
  pose proof (holds_mem _ _ _ HF Grp) as Crp. pose proof (holds_mem _ _ _ HF Gtr) as Ctr.
  rewrite h_ule in Frp, Ftr, Fts, Crp, Ctr. unfold IMG_HI in Frp, Ftr, Fts. rewrite uval_lit in Frp by lia. rewrite uval_lit in Ftr by lia. rewrite uval_lit in Fts by lia.
  destruct (pg_vals rho _ HF pgF_callF) as (VA & VD & V3 & VK & VT3 & VKT & VN).
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ (nd_tv ndTS) fr_hf None extraOH R_pgF rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN HD HZ HFR HR);
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ (nd_tv ndTS) fr_hf None (ss_objs (ax_S E_pgF)) Xk_pg rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN HD HZ HFR HX)).
  - unfold PGP.P0_pg. rewrite !rw_call', Hs12, Hs13, Hs14, Hs15, Hs16, Hs17, Hs18.
    change (bv_unsigned (eval rho (xfo 48))) with (uval rho (xfo 48)). change (bv_unsigned (eval rho (xfo 160))) with (uval rho (xfo 160)).
    change (bv_unsigned (eval rho pA)) with (uval rho pA). change (bv_unsigned (eval rho pDrp)) with (uval rho pDrp). change (bv_unsigned (eval rho pDtr)) with (uval rho pDtr).
    change (bv_unsigned (eval rho pDts)) with (uval rho pDts). change (bv_unsigned (eval rho needA)) with (uval rho needA).
    assert (E48 : uval rho (xfo 48) = uval rho hF + 48) by (unfold xfo; exact (foff_rng rho _ 48 HF HfF ltac:(lia))).
    assert (E160 : uval rho (xfo 160) = uval rho hF + 160) by (unfold xfo; exact (foff_rng rho _ 160 HF HfF ltac:(lia))).
    assert (InF : In (uval rho hF, 512, uval rho hFL) (FFx FF rho fr_hf)).
    { apply In_FFx. right. exists (hF, 3, hFL). split; [left; reflexivity | reflexivity]. }
    assert (Erp : uval rho (kb 4 pKrp) = 4 * uval rho pKrp) by (apply uval_kb; unfold B32 in VK; lia).
    assert (Etr : uval rho (kb 4 pKtr) = 4 * uval rho pKtr) by (apply uval_kb; unfold B32 in VKT; lia).
    assert (E3a : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
    assert (Eam : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
    assert (E3t : uval rho (kb 3 am2) = 3 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_kb; rewrite ?Eam; lia).
    assert (InB : forall d k, In (d, k) (nd_tv ndTS) -> uval rho d <> 0 -> In (uval rho d, uval rho k) (FBx FB rho (nd_tv ndTS))).
    { intros d k Hin Hnz. apply In_FBx. right. exists (d, k). split; [exact Hin|]. split; [|reflexivity]. unfold tnz. cbn [fst]. unfold uval in Hnz. exact Hnz. }
    split; [rewrite (ccount_FFx3 rho 6 ltac:(lia)); exact HC6|].
    split; [exists (uval rho hF), 512, (uval rho hFL); split; [exact InF | rewrite E48; lia]|].
    split; [exists (uval rho hF), 512, (uval rho hFL); split; [exact InF | rewrite E160; lia]|].
    split; [exists (uval rho pDrp), (uval rho (kb 4 pKrp)); split; [apply InB; [cbn; tauto | lia] | rewrite Erp; lia]|].
    split; [exists (uval rho pDtr), (uval rho (kb 4 pKtr)); split; [apply InB; [cbn; tauto | lia] | rewrite Etr; lia]|].
    exists (uval rho pDts), (uval rho (kb 1 pKts)); split; [apply InB; [cbn; tauto | lia] | rewrite uval_kb by (pose proof (uval_range rho pKts); lia); lia].
Qed.

Lemma XH_E_pg0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;SabA1Sd8R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cSd8SabA4S2eS0S2Z33Sa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. rewrite emeas_z0. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).

  apply (TR_absorb _ E_pg0r (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 6 23 cells_pg DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_pg0r_eq. apply (release_imp E_pg0t (objs_butlast E_pg0t) 6 23 cells_pg DUnknown [(160, 24); (48, 72)] _ _ rho tp tr ms md pg_rel pg_robjs).
    rewrite <- E_pg0t_eq2. exact (SPA_retile segs _ rho E_pg0 1 rt72 news72 (ax_S E_pg0t) tp _ E_pg0t_rt E_pg0t_wf Hw). }
  intros rho1 _. clear rho. rename rho1 into rho.

  pose proof pg_wf43 as W43. peel W43 F43. pose proof pg_wf45 as W45. peel W45 F45. pose proof pg_wf47 as W47. peel W47 F47.
  pose proof pgx_rfx as X1. peel X1 X1b. pose proof pgx_prv as X2. peel X2 X2b. pose proof pgx_nxt as X3. peel X3 X3b.
  pose proof pgx_p2d as X4. peel X4 X4b. pose proof pgx_out as X5. peel X5 X5b. pose proof pgx_pts as X6. peel X6 X6b.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)) E_pg rho tp).
  { intros w Hw. unfold E_pg, X_sub. cbn [app].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xOUT :: xP2D :: xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDrp (kb 4 pKrp) _ _ rho tp w X6 X6b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_pts rho VA V3 VK HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xP2D :: xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDtr (kb 4 pKtr) _ _ rho tp w X5 X5b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_out rho VA VT3 VKT HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X4 X4b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_p2d rho VA VN HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xPRV :: xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X3 X3b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_nxt rho VA VD VN HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X2 X2b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_prv rho VA VD VN HB8)|].
    apply (publish_sub_imp _ E_pg4 pDts (kb 1 pKts) _ _ rho tp w X1 X1b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_rfx rho VA VD VN HB8)|].
    rewrite <- E_pg4_eq2. apply (reshape_gen _ E_pg3b 47 O_rfx O_rfx' rho tp w pg_o47 eq_refl eq_refl eq_refl W47);
      [intros HF; destruct (pg_vals rho _ HF F47) as (VA & VD & _); exact (rfx_eqs_f rho VA VD)|].
    rewrite <- E_pg3b_eq. apply (reshape_gen _ E_pg3a 45 O_prv O_prv' rho tp w pg_o45 eq_refl eq_refl eq_refl W45);
      [intros HF; destruct (pg_vals rho _ HF F45) as (VA & VD & _); exact (prv_eqs_f rho VA VD)|].
    rewrite <- E_pg3a_eq. apply (reshape_gen _ E_pg3 43 O_nxt O_nxt' rho tp w pg_o43 eq_refl eq_refl eq_refl W43);
      [intros HF; destruct (pg_vals rho _ HF F43) as (VA & VD & _); exact (nxt_eqs_f rho VA VD)|].
    apply (SPA_axforms segs _ xf_pg2 rho E_pg2 E_pg3 tp w E_pg3_eq). apply (SPA_axforms segs _ xf_pg1 rho E_pg1 E_pg2 tp w E_pg2_eq).
    apply (facts_imp _ E_pg0r E_pg1 AR.ts_facts rho tp w E_pg1_eq2 pg_xff); [|exact Hw].
    intros tr md _ HF1. pose proof pg_tsF as TF. peel TF TN. exact (AR.ts_facts_ok rho (triA_vals rho _ HF1 TF) (holds_mem _ _ _ HF1 TN)). }

  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)) E_pgF rho tp).
  { intros w Hw. apply (facts_imp _ E_pgS E_pgF F_pgC rho tp w E_pgF_eq pgF_xff); [|exact (SPA_axforms segs _ [AXSplit 5 (SLit 16)] rho E_pg E_pgS tp w E_pgS_eq Hw)].
    intros tr md _ HF1. pose proof pgF_site as CS. peel CS CE. exact (pg_F_ok rho _ HF1 CS CE). }

  pose proof (pg_chkF XGL) as C. rewrite pg_call_chkF_unf in C.
  peel C HP0F. peel C Hs18. peel C Hs17. peel C Hs16. peel C Hs15. peel C Hs14. peel C Hs13. peel C Hs12. peel C HX. peel C HR. peel C HB. peel C Hpd. peel C Hwp. peel C Hbb. peel C Hnb. peel C Hnp. peel C Hdom. peel C Hta. peel C Hchk. rename C into HXk.
  rewrite <- (app_nil_r (nd_tv ndTS)). apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX PGP.P0_pg PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_pgF PGC.nd0 PD_pgF NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CPGF eq_refl
           E_pgF s_pg R_pgF Xk_pg rho tp (nd_tv ndTS) [] fr_hf (nd_bd ndTS) (nd_bd ndTS) ANone _ HXk R_pgF_eq Hchk Hta Hdom Hnp Hnb Hbb eq_refl eq_refl).
  - cbn [nd_bd PGC.nd0 bd_subst map app]. apply payA_same. exact Hwp.
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK'. rewrite app_nil_r in HN, HD, HZ.
    exact (HIN_pg rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK' HBf HFF HN HD HZ HFR).
  - pose proof T_pg0_chk as TC. peel TC TCis. peel TC TCib. peel TC TCos. rename TC into TCob.
    intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_pgF In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am PGC.nd0 import_tv bd_subst map app am_subst]; rewrite app_nil_r.
    +
      pose proof pgi_wf8 as W8. peel W8 Fw8. pose proof pgi_wf9 as W9. peel W9 Fw9. pose proof pgi_wf10 as W10. peel W10 Fw10.
      eapply TR_pre; [|apply (REENTER T_pgiR ndTS (50, z0) rho'); [innth 45 | rewrite !emeas_z0; lia]].
      intros w Hw. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
      rewrite <- T_pgiR_eq2. apply (reopenS_imp T_pgiR1 XT (nd_tv ndTS) _ 20 23 rho' tp' w (pgi_ro2 XGL)).
      rewrite <- T_pgiR1_eq. apply (reopen_imp T_pgi XT (nd_tv ndTS) _ 6 15 rho' tp' w (pgi_ro1 XGL)).
      apply (subX_imp _ T_pgi4 T_pgi XT6 rho' tp' w T_pgi_eq2 pgi_xsub). apply (SPA_axforms segs _ xf_pgb2 rho' T_pgi3 T_pgi4 tp' w T_pgi4_eq).
      rewrite <- T_pgi3_eq2. apply (SPA_arr_merge segs _ rho' T_pgi2 34 (ax_S T_pgi3) tp' w T_pgi3_am). apply (SPA_axforms segs _ xf_pgb1 rho' T_pgi1 T_pgi2 tp' w T_pgi2_eq).
      rewrite <- T_pgi1_c.
      rewrite <- T_pgic_eq2. apply (reshape_gen _ T_pgib 10 O_rfx1 O_rfx0 rho' tp' w pgi_o10 eq_refl eq_refl eq_refl W10);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw10) as (VA & VD & _); pose proof (rfx_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgib_eq. apply (reshape_gen _ T_pgia 9 O_prv1 O_prv0 rho' tp' w pgi_o9 eq_refl eq_refl eq_refl W9);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw9) as (VA & VD & _); pose proof (prv_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgia_eq. apply (reshape_gen _ T_pgi0 8 O_nxt1 O_nxt0 rho' tp' w pgi_o8 eq_refl eq_refl eq_refl W8);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw8) as (VA & VD & _); pose proof (nxt_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgi0_drop. apply (SPA_refacts segs _ rho' T_pgi0F _ tp' w); [rewrite <- T_pgi0F_ta; exact Hw | exact TCib | intros HF3; exact (facts_sub_holds rho' _ _ TCis HF3)].
    +
      pose proof pgo_wf8 as W8. peel W8 Fw8. pose proof pgo_wf9 as W9. peel W9 Fw9. pose proof pgo_wf10 as W10. peel W10 Fw10.
      eapply TR_pre; [|apply (REENTER T_pgoR ndTS (50, z0) rho'); [innth 44 | rewrite !emeas_z0; lia]].
      intros w Hw. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
      rewrite <- T_pgoR_eq2. apply (reopenS_imp T_pgoR1 XT (nd_tv ndTS) _ 20 23 rho' tp' w (pgo_ro2 XGL)).
      rewrite <- T_pgoR1_eq. apply (reopen_imp T_pgo XT (nd_tv ndTS) _ 6 15 rho' tp' w (pgo_ro1 XGL)).
      apply (subX_imp _ T_pgo4 T_pgo XT6 rho' tp' w T_pgo_eq2 pgo_xsub). apply (SPA_axforms segs _ xf_pgb2 rho' T_pgo3 T_pgo4 tp' w T_pgo4_eq).
      rewrite <- T_pgo3_eq2. apply (SPA_arr_merge segs _ rho' T_pgo2 34 (ax_S T_pgo3) tp' w T_pgo3_am). apply (SPA_axforms segs _ xf_pgb1 rho' T_pgo1 T_pgo2 tp' w T_pgo2_eq).
      rewrite <- T_pgo1_eq2. apply (reshape_gen _ T_pgob 10 O_rfx1 O_rfx0 rho' tp' w pgo_o10 eq_refl eq_refl eq_refl W10);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw10) as (VA & VD & _); pose proof (rfx_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgob_eq. apply (reshape_gen _ T_pgoa 9 O_prv1 O_prv0 rho' tp' w pgo_o9 eq_refl eq_refl eq_refl W9);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw9) as (VA & VD & _); pose proof (prv_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgoa_eq. apply (reshape_gen _ T_pgo0 8 O_nxt1 O_nxt0 rho' tp' w pgo_o8 eq_refl eq_refl eq_refl W8);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw8) as (VA & VD & _); pose proof (nxt_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgo0_drop. apply (SPA_refacts segs _ rho' T_pgo0F _ tp' w); [rewrite <- T_pgo0F_ta; exact Hw | exact TCob | intros HF3; exact (facts_sub_holds rho' _ _ TCos HF3)].
Qed.

Lemma XH_E_g1_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S125R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS125Sa9A4S2eS0S2Z28SaaZ3bA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g1_vlF) as VB. pose proof g1_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (TR_absorb _ E_g1_1x (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 38 39 cells_g1b DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_g1_1x_eq. exact (release0_imp E_g1_0 (objs_butlast E_g1_0) 38 39 cells_g1b DUnknown _ _ rho tp tr ms md g1_rel1 g1_robjs1 Hw). }
  intros rho1 HE1. rewrite <- (emeas_eq E_g1_0 ndLL 40 (VL 59) rho rho1 HE1).
  assert (VB1 : uval rho1 pL <= uval rho1 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE1; exact VB). clear VB HE1. rename VB1 into VB.
  apply (TR_absorb _ E_g1_3 (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG 28 33 cells_g1a DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_g1_3x_eq. exact (release_imp E_g1_1x (objs_butlast E_g1_1x) 28 33 cells_g1a DUnknown [(224, 36)] _ _ rho1 tp tr ms md g1_rel2 g1_robjs2 Hw). }
  intros rho2 HE2. rewrite <- (emeas_eq E_g1_0 ndLL 40 (VL 59) rho1 rho2 HE2).
  assert (VB2 : uval rho2 pL <= uval rho2 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE2; exact VB). clear VB HE2. rename VB2 into VB. rename rho into rho00. rename rho2 into rho.
  pose proof g1_wf2 as W2. peel W2 W2f. pose proof g1_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g1 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g1c E_g1 (g_need E_g1_3) rho tp w E_g1_eq3 g1_xff);
      [intros tr md _ HF1; rewrite g1_gneed; pose proof g1_gF as GC; peel GC GV; exact (g_need_ok rho _ (SExt false 32 (SVar 481)) HF1 GC (sext_lt rho _ _ (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g1c_eq. apply (reshape_fwd _ E_g1b 35 pDco off_g1 off_g1 12 DUnknown rho tp w g1_oi eq_refl g1_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gz rho _ pDco (SVar 481) HF g1_bnd)).
    rewrite <- E_g1b_eq. apply (reshape_ffwd _ E_g1a 2 224 236 DUnknown rho tp w g1_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g1 rho E_g1_3 E_g1a tp w E_g1a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g1 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g1) R_g1 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g1 memcpy_pc (s_g E_g1) R_g1 rho tp tr ms md Hsm HM HX R_g1_eq2)
           eq_refl eq_refl R_g1_eq2 (g1_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_g1 ndLL (40, VL 58) rho'); [innth 49 |
    rewrite !VL_VM; exact (VM_meas_ag E_g1_0 T_g1 ndLL ndLL 40 pNT pL 58 59 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (SPA_axforms segs _ _ rho' T_g1v T_g1 tp' w T_g1_eq2).
  rewrite <- T_g1v_eq. apply (reshape_bwd _ T_g1u 2 pDco off_g1 off_g1 12 DUnknown rho' tp' w g1_to2 eq_refl g1_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gz rho' _ pDco (SVar 481) HF g1_tbnd)).
  rewrite <- T_g1u_eq. apply (reshape_fbwd _ T_g1t 1 224 236 DUnknown rho' tp' w g1_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_g1t_eq. exact Hw.
Qed.

Lemma XH_E_g2_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S126R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS126Sa9A4S2eS0S2Z28SaaZ39A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g2_vlF) as VB. pose proof g2_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  pose proof g2_wf2 as W2. peel W2 W2f. pose proof g2_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g2 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g2c E_g2 (g_need E_g2_0) rho tp w E_g2_eq3 g2_xff);
      [intros tr md _ HF1; rewrite g2_gneed; pose proof g2_gF as GC; peel GC GV; exact (g_need_ok rho _ (SVar 482) HF1 GC (proj1 (h_ult _ _ _) (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g2c_eq. apply (reshape_fwd _ E_g2b 35 pDco off_g2 off_g2 12 DUnknown rho tp w g2_oi eq_refl g2_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho _ pDco (SVar 482) HF g2_bnd)).
    rewrite <- E_g2b_eq. apply (reshape_ffwd _ E_g2a 2 236 248 DUnknown rho tp w g2_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g2 rho E_g2_0 E_g2a tp w E_g2a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g2 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g2) R_g2 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g2 memcpy_pc (s_g E_g2) R_g2 rho tp tr ms md Hsm HM HX R_g2_eq2)
           eq_refl eq_refl R_g2_eq2 (g2_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_g2 ndLL (40, VL 56) rho'); [innth 50 |
    rewrite !VL_VM; exact (VM_meas_ag E_g2_0 T_g2 ndLL ndLL 40 pNT pL 56 57 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (SPA_axforms segs _ _ rho' T_g2v T_g2 tp' w T_g2_eq2).
  rewrite <- T_g2v_eq. apply (reshape_bwd _ T_g2u 2 pDco off_g2 off_g2 12 DUnknown rho' tp' w g2_to2 eq_refl g2_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho' _ pDco (SVar 482) HF g2_tbnd)).
  rewrite <- T_g2u_eq. apply (reshape_fbwd _ T_g2t 1 236 248 DUnknown rho' tp' w g2_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_g2t_eq. exact Hw.
Qed.

Lemma XH_E_g3_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S127R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS127Sa9A4S2eS0S2Z28SaaZ37A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g3_vlF) as VB. pose proof g3_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  pose proof g3_wf2 as W2. peel W2 W2f. pose proof g3_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g3 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g3c E_g3 (g_need E_g3_0) rho tp w E_g3_eq3 g3_xff);
      [intros tr md _ HF1; rewrite g3_gneed; pose proof g3_gF as GC; peel GC GV; exact (g_need_ok rho _ (SVar 483) HF1 GC (proj1 (h_ult _ _ _) (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g3c_eq. apply (reshape_fwd _ E_g3b 35 pDco off_g3 off_g3 12 DUnknown rho tp w g3_oi eq_refl g3_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho _ pDco (SVar 483) HF g3_bnd)).
    rewrite <- E_g3b_eq. apply (reshape_ffwd _ E_g3a 2 248 260 DUnknown rho tp w g3_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g3 rho E_g3_0 E_g3a tp w E_g3a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g3 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g3) R_g3 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g3 memcpy_pc (s_g E_g3) R_g3 rho tp tr ms md Hsm HM HX R_g3_eq2)
           eq_refl eq_refl R_g3_eq2 (g3_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.

  apply (TR_pre (fun w => exists bL, (bL = 0 \/ bL = (224 + 36) mod 8)
                   /\ SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) (shadow_reopen_cells_stateA G3back (Xw G3back) hG 28 39 (gcs 224 36 bL)) rho' tp' w)).
  { intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) in Hw.
    apply (reopenC_imp G3back (Xw G3back) (nd_tv ndLL) _ 28 39 224 36 rho' tp' w (g3_roC XGL)). rewrite <- G3back_eq.
    apply (SPA_axforms segs _ _ rho' T_g3v T_g3w tp' w T_g3w_eq).
    rewrite <- T_g3v_eq. apply (reshape_bwd _ T_g3u 2 pDco off_g3 off_g3 12 DUnknown rho' tp' w g3_to2 eq_refl g3_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho' _ pDco (SVar 483) HF g3_tbnd)).
    rewrite <- T_g3u_eq. apply (reshape_fbwd _ T_g3t 1 248 260 DUnknown rho' tp' w g3_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
    rewrite <- T_g3t_eq. exact Hw. }
  apply TR_exw. intros bL. apply (TR_pureP _ (bL = 0 \/ bL = (224 + 36) mod 8)); [intros w [HbL _]; exact HbL|]. intros HbL.
  assert (MS : 0 <= emeasA (T_g3_0, ndLL, (40, VL 54)) rho' < emeasA (E_g3_0, ndLL, (40, VL 55)) rho).
  { rewrite !VL_VM. exact (VM_meas_ag E_g3_0 T_g3_0 ndLL ndLL 40 pNT pL 54 55 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia)). }
  change (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) with (JAv ndLL).
  destruct HbL as [-> | ->].
  - eapply TR_pre; [intros w [_ Hw]; rewrite T_g3_0_eq in Hw; exact Hw|]. apply (REENTER T_g3_0 ndLL (40, VL 54) rho'); [innth 68 | exact MS].
  - eapply TR_pre; [intros w [_ Hw]; change ((224 + 36) mod 8) with 4 in Hw; rewrite T_g3_4_eq in Hw; exact Hw|].
    apply (REENTER T_g3_4 ndLL (40, VL 54) rho'); [innth 51 | exact MS].
Qed.

Lemma XH_E_mi4_w : ltac2:(tb__ "0|4|
S3dS2dS11A1S26S30S1a5R2Sd9R2A1Z1cM0Z27M1R1SdS1b3S61Sa9A1S62Sa9A1A9S31A3S26S2dS5A1SeS3eR3A1A1S36S5Sd9R3A1S32S5Se4S99G0G1R2SdA5S34S5A1A3A3A3S26S3dS171S1b2R4A1S3fS1b5A1M2A2S1b5A3S26S30S176G2S3fS1b2R5A1A1A2S31A3S26S30S131S9S3eR6A1A1A1S31A3S3S2dS7aQ40A1A1M3G3VTR;S76S5bVJAv;Sa9A1RaR3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cRaSa9A4S2eS0S2Z28SaaZ35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;F_;F_;F_;F_;F_;Fcells;FE0;").
Proof.
  intros E0 cells w_rel w_robjs w_eq w_incl w_vlF rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 w_vlF) as VB.
  pose proof mi4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  apply (TR_absorb _ E_mi4_1 ndLL rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 28 39 cells DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    apply (subX_imp _ (E_mi4_1w E0) E_mi4_1 (ax_X E_mi4_1) _ tp _ w_eq w_incl). unfold E_mi4_1w.
    change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) in Hw |- *.
    exact (releaseP_imp E0 (objs_butlast E0) 28 39 cells DUnknown L_win _ _ rho tp tr ms md w_rel w_robjs Hw). }
  intros rho1 HE1.
  rewrite <- (emeas_eq E0 ndLL 40 (VL 53) rho rho1 HE1).
  assert (VB1 : uval rho1 pL <= uval rho1 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE1; exact VB). clear VB HE1. rename VB1 into VB.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) fr_hf (nd_bd ndLL) ANone)) E_mi4 rho1 tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mi4 rho1 tp w mi4_tvp).
    apply (xff_imp _ E_mi4_1 E_mi41x E_mi4 (xf_vr 15 496) (vr_need 12 (SAlu ALU_ADD (cMI pL) (SLit 3)) (NMI pA)) rho1 tp w E_mi41x_eq E_mi4_eq2 mi4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_mi4_ok rho1 _ HF1 mi4_needF). }
  apply (X_VR E_mi4 kept_mi4 lDmi lKmi 12 496 (nd_bd ndLL) brest_mi4 s_mi4 R_mi4 (XkeepF lDmi (ax_X E_mi4_1)) rho1 tp _ T_mi4k0 T_mi4f0 T_mi4g0 (SVar 679) (SVar 680) bdK_mi4 bdG_mi4
           (mi4_chk XGL) R_mi4_eq T_mi4k0_ta mi4_iK mi4_bK T_mi4f0_ta mi4_iF T_mi4g0_ta mi4_iG mi4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi4 ndL4a (40, VL 52) (rho_sub rho' s_mi4k)); [innth 52 | rewrite !VL_VM; exact (VM_meas_sub E0 JR_mi4 ndLL ndL4a 40 pNT pL 52 53 rho1 rho' s_mi4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mi4k JR_mi4 s_mi4k (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) tv2_mi4k (bdK_mi4 ++ brest_mi4) bd2_mi4k _ _ rho' tp' w mi4k_land mi4k_bd).
    apply (xff_imp _ T_mi4k0 T_mi4k1 T_mi4k (xf_backV 14 28 496) [SPUle (SLit IMG_HI) lDmi] rho' tp' w T_mi4k1_ap T_mi4k_eq2 mi4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cMI pL) 3 lKmi HF1 ltac:(lia) mi4k_live in live_holds _ rho' tp' tr md lDmi 12 lKmi HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mi4 ndL4af (20, z0) (rho_sub rho' s_mi4f)); [innth 53 | rewrite emeas_z0; pose proof (emeas_lb E0 ndLL 40 (VL 53) rho1 ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_mi4f (XnoLoc T_mi4f) hG 38 39) (XnoLoc T_mi4f) hG 28 33) JF_mi4 s_mi4f (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) tv2_mi4f (firstn 1 brest_mi4) (firstn 1 brest_mi4) _ _ rho' tp' w mi4f_land mi4f_bd).
    apply (drop_imp _ _ fr_hf brest_mi4 1 rho' tp' w mi4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_mi4f (XnoLoc T_mi4f) hG 38 39) (XnoLoc T_mi4f) (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) _ 28 33 rho' tp' w (mi4f_ro1 XGL)).
    apply (reopen_imp T_mi4f (XnoLoc T_mi4f) (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) _ 38 39 rho' tp' w (mi4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 14 28 496) rho' T_mi4f0 T_mi4f tp' w T_mi4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi4 ndL4a (40, VL 52) (rho_sub rho' s_mi4g)); [innth 52 | rewrite !VL_VM; exact (VM_meas_sub E0 JR_mi4 ndLL ndL4a 40 pNT pL 52 53 rho1 rho' s_mi4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mi4g JR_mi4 s_mi4g (kept_mi4 ++ [(SVar 679, (kb 12 (SVar 680)))]) tv2_mi4g (bdG_mi4 ++ brest_mi4) bd2_mi4g _ _ rho' tp' w mi4g_land mi4g_bd).
    exact (SPA_axforms segs _ (xf_backV 14 28 496) rho' T_mi4g0 T_mi4g tp' w T_mi4g_ap Hw).
Qed.

Lemma XH_E_mi4_0_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S1b0R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1b0Sa9A4S2eS0S2Z28SaaZ35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. exact (XH_E_mi4_w E_mi4_0_0 cells_w0 w0_rel w0_robjs w0_eq w0_incl w0_vlF). Qed.
Lemma XH_E_mi4_0_4 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sa9A1S1b1R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1b1Sa9A4S2eS0S2Z28SaaZ35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. exact (XH_E_mi4_w E_mi4_0_4 cells_w4 w4_rel w4_robjs w4_eq w4_incl w4_vlF). Qed.

Lemma XH_E_fv4_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb2A1S1b4R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1b4Sb2A4S2eS0S2Z28SaaZeA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 fv4_vlF) as VB.
  pose proof fv4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4a) with (JAv (NDA (nd_tv ndL4a) fr_hf (nd_bd ndL4a) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) fr_hf (nd_bd ndL4a) ANone)) E_fv4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_fv4 rho tp w fv4_tvp).
    apply (xff_imp _ E_fv4_0 E_fv41x E_fv4 (xf_vr 16 528) (vr_need 4 (SAlu ALU_ADD (cFV pL) (SLit 1)) (NFV pA)) rho tp w E_fv41x_eq E_fv4_eq2 fv4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ fv_c fv_n HF1 fv4_needF). }
  apply (X_VR E_fv4 kept_fv4 lDfv lKfv 4 528 (nd_bd ndL4a) brest_fv4 s_fv4 R_fv4 (XkeepF lDfv (ax_X E_fv4_0)) rho tp _ T_fv4k0 T_fv4f0 T_fv4g0 (SVar 564) (SVar 565) bdK_fv4 bdG_fv4
           (fv4_chk XGL) R_fv4_eq T_fv4k0_ta fv4_iK fv4_bK T_fv4f0_ta fv4_iF T_fv4g0_ta fv4_iG fv4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv4 ndL4b (40, VL 13) (rho_sub rho' s_fv4k)); [innth 55 | rewrite !VL_VM; exact (VM_meas_sub E_fv4_0 JR_fv4 ndL4a ndL4b 40 pNT pL 13 14 rho rho' s_fv4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_fv4k JR_fv4 s_fv4k (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) tv2_fv4k (bdK_fv4 ++ brest_fv4) bd2_fv4k _ _ rho' tp' w fv4k_land fv4k_bd).
    apply (xff_imp _ T_fv4k0 T_fv4k1 T_fv4k (xf_backV 15 29 528) [SPUle (SLit IMG_HI) lDfv] rho' tp' w T_fv4k1_ap T_fv4k_eq2 fv4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cFV pL) 1 lKfv HF1 ltac:(lia) fv4k_live in live_holds _ rho' tp' tr md lDfv 4 lKfv HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_fv4 ndL4bf (20, z0) (rho_sub rho' s_fv4f)); [innth 56 | rewrite emeas_z0; pose proof (emeas_lb E_fv4_0 ndL4a 40 (VL 14) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_fv4f (XnoLoc T_fv4f) hG 38 39) (XnoLoc T_fv4f) hG 28 33) JF_fv4 s_fv4f (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) tv2_fv4f (firstn 1 brest_fv4) (firstn 1 brest_fv4) _ _ rho' tp' w fv4f_land fv4f_bd).
    apply (drop_imp _ _ fr_hf brest_fv4 1 rho' tp' w fv4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_fv4f (XnoLoc T_fv4f) hG 38 39) (XnoLoc T_fv4f) (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) _ 28 33 rho' tp' w (fv4f_ro1 XGL)).
    apply (reopen_imp T_fv4f (XnoLoc T_fv4f) (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) _ 38 39 rho' tp' w (fv4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fv4f0 T_fv4f tp' w T_fv4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv4 ndL4b (40, VL 13) (rho_sub rho' s_fv4g)); [innth 55 | rewrite !VL_VM; exact (VM_meas_sub E_fv4_0 JR_fv4 ndL4a ndL4b 40 pNT pL 13 14 rho rho' s_fv4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_fv4g JR_fv4 s_fv4g (kept_fv4 ++ [(SVar 564, (kb 4 (SVar 565)))]) tv2_fv4g (bdG_fv4 ++ brest_fv4) bd2_fv4g _ _ rho' tp' w fv4g_land fv4g_bd).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fv4g0 T_fv4g tp' w T_fv4g_ap Hw).
Qed.

Lemma XH_E_mm4_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb3A1S1b6R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1b6Sb3A4S2eS0S2Z28SaaZaA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 mm4_vlF) as VB.
  pose proof mm4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4b) with (JAv (NDA (nd_tv ndL4b) fr_hf (nd_bd ndL4b) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) fr_hf (nd_bd ndL4b) ANone)) E_mm4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mm4 rho tp w mm4_tvp).
    apply (xff_imp _ E_mm4_0 E_mm41x E_mm4 (xf_vr 17 560) (vr_need 4 (SAlu ALU_ADD (cMM pL) (SLit 1)) (NMM pA)) rho tp w E_mm41x_eq E_mm4_eq2 mm4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ mm_c mm_n HF1 mm4_needF). }
  apply (X_VR E_mm4 kept_mm4 lDmm lKmm 4 560 (nd_bd ndL4b) brest_mm4 s_mm4 R_mm4 (XkeepF lDmm (ax_X E_mm4_0)) rho tp _ T_mm4k0 T_mm4f0 T_mm4g0 (SVar 788) (SVar 789) bdK_mm4 bdG_mm4
           (mm4_chk XGL) R_mm4_eq T_mm4k0_ta mm4_iK mm4_bK T_mm4f0_ta mm4_iF T_mm4g0_ta mm4_iG mm4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm4 ndL4c (40, VL 9) (rho_sub rho' s_mm4k)); [innth 58 | rewrite !VL_VM; exact (VM_meas_sub E_mm4_0 JR_mm4 ndL4b ndL4c 40 pNT pL 9 10 rho rho' s_mm4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mm4k JR_mm4 s_mm4k (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) tv2_mm4k (bdK_mm4 ++ brest_mm4) bd2_mm4k _ _ rho' tp' w mm4k_land mm4k_bd).
    apply (xff_imp _ T_mm4k0 T_mm4k1 T_mm4k (xf_backV 16 30 560) [SPUle (SLit IMG_HI) lDmm] rho' tp' w T_mm4k1_ap T_mm4k_eq2 mm4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cMM pL) 1 lKmm HF1 ltac:(lia) mm4k_live in live_holds _ rho' tp' tr md lDmm 4 lKmm HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mm4 ndL4cf (20, z0) (rho_sub rho' s_mm4f)); [innth 59 | rewrite emeas_z0; pose proof (emeas_lb E_mm4_0 ndL4b 40 (VL 10) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_mm4f (XnoLoc T_mm4f) hG 28 33) (XnoLoc T_mm4f) hG 38 39) JF_mm4 s_mm4f (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) tv2_mm4f (firstn 1 brest_mm4) (firstn 1 brest_mm4) _ _ rho' tp' w mm4f_land mm4f_bd).
    apply (drop_imp _ _ fr_hf brest_mm4 1 rho' tp' w mm4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_mm4f (XnoLoc T_mm4f) hG 28 33) (XnoLoc T_mm4f) (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) _ 38 39 rho' tp' w (mm4f_ro1 XGL)).
    apply (reopen_imp T_mm4f (XnoLoc T_mm4f) (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) _ 28 33 rho' tp' w (mm4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mm4f0 T_mm4f tp' w T_mm4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm4 ndL4c (40, VL 9) (rho_sub rho' s_mm4g)); [innth 58 | rewrite !VL_VM; exact (VM_meas_sub E_mm4_0 JR_mm4 ndL4b ndL4c 40 pNT pL 9 10 rho rho' s_mm4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mm4g JR_mm4 s_mm4g (kept_mm4 ++ [(SVar 788, (kb 4 (SVar 789)))]) tv2_mm4g (bdG_mm4 ++ brest_mm4) bd2_mm4g _ _ rho' tp' w mm4g_land mm4g_bd).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mm4g0 T_mm4g tp' w T_mm4g_ap Hw).
Qed.

Lemma XH_E_sg4_0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;Sb4A1S1b7R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS1b7Sb4A4S2eS0S2Z28SaaZ8A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 sg4_vlF) as VB.
  pose proof sg4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4c) with (JAv (NDA (nd_tv ndL4c) fr_hf (nd_bd ndL4c) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) fr_hf (nd_bd ndL4c) ANone)) E_sg4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_sg4 rho tp w sg4_tvp).
    apply (xff_imp _ E_sg4_0 E_sg41x E_sg4 (xf_vr 18 592) (vr_need 4 (SAlu ALU_ADD (cSG pL) (SLit 1)) (NSG pA)) rho tp w E_sg41x_eq E_sg4_eq2 sg4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ sg_c sg_n HF1 sg4_needF). }
  apply (X_VR E_sg4 kept_sg4 lDsg lKsg 4 592 (nd_bd ndL4c) brest_sg4 s_sg4 R_sg4 (XkeepF lDsg (ax_X E_sg4_0)) rho tp _ T_sg4k0 T_sg4f0 T_sg4g0 (SVar 656) (SVar 657) bdK_sg4 bdG_sg4
           (sg4_chk XGL) R_sg4_eq T_sg4k0_ta sg4_iK sg4_bK T_sg4f0_ta sg4_iF T_sg4g0_ta sg4_iG sg4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg4 ndL4d (40, VL 7) (rho_sub rho' s_sg4k)); [innth 60 | rewrite !VL_VM; exact (VM_meas_sub E_sg4_0 JR_sg4 ndL4c ndL4d 40 pNT pL 7 8 rho rho' s_sg4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4k (XnoLoc T_sg4k) hG 28 33) (XnoLoc T_sg4k) hG 38 39) JR_sg4 s_sg4k (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) tv2_sg4k (bdK_sg4 ++ brest_sg4) bd2_sg4k _ _ rho' tp' w sg4k_land sg4k_bd).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4k (XnoLoc T_sg4k) hG 28 33) (XnoLoc T_sg4k) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 38 39 rho' tp' w (sg4k_ro1 XGL)).
    apply (reopen_imp T_sg4k (XnoLoc T_sg4k) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 28 33 rho' tp' w (sg4k_ro0 XGL)).
    apply (xff_imp _ T_sg4k0 T_sg4k1 T_sg4k (xf_backV 17 31 592) [SPUle (SLit IMG_HI) lDsg] rho' tp' w T_sg4k1_ap T_sg4k_eq2 sg4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cSG pL) 1 lKsg HF1 ltac:(lia) sg4k_live in live_holds _ rho' tp' tr md lDsg 4 lKsg HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_sg4 ndL4df (20, z0) (rho_sub rho' s_sg4f)); [innth 61 | rewrite emeas_z0; pose proof (emeas_lb E_sg4_0 ndL4c 40 (VL 8) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4f (XnoLoc T_sg4f) hG 28 33) (XnoLoc T_sg4f) hG 38 39) JF_sg4 s_sg4f (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) tv2_sg4f (firstn 1 brest_sg4) (firstn 1 brest_sg4) _ _ rho' tp' w sg4f_land sg4f_bd).
    apply (drop_imp _ _ fr_hf brest_sg4 1 rho' tp' w sg4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4f (XnoLoc T_sg4f) hG 28 33) (XnoLoc T_sg4f) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 38 39 rho' tp' w (sg4f_ro1 XGL)).
    apply (reopen_imp T_sg4f (XnoLoc T_sg4f) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 28 33 rho' tp' w (sg4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sg4f0 T_sg4f tp' w T_sg4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg4 ndL4d (40, VL 7) (rho_sub rho' s_sg4g)); [innth 60 | rewrite !VL_VM; exact (VM_meas_sub E_sg4_0 JR_sg4 ndL4c ndL4d 40 pNT pL 7 8 rho rho' s_sg4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4g (XnoLoc T_sg4g) hG 28 33) (XnoLoc T_sg4g) hG 38 39) JR_sg4 s_sg4g (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) tv2_sg4g (bdG_sg4 ++ brest_sg4) bd2_sg4g _ _ rho' tp' w sg4g_land sg4g_bd).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4g (XnoLoc T_sg4g) hG 28 33) (XnoLoc T_sg4g) (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 38 39 rho' tp' w (sg4g_ro1 XGL)).
    apply (reopen_imp T_sg4g (XnoLoc T_sg4g) (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 28 33 rho' tp' w (sg4g_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sg4g0 T_sg4g tp' w T_sg4g_ap Hw).
Qed.

Lemma XH_E_f5o0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S106A1S191R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS191S106A4S2eS0S2ZdSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndEo) with (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)) E_f5o rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXUnbase (ilast E_f5o1) SHB] rho E_f5o1 E_f5o tp w E_f5o_eq2). rewrite <- E_f5o1_eq.
    exact (reopen_imp E_f5o0 (XR E_f5o0) (nd_tv ndEo) _ 0 64 rho tp w (f5o_ro XGL) Hw). }
  apply (X_purecT0 Pre_f5 [L_f5] E_f5o (nd_tv ndEo) (nd_bd ndEo) s_f5o R_f5o rho tp _ (fun Ai rho1 tp1 => CF5 Ai rho1 tp1) eq_refl eq_refl R_f5o_eq (f5o_chk XGL)).
  intros L0 rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_f5o ndEo (12, z0) rho'); [innth 65 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndEo) with (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)). rewrite <- T_f5o_eq2.
  apply (carve_imp T_f5o1 objs_f5o1 sh_f5o1 0 64 (nd_tv ndEo) _ rho' tp' w T_f5o1_objs sh_f5o1_eq ltac:(lia) ltac:(lia) (f5o_carve XGL)).
  apply (SPA_axforms segs _ _ rho' T_f5o0 T_f5o1 tp' w T_f5o1_eq). unfold Pre_f5, L_f5 in *. rewrite <- T_f5o0_eq. exact Hw.
Qed.
Lemma XH_E_f5f0 : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0G0VTR;S76S5bVJAv;S104A1S190R3R2A5VFAM;S5dS2eS2fS3dS5cA2S2fS0S2A2S2eS3dS5cS190S104A4S2eS0S2ZdSa8A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndEf) with (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)) E_f5f rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXUnbase (ilast E_f5f1) SHB] rho E_f5f1 E_f5f tp w E_f5f_eq2). rewrite <- E_f5f1_eq.
    exact (reopen_imp E_f5f0 (XR E_f5f0) (nd_tv ndEf) _ 0 64 rho tp w (f5f_ro XGL) Hw). }
  apply (X_purecT0 Pre_f5 [L_f5] E_f5f (nd_tv ndEf) (nd_bd ndEf) s_f5f R_f5f rho tp _ (fun Ai rho1 tp1 => CF5 Ai rho1 tp1) eq_refl eq_refl R_f5f_eq (f5f_chk XGL)).
  intros L0 rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_f5f ndEf (12, z0) rho'); [innth 64 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndEf) with (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)). rewrite <- T_f5f_eq2.
  apply (carve_imp T_f5f1 objs_f5f1 sh_f5f1 0 64 (nd_tv ndEf) _ rho' tp' w T_f5f1_objs sh_f5f1_eq ltac:(lia) ltac:(lia) (f5f_carve XGL)).
  apply (SPA_axforms segs _ _ rho' T_f5f0 T_f5f1 tp' w T_f5f1_eq). unfold Pre_f5, L_f5 in *. rewrite <- T_f5f0_eq. exact Hw.
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|5|
S3dS3dS3dS2dS2fS2S2A2A1S2dS49A1S3S2dS7aQ40A1A1M0S0G0S0S26S37S3dA1S18bRaS32S18aS18cS19dA1S34S18aA1A3A2S38S3dR9A2A3S26S3dS45RaS1c8S3eRaA1M1S7eS5S192SeG1A1A3A2A2R9A3S26S30S33S33SeaPa0PaaS99Z3S7fS5S192SeS3eRbA1M2A1A3A5S137S9G2A1A1A2S64SaG2A1S5fR9S80R8S5eA4A2A2S31A3SbbS2fS2fS3dS5cA2M3S2fS0S2A2M4A2S2eG3G4S2eS3dS5cRbS5fRaS34S2fS2fS2S0A2S2A2A1R9S5eA4A4S2eS0S2R4Sa8A4A4S169A3S53Z0R5A2S53S57S54R6Z1A2S55Z2Z40A2A2R8A2VTR;S76S5bVJAv;S5fRdS80RcS5eA4A1R10RbRaA5VFAM;R9R8A2A2F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC CK HinC Hrk Hb. peel CK Hnb. peel CK Hfe. rename CK into HR.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn NREL (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn NREL (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn NREL (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hf).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG X1 (firstn NREL (ss_objs (ax_S X1))) (skipn NREL (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rlo : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0S53S57ZbS55Z2Z40A2A2R2A2VTR;S76S5bVJAv;S106A1S19cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. unfold ndEo. apply (X_X_rl X_rlo X_rlo1 C_rlo tvQ _ rho tp b tp0 10 X_rlo1_eq C_rlo_eq2 rlo_chk); [innth 67 | lia | lia]. Qed.
Lemma XH_X_rlf : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0S53S57ZbS55Z2Z40A2A2R2A2VTR;S76S5bVJAv;S104A1S19bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. unfold ndEf. apply (X_X_rl X_rlf X_rlf1 C_rlf tvQ _ rho tp b tp0 10 X_rlf1_eq C_rlf_eq2 rlf_chk); [innth 66 | lia | lia]. Qed.

Definition conullF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S33S33S33SbaS4SbS1cS18Sa4S88S6Z0A1A3A1A1VF;A3SbaS4SbS18Sa6S6Z2A1S81A3A1VF;A3A2SbaS4SbScS81S89A2A1VF;A3A2SbaS4SbScS89S6SccA1A2A1VF;A3A2").
Definition avnullF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S33S33S33S33SbaS4SbS1cS18Sa4S9fS6Z0A1A3A1A1VF;A3SbaS4SbS1aS19S31Q20S24P1e1A1A3S9cA2A1VF;A3A2SbaS4SbScS9cS6ScfA1A2A1VF;A3A2SbaS4SbScS98Z3S9cA2S9dA2A1VF;A3A2SbaS4SbScS9dS6SccA1A2A1VF;A3A2").
Lemma conull_chk : ltac2:(tb__ "0|0|
S26S30S1c3S9S3eS10cA1A1A1S31A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma avnull_chk : ltac2:(tb__ "0|0|
S26S30S1c2S9S3eSfcA1A1A1S31A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma null_contra : ltac2:(tb__ "0|0|
S3S2S7R2S1cS18Sa4R1S6Z0A1A3A1A2S7R3ScS6S154A1R2A2A2S2bF_;F_;Fd;Frho;").
Proof.
  intros rho d H0 H1. rewrite h_ule in H1. rewrite uval_lit in H1 by (unfold IMG_HI; lia).
  apply H0. cbn [holds eval branch_taken]. unfold bv_eqb. rewrite lit_unsigned by lia.
  apply negb_true_iff. apply Z.eqb_neq. change (bv_unsigned (eval rho d)) with (uval rho d). unfold IMG_HI in H1. lia.
Qed.
Lemma XH_X_conull : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0VTR;S76S5bVJAv;S105A1S10cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply (TR_pureP _ False); [|intros []].
  intros w [_ HJ].
  pose proof conull_chk as C. unfold conullF in C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  apply (null_contra rho pDco F1). apply (live_holds ndXA rho tp _ _ pDco 12 pKco HJ); [cbn; tauto | lia | unfold B32; lia | lia].
Qed.
Lemma XH_X_avnull : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0VTR;S76S5bVJAv;SaeA1SfcR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply (TR_pureP _ False); [|intros []].
  intros w [_ HJ].
  pose proof avnull_chk as C. unfold avnullF in C. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3, F4, F5. rewrite h_ult in F2. unfold B32 in F5. unfold two40, RA.two40 in F3. rewrite uval_lit in F3 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho (SExt true 32 (SVar 481))) as Rv.
  rewrite uval_kb in F4 by lia.
  apply (null_contra rho av_d F1). apply (live_holds ndRP rho tp _ _ av_d 4 av_k HJ); [cbn; tauto | lia | unfold B32; lia | lia].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0VTR;S76S5bVJAv;S198A1S194R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S3S2dS7aQ40A1A1M0S0G0VTR;S76S5bVJAv;S197A1S193R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S3dS5cS2fS0S2A2M0S3S2dS7aQ40A1A1M1G1SbbS2fS2fS3dS5cA2M2G0A2S2eG2G0S2eS3dS5cR6R5A4R4A4S16aA3VTR;S76S5bVJAv;R6A1R7R4R3A5VFAM;S5dS2eG2G0S2eS3dS5cR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsF2] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_co.
  - apply XH_E_pc.
  - apply XH_E_da.
  - apply XH_E_dg. rewrite emeas_z0. lia.
  - apply XH_E_mi0.
  - apply XH_E_fv0.
  - apply XH_E_mm0.
  - apply XH_E_sg0.
  - apply XH_XEf42.
  - apply XH_XEo42.
  - apply XH_E_trg0.
  - apply XH_E_trb0.
  - apply XH_E_tdg0.
  - apply XH_E_rp0.
  - apply XH_E_ts0.
  - apply XH_E_pg0.
  - apply XH_E_wdg0.
  - apply XH_XJ.
  - apply XH_XLJ.
  - apply XH_E_g1_0.
  - apply XH_E_g2_0.
  - apply XH_E_g3_0.
  - apply XH_E_mi4_0_4.
  - apply XH_E_fv4_0.
  - apply XH_E_mm4_0.
  - apply XH_E_sg4_0.
  - apply XH_XEf6a.
  - apply XH_XEf6b.
  - apply XH_XEo6.
  - apply XH_E_f5f0.
  - apply XH_E_f5o0.
  - apply XH_X_rlf. rewrite emeas_z0. lia.
  - apply XH_X_rlo. rewrite emeas_z0. lia.
  - apply X_P_fail.
  - apply X_P_ok.
  - apply XH_E_mi4_0_0.
  - apply XH_X_conull.
  - apply XH_X_avnull.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S75S5bVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S15eS5bS158VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0SbbS0R1S32S0Z0S32S0Zf5S32S0Zf8S34S0A1A3A3A3A3S1baS5bS158VAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem handle_f_sum : ltac2:(tb__ "0|0|
S2dS7aQ40A1A1Sc1S5bVok;S76S5bS65VAInv;VCST;VXGL;VKc;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60S87AaS8bVrho0;R1A5Sc3S5bS97Vrho0;R1S122A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA FUEL_hf cutpcs_hfF NPH
                (map edropA cutsF2) (map edropA exitsF2) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertF_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsF2)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (fun P Q Q' HQ HT => @triple_conseq segs ok P P Q Q' (fun w Hw => Hw) HQ HT) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (PGP.tess_polygon_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC).
         intros xx Hxx. apply SSC. cbn in Hxx |- *. tauto.
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 3 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (SSC 245 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_bw s R Posts_bwH rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply b_warn_sumH; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NPH (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue ok (map edropA cutsF2) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_hf CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hfJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S15fS5bS158VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0SbbS0R1S32S0Z0S32S0Zf5S32S0Zf8S34S0A1A3A3A3A3S1bbS5bS158VAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem handle_f_sum_ex : ltac2:(tb__ "0|0|
S2dS7aQ40A1A1Sc0S5bS76S5bS65VAInv;VCST;VXGL;VKc;Sb8VCST;VFB;VFF;A3VFB;VFF;VBX;S60S87AaS8bVrho0;R1A5Sc3S5bS97Vrho0;R1S122A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA FUEL_hf cutpcs_hfF NPH cutsF2 exitsF2 (Q tp0) ejcertF_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue) cutsF2) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (fun P Q Q' HQ HT => @etriple_conseq segs P P Q Q' (fun w Hw => Hw) HQ HT) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (PGP.tess_polygon_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc FFc BXc HB0 rho1 ACX).
         intros xx Hxx. apply SSCX. cbn in Hxx |- *. tauto.
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 3 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros Ai rho1 tp1. apply (SSCX 245 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_bw s R Posts_bwH rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply b_warn_sumH_ex. apply (frozen_stable NPH (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue cutsF2 T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_hf CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hfJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem handle_f_ok : handle_f_stmt.
Proof.
  intros AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC tp0.
  exact (handle_f_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC tp0).
Qed.
Theorem handle_f_ok_ex : handle_f_stmt_ex.
Proof.
  intros AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX tp0.
  exact (handle_f_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX tp0).
Qed.

End Lib_handle_f_pf.

