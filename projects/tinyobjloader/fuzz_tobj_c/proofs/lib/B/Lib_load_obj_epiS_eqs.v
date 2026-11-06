(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "true"; "app"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "SVar"; "SAlu"; "SPBranch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_eqs"; "zl"; "RB"; "ndZ"; "ndK"; "cutsS1"; "cutsS2a"; "cutsS4"; "exitsS1"; "exitsS2a"; "exitsS4"; "ndZ8"; "H_ecertS1_ok"; "H_ecertS2a_ok"; "H_ecertS4_ok"; "keep_ecertS1_ok"; "keep_ecertS2a_ok"; "keep_ecertS4_ok"; "ndK8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "ndAt"; "brestAt"; "nd_rp"; "B_1"; "E_wm0"; "L_cf0"; "L_rp0"; "L_rpx"; "L_v0a"; "L_w"; "T_rp"; "T_wm"; "T_wr"; "cps_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_succ"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "nd_s0"; "Es_fs0"; "K_succ"; "L_dz"; "L_sk"; "L_sn"; "T_fz2"; "T_nop2"; "T_ok2"; "cps_s"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS4"; "nd9"; "brest8"; "nd8"; "B_8"; "B_9"; "C_9v"; "E0_8"; "E_fu0"; "L_d6f"; "L_d6y"; "L_d6z"; "L_d7"; "L_land"; "T_fu"; "Tz_8"; "cps_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "PhisS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS3"; "B_2"; "B_3"; "B_4"; "B_5"; "B_6"; "B_7"; "E0_1"; "E0_2"; "E0_3"; "E0_4"; "E0_5"; "E0_6"; "L_d1"; "Tz_1"; "Tz_2"; "Tz_3"; "Tz_4"; "Tz_5"; "Tz_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_st1"; "Tf_1"; "Tf_2"; "Tf_3"; "Tk_1"; "Tk_2"; "Tk_3"; "Ty_1"; "Ty_2"; "Ty_3"; "qHk_1"; "qHk_2"; "qHk_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_st2"; "Tf_4"; "Tf_5"; "Tf_6"; "Tk_4"; "Tk_5"; "Tk_6"; "Ty_4"; "Ty_5"; "Ty_6"; "qHk_4"; "qHk_5"; "qHk_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS_st3"; "Tf_8"; "Tk_8"; "Ty_8"; "qHk_8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiS1 Lib_load_obj_epiS2 Lib_load_obj_epiS3 Lib_load_obj_epiS_st1 Lib_load_obj_epiS_st2 Lib_load_obj_epiS4 Lib_load_obj_epiS_st3.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VF. Include Lib_vec_finalize. End VF. Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP.

Definition zl (k : Z) : sv := SLit k.
Definition RB : Z := 391.

Definition ndK (j : nat) (qh : sv) : ndesc := ltac2:(tb__ "0|0|
SbS58S57S27Vj;A1SaVqh;S5A2A4").
Definition ndZ (j : nat) : ndesc := ltac2:(tb__ "0|0|
SbS58S57S27Vj;A1SaS60S5A2A4").
Definition ndK8 : ndesc := ltac2:(tb__ "0|0|
SbS58S57S48SaS8fS5A2A4").
Definition ndZ8 : ndesc := ltac2:(tb__ "0|0|
SbS58S57S48SaS60S5A2A4").

Definition cutsS1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S90S3aA4U0M4A4S0ScSdZ18fS45A4A4S1G3S0G1G2S0G0S2S0S8S9S41S38A4G4A4S0ScSdZ18dS45A4M5A4S1G3S0G1G2S0G0S2S0S8S9S42S39A4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S40S37A4G4A4G5A4S4G3A1A3A3A3A3").
Definition exitsS1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S3bS3aA4U0M4A4S0ScSdZ18eS45A4A4S1G3S0G1G2S0G0S2S0S8S9S3fS38A4G4A4S0ScSdZ18cS45A4M5A4S1G3S0G1G2S0G0S2S0S8S9S3eS39A4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S3dS37A4G4A4G5A4S4G3A1A3A3A3A3").

Definition cutsS2a : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S3cS36A4U0M4A4S0ScSdZ18bS45A4A4S1G3S0G1G2S0G0S2S0S8S9S32S36A4G4A4S0ScSdZ18aM5S14Z14A1A4A4S1G3S0G1G2S0G0S2S0S8S9S31S36A4G4A4S0ScSdG5S14ZaA1A4A4S4G3A1A3A3A3").
Definition exitsS2a : list efnode := ltac2:(tb__ "0|7|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S2eS36A4U0M4A4S0ScSdZ18aM5S45A4M6A4S1G3S0G1G2S0G0S2S0S8S9S2fS36A4G4A4S0ScSdG5S14Z1eA1A4A4S1G3S0G1G2S0G0S2S0S8S9S2aS36A4G4A4S0ScSdG5S14Z13A1A4A4S1G3S0G1G2S0G0S2S0S8S9S2bS36A4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S2cS36A4G4A4G6A4S4G3A1A3A3A3A3A3").

Definition cutsS2b : list efnode := ltac2:(tb__ "0|1d|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S29S26U1M4A1A4U0M5A4S0ScSdS15S14Z37aA1A4A4S1G3S0G1G2S0G0S2S0S8S9S30S28A4G5A4S0ScSdS15S14Z37eA1A4A4S1G3S0G1G2S0G0S2S0S8S9S6eS16G4A1M6A4G5A4S0ScSdS15S14Z378A1A4M7A4S1G3S0G1G2S0G0S2S0S8S9S74S26U2M8A1M9A4G5A4G7A4S1G3S0G1G2S0G0S2S0S8S9S77S17G4S7dA2A4G5A4G7A4S1G3S0G1G2S0G0S2S0S8S9S7aG6A4G5A4G7A4S1G3S0G1G2S0G0S2S0S8S9S61G9A4G5A4S0ScSdS15S14Z370A1A4A4S1G3S0G1G2S0G0S2S0S8S9S6fS16G8A1MaA4G5A4S0ScSdS15S14Z36eA1A4MbA4S1G3S0G1G2S0G0S2S0S8S9S75S26U3McA1MdA4G5A4GbA4S1G3S0G1G2S0G0S2S0S8S9S78S17G8S7eA2A4G5A4GbA4S1G3S0G1G2S0G0S2S0S8S9S7bGaA4G5A4GbA4S1G3S0G1G2S0G0S2S0S8S9S62GdA4G5A4S0ScSdS15S14Z366A1A4A4S1G3S0G1G2S0G0S2S0S8S9S70S16GcA1MeA4G5A4S0ScSdS15S14Z364A1A4MfA4S1G3S0G1G2S0G0S2S0S8S9S76S26U4M10A1M11A4G5A4GfA4S1G3S0G1G2S0G0S2S0S8S9S79S17GcS7fA2A4G5A4GfA4S1G3S0G1G2S0G0S2S0S8S9S7cGeA4G5A4GfA4S1G3S0G1G2S0G0S2S0S8S9S63G11A4G5A4S0ScSdS15S14Z35cA1A4A4S1G3S0G1G2S0G0S2S0S8S9S71S16G10A1M12A4G5A4S0ScSdS15S14Z35aA1A4M13A4S1G3S0G1G2S0G0S2S0S8S9S80S26U5M14A1M15A4G5A4G13A4S1G3S0G1G2S0G0S2S0S8S9S83S17G10S89A2A4G5A4G13A4S1G3S0G1G2S0G0S2S0S8S9S86G12A4G5A4G13A4S1G3S0G1G2S0G0S2S0S8S9S64G15A4G5A4S0ScSdS15S14Z352A1A4A4S1G3S0G1G2S0G0S2S0S8S9S72S16G14A1M16A4G5A4S0ScSdS15S14Z350A1A4M17A4S1G3S0G1G2S0G0S2S0S8S9S81S26U6M18A1M19A4G5A4G17A4S1G3S0G1G2S0G0S2S0S8S9S84S17G14S8aA2A4G5A4G17A4S1G3S0G1G2S0G0S2S0S8S9S87G16A4G5A4G17A4S1G3S0G1G2S0G0S2S0S8S9S65G19A4G5A4S0ScSdS15S14Z348A1A4A4S1G3S0G1G2S0G0S2S0S8S9S73S16G18A1M1aA4G5A4S0ScSdS15S14Z346A1A4M1bA4S1G3S0G1G2S0G0S2S0S8S9S82S26U7A1M1cA4G5A4G1bA4S1G3S0G1G2S0G0S2S0S8S9S85S17G18S8bA2A4G5A4G1bA4S1G3S0G1G2S0G0S2S0S8S9S88G1aA4G5A4G1bA4S1G3S0G1G2S0G0S2S0S8S9S66G1cA4G5A4S0ScSdS15S14Z33eA1A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition exitsS2b : list efnode := ltac2:(tb__ "0|c|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S2dS28A4U0M4A4S0ScSdS15S14Z37dA1A4A4S1G3S0G1G2S0G0S2S0S8S9S67S26U1A1M5A4G4A4S0ScSdS15S14Z379A1A4M6A4S1G3S0G1G2S0G0S2S0S8S9S68S26U2A1A4G4A4S0ScSdS15S14Z36fA1A4A4S1G3S0G1G2S0G0S2S0S8S9S69S26U3A1A4G4A4S0ScSdS15S14Z365A1A4A4S1G3S0G1G2S0G0S2S0S8S9S6aS26U4A1A4G4A4S0ScSdS15S14Z35bA1A4A4S1G3S0G1G2S0G0S2S0S8S9S6bS26U5A1A4G4A4S0ScSdS15S14Z351A1A4A4S1G3S0G1G2S0G0S2S0S8S9S6cS26U6M7A1A4G4A4S0ScSdS15S14Z347A1A4A4S1G3S0G1G2S0G0S2S0S8S9S4fS26U7A1M8A4G4A4S0ScSdS15S14Z345A1A4M9A4S1G3S0G1G2S0G0S2S0S8S9S51S16G7A1MaA4G4A4G9A4S1G3S0G1G2S0G0S2S0S8S9S50GaA4G4A4G9A4S1G3S0G1G2S0G0S2S0S8S9S52G8A4G4A4S0ScSdS15S14Z33dA1A4MbA4S1G3S0G1G2S0G0S2S0S8S9S4eG8A4G4A4GbA4S1G3S0G1G2S0G0S2S0S8S9S6dG5A4G4A4G6A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition cutsS4 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S54S26U7A1A4U0M4A4S0ScSdS15S14Z33cA1A4A4S1G3S0G1G2S0G0S2S0S8S9S4aS49A4G4A4S0ScSdS15S14Z334A1A4A4S1G3S0G1G2S0G0S2S0S8S9S55S1eA4G4A4S0ScSdS15S14Z332A1A4M5A4S1G3S0G1G2S0G0S2S0S8S9S8cS47A4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S8dS25A4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S8eS1eA4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S4bS47A4G4A4S0ScSdS15S14Z32aA1A4A4S1G3S0G1G2S0G0S2S0S8S9S4cS47A4G4A4S0ScSdS15S14Z328A1A4A4S4G3A1A3A3A3A3A3A3A3A3").
Definition exitsS4 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S8S9A2M0S2A2M1S3ScSdA2M2A2M3S0G1G2S0G0S2S0S8S9S4dS49A4U0M4A4S0ScSdS15S14Z333A1A4A4S1G3S0G1G2S0G0S2S0S8S9S53S47A4G4A4S0ScSdS15S14Z325A1A4A4S4G3A1A3A3").

Definition keep_ecertS1_ok : list sprop := [].
Definition H_ecertS1_ok : list sprop := ltac2:(tb__ "0|0|
S5dS22S6S34S18S1bA3A2").
Lemma ecertS1_ok : ltac2:(tb__ "0|1|
S59S7S35S5aS46S5bU12cS43S46S44S34S34S5cS1fA1M0S18A4S44S34S34G0S1bA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertS2a_ok : list sprop := ltac2:(tb__ "0|0|
S1SeS10S11P191A1SfZ10000000000A1A2S1SeS10S11PfA1SfZ800000000000A1A2S4SeA1A3A3").
Definition H_ecertS2a_ok : list sprop := ltac2:(tb__ "0|0|
S5dS23S6S34S19S1cA3A2").
Lemma ecertS2a_ok : ltac2:(tb__ "0|1|
S59S7S35S5aS46S5bU12cS33S46S44S34S34S5cS20A1M0S19A4S44S34S34G0S1cA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertS4_ok : list sprop := ltac2:(tb__ "0|6|
S1SeS10S11P1d1A1M0SfZ7fffff800000A1M1A2S1SeS10S11PcA1SfZ800000000000A1M2A2S1SeS13S5fSfN10d0A1S12S5eS11P13A1SfZ100A1A3M3A3S1SeS13S5fG3SfN4000000000A1A3S1SeS10G0S11P1eA1M4A2S1SeS10G4G1A2S1SeS10SfZ643000A1S12S5eS11P6eA1SfZ1c0A1A3M5A2S1SeS10G5G2A2S4SeA1A3A3A3A3A3A3A3A3").
Definition H_ecertS4_ok : list sprop := ltac2:(tb__ "0|0|
S5dS24S6S34S1aS1dA3A2").
Lemma ecertS4_ok : ltac2:(tb__ "0|1|
S59S7S35S5aS46S5bU12cS56S46S44S34S34S5cS21A1M0S1aA4S44S34S34G0S1dA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
