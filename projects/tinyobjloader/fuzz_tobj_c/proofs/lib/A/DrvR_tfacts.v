(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "Some"; "pair"; "prod"; "option"; "list"; "nat"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_objs"; "sobj"; "sstate"; "sprop"; "ss_facts"; "ss_next"; "swf"; "SPUle"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "mkLeafA"; "ax_setS"; "sym_runA"; "ax_base"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXRebase"; "AXSelect"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts"; "node_okb"; "nd_R"; "N_exR"; "N_fw"; "bd_R"; "carve_st"; "carve_chk"; "bd_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts"; "nobj"; "N_fp"; "tailF_facts"; "A3_ref"; "S1_ref"; "A2_ref"; "A4_ref"; "B1_ref"; "B4_ref"; "R_xref"; "nd_X"; "A1_ref"; "B2_ref"; "B3_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "CX_ref"; "T_ref"; "x4_okb"; "U_ref"; "s_exR"; "C_ref"; "X_ref"; "V_ref"; "ex_img_okb"; "fp_u1"; "fw_u1"; "selA"; "splitA"; "CF_ov1"; "CF_sh0"; "CF_sh1"; "CF_shZ"; "CX_ov1"; "CX_sh0"; "CX_sh1"; "CX_shZ"; "C_ov1"; "C_sh0"; "C_sh1"; "C_shZ"; "E_ov1"; "E_ref"; "E_sh0"; "E_sh1"; "E_shZ"; "F_ov1"; "F_sh0"; "F_sh1"; "F_shZ"; "LV_xref"; "RF_ov1"; "RF_sh0"; "RF_sh1"; "RF_shZ"; "R_ov1"; "R_ref"; "R_sh0"; "R_sh1"; "R_shZ"; "TF_ov1"; "TF_sh0"; "TF_sh1"; "TF_shZ"; "T_ov1"; "T_sh0"; "T_sh1"; "T_shZ"; "U_ov1"; "U_sh0"; "U_sh1"; "U_shZ"; "V_ov1"; "V_sh0"; "V_sh1"; "V_shZ"; "W_ov1"; "W_sh0"; "W_sh1"; "W_shZ"; "X_ov1"; "X_sh0"; "X_sh1"; "X_shZ"; "exS_idxs"; "fp_rtc"; "fp_u2"; "fw_u2"; "ms16_at"; "sF_ov1"; "sF_sh0"; "sF_sh1"; "sF_shZ"; "s_ov1"; "s_ref"; "s_sh0"; "s_sh1"; "s_shZ"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "KU"; "BIc"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "vCap"; "PreF"; "DEEP"; "PostF"; "dropX"; "locate"; "spM"; "vTP"; "sp0"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts.TF"; "ndT"; "E1x"; "TA2"; "TA3"; "TB2"; "TS1"; "R_xx"; "TB0'"; "TB1"; "TB4"; "TA1"; "TB0"; "TB3"; "ndTk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lc_obj"; "lcarve"; "carve_okb"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "CUTS_R"; "T_after"; "optR"; "Lov1"; "Lref"; "Lsh0"; "Lsh1"; "LshZ"; "ax_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "KP_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ANone"; "NDA"; "nd_below";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "EBUF"; "P_fw"; "Posts_fw"; "Pre_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue"; "pub_lit_okb2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "P_ref"; "Pre_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "CAP0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.Lists.List"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR AxXform DrvGlueA DrvGlueB SysStepA SysA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysStepA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR_facts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition carveA (A : axst) (N : list lcarve) : axst := ltac2:(tb__ "0|0|
S1eVA;S2dS1aVA;A1VN;A2A2").

Definition N_fp : list lcarve := ltac2:(tb__ "0|b|
S4S8S8S22S22A2M0SaS8S8S22SbA2M1S22A2M2A1M3A2M4S7G0G3S7S22S22Zf20d8M5Zf20daA4S4G2S7G1S22S7S22SbG5U1M6A4Z1M7A4S4G2S7G1S22S7S22SbZf20d9G6A4G7A4S5G2A1M8A3A3A4S4G4S7G0G3S7S22S22Ze9ae8M9Ze9af8A4S4G2S7G1S22S7S22SbG9U8MaA4Zddf74A4S4G2S7G1S22S7S22SbZe9af0GaA4Zde378A4G8A3A3A4S5G4A1A3A3").
Lemma N_fp_eq : ltac2:(tb__ "0|0|
S0SaS10A1Sa4SbaS10Sb9S31A4S83A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fp_un : ltac2:(tb__ "0|0|
S0S3SbcSc6S31A2S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition A1_ref : axst := x4set (SLit TP) E_ref.
Definition A2_ref : axst := splitA 0 (SLit (-2688)) A1_ref.
Definition A3_ref : axst := carveA A2_ref N_fp.
Definition A4_ref : axst := ltac2:(tb__ "0|0|
S96S33S4S8SdSdA2S7SdSdSeZ1a7c0A1SeZ80A1A4S1cS33A1A3A2").
Definition S1_ref : axst := ltac2:(tb__ "0|0|
S49S47S30S3fA1A1S3fA2").

Definition B1_ref : axst := ltac2:(tb__ "0|0|
S96S4aU0SeN480A1S44A3S5S8SdSdA2A1A2").
Definition B2_ref : axst := ex_img B1_ref.
Definition B3_ref : axst := carveA B2_ref N_exR.
Definition B4_ref : axst := x4set (SLit TP) B3_ref.
Definition R_xref : list sobj := ltac2:(tb__ "0|1|
SbfS97S3eSa5Z0M0Z2A2S42G0S3eA2A3A1").
Lemma ref_facts : ltac2:(tb__ "0|10|
S1S0S3S28Sc1S29A2S2A3S1S0S3S40S58SeSd0A1M0A2S2A3S1S0S9S11A1M1Sb4S1aS3bA1U0M2SeNa80A1A3S6S11S1aS35A1A2A3S1S0S3S2eS35S4S8SdSdA2M3S7SdSdS9aS9bA4S5G3A1M4A3M5S31A3S2A3S1S0S3Sd1S33G5Z1a7c0Z80A4S2A3S1S0S19SdaS4S12S86Sa3Z998A2M6S5S12A1A3S36A2S43A3S1S0S3Se1S12S17S14S1aS36A1M7A1A1S4S12G6S13G7A1A3A3S2A3S1S0S3S28S43S29A2S2A3S1S0S19SbeSd5S43S8cS66Sd4A5S3fA3S1S0S9S19A1M8S24S3fS4S23S26S47S30S3fA1A1A1S5S23A1M9A3A2S6S19S34A2A3S1S0SaS10A1MaSfS1aS34A1MbA1ScS10SfS1aS41A1A1McSa4SbaS10Sb9S31A4A3A3S1S0S3ScaS14GbA1S29A2S2A3S1S0S19S1eS34Sb7GbGcA2A2S41A3S1S0G8S24S41S4S23S25G2A1S4S23S26S84S30S41A1A1A1S4S23S27G2A1G9A3A3A3A2S6S19S45A2A3S1S0S3S28S45S29A2S2A3S1S0SaS1bA1S60S4S1bS1dS44Sb6A2S5S1bA1A3A3S1S0G1Sb4S1aS44A1G2SeN480A1A3S6S11S1aS37A1A2A3S1S0S3S46S37A1S2A3S1S0S3S2eS3cG5S2aA3S2A3S1S0S3S40S3dG0A2S2A3S1S0S3ScbG4S1cS38A1A2S2A3S1S0S19S96S38G4A2S3eA3S1S0S3S28S3eS29A2S2A3S1S0S9GaA1S97S3eSa5Z0MdZ2A2MeS42GdS3eA2MfA3S6GaS39A2A3S0S3S98S3eGeGfS39S5S19A1A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition nd_X : ndesc := ltac2:(tb__ "0|0|
Sc9S5S8SdSdA2A1S5S8S8SdS22A2SdA2A1S5S91A1Sc8A4").

Section TF.

Variables (tb tl : sv) (bd : list bitem) (msg len blkB blkL : Z).
Variables (Lx Ex Cx Tx Ux Vx Wx Fx CFx TFx Xx CXx : axst) (sx sF : wsub) (Rx RF : list sobj).
Definition ndT : ndesc := ltac2:(tb__ "0|1|
Sc9S4S8SdSdA2M0S7SdSdVtb;Vtl;A4S5G0A1A3S5S8S8SdS22A2SdA2A1Vbd;Sc8A4").
Definition ndTk : ndesc := ltac2:(tb__ "0|1|
Sc9S4S8SdSdA2M0S7SdSdVtb;Vtl;A4S5G0A1A3S5S8S8SdS22A2SdA2A1ScS91Vbd;S4S91S93Z0Z1S92A3S5S91A1A3A3Sc8A4").
Definition TA1 : axst := x4set (SLit TP) Ex.
Definition TA2 : axst := splitA 0 (SLit (-2528)) TA1.
Definition TA3 : axst := carveA TA2 N_fw.
Definition TS1 : axst := ltac2:(tb__ "0|0|
S49S48S30VTx;A1A1VTx;A2").
Definition E1x : axst := ltac2:(tb__ "0|0|
Sc5S24VXx;S4S23S25Sa0SfS1aVXx;A1A1Sa1SeSd3S9dA1A1A3A1S5S23A1A3A2VXx;A2").
Definition TB0 : axst := selA (exS_idxs E1x) E1x.
Definition TB0' : axst := mergeA 0 TB0.
Definition TB1 : axst := ltac2:(tb__ "0|0|
S96S4aU0SeN430A1SadA3S5S8SdSdA2A1A2").
Definition TB2 : axst := ex_img TB1.
Definition TB3 : axst := carveA TB2 N_exR.
Definition TB4 : axst := x4set (SLit TP) TB3.
Definition R_xx : list sobj := ltac2:(tb__ "0|0|
SbfS97VCXx;Sa5Z0Z2A2S42SccVCXx;A2A3A1").

Definition tailF_facts : Prop := ltac2:(tb__ "0|20|
S1S0S3S28VLx;Sa6A2S2A3S1S0S9SaS1bA1M0A1M1S1fSb8U14M2SbdVLx;S2A5S6G0S4S1bS1dVEx;Sb6A2S5S1bA1M3A3A2A3S1S0S3S40VEx;SeSd0A1M4A2S2A3S1S0S9S11A1M5Sb4S1aSb0A1U0M6SeN9e0A1A3S6S11S1aSa8A1M7A2A3S1S0S3S15S2dG7S2bA2A1S2A3S1S0S3SbbS13G7A1SfG7A1S1cSa8A1Sc6Sc7S4S8SdSdA2M8S7SdSdVtb;Vtl;A4M9S5G8A1MaA3MbS2bA7S2A3S1S0SdS20Sa8A1SeSdfA1McA3S1S0S3Sd1Sa9GbVblkB;VblkL;A4S2A3S1S0S19S96Sa9S4G8S7SdSdSeVblkB;A1SeVblkL;A1A4MdS1cSa9A1A3A2VCx;A3S1S0S3S28VCx;Sa6A2S2A3S1S0S9SaS10A1MeA1MfS97VCx;ScfVmsg;Vlen;A2M10Vsx;A3S6GeVRx;A2A3S1S0S3S98VCx;G10Vsx;VRx;Sa4S1bS19S21SceA4A5S2A3S1S0S19SbeG10VCx;Vsx;VRx;ScdA5VTx;A3S1S0S9S19A1M11S24VTx;S4S23S26S48S30VTx;A1A1A1S5S23A1M12A3A2S6S19SabA2A3S1S0GeSfS1aSabA1M13A1ScS10SfS1aVUx;A1A1M14Sa4SbaS10Sb9S2bA4A3A3S1S0S3ScaS14G13A1Sa6A2S2A3S1S0S19S1eSabSb7G13G14A2A2VUx;A3S1S0G11S24VUx;S4S23S25G6A1S4S23S26S85S30VUx;A1A1A1S4S23S27G6A1G12A3A3A3A2S6S19VVx;A2A3S1S0S3S40VVx;Sa2A2S2A3S1S0S19S90Sa2VVx;A2VWx;A3S1S0S3S28VWx;Sa6A2S2A3S1S0G1S1fSb8G2SbdVWx;S2A5S6G0S4S1bS1dVFx;Sb6A2G3A3A2A3S1S0S3ScbS1cVCFx;A1M15S1cVFx;A1A2S2A3S1S0S19S9fGdS9fG9VFx;A2A2VCFx;A3S1S0S3S28VCFx;Sb3A2S2A3S1S0GfS97VCFx;S9cVsF;A3S6GeVRF;A2A3S1S0S3S99VCFx;S9cVsF;VRF;S4S19S9eS5S19A1M16A3A5S2A3S1S0S3SdeSdcVsF;A2S2A3S1S0S3S94S14S1aVCFx;A1M17A1S5S91A1M18A2S2A3S1S0SdSd2VsF;PcA2Vtb;A3S1S0SdSd2VsF;PdA2Vtl;A3S1S0S3S95S13G17A1M19SeZ0M1aA1S92ScS91Vbd;S4S91S93G1aZ1S92A3G18A3A3G18A5S2A3S1S0S3Sd8G19GbS6SbG6A2M1bVRF;A4S2A3S1S0S3Sd9G19GbG1bSfG17A1Sd7G15A6S2A3S1S0S3Se0S12S18S16SeZ1000A1Vtb;A2A1G19A3S2A3S1S0S19SddS9cVCFx;VsF;VRF;S9eA5VTFx;A3S1S0S3S28VTFx;S3aA2S2A3S1S0G1S1fSb8U3cSbdVTFx;S2A5S6G0S4S1bS1dVXx;Sb6A2G3A3A2A3S1S0G11S24VXx;S4S23S25Sa0SfS1aVXx;A1A1Sa1SeSd3S9dA1A1A3A1G12A3A2S6S19Sa7A2A3S1S0S3SdbS30Sa7A1S82Sa7A1A2S2A3S1S0G5Sb5S1aSb1A1G6A2S6S11S1aSadA1M1cA2A3S1S0G5Sb4G1cG6SeN430A1A3S6S11S1aSaeA1A2A3S1S0S3S46SaeA1S2A3S1S0S3S15S2dS1aSaaA1M1dS2aA2A1S2A3S1S0S3SbbS13G1dA1SfG1dA1S1cSaaA1Sc6Sc7GaS2aA7S2A3S1S0SdS20SaaA1GcA3S1S0S3S40Sb2G4A2S2A3S1S0S3ScbGaS1cSafA1A2S2A3S1S0S19S96SafGaA2VCXx;A3S1S0S3S28VCXx;S3aA2S2A3S1S0GfS97VCXx;Sa5G1aZ2A2M1eS42SccVCXx;A2M1fA3S6GeSacA2A3S0S3S98VCXx;G1eG1fSacG16A5S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
End TF.

Lemma sh1_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ21441Z1fZ21440Z40Sc3S5aS55S70S74S78S7cS5eS4dS6cS80S51S8eS89S68S63A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ov1_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ1609eZ1fZ16080Z40Sc0S57S53S6eS72S76S7aS5cS4bS6aS7eS4fS8bS87S65S61A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sh0_facts : ltac2:(tb__ "0|0|
S32S9aS9bS2cZ21441Z1fZ21440Z40Sc2S59S54S6fS73S77S7bS5dS4cS6bS7fS50S8dS88S67S62A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shZ_facts : ltac2:(tb__ "0|0|
S32S9aSeSd6A1S2fZ21441Z1fZ21440Z40Sc4S5bS56S71S75S79S7dS5fS4eS6dS81S52S8fS8aS69S64A17").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
