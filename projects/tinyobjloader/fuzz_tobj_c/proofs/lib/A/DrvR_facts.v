(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "sstate"; "SVar"; "ss_facts"; "ss_next"; "sprop_eqb"; "ss_objs"; "SPUle"; "SPBranch"; "cell"; "SPNot"; "sprop_below"; "SAlu"; "DUnknown"; "mkObj"; "reg_sv"; "ss_pc"; "swf"; "SExt"; "ss_lenient"; "sv_eqb"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sv_below"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "pair"; "Some"; "prod"; "list"; "option"; "nat"; "app"; "orb"; "andb"; "negb"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "mkLeafA"; "ax_X"; "ax_setS"; "ax_base"; "mkAX"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts"; "node_okb"; "nd_R"; "nd_Z"; "bd_R"; "N_mc"; "N_rd"; "bd_mid"; "carve_st"; "len1"; "carve_chk"; "nd_G0"; "nd_G1"; "H0c"; "H1c"; "N_fw"; "Q1c"; "Z3h"; "Z3k"; "Z5k"; "Z7h"; "H0b"; "H1b"; "Q1b"; "Ra0"; "Ra1"; "Rb1"; "Z4h"; "Z4k"; "Z6k"; "Z8h"; "bd_Z"; "A2_oom"; "A3_mc"; "A3_s0"; "A4_rd0"; "A4_rd1"; "B2_oom"; "E_mGf"; "L0s"; "N_exR"; "Rb0"; "S1_oom"; "VR"; "Z2h"; "Z2k"; "Z5h"; "Z6h"; "bk_facts"; "bkz_facts"; "qz_facts"; "A2_mc"; "A2_rd0"; "A2_rd1"; "A2_s0"; "A3_rd0"; "A3_rd1"; "B1_oom"; "B3_oom"; "B4_oom"; "F_bkZh"; "H0a"; "H1a"; "Lb0"; "LcH"; "LtrK"; "Q1a"; "R_xoom"; "Z1h"; "Z1k"; "nd_G2"; "A0_rd0"; "A0_rd1"; "A0_s0"; "A1_mc"; "A1_oom"; "A1_rd0"; "A1_rd1"; "A1_s0"; "B1a"; "B1b"; "B1c"; "B1d"; "BZHa"; "BZHb"; "BZHc"; "BZKa"; "BZKb"; "BZKc"; "F1a"; "F1b"; "F1c"; "F1d"; "G1a"; "G1b"; "G1c"; "G1d"; "GZa"; "GZb"; "GZc"; "O_rdsW"; "O_rdsZ"; "O_rdsZL"; "S1cp"; "S2cp"; "S3cp"; "S4cp"; "S5cp"; "S6cp"; "S7cp"; "S8cp"; "ZCa"; "ZCb"; "ZHa"; "ZHb"; "ZKa"; "ZKb"; "cp_site_facts"; "nU_oom"; "nV_oom"; "nd_G1k"; "nd_RT"; "nd_Rk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "vCap"; "vLen"; "ATOPHI"; "bd_T"; "tv_T"; "PostF"; "PreF"; "nd_T"; "vH"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "RsSymJump"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "vWant"; "s_RDa"; "ibS"; "RS"; "vResH"; "vRes1"; "O_rdsL"; "s_T"; "vRes0"; "X_R"; "s_RDb"; "G_cut"; "ax_of"; "s_bk1"; "s_bkG"; "two_cap"; "s_G"; "s_bkZh"; "O_rdsC"; "XF_q"; "objs37"; "s_GZ"; "s_bkZk"; "s_rd0"; "s_rd1"; "vN'"; "C_f"; "Lcl0"; "Lcl1"; "Lcp1"; "hcZ"; "irds"; "s_cp1"; "s_mG"; "s_mc"; "s_s0"; "C_mc"; "E_cl0"; "E_cl1"; "E_clZ"; "F2"; "Ltr"; "O_rdsP"; "QZhf"; "QZkf"; "clen_x"; "s_czh"; "s_czk"; "s_f"; "B1u"; "BZhu"; "BZku"; "C_czh"; "C_czk"; "C_rd0"; "C_rd1"; "C_s0"; "E_m"; "E_mG"; "E_mZ"; "E_mZG"; "E_mc"; "F1"; "F_bk1"; "G_mok"; "Hc0"; "Lb1"; "LbZh"; "Lc0k"; "Lg1"; "LgZh"; "Lr1"; "Ls0h";
"Ls0k"; "LtrR"; "O_dstL"; "PreM"; "Q1"; "RD1"; "R_mG"; "errV_okb"; "rds_cellsL"; "Bg"; "E_f"; "E_mcf"; "E_rd0"; "E_rd1"; "E_s0"; "G_mnull"; "Hc1"; "HcZ"; "LbZk"; "Loom"; "O_dstC"; "O_dstZ"; "QZh"; "QZk"; "RD0"; "R_f"; "T_after"; "T_f"; "T_mc"; "T_s0h"; "T_s0h'"; "T_s0k"; "T_s0k'"; "XF_bka"; "XF_bkb"; "X_G"; "errL"; "errL_okb"; "CUTS_R"; "C_cp1"; "LV_C1"; "LV_Gnull"; "LV_Gok"; "LV_R0"; "LV_R1"; "LV_S0"; "LV_S0h"; "LV_S0k"; "LV_T0k"; "LV_T1k"; "LV_Zh"; "LV_Zk"; "LV_c0"; "LV_c1"; "LV_cZ"; "LV_f"; "LV_h0"; "LV_h1"; "LV_hZ"; "LV_mc"; "Lg"; "Lov1"; "Lref"; "Lsh0"; "Lsh1"; "LshZ"; "PostsC"; "PostsCH"; "PostsMC"; "PreMC"; "R0c"; "R1c"; "R_mc"; "S0f"; "T_cp1"; "T_czh"; "T_czk"; "T_rd0k"; "T_rd1k"; "XF_bkza"; "XF_bkzb"; "XF_f"; "XF_qz"; "flg_x"; "inew"; "mc_kfacts"; "mc_rtc"; "objs38"; "optR"; "plen_x"; "rd_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_TOP"; "AE_A"; "UStopLe"; "L_malloc_null"; "L_malloc_ok"; "V_RES"; "ulink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bud_le"; "KU"; "BIc"; "batom"; "ASv"; "BI"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lc_obj"; "lcarve"; "uncarve_okb"; "carve_okb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_NE"; "instr"; "BC_EQ"; "ALU_SLL"; "BC_LTU"; "Ecall"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "CAP0"; "X_R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@Stdlib.PArith.BinPos.Pos"; "ltb"; "to_nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "CX_oom"; "C_oom"; "T_oom"; "U_oom"; "X_oom"; "V_oom"; "s_exR"; "x4_okb"; "E_oom"; "LV_xoom"; "R_oom"; "ex_carvedR"; "ex_img_okb"; "fw_rtc"; "fw_u1"; "fw_u2"; "s_oom"; "splitA"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "KP_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read"; "P_rd"; "Pre_rd"; "hc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_sub"; "wsub_bound"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "EBUF"; "P_fw";
"Pre_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr"; "P_icpt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "P_icpt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs"; "P_icpt"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition VR : Z := V_T + 2 ^ 27.
Definition bd_R : list bitem := ltac2:(tb__ "0|1|
S22S179S180Z1Z0S22S26S3bS17eA2M0S24S3bS17eN2S17fSb8A1A4S23G0A1A3S67A4S23S179A1A3").
Definition nd_R : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2Sb7Sb8A4S23G0A1A3S23S26S26S2S3bA2S2A2A1S40S195A4").
Definition bd_Z : list bitem := ltac2:(tb__ "0|0|
S22S179S17dZ1Z0S1c5S67S1c4Z2Z10000A2A2A3S23S179A1A3").
Definition nd_Z : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2Sb7S3S19aA1A4S23G0A1A3S23S26S26S2S3bA2S2A2A1S5bS195A4").

Definition N_rd : list lcarve := ltac2:(tb__ "0|c|
S22S26S26S3bS3bA2M0S27S26S26S3bS29A2M1S3bA2M2A1M3A2M4S24G0G3S24S3bS3bZf20d8M5Zf20daA4S22G2S24G1S3bS24S3bS29G5U1M6A4Z1M7A4S22G2S24G1S3bS24S3bS29Zf20d9G6A4G7A4S23G2A1M8A3A3A4S22G4S24G0G3S24S3bS3bZf20e0M9Zf20f8A4S22G2S24G1S3bS24S3bS29G9U8MaA4Z7fffffffffffA4S22G2S24G1S3bS24S3bS29Zf20e8GaA4Z0MbA4S22G2S24G1S3bS24S3bS29Zf20f0GaA4GbA4G8A3A3A3A4S23G4A1A3A3").
Lemma N_rd_eq : ltac2:(tb__ "0|0|
S0S27S4A1S186S188S4S187S42A4S171A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_rd_un : ltac2:(tb__ "0|0|
S0S21S189S1b4S42A2S20A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition node_okb (A : axst) (nd : ndesc) : bool := ltac2:(tb__ "0|3|
S2cS2cS2cS2cS2cS19fS1bdS9S30VA;A1M0A1M1A2S2dS18G0A1A1A2S194G1Vnd;A2A2Sc3S5S10G1A1S8G0A1M2A3A2S19S36VA;A1S3S1c1A1A2A2S1ccG2A1A2").
Lemma node_okb_sound : ltac2:(tb__ "0|3|
S32S197S0S21S3dR2R1A2S20A3S1S0S21S19fS1bdS9S30R3A1M0A1M1A2S20A3S1S0S21S18G0A1S2fA3S1S0S21S194G1R2A2S20A3S1S0S21Sc3S5S10G1A1S8G0A1M2A3S20A3S1S0S2S36R3A1S3S1c1A1A3S0S21S1ccG2A1S20A3A2A2A2A2A2F_;Fnd;FA;").
Proof.
  intros A nd H. unfold node_okb in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H5. destruct (ss_lenient (ax_S A)); [discriminate|]. repeat split; assumption.
Qed.

Definition carve_st (S : sstate) (N : list lcarve) : sstate := ltac2:(tb__ "0|0|
S1aS15VS;A1S1dVS;A1S1cVS;A1S1bVS;A1S1eVS;A1S2aS4SbVS;A1S186S188S4S187VN;A4A3S8VS;A1S9VS;A1S18VS;A1A9").
Definition carve_chk (A : axst) (tv : list (sv * sv)) (N : list lcarve) : bool := ltac2:(tb__ "0|1|
S2cS2cS16S44S30VA;A1M0VN;A2A1S18aS8G0A1SbG0A1S34VA;A1S1b4S1b5Vtv;VN;A7A2S19S36VA;A1S3S1c1A1A2A2").

Definition A0_rd1 : axst := errV E_rd1.
Definition A1_rd1 : axst := rd_w1 A0_rd1.
Definition A2_rd1 : axst := rd_w2 A1_rd1.
Definition A3_rd1 : axst := rd_s1 A2_rd1.
Definition A4_rd1 : axst := rd_rs A3_rd1.
Lemma rd1_site : ltac2:(tb__ "0|9|
S1S0S21S3dS11cS3eA2S20A3S1S0S21S11eS124A1S20A3S1S0S28S6A1M0Sc8S30S84A1U0M1S3N8d0A1A3S25S6S30S89A1M2A2A3S1S0G0Sc8G2G1S3N920A1A3S25S6S30S71A1M3A2A3S1S0G0Sc8G3SedS71A1S198S3Sd1A1SceA2A3S25S6S30S74A1M4A2A3S1S0S28S4A1Sc2S4SbG4A1SedS74A1M5A3S25S4Sd4SceS23SeA1M6A2A2A3S1S0S6S183G4G5Se0SceG6A2A3S30S60A1M7A3S1S0S21S184G4G7A2S20A3S1S0S21S46S60S22S26S2S2A2M8S24S2S2Sb7Sb8A4S23G8A1A3S42A3S20A3S1S0S32S35S60S44G7S42A2A2S105A3S1S0S21S3dS105S3eA2S20A3S0S21Sc1S5SaScSceS3Z10000A1A2A1S8S30S124A1A1A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma rd1_call : ltac2:(tb__ "0|4|
S1S0S2S3aSe6P13A2SceA3S1S0S2S3aSe6P11A2S3Z0A1A3S1S0S2S3aSe6PfA2S3Sd1A1A3S1S0S2S3aSe6P10A2S3Z10000A1A3S1S0S21S2bS2bS2dS19dP64M0S9S30S1b7A1A1M1A2A1S1baSe6G0A2A2S19dG0S9S30S105A1A1M2A2A2S20A3S1S0S2S3aS1b9Se6G1S30S1b6S23SeA1G0A2A1M3G2A4G0A2Sd3A3S1S0S21S1b2S19eG0A1S19eS9G3A1A1A2S20A3S1S0S21S3dS165S3eA2S20A3S0S27S31A1S148S22S31S33SebSc4A2S22S31S33SeaSc4A2S23S31A1A3A3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Q1a : axst := ltac2:(tb__ "0|0|
SdaScaSebSe1A2SebA2").
Definition Q1b : axst := q2 vWant Q1a.
Definition Q1c : axst := ltac2:(tb__ "0|0|
SdaScaS53S22ScbSccU26A1S23ScbA1A3A2S53A2").
Lemma rd1_cont : ltac2:(tb__ "0|8|
S1S0S28S32A1M0ScaSebSe1A2S25S32S7eA2A3S1S0S28S4A1Sc2S4SbS30S7eA1M1A1U26M2A3S25S4Sf8SceS23SeA1M3A2A2A3S1S0S6S183G1G2Sd4SceG3A2A3S30S53A1M4A3S1S0S21S184G1G4A2S20A3S1S0G0ScaS53S22ScbSccG2A1S23ScbA1A3A2S25S32S4cA2A3S1S0S27S4A1SbS30S4cA1M5A1S2aS4Se2S4cA1M6S186S188S4S187S42A4A3A3S1S0S21S194S9G5A1S3eA2S20A3S1S0S21S19cSd7S34S4cA1A2S20A3S1S0S32S199S35S4cSc5G5G6A2A2Sd7A2S11bA3S1S0S21S3dS11bS3eA2S20A3S1S0S21Sc1S5SaSdS18bSd3S3Z0A1A3A1S8S30SebA1A1M7A3S20A3S0S21Sc1S5SaScSceS3Z10000A1A2A1G7A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition H1a : axst := ltac2:(tb__ "0|0|
SdaScaSeaSe1A2SeaA2").
Definition H1b : axst := q2 vWant H1a.
Definition H1c : axst := ltac2:(tb__ "0|0|
SdaScaS52S22ScbSccU26A1S23ScbA1A3A2S52A2").
Lemma rd1_close : ltac2:(tb__ "0|8|
S1S0S28S32A1M0ScaSeaSe1A2S25S32S7aA2A3S1S0S28S4A1Sc2S4SbS30S7aA1M1A1U26M2A3S25S4Sf8SceS23SeA1M3A2A2A3S1S0S6S183G1G2Sd4SceG3A2A3S30S52A1M4A3S1S0S21S184G1G4A2S20A3S1S0G0ScaS52S22ScbSccG2A1S23ScbA1A3A2S25S32S4aA2A3S1S0S27S4A1SbS30S4aA1M5A1S2aS4Se2S4aA1M6S186S188S4S187S42A4A3A3S1S0S21S194S9G5A1S3eA2S20A3S1S0S21S19cSd7S34S4aA1A2S20A3S1S0S32S199S35S4aSc5G5G6A2A2Sd7A2S127A3S1S0S21S3dS127S3eA2S20A3S1S0S21Sc1S5SaSfSdS18bSd3S3Z0A1A3A1A1S8S30SeaA1A1M7A3S20A3S0S21Sc1S5SaScSceS3Z10000A1A2A1G7A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition N_mc : list lcarve := ltac2:(tb__ "0|d|
S22S26S26S3bS3bA2M0S27S26S26S3bS29A2M1S3bA2M2A1M3A2M4S24G0G3S24S3bS3bZf20d8M5Zf20daA4S22G2S24G1S3bS24S3bS29G5U1M6A4Z1M7A4S22G2S24G1S3bS24S3bS29Zf20d9G6A4G7A4S23G2A1M8A3A3A4S22G4S24G0G3S24S3bS3bZf20e0M9Zf20f8A4S22G2S24G1S3bS24S3bS29G9U8MaA4Z7fffffffffffA4S22G2S24G1S3bS24S3bS29Zf20e8GaA4Z0MbA4S22G2S24G1S3bS24S3bS29Zf20f0GaA4GbA4G8A3A3A3A4S22G4S24G0G3S24S3bS3bZe9ae8McZe9af0A4S22G2S24G1S3bS24S3bS29GcGaA4Zddf74A4G8A3A4S23G4A1A3A3A3").
Lemma N_mc_eq : ltac2:(tb__ "0|0|
S0S27S4A1S186S188S4S187S41A4S16dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_mc_un : ltac2:(tb__ "0|0|
S0S21S189S1b4S41A2S20A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition oget (x : option sstate) (d : sstate) : sstate := match x with Some s => s | None => d end.
Definition S1cp : sstate := Eval vm_compute in oget (cp_w1 (ax_S Q1)) (ax_S Q1).
Definition S2cp : sstate := Eval vm_compute in oget (cp_w2 S1cp) S1cp.
Definition S3cp : sstate := Eval vm_compute in oget (cp_b0 S2cp) S2cp.
Definition S4cp : sstate := Eval vm_compute in oget (cp_b1 S3cp) S3cp.
Definition S5cp : sstate := Eval vm_compute in oget (cp_b2 vRes1 S4cp) S4cp.
Definition S6cp : sstate := Eval vm_compute in cp_rsd vRes1 S5cp.
Definition S7cp : sstate := Eval vm_compute in oget (cp_s1 vRes1 S6cp) S6cp.
Definition S8cp : sstate := Eval vm_compute in cp_rss vRes1 S7cp.
Section CpSite.
  Variable (r : sv) (Q : axst) (S1 S2 S3 S4 S5 S6 S7 S8 : sstate) (C : axst).
  Definition cp_site_facts : Prop := ltac2:(tb__ "0|f|
S1S0S28S6A1M0Sc8S30VQ;A1M1U0M2S3N8f0A1A3S25S6VS1;A2A3S1S0G0Sc8VS1;G2S3N940A1A3S25S6VS2;A2A3S1S0G0Sc8VS2;Sd0VS2;Sb7S3Z0A1M3A3S3Z4A1M4A3S25S6VS3;A2A3S1S0G0Sc8VS3;Sd0VS3;Sb7G4A3Sb9A3S25S6VS4;A2A3S1S0G0Sc8VS4;Sd0VS4;Sb7Sb9A3S198Sb9Vr;A2A3S25S6VS5;A2A3S1S0S28S4A1M5Sc2S4SbVS5;A1Sd0VS5;Sb7Sb9A3M6A3S25S4S119Vr;A1A2A3S1S0S6S183VS5;G6S12bVr;A1A3VS6;A3S1S0S21S184VS5;VS6;A2S20A3S1S0G0Sc8VS6;Sd0VS6;G3S3Sd1A1M7A3S198G7Vr;A2A3S25S6VS7;A2A3S1S0G5Sc2S4SbVS7;A1Sd0VS7;G3G7A3M8A3S25S4Sd4Vr;S23SeA1M9A2A2A3S1S0S6S183VS7;G8Se0Vr;G9A2A3VS8;A3S1S0S21S184VS7;VS8;A2S20A3S1S0S21S46S37VS8;S34VQ;A1MaS36VQ;A1MbA3S22S26S2S2A2McS24S2S2Sb7Sb8A4S23GcA1A3S41A3S20A3S1S0S32S37S44VS8;S41A2GaGbA3VC;A3S1S0S21S3dVC;S3eA2S20A3S1S0S21Sc1S5SaScSb7S3SbaA1A2A1S8G1A1MdA3S20A3S1S0S21Sc1S5SaScS3Z1000A1Sb7A2A1GdA3S20A3S1S0S27S5A1S8S30VC;A1MeA1GdA3S0S3cS9GeA1S9G1A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
End CpSite.
Lemma cp1_site : ltac2:(tb__ "0|0|
Sb1Sd3S11bSa3Sa4Sa5Sa6Sa7Sa8Sa9SaaS13eAb").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma cp1_call : ltac2:(tb__ "0|2|
S1S0S2S3aSeePfA2Sb7A3S1S0S2S3aSeeP10A2Sb8A3S1S0S2S3aSeeP13A2S3Sd1A1A3S1S0S2S3aSeeP34A2S3Z10000A1A3S1S0S2S3aSeeP12A2Sd3A3S1S0S27S31A1M0S159S22S31S33S1d3Sc6A2S23S31A1M1A3A3S1S0S21S3dS161S3eA2S20A3S0G0S13fS22S31S33S115Sc4A2S22S31S33S113Sc4A2S22S31S33S110Sc4A2G1A3A3A3A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section BkPieces.
  Variable (r : sv) (X : list (sv * sv)) (Lf Ba Bb Bc Bd B : axst).
  Definition bk_facts : Prop := ltac2:(tb__ "0|d|
S1S0S28S32A1M0ScaVLf;S138A2S25S32VBa;A2A3S1S0S28S4A1M1Sc2S4SbS30VBa;A1M2A1UbM3A3S25S4S12bVr;A1A2A3S1S0S6S183G2G3S119Vr;A1A3S30VBb;A1M4A3S1S0S21S184G2G4A2S20A3S1S0S27S26S2S2A2A1M5S34VBb;A1M6S34VBa;A1A3S1S0S2S36VBb;A1M7S36VBa;A1A3S1S0G1Sc2S4SbG4A1U29M8A3S25S4Sf8Vr;S23SeA1M9A2A2A3S1S0S6S183G4G8Sd4Vr;G9A2A3S30VBc;A1MaA3S1S0S21S184G4GaA2S20A3S1S0G5S34VBc;A1G6A3S1S0S2S36VBc;A1G7A3S1S0G0ScaVBc;S139A2S25S32VBd;A2A3S1S0S27S4A1SbS30VBd;A1MbA1S2aS4Se2VBd;A1McS186S188S4S187S41A4A3A3S1S0S21S194S9GbA1S3eA2S20A3S1S0S21S19cVX;S34VBd;A1A2S20A3S1S0S32S199S35VBd;Sc5GbGcA2A2VX;A2VB;A3S1S0S21S3dVB;S3eA2S20A3S0S21Sc1S5SaScSb7S3SbaA1A2A1S8S30VLf;A1A1A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
End BkPieces.
Definition bka (Lf : axst) : axst := ltac2:(tb__ "0|0|
SdaScaVLf;S138A2VLf;A2").
Definition bkb (r : sv) (Ba : axst) : axst := ltac2:(tb__ "0|0|
S35VBa;S183S30VBa;A1UbS119Vr;A1A3A2").
Definition bkc (r : sv) (Bb : axst) : axst := ltac2:(tb__ "0|0|
S35VBb;S183S30VBb;A1U29Sd4Vr;S23SeA1A2A3A2").
Definition bkd (Bc : axst) : axst := ltac2:(tb__ "0|0|
SdaScaVBc;S139A2VBc;A2").
Definition B1a : axst := Eval vm_compute in bka Lb1.   Definition B1b : axst := Eval vm_compute in bkb vRes1 B1a.
Definition B1c : axst := Eval vm_compute in bkc vRes1 B1b. Definition B1d : axst := Eval vm_compute in bkd B1c.
Definition G1a : axst := Eval vm_compute in bka Lg1.   Definition G1b : axst := Eval vm_compute in bkb vRes1 G1a.
Definition G1c : axst := Eval vm_compute in bkc vRes1 G1b. Definition G1d : axst := Eval vm_compute in bkd G1c.
Definition F1a : axst := Eval vm_compute in bka Lr1.   Definition F1b : axst := Eval vm_compute in bkb vRes1 F1a.
Definition F1c : axst := Eval vm_compute in bkc vRes1 F1b. Definition F1d : axst := Eval vm_compute in bkd F1c.

Definition len1 : sv := add vRes1 vLen.
Lemma cp1_back : ltac2:(tb__ "0|7|
S1S6cSd3Sd7S110S8bS8cS8dS8eSffA8S1S0S21Sc1S5SaSfSdS18dS45Sb8A3A1A1S8S30S110A1A1A3S20A3S1S0S27S5A1S10dS22S5ScS198S45S3Z1A1A2Sb8A2S22S5ScS45Sb8A2S23S5A1A3A3A3S1S0S21Sc3S5S10S9S30SffA1A1A1S10dA3S20A3S1S0S21S3dS1bcS10dSffA2M0S3eA2S20A3S1S0S2S3aSdbP18M1A2S7G1A1A3S1S0S2S3aSdbS172A2S7S172A1A3S1S0S2S3aSdbP2aA2S45A3S1S0S2S3aSdbP29M2A2S7G2A1A3S1S0S2S3aSdbP28M3A2S7G3A1A3S1S0S2S3aSdbP2dM4A2S7G4A1A3S1S0S21S193SdbS22S26S2S2A2M5S24S2S2Sb7Sb8A4S23G5A1A3M6G6A3S20A3S0S21S17bS8S30G0A1A1S17aSdbS40A2S40A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma cp1_grow : ltac2:(tb__ "0|1|
S1S6cSd3Sd7S113S99S9aS9bS9cS107A8S1S0S21Sc1S5SaSdS18dS45Sb8A3A1S8S30S113A1A1M0A3S20A3S0S21Sc1S5SaSfSdS18bS11S191S45S3Z1aA1A3S3Z0A1A3A1A1G0A3S20A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma cp1_ref : ltac2:(tb__ "0|1|
S1S6cSd3Sd7S115S95S96S97S98S155A8S1S0S21Sc1S5SaSdS18dS45Sb8A3A1S8S30S115A1A1M0A3S20A3S0S21Sc1S5SaSdS18bS11S191S45S3Z1aA1A3S3Z0A1A3A1G0A3S20A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ra1 : axst := Eval vm_compute in nthA R1c LV_R1 0.
Definition Rb1 : axst := Eval vm_compute in nthA R1c LV_R1 1.
Lemma head1_facts : ltac2:(tb__ "0|11|
S1S0S21S3dS15eS3eA2S20A3S1S0S27S31A1S143S22S31S33S55Sc4A2S22S31S33S56Sc4A2S23S31A1A3A3A3S1S0S21S38S55S11cScfA3S20A3S1S0S21S38S56S11cSd8A3S20A3S1S0S21S3dS55S3eA2S20A3S1S0S21S3dS56S3eA2S20A3S1S0S2S3aScfP18M0A2S7G0A1M1A3S1S0S2S3aScfS172A2S7S172A1M2A3S1S0S2S3aScfP31M3A2S11S192Sb8Sb9A3M4A3S1S0S2S3aScfP2aM5A2S7G5A1M6A3S1S0S2S3aScfP29M7A2S7G7A1M8A3S1S0S2S3aScfP2dM9A2S7G9A1MaA3S1S0S2S3aSd8G0A2G1A3S1S0S2S3aSd8S172A2G2A3S1S0S2S3aSd8G3A2S3Z10000A1MbA3S1S0S2S3aSd8G5A2G6A3S1S0S2S3aSd8G7A2G8A3S1S0S2S3aSd8G9A2GaA3S1S0S21S193ScfS22S26S2S2A2McS24S2S2Sb7Sb8A4S23GcA1A3MdGdA3S20A3S1S0S21S193Sd8GdGdA3S20A3S1S0S21S17bS8S30S55A1A1MeS17aScfS40A2S40A3S20A3S1S0S21S17bS8S30S56A1A1MfS17aSd8S40A2S40A3S20A3S1S0S21Sc1S5SaSdS18fG4GbA3M10A1GeA3S20A3S0S21Sc1S5SaSfG10A1A1GfA3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_mGf : axst := ltac2:(tb__ "0|0|
S1bcS22S5ScSb8S3S1c3Z2Z19A2A1A2S23S5A1A3S108A2").
Lemma grow_pre_facts : ltac2:(tb__ "0|e|
S1S0S21S16S30S108A1M0A1S20A3S1S0S3cS9G0A1M1S9S30S107A1M2A1A3S1S0S28S26S27S26S2S2A2M3A1M4S27S5A1M5A2M6A1S185G2G0A2S25G6S24G4G5S22G3S24S2S2S11S18eS45S3Z1A1A3SddA4M7S22G3S24S2S2S45Sb8A4S22G3G7S23G3A1M8A3A3A3S23S5A1M9A4A2A3S1S0S32S35S107G0A2S108A3S1S0S21Sc3S5S10G1A1S22S5ScSb8S3S1c3Z2Z19A2A1A2G9A3A3S20A3S1S0S21S38S62Sd9SdeA3S20A3S1S0S21S3dS62S3eA2S20A3S1S0S21S3dSd9S3eA2S20A3S1S0S2S3aSdeP18MaA2S7GaA1A3S1S0S2S3aSdeS172A2S7S172A1A3S1S0S2S3aSdeP29MbA2S7GbA1A3S1S0S2S3aSdeP2dMcA2S7GcA1A3S1S0S21S193SdeS22G3S24S2S2Sb7Sb8A4G8A3MdGdA3S20A3S0S21S17bS8S30S62A1A1S17aSdeS40A2S40A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition bd_mid : list bitem := ltac2:(tb__ "0|2|
S22S179S180Z1M0Z0S22S26S3bS17eA2M1S24S3bS17eN2S17fS11S18eSb8S3G0A1A3A1A4S23G1A1A3S67A4S23S179A1A3").
Definition nd_Rk : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2Sb7Sb8A4S23G0A1A3S23S26S26S2S3bA2S2A2A1S2aS179S40S22S179S17dZ0Z1S17cA3S23S179A1A3A3S195A4").
Definition nd_G0 : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2Sb7Sb8A4S23G0A1A3S23S26S26S2S3bA2S2A2A1S43S195A4").
Definition nd_G1 : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2S7Se7A1SddA4S22G0S24S2S2Sb7Sb8A4S23G0A1A3A3S23S26S26S2S3bA2S2A2A1S43S195A4").
Definition nd_G1k : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2S7Se7A1SddA4S22G0S24S2S2Sb7Sb8A4S23G0A1A3A3S23S26S26S2S3bA2S2A2A1S2aS179S43S22S179S17dZ0Z1S17cA3S23S179A1A3A3S195A4").
Definition nd_G2 : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2S7Se7A1SddA4S23G0A1A3S23S26S26S2S3bA2S2A2A1S43S195A4").

Lemma grow_malloc_facts : ltac2:(tb__ "0|e|
S1S0S21S3dSd9Sb6A2S20A3S1S0S21S1c0S1bdSefA2S20A3S1S0S2S3aSefPcA2M0S11S18eSb8S3Z1M1A1A3M2A3S1S0S21S1fS9S30Sd9A1M3A1M4G0A2S20A3S1S0S2S3aS1d1SefS11aS176S173S23S178A1M5S174A3M6Sd9A4S177A2S7S1bbG4UaA2A1M7A3S1S0S2G7S7Se7A1A3S1S0S21S181G4S43A2S20A3S1S0S21S182S8G3A1M8G2S17cS2aS179S40S22S179S17dZ0G1S17cA3S23S179A1A3A3S43A5S20A3S1S0S21S1cbG8S22S26S2S2A2M9S24S2S2Sb7Sb8A4S23G9A1A3MaS2eS29A1MbS11dA4S20A3S1S0S21S1cdG8GaGbSbG3A1S1caS34Sd9A1A6S20A3S1S0S32S1bfS11aSd9SefS11dS175S173G5S174A3A5S126A3S1S0S32S1bfS11aSd9SefS11dG6A5S10eA3S1S0S21S3dS126S47A2S20A3S1S0S21S3dS10eS48A2S20A3S1S0S27S31A1McS140S22S31S33S12aSc4A2S23S31A1MdA3A3S1S0GcS141S22S31S33S10bSc4A2GdA3A3S1S0S21Sc1S5SaScS3Z10000A1Sb8A2A1G8A3S20A3S0S21Sc1S5SaScSb8S3S1c3Z2Z19A2A1A2A1G8A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition A1_mc : axst := mc_w1 E_mcf.
Definition A2_mc : axst := mc_w2 A1_mc.
Definition A3_mc : axst := mc_b1 A2_mc.
Lemma grow_mc_facts : ltac2:(tb__ "0|d|
S1S0S21Sc3S5S10S9S30S10bA1M0A1A1S16cA3S20A3S1S0S21S3dS122S48A2S20A3S1S0S28S6A1M1Sc8S30S122A1U0M2S3N870A1A3S25S6S30S86A1M3A2A3S1S0G1Sc8G3G2S3N8c0A1A3S25S6S30S6fA1M4A2A3S1S0G1Sc8G4S16bS6fA1Sb8A3S25S6S30S5dA1M5A2A3S1S0S21S46S5dS22S26S2S2A2M6S24S2S2S7Se7A1M7SddA4S22G6S24S2S2Sb7Sb8A4S23G6A1A3A3S41A3S20A3S1S0S32S35S5dS44G5S41A2A2Sf2A3S1S0S21S3dSf2S48A2S20A3S1S0S2S3aSf0PfA2G7A3S1S0S2S3aSf0P13A2Sb7A3S1S0S2S3aSf0P10A2SddA3S1S0S2S3aSf0P34A2Sb8A3S1S0S32S131S15cSf2Sf0S15fS1ceA5S133A3S1S0S21S3dS133S48A2S20A3S1S0S27S31A1M8S152S22S31S33S121Sc4A2S23S31A1M9A3A3S1S0S21Sc1S5SaScS3Z1000A1MaG7A2A1MbS8G0A1A3S20A3S1S0S21S3dS10bS48A2S20A3S1S0S21S3dS10eS48A2S20A3S1S0S21Sc1S5GbS8S30Sf2A1A1McA3S20A3S1S0S21Sc1S5SaScGaSb7A2A1GcA3S20A3S0G8S15bS22S31S33S1ceSc6A2G9A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma grow_free_facts : ltac2:(tb__ "0|d|
S1S0S28S32A1ScaS121S168A2S25S32S10cA2A3S1S0S32S199S10cS13aA2Sf6A3S1S0S21S19cS13aS34S10cA1A2S20A3S1S0S27S4A1SbS30Sf6A1M0A1S2aS4S16eSf6A1M1S186S188S4S187S41A4A3A3S1S0S21S194S9G0A1S48A2S20A3S1S0S32S35Sf6Sc5G0G1A2A2Se8A3S1S0S21S3dSe8Sb4A2S20A3S1S0S21S1c0S1bdSfeA2S20A3S1S0S2S3aSfePcA2Sb7A3S1S0S2S3aSfePdA2Sb8A3S1S0S21S181S9S30Se8A1M2A1S43A2S20A3S1S0S21S182S8G2A1M3S3Z0M4A1S17cS2aS179S43S22S179S17dG4Z1S17cA3S23S179A1A3A3S43A5S20A3S1S0S21S1cbG3S22S26S2S2A2M5S24S2S2S7Se7A1M6SddA4M7S22G5S24S2S2Sb7Sb8A4S23G5A1M8A3M9A3MaS25S29U1A2MbS130A4S20A3S1S0S21S1cdG3GaGbSbG2A1S1caS34Se8A1A6S20A3S1S0S21Sc1S5SaScS3Z1000A1Sb7A2A1G3A3S20A3S1S0S32S1bfSbeSe8SfeS130SbdA5S132A3S1S0S21S3dS132S82A2S20A3S1S0S27S31A1S14eS22S31S33S153Sc4A2S23S31A1A3A3S1S0S21S3dS120S82A2S20A3S1S0S2S3aSdcP18McA2S7GcA1A3S1S0S2S3aSdcS172A2S7S172A1A3S1S0S2S3aSdcP28A2G6A3S1S0S2S3aSdcP29A2SddA3S1S0S2S3aSdcP2aA2Sb8A3S1S0S2S3aSdcP2dA2S17S20Q20Sc0A3A3S1S0S21S193SdcS22G5G7G8A3G9A3S20A3S0S21S17bS8S30S120A1A1S17aSdcS40A2S43A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma close1_facts : ltac2:(tb__ "0|3|
S1S0S27S31A1M0S14cS22S31S33Sf4Sc4A2S23S31A1M1A3A3S1S0S28S18cA1Sc7S1b3S15S30Sf4A1M2A1A2S25S18cS190A2A3S1S0S2S14G2Z11A2S3Z39A1A3S1S0S2S14G2ZaA2S3Z3A1A3S1S0S21S3dSf4S3eA2S20A3S1S0S21S3dS1beSf4S3Z0A1A2S3eA2S20A3S0G0S150S22S31S33S157Sc4A2S22S31S33S154Sc4A2S22S31S33Sf7Sc4A2G1A3A3A3A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma close0_facts : ltac2:(tb__ "0|3|
S1S0S21S3dS10fS3eA2S20A3S1S0S27S31A1M0S14bS22S31S33Sf3Sc4A2S23S31A1M1A3A3S1S0S28S18cA1Sc7S1b3S15S30Sf3A1M2A1A2S25S18cS190A2A3S1S0S2S14G2Z11A2S3Z39A1A3S1S0S2S14G2ZaA2S3Z3A1A3S1S0S21S3dSf3S3eA2S20A3S1S0S21S3dS1beSf3S3Z0A1A2S3eA2S20A3S0G0S14fS22S31S33S156Sc4A2G1A3A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma closeZ_facts : ltac2:(tb__ "0|3|
S1S0S21S3dS128S3fA2S20A3S1S0S27S31A1M0S14dS22S31S33Sf5Sc4A2S23S31A1M1A3A3S1S0S28S18cA1Sc7S1b3S15S30Sf5A1M2A1A2S25S18cS190A2A3S1S0S2S14G2Z11A2S3Z39A1A3S1S0S2S14G2ZaA2S3Z3A1A3S1S0S21S3dSf5S3fA2S20A3S1S0S21S3dS1beSf5S3Z0A1A2S3fA2S20A3S0G0S151S22S31S33S158Sc4A2G1A3A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition LtrK : axst := ltac2:(tb__ "0|0|
S1bcS22S5ScSfbS3Z7fffA1A2S23S5A1A3S118A2").
Definition nd_RT : ndesc := ltac2:(tb__ "0|1|
S196S22S26S2S2A2M0S24S2S2Sb7Sb8A4S23G0A1A3S23S26S26S2S3bA2S2A2A1SbbS195A4").
Lemma tr_facts : ltac2:(tb__ "0|10|
S1S0S21S3dSf7S3eA2S20A3S1S0S21Sc1S5SaSfSdS18bSd3S3Z0A1M0A3A1A1S8S30Sf7A1M1A1M2A3S20A3S1S0S21Sc1S5SaSfSdS18fSb9S198SfbS3Z6A1A2A3A1A1G2A3S20A3S1S0S28S26S27S26S2S2A2M3A1M4S27S5A1M5A2M6A1S185G1S30S118A1M7A2S25G6S24G4G5S22G3S24S2S2Sd3G0A4S23G3A1M8A3S23S5A1M9A4A2A3S1S0S21S16G7A1S20A3S1S0S3cS9G7A1MaS9G1A1A3S1S0S32S35Sf7G7A2S118A3S1S0S21Sc3S5S10GaA1S22S5ScSfbS3Z7fffA1A2G9A3A3S20A3S1S0S21S3dS7dSb5A2S20A3S1S0S2S3aSd5P18MbA2S7GbA1A3S1S0S2S3aSd5S172A2S7S172A1A3S1S0S2S3aSd5P28McA2S7GcA1A3S1S0S2S3aSd5P29MdA2S7GdA1A3S1S0S2S3aSd5P2aMeA2S7GeA1A3S1S0S2S3aSd5P2bA2SfbA3S1S0S2S3aSd5P2cA2S170A3S1S0S2S3aSd5P2dMfA2S7GfA1A3S1S0S2S3aSd5P2eA2S16aA3S1S0S21S193Sd5S22G3S24S2S2Sb7Sb8A4G8A3SbcA3S20A3S1S0S21S17bS8S30S7dA1A1S17aSd5SbbA2SbbA3S20A3S0S197SbfS196SbcS23S26S26S2S3bA2S2A2A1SbbS195A4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition N_fw : list lcarve := ltac2:(tb__ "0|8|
S22S26S26S3bS3bA2M0S27S26S26S3bS29A2M1S3bA2M2A1M3A2M4S24G0G3S24S3bS3bZf20d8M5Zf20daA4S22G2S24G1S3bS24S3bS29G5U1M6A4Z1M7A4S22G2S24G1S3bS24S3bS29Zf20d9G6A4G7A4S23G2A1A3A3A4S23G4A1A3").
Lemma N_fw_eq : ltac2:(tb__ "0|0|
S0S27S4A1S186S188S4S187S4bA4S1adA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fw_un : ltac2:(tb__ "0|0|
S0S21S189S1b4S4bA2S20A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition N_exR : list lcarve := N_ex.
Lemma N_exR_eq : ltac2:(tb__ "0|0|
S0S27S4A1S186S188S4S187S64A4S1abA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition A1_oom : axst := x4set (SLit TP) E_oom.
Definition A2_oom : axst := splitA 0 (SLit (-2400)) A1_oom.
Definition nU_oom : nat := length (ss_objs (ax_S T_oom)).
Definition S1_oom : axst := selA (fw_u1 nU_oom) T_oom.
Definition nV_oom : nat := length (ss_objs (ax_S U_oom)).

Definition B1_oom : axst := ltac2:(tb__ "0|0|
S199S1b1U0S3N400A1S1a4A3S23S26S2S2A2A1A2").
Definition B2_oom : axst := ex_img B1_oom.
Definition B3_oom : axst := app_objs ex_carvedR B2_oom.
Definition B4_oom : axst := x4set (SLit TP) B3_oom.
Definition R_xoom : list sobj := ltac2:(tb__ "0|0|
S16fS1cfS1a0S1c6Z0Z2A2S1a6S1c7S1a0A2A3A1").
Lemma oom_facts : ltac2:(tb__ "0|e|
S1S0S21S3dS12aS47A2S20A3S1S0S21S1a7S1a8S3S1d2A1M0A2S20A3S1S0S28S6A1M1Sc8S30S87A1U0M2S3N960A1A3S25S6S30S5cA1M3A2A3S1S0S21S46S5cS22S26S2S2A2M4S24S2S2Sb7Sb8A4S23G4A1M5A3M6S4bA3S20A3S1S0S32S35S5cS44G3S4bA2A2S1a1A3S1S0S21S3dS1a1S47A2S20A3S1S0S32S131S1c9Z14d77Z13A2S1a1S1b0S1aaS1c8A5S1a2A3S1S0S21S3dS1a2S47A2S20A3S1S0S28S32A1M7ScaS1a2S22ScbScdS1aeSb2A1A1S23ScbA1M8A3A2S25S32S66A2A3S1S0S27S4A1M9SbS30S66A1MaA1S2aS4SbS30S1a3A1A1MbS186S188S4S187S4bA4A3A3S1S0S21S194S9GaA1S47A2S20A3S1S0S32S35S66Sc5GaGbA2A2S1a3A3S1S0G7ScaS1a3S22ScbScdS1afSb3A1A1S22ScbSccG2A1G8A3A3A2S25S32S1a5A2A3S1S0S21S3dS1a5S47A2S20A3S1S0S27S31A1S1a9S22S31S33S1a4Sc4A2S23S31A1A3A3S1S0G1Sc8S30S1a4A1G2S3N400A1A3S25S6S30S75A1A2A3S1S0S21S1acS75A1S20A3S1S0S21S46S61G6S64A3S20A3S1S0S32S35S61S44S30S61A1S64A2A2S76A3S1S0S21S1a7S76G0A2S20A3S1S0S21S19cG5S34S77A1A2S20A3S1S0S32S199S77G5A2S1a0A3S1S0S21S3dS1a0S47A2S20A3S1S0S28G9A1S1cfS1a0S1c6Z0Z2A2McS1a6S1c7S1a0A2MdA3S25G9S7fA2A3S0S21S1d0S1a0GcGdS7fS23S32A1A5S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition L0s : axst := Eval vm_compute in nthA S0f LV_S0 0.
Definition A0_s0 : axst := errV E_s0.
Definition A1_s0 : axst := rd_w1 A0_s0.
Definition A2_s0 : axst := rd_w2 A1_s0.
Definition A3_s0 : axst := rd_rsZ A2_s0.
Definition O_rdsZ : sobj := ltac2:(tb__ "0|0|
S13S3Z0A1S3Sd1A1S3S1c2Sd1Z10000A2A1S23SeA1S12A5").
Definition LcH : axst := Eval vm_compute in nthA S0f LV_S0h 1.
Lemma s0_site : ltac2:(tb__ "0|a|
S1S0S21S3dS160S3fA2S20A3S1S0S27S31A1M0S144S22S31S33S63Sc4A2S23S31A1M1A3A3S1S0S21S3dS63S3fA2S20A3S1S0S28G0A1S39S1b3U14S13dS63S20A5S25G0S22S31S33S125Sc4A2G1A3A2A3S1S0S21S11eS125A1S20A3S1S0S28S6A1M2Sc8S30S85A1U0M3S3N8d0A1A3S25S6S30S8aA1M4A2A3S1S0G2Sc8G4G3S3N920A1A3S25S6S30S72A1M5A2A3S1S0S28S4A1Sc2S4SbG5A1SedS72A1M6A3S25S4Sa1A2A3S1S0S6S183G5G6Se0S3S19aA1M7S23SeA1A2A3S30S5eA1M8A3S1S0S21S184G5G8A2S20A3S1S0S21S46S5eS22S26S2S2A2M9S24S2S2Sb7G7A4S23G9A1A3S42A3S20A3S1S0S32S35S5eS44G8S42A2A2S106A3S1S0S21S3dS106S3fA2S20A3S0S2S3aSf1P13A2G7A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma s0_call : ltac2:(tb__ "0|c|
S1S0S21S2bS2bS2dS19dP64M0S9S30S1b7A1A1M1A2A1S1baSf1G0A2A2S19dG0S9S30S106A1A1M2A2A2S20A3S1S0S21S2bS2bS2dS19dP65M3G1A2A1S1baSf1G3A2A2S19dG3G2A2A2S20A3S1S0S2S3aS1b9Sf1G1S30S1b6S23SeA1G0A2A1M4G2A4G0A2S7G0A1M5A3S1S0S2S3aS1b9Sf1G1S30S1b6S1b8G3A2A1M6G2A4M7G0A2G5A3S1S0S2S3aG7G3A2S7G3A1A3S1S0S21S1b2S19eG0A1M8S19eS9G4A1A1A2S20A3S1S0S21S1b2G8S19eS9G6A1A1M9A2S20A3S1S0S21S1b2S19eG3A1G9A2S20A3S1S0S21S13cS137A1S20A3S1S0S32S13bS137A1S136A3S1S0S21S13cS135A1S20A3S1S0S32S13bS135A1S134A3S1S0S21S3dS136S3fA2S20A3S1S0S21S3dS134S3fA2S20A3S1S0S27S31A1MaS146S22S31S33S117Sc4A2S22S31S33S112Sc4A2S23S31A1MbA3A3A3S0GaS145S22S31S33S116Sc4A2S22S31S33S7cSc4A2GbA3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition O_rdsW (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S13S3Sd1A1S3Z0A1S3Z10000A1Vcs;S12A5").
Definition O_rdsZL (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S13S3Z0A1S3Sd1A1S3S1c2Sd1Z10000A2A1S11fVcs;A1S12A5").
Section QzPieces.
  Variable (cs : list cell) (Lf Qa Qb Qd : axst).
  Definition qz_facts : Prop := ltac2:(tb__ "0|5|
S1S0S28S32A1ScaVLf;S169A2S25S32VQa;A2A3S1S0S28S4A1Sc2S4SbS30VQa;A1M0A1U26M1A3S25S4Sa0Vcs;A1A2A3S1S0S6S183G0G1Sa2Vcs;A1A3S30VQb;A1M2A3S1S0S21S184G0G2A2S20A3S1S0S27S26S2S2A2A1S34VQb;A1M3S34VQa;A1A3S1S0S2S36VQb;A1S36VQa;A1A3S1S0S27S4A1SbG2A1S2aS4Se2VQb;A1M4S186S188S4S187S42A4A3A3S1S0S21S194S9G2A1S3fA2S20A3S1S0S21S19cS19bG3A2S20A3S1S0S32S199S35VQb;Sc5G2G4A2A2S19bA2VQd;A3S0S21S3dVQd;S3fA2S20A3A2A2A2A2A2A2A2A2A2A2").
End QzPieces.
Definition ZKa : axst := Eval vm_compute in ax_of (apply_axforms Ls0k XF_qz) Ls0k.  Definition ZKb : axst := Eval vm_compute in qz2 [] ZKa.
Definition ZHa : axst := Eval vm_compute in ax_of (apply_axforms Ls0h XF_qz) Ls0h.  Definition ZHb : axst := Eval vm_compute in qz2 hcZ ZHa.
Definition ZCa : axst := Eval vm_compute in ax_of (apply_axforms Lc0k XF_qz) Lc0k.  Definition ZCb : axst := Eval vm_compute in qz2 [] ZCa.
Lemma s0_contK : ltac2:(tb__ "0|0|
S1S6eS23SeA1S117SafSb0S12eA5S0S21Sc1S5SaSdS18bSd6S3Z0A1A3A1S8S30S117A1A1A3S20A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma s0_contH : ltac2:(tb__ "0|1|
S1S6eSecS116SadSaeS12dA5S1S0S21Sc1S5SaSdS18bSd2S3Z0A1A3M0A1S8S30S116A1A1A3S20A3S0S21Sc1S5SaSfG0A1A1S8S30S7cA1A1A3S20A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma s0_contZ : ltac2:(tb__ "0|0|
S1S6eS23SeA1S112SabSacS128A5S0S21Sc1S5SaSfSdS18bSd6S3Z0A1A3A1A1S8S30S112A1A1A3S20A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Z1k : sstate := Eval vm_compute in oget (cp_w1 (ax_S QZkf)) (ax_S QZkf).
Definition Z2k : sstate := Eval vm_compute in oget (cp_w2 Z1k) Z1k.
Definition Z3k : sstate := Eval vm_compute in oget (cz_b1 vRes0 Z2k) Z2k.
Definition Z4k : sstate := Eval vm_compute in cz_rsd vRes0 Z3k.
Definition Z5k : sstate := Eval vm_compute in oget (cp_s1 vRes0 Z4k) Z4k.
Definition Z6k : sstate := Eval vm_compute in set_obj_at Z5k (ibS Z5k (SLit 0) (SLit RS)) (O_rdsC vRes0 []).
Lemma czk_site : ltac2:(tb__ "0|e|
S1S0S21Sc3S5S10S9S30S12eA1A1A1S22S5ScSd6S3Z3A1A2S23S5A1A3A3S20A3S1S0S21S3dSfaS3fA2S20A3S1S0S28S6A1M0Sc8S30SfaA1M1U0M2S3N8f0A1A3S25S6S81A2A3S1S0G0Sc8S81G2S3N940A1A3S25S6S69A2A3S1S0G0Sc8S69Sd0S69Sb7S3Z0A1M3A3Sd6A3S25S6S4eA2A3S1S0S28S4A1M4Sc2S4SbS4eA1Sd0S4eSb7G3A3M5A3S25S4S13Sb7G3Sd6S23SeA1M6S12A5A2A3S1S0S6S183S4eG5S12cSd6A1A3S58A3S1S0S21S184S4eS58A2S20A3S1S0G0Sc8S58Sd0S58G3S3Sd1A1M7A3S198G7Sd6A2A3S25S6S4fA2A3S1S0G4Sc2S4SbS4fA1Sd0S4fG3G7A3M8A3S25S4Sd4Sd6G6A2A2A3S1S0S6S183S4fG8Se0Sd6G6A2A3S59A3S1S0S21S184S4fS59A2S20A3S1S0S21S46S37S59S34SfaA1M9S36SfaA1MaA3S22S26S2S2A2MbS24S2S2Sb7S3S19aA1McA4S23GbA1A3S41A3S20A3S1S0S32S37S44S59S41A2G9GaA3S103A3S1S0S21S3dS103S3fA2S20A3S1S0S21Sc1S5SaScSb7S3SbaA1A2A1S8G1A1MdA3S20A3S1S0S21Sc1S5SaScS3Z1000A1Sb7A2A1GdA3S20A3S1S0S3cS9S30S103A1A1S9G1A1A3S1S0S2S3aSfdPfA2Sb7A3S1S0S2S3aSfdP10A2GcA3S1S0S2S3aSfdP13A2G7A3S1S0S2S3aSfdP34A2S3Z10000A1A3S1S0S21S3dS163S3fA2S20A3S0S27S31A1S14aS22S31S33S129Sc4A2S23S31A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section BkzPieces.
  Variable (r : sv) (cs : list cell) (Lf Ba Bb Bc B : axst).
  Definition bkz_facts : Prop := ltac2:(tb__ "0|6|
S1S0S28S32A1M0ScaVLf;S166A2S25S32VBa;A2A3S1S0S28S4A1Sc2S4SbS30VBa;A1M1A1U27M2A3S25S4S13S3Sd1A1S3Z0A1Vr;Vcs;S12A5A2A3S1S0S6S183G1G2Sd4Vr;S11fVcs;A1A2A3S30VBb;A1M3A3S1S0S21S184G1G3A2S20A3S1S0S27S26S2S2A2A1S34VBb;A1S34VBa;A1A3S1S0S2S36VBb;A1S36VBa;A1A3S1S0G0ScaVBb;S167A2S25S32VBc;A2A3S1S0S27S4A1SbS30VBc;A1M4A1S2aS4Se2VBc;A1M5S186S188S4S187S41A4A3A3S1S0S21S194S9G4A1S3fA2S20A3S1S0S21S19cS19bS34VBc;A1A2S20A3S1S0S32S199S35VBc;Sc5G4G5A2A2S19bA2VB;A3S0S21Sc1S5SaScSb7S3SbaA1A2A1S8S30VLf;A1A1A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
End BkzPieces.
Definition BZKa : axst := Eval vm_compute in ax_of (apply_axforms LbZk XF_bkza) LbZk.
Definition BZKb : axst := Eval vm_compute in ax_setS BZKa (bkz2 vRes0 [] [] (ax_S BZKa)).
Definition BZKc : axst := Eval vm_compute in ax_of (apply_axforms BZKb XF_bkzb) BZKb.
Lemma czk_back : ltac2:(tb__ "0|4|
S1S6dSd6S23SeA1S129S92S93S94S101A7S1S0S21S3dS101S3fA2S20A3S1S0S2S3aSe4P18M0A2S7G0A1A3S1S0S2S3aSe4S172A2S7S172A1A3S1S0S2S3aSe4P2aA2Sd6A3S1S0S2S3aSe4P29A2S3S19aA1M1A3S1S0S21S193Se4S22S26S2S2A2M2S24S2S2Sb7G1A4S23G2A1M3A3S22G2S24S2S2Sb7Sb8A4G3A3A3S20A3S0S21S17bS8S30S101A1A1S17aSe4S40A2S5bA3S20A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Z1h : sstate := Eval vm_compute in oget (cp_w1 (ax_S QZhf)) (ax_S QZhf).
Definition Z2h : sstate := Eval vm_compute in oget (cp_w2 Z1h) Z1h.
Definition Z3h : sstate := Eval vm_compute in oget (cz_b1 vResH Z2h) Z2h.
Definition Z4h : sstate := Eval vm_compute in cz_rsd vResH Z3h.
Definition Z5h : sstate := Eval vm_compute in oget (czh_h1 Z4h) Z4h.
Definition Z6h : sstate := Eval vm_compute in oget (czh_h2 vResH Z5h) Z5h.
Definition Z7h : sstate := Eval vm_compute in oget (czh_h3 Z6h) Z6h.
Definition Z8h : sstate := Eval vm_compute in set_obj_at Z7h (ibS Z7h (SLit 0) (SLit RS)) (O_rdsC vResH hcZ).
Lemma czh_site' : ltac2:(tb__ "0|11|
S1S0S21Sc3S5S10S9S30S12dA1A1A1S22S5ScS3Z4M0A1Sd2A2S23S5A1A3A3S20A3S1S0S21S3dSf9S3fA2S20A3S1S0S28S6A1M1Sc8S30Sf9A1M2U0M3S3N8f0A1A3S25S6S80A2A3S1S0G1Sc8S80G3S3N940A1A3S25S6S68A2A3S1S0G1Sc8S68Sd0S68Sb7S3Z0A1M4A3Sd2A3S25S6S4dA2A3S1S0S28S4A1M5Sc2S4SbS4dA1Sd0S4dSb7G4A3M6A3S25S4S13Sb7G4Sd2S23SeA1S12A5A2A3S1S0S6S183S4dG6S12cSd2A1A3S57A3S1S0S21S184S4dS57A2S20A3S1S0G1Sc8S57Sd0S57G4S3Sd1A1M7A3S3S1c2Sd1G0A2A1M8A3S25S6S6aA2A3S1S0G1Sc8S6aSd0S6aG4G8A3S198G7Sd2A2A3S25S6S6bA2A3S1S0G1Sc9S6bSd0S6bG4G7A3A2S25S6S50A2A3S1S0G5Sc2S4SbS50A1Sd0S50G4G7A3M9A3S25S4Sd4Sd2S11fSecA1A2A2A3S1S0S6S183S50G9Se0Sd2SecA2A3S5aA3S1S0S21S184S50S5aA2S20A3S1S0S21S46S37S5aS34Sf9A1MaS36Sf9A1MbA3S22S26S2S2A2McS24S2S2Sb7S3S19aA1MdA4S23GcA1A3S41A3S20A3S1S0S32S37S44S5aS41A2GaGbA3S102A3S1S0S21S3dS102S3fA2S20A3S1S0S21Sc1S5SaScSb7S3SbaA1A2A1S8G2A1MeA3S20A3S1S0S21Sc1S5SaScS3Z1000A1Sb7A2A1GeA3S20A3S1S0S3cS9S30S102A1A1S9G2A1A3S1S0S2S3aSfcPfA2Sb7A3S1S0S2S3aSfcP10A2GdA3S1S0S2S3aSfcP13A2G7A3S1S0S2S3aSfcP34A2S3Z10000A1A3S1S0S27S31A1MfS15aS22S31S33S1d4Sc6A2S23S31A1M10A3A3S1S0S21S3dS162S3fA2S20A3S0GfS149S22S31S33S114Sc4A2S22S31S33S111Sc4A2G10A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition BZHa : axst := Eval vm_compute in ax_of (apply_axforms LbZh XF_bkza) LbZh.
Definition BZHb : axst := Eval vm_compute in ax_setS BZHa (bkz2 vResH hcD hcZ (ax_S BZHa)).
Definition BZHc : axst := Eval vm_compute in ax_of (apply_axforms BZHb XF_bkzb) BZHb.
Definition F_bkZh : list sprop := ltac2:(tb__ "0|0|
S22S5ScS198Sd2S3Z1A1A2S3S19aA1A2S23S5A1A3").
Lemma czh_back : ltac2:(tb__ "0|5|
S1S6dSd2SecS111S8fS90S91S100A7S1S0S21Sc1S5SaSfSdS18dSd2S3S19aA1M0A3A1A1S8S30S111A1A1A3S20A3S1S0S21Sc3S5S10S9S30S100A1A1A1S78A3S20A3S1S0S21S3dS1bcS78S100A2M1S3fA2S20A3S1S0S2S3aSdfP18M2A2S7G2A1A3S1S0S2S3aSdfS172A2S7S172A1A3S1S0S2S3aSdfP2aA2Sd2A3S1S0S2S3aSdfP29A2G0A3S1S0S2S3aSdfP2dA2S17S20Q20S7P64A1A3A3S1S0S21S193SdfS22S26S2S2A2M3S24S2S2Sb7G0A4S23G3A1M4A3S22G3S24S2S2Sb7Sb8A4G4A3A3S20A3S0S21S17bS8S30G1A1A1S17aSdfS40A2S5bA3S20A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition GZa : axst := Eval vm_compute in ax_of (apply_axforms LgZh XF_bkza) LgZh.
Definition GZb : axst := Eval vm_compute in ax_setS GZa (bkz2 vResH hcD hcZ (ax_S GZa)).
Definition GZc : axst := Eval vm_compute in ax_of (apply_axforms GZb XF_bkzb) GZb.
Lemma czh_grow : ltac2:(tb__ "0|9|
S1S6dSd2SecS114S9dS9eS9fS109A7S1S0S21Sc1S5SaSdS18dSd2S3S19aA1M0A3A1S8S30S114A1A1A3S20A3S1S0S28S26S27S26S2S2A2M1A1M2S27S5A1M3A2M4A1S185S30S109A1M5S30S10aA1M6A2S25G4S24G2G3S22G1S24S2S2Sd2G0A4S23G1A1M7A3S23S5A1A4A2A3S1S0S21S16G6A1S20A3S1S0S3cS9G6A1S9G5A1A3S1S0S32S35S109G6A2S10aA3S1S0S21S3dS10aS3fA2S20A3S1S0S2S3aSe3P18M8A2S7G8A1A3S1S0S2S3aSe3S172A2S7S172A1A3S1S0S2S3aSe3P29A2G0A3S1S0S2S3aSe3P2dA2S17S20Q20S7P64A1A3A3S1S0S21S193Se3S22G1S24S2S2Sb7G0A4G7A3S22G1S24S2S2Sb7Sb8A4G7A3A3S20A3S0S21S17bS8G6A1S17aSe3S40A2S5bA3S20A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ra0 : axst := Eval vm_compute in nthA R0c LV_R0 0.
Definition Rb0 : axst := Eval vm_compute in nthA R0c LV_R0 1.
Lemma head0_facts : ltac2:(tb__ "0|8|
S1S0S21S3dS15dS3eA2S20A3S1S0S27S31A1S142S22S31S33S54Sc4A2S22S31S33S65Sc4A2S23S31A1A3A3A3S1S0S21S3dS54S3eA2S20A3S1S0S21S3dS65S3eA2S20A3S1S0S21S38S54S12fScfA3S20A3S1S0S2S3aScfP18M0A2S7G0A1A3S1S0S2S3aScfS172A2S7S172A1A3S1S0S2S3aScfP2aM1A2S7G1A1A3S1S0S2S3aScfP29M2A2S7G2A1A3S1S0S2S3aScfP31A2S11S192Sb8Sb9A3M3A3S1S0S21S193ScfS22S26S2S2A2M4S24S2S2Sb7Sb8A4S23G4A1A3M5G5A3S20A3S1S0S21S17bS8S30S54A1A1M6S17aScfS40A2S40A3S20A3S1S0S21Sc1S5SaSdS18fG3S3Z10000A1A3M7A1G6A3S20A3S0S21Sc1S5SaSfG7A1A1S8S30S65A1A1A3S20A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition A0_rd0 : axst := errV E_rd0.
Definition A1_rd0 : axst := rd_w1 A0_rd0.
Definition A2_rd0 : axst := rd_w2 A1_rd0.
Definition A3_rd0 : axst := rd_s1 A2_rd0.
Definition A4_rd0 : axst := rd_rs A3_rd0.
Definition Lb0 : axst := Eval vm_compute in nthA R0c LV_T0k 0.
Lemma rd0_site : ltac2:(tb__ "0|9|
S1S0S21S3dS12fS3eA2S20A3S1S0S21S11eS123A1S20A3S1S0S28S6A1M0Sc8S30S83A1U0M1S3N8d0A1A3S25S6S30S88A1M2A2A3S1S0G0Sc8G2G1S3N920A1A3S25S6S30S70A1M3A2A3S1S0G0Sc8G3SedS70A1S198S3Sd1A1SceA2A3S25S6S30S73A1M4A2A3S1S0S28S4A1Sc2S4SbG4A1SedS73A1M5A3S25S4Sd4SceS23SeA1M6A2A2A3S1S0S6S183G4G5Se0SceG6A2A3S30S5fA1M7A3S1S0S21S184G4G7A2S20A3S1S0S21S46S5fS22S26S2S2A2M8S24S2S2Sb7Sb8A4S23G8A1A3S42A3S20A3S1S0S32S35S5fS44G7S42A2A2S104A3S1S0S21S3dS104S3eA2S20A3S0S21Sc1S5SaScSceS3Z10000A1A2A1S8S30S123A1A1A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma rd0_call : ltac2:(tb__ "0|5|
S1S0S2S3aSe5P13A2SceA3S1S0S2S3aSe5P11A2S3Z0A1M0A3S1S0S2S3aSe5PfA2S3Sd1A1A3S1S0S2S3aSe5P10A2S3Z10000A1A3S1S0S21S2bS2bS2dS19dP64M1S9S30S1b7A1A1M2A2A1S1baSe5G1A2A2S19dG1S9S30S104A1A1M3A2A2S20A3S1S0S2S3aS1b9Se5G2S30S1b6S23SeA1G1A2A1M4G3A4G1A2Sd3A3S1S0S21S1b2S19eG1A1S19eS9G4A1A1A2S20A3S1S0S21S3dS164S3eA2S20A3S1S0S27S31A1S147S22S31S33S7bSc4A2S22S31S33Se9Sc4A2S23S31A1A3A3A3S0S21Sc1S5SaSdS18bSd3G0A3A1S8S30S7bA1A1A3S20A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition H0a : axst := ltac2:(tb__ "0|0|
SdaScaSe9Se1A2Se9A2").
Definition H0b : axst := q2 vWant H0a.
Definition H0c : axst := ltac2:(tb__ "0|0|
SdaScaS51S22ScbSccU26A1S23ScbA1A3A2S51A2").
Lemma rd0_close : ltac2:(tb__ "0|8|
S1S0S28S32A1M0ScaSe9Se1A2S25S32S79A2A3S1S0S28S4A1Sc2S4SbS30S79A1M1A1U26M2A3S25S4Sf8SceS23SeA1M3A2A2A3S1S0S6S183G1G2Sd4SceG3A2A3S30S51A1M4A3S1S0S21S184G1G4A2S20A3S1S0G0ScaS51S22ScbSccG2A1S23ScbA1A3A2S25S32S49A2A3S1S0S27S4A1SbS30S49A1M5A1S2aS4Se2S49A1M6S186S188S4S187S42A4A3A3S1S0S21S194S9G5A1S3eA2S20A3S1S0S21S19cSd7S34S49A1A2S20A3S1S0S32S199S35S49Sc5G5G6A2A2Sd7A2S10fA3S1S0S21S3dS10fS3eA2S20A3S1S0S21Sc1S5SaSfSdS18bSd3S3Z0A1A3A1A1S8S30Se9A1A1M7A3S20A3S0S21Sc1S5SaScSceS3Z10000A1A2A1G7A3S20A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
