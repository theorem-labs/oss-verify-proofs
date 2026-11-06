(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "bool"; "prod"; "option"; "nil"; "andb"; "false"; "list"; "nat"; "negb"; "true"; "None"; "Some"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "edescA"; "ANone"; "NDA"; "ND"; "eda_rank"; "eda_state"; "eda_var"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "eda_nd"; "fr_sub_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "SLit"; "SPUlt"; "ss_facts"; "ss_next"; "sv_below"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "z0"; "VL"; "VR"; "ndG"; "ndLL"; "ndGF"; "ndTS"; "ndRP"; "ndTR"; "ndL4"; "ndFV"; "ndL4a"; "ndL4b"; "ndL4f"; "ndMI"; "VK3"; "ndP"; "NDS"; "TGT"; "cutsF"; "ndH"; "ndJN"; "ndL4c"; "ndMM"; "ndT"; "ndTRf"; "cutpcs_hfF"; "edge_dbg"; "ndEf'"; "ndEo'"; "ndFVf"; "ndJ"; "ndL4af"; "ndL4bf"; "ndL4cf"; "ndL4d"; "ndL4df"; "ndMIf"; "ndMMf"; "ndRPf"; "ndSG"; "ndSGf"; "ndTSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pDco"; "pKco"; "sg_k"; "sg_d"; "ts_k"; "mm_k"; "pQ"; "ts_d"; "mm_d"; "rp_k"; "fv_k"; "rp_d"; "fv_d"; "tr_k"; "mi_k"; "tr_d"; "mi_d"; "ndR"; "fr_hf"; "ndL"; "cVF"; "nd0"; "pA"; "pP"; "tv_hf"; "C_pre"; "C_pro"; "E_co0"; "E_ms0"; "E_sm0"; "FUEL_hf"; "H"; "JF_co"; "JR_co"; "K"; "L1"; "L2"; "Pre_hf"; "X_pro"; "am1"; "am2"; "bd_hf"; "co_k"; "co_n"; "fv_n"; "mi_n"; "mm_n"; "ndFc"; "pT0"; "rp_n"; "sg_n"; "tr_n"; "ts_n"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "ndXA"; "pDmi"; "pKmi"; "ndEf"; "ndEo"; "pDfv"; "pKfv"; "bd_face"; "pX"; "qCUR"; "tvQ"; "C36"; "E_dg0"; "E_fv0"; "E_mc0"; "E_mi0"; "E_mm0"; "JF_fv"; "JF_mi"; "JR_fv"; "JR_mi"; "RJ"; "RW"; "T_dg"; "T_mcq"; "XA"; "pR"; "qA"; "qKco"; "qKfv"; "qKmi"; "qKmm"; "qKrp"; "qKsg"; "qKtr"; "qKts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "E_tdg0"; "E_trb0"; "E_trg0"; "JF_trb"; "JF_trg"; "JR_trb"; "JR_trg"; "K1"; "K1Xb"; "K1Xg"; "K2"; "T_tdg"; "pI"; "pT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "pDm4"; "pKm4"; "pDf4"; "pKf4"; "pDn4"; "pKn4"; "pDs4"; "pKs4"; "E_c4_0"; "E_fv4_0"; "E_m4_0"; "E_mi4_0"; "JF_fv4"; "JF_mi4"; "JR_fv4"; "JR_mi4"; "T_c4"; "T_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "lDsg"; "lKsg"; "lDmm"; "lKmm"; "lDfv"; "lKfv"; "E_g1_0"; "E_g2_0"; "E_g3_0"; "L14"; "T_g1"; "T_g2"; "T_g3"; "XLJ"; "lDmi"; "lKmi"; "pL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "kb"; "PROG"; "av_d"; "av_k"; "tE"; "tI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3"; "pDmm"; "pKmm"; "pDsg"; "pKsg"; "E_sg0"; "JF_mm"; "JF_sg"; "JR_mm"; "JR_sg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDrp"; "pKrp"; "pDts"; "pKts"; "E_rp0"; "E_ts0"; "JF_rp"; "JF_ts"; "JR_rp"; "JR_ts"; "K3"; "K3m"; "K3x"; "TS"; "pG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem";
"bd_subst"; "bud_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "qDrp'"; "qDts'"; "qKrp'"; "qKts'"; "E_wdg0"; "J"; "T_pgiR"; "T_pgoR"; "T_wdg"; "XJ"; "pNT"; "@Stdlib.Lists.List"; "nth_error"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "ea_leaf"; "ea_src"; "ea_sub"; "ea_tgt"; "leaf_matchesA"; "leaf_refuted"; "leaves_edgesA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "C_Ef2"; "C_Eo2"; "C_rlf"; "C_rlo"; "E_f5f0"; "E_f5o0"; "P_fail"; "P_ok"; "T_f5f"; "T_f5o"; "XEf42"; "XEo42"; "X_rlf"; "X_rlo"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "E_da0"; "E_pc0"; "T_da"; "T_ms"; "T_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "E_md0"; "E_pg0"; "T_md"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "E_mm4_0"; "E_sg4_0"; "JF_mm4"; "JF_sg4"; "JR_mm4"; "JR_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA"; "ejcert_hdr"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ndG (dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : ndesc := ltac2:(tb__ "0|0|
S12S70SeaSebVdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;Vdco;Vkco;Vdrp;Vkrp;Vdtr;Vktr;Vdts;Vkts;A12S6aS95S96S6eVkmi;Vkfv;Vkmm;Vksg;Vkco;Vkrp;Vktr;Vkts;AaS11A4").

Definition ndGF (dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : ndesc := ltac2:(tb__ "0|0|
S12S70SeaSebVdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;Vdco;Vkco;Vdrp;Vkrp;Vdtr;Vktr;Vdts;Vkts;A12S6aS1S106Se9S6cS96A2S5S106A1A3S11A4").

Definition ndP : ndesc := ltac2:(tb__ "0|0|
S12S8dS6aS81SedS85S66S84S62S86S5dS8aS5aS83S82S89S61S8bS65S8cS5cA11S11A4").
Definition ndH : ndesc := ltac2:(tb__ "0|0|
S6bS6fS58S59A3").
Definition ndT : ndesc := ltac2:(tb__ "0|0|
S6bS88S58S59A3").
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S6bS5eS58S59A3").

Definition ndMI : ndesc := ltac2:(tb__ "0|0|
S30S8fS90S64S62S60S5dS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndMIf : ndesc := ltac2:(tb__ "0|0|
S32S8fS90S64S62S60S5dS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndFV : ndesc := ltac2:(tb__ "0|0|
S30S8fS90S93S94S60S5dS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndFVf : ndesc := ltac2:(tb__ "0|0|
S32S8fS90S93S94S60S5dS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndMM : ndesc := ltac2:(tb__ "0|0|
S30S8fS90S93S94SeeSefS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndMMf : ndesc := ltac2:(tb__ "0|0|
S32S8fS90S93S94SeeSefS5bS5aS58S59S63S61S67S65S5fS5cA10").
Definition ndSG : ndesc := ltac2:(tb__ "0|0|
S30S8fS90S93S94SeeSefSf0Sf1S58S59S63S61S67S65S5fS5cA10").
Definition ndSGf : ndesc := ltac2:(tb__ "0|0|
S32S8fS90S93S94SeeSefSf0Sf1S58S59S63S61S67S65S5fS5cA10").

Definition ndTR : ndesc := ltac2:(tb__ "0|0|
S30S68S66S64S62S60S5dS5bS5aS58S59S63S61Sb2Sb3S5fS5cA10").
Definition ndTRf : ndesc := ltac2:(tb__ "0|0|
S32S68S66S64S62S60S5dS5bS5aS58S59S63S61Sb2Sb3S5fS5cA10").
Definition ndRP : ndesc := ltac2:(tb__ "0|0|
S30S68S66S64S62S60S5dS5bS5aS58S59Sf7Sf8Sb2Sb3S5fS5cA10").
Definition ndRPf : ndesc := ltac2:(tb__ "0|0|
S32S68S66S64S62S60S5dS5bS5aS58S59Sf7Sf8Sb2Sb3S5fS5cA10").
Definition ndTS : ndesc := ltac2:(tb__ "0|0|
S30S68S66S64S62S60S5dS5bS5aS58S59Sf7Sf8Sb2Sb3Sf9SfaA10").
Definition ndTSf : ndesc := ltac2:(tb__ "0|0|
S32S68S66S64S62S60S5dS5bS5aS58S59Sf7Sf8Sb2Sb3Sf9SfaA10").
Definition ndJN : ndesc := ltac2:(tb__ "0|0|
S30S68S66S64S62S60S5dS5bS5aS58S59S109S10bSb2Sb3S10aS10cA10").

Definition ndL4 (dmi kmi dfv kfv dmm kmm dsg ksg : sv) : ndesc := ltac2:(tb__ "0|0|
S30Vdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;S58S59S109S10bSb2Sb3S10aS10cA10").
Definition ndL4f (dmi kmi dfv kfv dmm kmm dsg ksg : sv) : ndesc := ltac2:(tb__ "0|0|
S32Vdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;S58S59S109S10bSb2Sb3S10aS10cA10").
Definition ndLL : ndesc := ltac2:(tb__ "0|0|
S36Se2Se3Sd8Sd9Sd6Sd7Sd4Sd5A8").
Definition ndL4a : ndesc := ltac2:(tb__ "0|0|
S36Sc2Sc3Sd8Sd9Sd6Sd7Sd4Sd5A8").
Definition ndL4af : ndesc := ltac2:(tb__ "0|0|
S3aSc2Sc3Sd8Sd9Sd6Sd7Sd4Sd5A8").
Definition ndL4b : ndesc := ltac2:(tb__ "0|0|
S36Sc2Sc3Sc4Sc5Sd6Sd7Sd4Sd5A8").
Definition ndL4bf : ndesc := ltac2:(tb__ "0|0|
S3aSc2Sc3Sc4Sc5Sd6Sd7Sd4Sd5A8").
Definition ndL4c : ndesc := ltac2:(tb__ "0|0|
S36Sc2Sc3Sc4Sc5Sc6Sc7Sd4Sd5A8").
Definition ndL4cf : ndesc := ltac2:(tb__ "0|0|
S3aSc2Sc3Sc4Sc5Sc6Sc7Sd4Sd5A8").
Definition ndL4d : ndesc := ltac2:(tb__ "0|0|
S36Sc2Sc3Sc4Sc5Sc6Sc7Sc8Sc9A8").
Definition ndL4df : ndesc := ltac2:(tb__ "0|0|
S3aSc2Sc3Sc4Sc5Sc6Sc7Sc8Sc9A8").

Definition ndEo' : ndesc := ltac2:(tb__ "0|0|
S13S98S5S3S3S25S2cA2S25A2A1S95S97Sa9SacSabSadSafSaaSaeSb0Sb1AaA3").
Definition ndEf' : ndesc := ltac2:(tb__ "0|0|
S13S98S5S3S3S25S2cA2S25A2A1S1S106Se9S6cS97A2S5S106A1A3A3").

Definition z0 : sv := SLit 0.
Definition VR (cur : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S26Se6Se8Z40S26Se5SecVcur;A3A2S27Vpos;A1A3").
Definition VL (pos : Z) : sv := ltac2:(tb__ "0|0|
S26Se6Se8Z40S26Se5S113Se4A3A2S27Vpos;A1A3").
Definition VK3 (pos : Z) : sv := ltac2:(tb__ "0|0|
S26Se6Se8Z4S26Se5S6eS105A3A2S27Vpos;A1A3").

Definition cutsF : list edescA := ltac2:(tb__ "0|1d|
S1S3S3S20SfA2M0S3S2cS25A2M1A2M2S0G0G1S0S20SfS7dS6dA4S0S2cS25Z64S2dA4A4S1G2S0G0G1S0S20SfS72S3dA4S0S2cS25Z60S2dA4A4S1G2S0G0G1S0S20SfS71S3dA4S0S2cS25Z5cS2dA4A4S1G2S0G0G1S0S20SfS77S41A4S0S2cS25Z50M3S2fS6fZ2M4A2A4A4S1G2S0G0G1S0S20SfS7bS41A4S0S2cS25G3S2fS5eZ1M5A2A4A4S1G2S0G0G1S0S20SfS7cS45A4S0S2cS25G3S2fS5eZ0M6A2A4A4S1G2S0G0G1S0S20SfS7aS45A4S0S2cS25G3S2fS5eZ3cM7A2A4A4S1G2S0G0G1S0S20SfS79S69A4S0S2cS25G3S2fS5eZ3aM8A2A4A4S1G2S0G0G1S0S20SfS78S87A4S0S2cS25Z1eS2dA4A4S1G2S0G0G1S0S20SfS134S69A4S0S2cS25G3S2fS5eZ38M9A2A4A4S1G2S0G0G1S0S20SfS135S69A4S0S2cS25G3S2fS5eZ36MaA2A4A4S1G2S0G0G1S0S20SfS133S69A4S0S2cS25G3S2fS5eZ34MbA2A4A4S1G2S0G0G1S0S20SfSa7S8eA4S0S2cS25Z46S2dA4A4S1G2S0G0G1S0S20SfSa5S8eA4S0S2cS25Z44S2dA4A4S1G2S0G0G1S0S20SfSa4S8eA4S0S2cS25Z42McS2dA4A4S1G2S0G0G1S0S20SfSa2S3bA4S0S2cS25Z40S2dA4MdA4S1G2S0G0G1S0S20SfSa0S52A4S0S2cS25Z14S2dA4MeA4S1G2S0G0G1S0S20SfS99S3bA4S0S2cS25Z3eMfSa8A4A4S1G2S0G0G1S0S20SfSa3S3bA4S0S2cS25G7S2dA4M10A4S1G2S0G0G1S0S20SfSa1S37A4S0S2cS25G8S2dA4A4S1G2S0G0G1S0S20SfS9fS4bA4GeA4S1G2S0G0G1S0S20SfSa6S37A4S0S2cS25G9S2dA4M11A4S1G2S0G0G1S0S20SfSf5S44A4S0S2cS25GaS2dA4M12A4S1G2S0G0G1S0S20SfSf3S53A4GeA4S1G2S0G0G1S0S20SfSf6S55A4S0S2cS25GbS2dA4M13A4S1G2S0G0G1S0S20SfSf4S56A4GeA4S1G2S0G0G1S0S20SfSbbS8eA4S0S2cS25GcS26Se5S7fSc0A3A4A4S1G2S0G0G1S0S20SfSbdS8eA4GdA4S1G2S0G0G1S0S20SfSbcS8eA4GdA4S1G2S0G0G1S0S20SfSbaS35A4S0S2cS25GfS2dA4M14A4S1G2S0G0G1S0S20SfSb8S46A4GeA4S1G2S0G0G1S0S20SfSb9S35A4G14A4S1G2S0G0G1S0S20SfSb7S46A4GeA4S1G2S0G0G1S0S20SfSbfS35A4G10A4S1G2S0G0G1S0S20SfSbeS35A4S0S2cS25G8S26Se5S80Sc1A3A4A4S1G2S0G0G1S0S20SfSffS34A4G10A4S1G2S0G0G1S0S20SfSfdS54A4GeA4S1G2S0G0G1S0S20SfS101S34A4S0S2cS25G8S3cG4A1A4A4S1G2S0G0G1S0S20SfS102S34A4S0S2cS25G8S3cG5A1A4A4S1G2S0G0G1S0S20SfS103S34A4S0S2cS25G8S3cG6A1A4A4S1G2S0G0G1S0S20SfS104S34A4G11A4S1G2S0G0G1S0S20SfS100S33A4G12A4S1G2S0G0G1S0S20SfSfeS57A4GeA4S1G2S0G0G1S0S20SfS13bS33A4G13A4S1G2S0G0G1S0S20SfS110S33A4S0S2cS25Z32M15S2dA4M16A4S1G2S0G0G1S0S20SfS10fS33A4G16A4S1G2S0G0G1S0S20SfS111S33A4S0S2cS25Z30M17S2dA4A4S1G2S0G0G1S0S20SfS10eS42A4S0S2cS25Z2eM18S2dA4A4S1G2S0G0G1S0S20SfSddS31A4S0S2cS25Z28M19S2eG7A1A4A4S1G2S0G0G1S0S20SfSdeS31A4S0S2cS25G19S2eG8A1A4A4S1G2S0G0G1S0S20SfSdfS31A4S0S2cS25G19S2eG9A1A4A4S1G2S0G0G1S0S20SfSe0S31A4S0S2cS25G19S2eGaA1A4A4S1G2S0G0G1S0S20SfSd1S38A4S0S2cS25G19S2eGbA1A4A4S1G2S0G0G1S0S20SfScfS4dA4GeA4S1G2S0G0G1S0S20SfSd2S38A4S0S2cS25G19S2eG15A1A4A4S1G2S0G0G1S0S20SfSd0S39A4S0S2cS25G19S2eG17A1A4A4S1G2S0G0G1S0S20SfSceS4eA4GeA4S1G2S0G0G1S0S20SfSd3S39A4S0S2cS25G19S2eG18A1A4A4S1G2S0G0G1S0S20SfS140S43A4S0S2cS25G19S2eZ2cA1A4A4S1G2S0G0G1S0S20SfS13eS4fA4GeA4S1G2S0G0G1S0S20SfS141S50A4S0S2cS25G19S2eZ2aA1A4A4S1G2S0G0G1S0S20SfS13fS51A4GeA4S1G2S0G0G1S0S20SfS121S91A4S0S2cS25ZeS2dA4M1aA4S1G2S0G0G1S0S20SfS122S92A4G1aA4S1G2S0G0G1S0S20SfS129S91A4S0S2cS25ZcS2dA4M1bA4S1G2S0G0G1S0S20SfS12aS92A4G1bA4S1G2S0G0G1S0S20SfS123S49A4S0S2cS25ZaS2dA4M1cA4S1G2S0G0G1S0S20SfS124S4aA4G1cA4S5G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition exitsF : list edescA := ltac2:(tb__ "0|15|
S1S3S3S20SfA2M0S3S2cS25A2M1A2M2S0G0G1S0S20SfS75S6dA4S0S2cS25Z62S2dA4A4S1G2S0G0G1S0S20SfS7eS3dA4S0S2cS25Z5eS2dA4A4S1G2S0G0G1S0S20SfS73S4cA4S0S2cS25Z50M3S2fS5eZ3bM4A2A4A4S1G2S0G0G1S0S20SfS74S69A4S0S2cS25G3S2fS5eZ39M5A2A4A4S1G2S0G0G1S0S20SfS132S69A4S0S2cS25G3S2fS5eZ37M6A2A4A4S1G2S0G0G1S0S20SfS131S69A4S0S2cS25G3S2fS5eZ35M7A2A4A4S1G2S0G0G1S0S20SfS9aS8eA4S0S2cS25Z45S2dA4A4S1G2S0G0G1S0S20SfS9dS8eA4S0S2cS25Z41S2dA4A4S1G2S0G0G1S0S20SfS9bS3bA4S0S2cS25G4S2dA4A4S1G2S0G0G1S0S20SfS9cS37A4S0S2cS25G5S2dA4A4S1G2S0G0G1S0S20SfS9eS37A4S0S2cS25G6S2dA4M8A4S1G2S0G0G1S0S20SfSf2S44A4S0S2cS25G7S2dA4M9A4S1G2S0G0G1S0S20SfS12bS91A4S0S2cS25Z10S2dA4MaA4S1G2S0G0G1S0S20SfS12cS92A4GaA4S1G2S0G0G1S0S20SfSb6S8eA4S0S2cS25Z3fS2dA4MbA4S1G2S0G0G1S0S20SfSb5S8eA4GbA4S1G2S0G0G1S0S20SfSb4S35A4S0S2cS25Z3dS2dA4McA4S1G2S0G0G1S0S20SfSfbS35A4GcA4S1G2S0G0G1S0S20SfSfcS34A4G8A4S1G2S0G0G1S0S20SfS139S33A4G9A4S1G2S0G0G1S0S20SfS13aS33A4S0S2cS25Z33MdS2dA4A4S1G2S0G0G1S0S20SfS10dS33A4S0S2cS25Z31MeS2dA4A4S1G2S0G0G1S0S20SfS112S42A4S0S2cS25Z2fMfS2dA4A4S1G2S0G0G1S0S20SfSe1S31A4S0S2cS25Z2dM10S2dA4A4S1G2S0G0G1S0S20SfSdaS31A4S0S2cS25Z28M11S2eG4A1A4A4S1G2S0G0G1S0S20SfSdbS31A4S0S2cS25G11S2eG5A1A4A4S1G2S0G0G1S0S20SfSdcS31A4S0S2cS25G11S2eG6A1A4A4S1G2S0G0G1S0S20SfScdS31A4S0S2cS25G11S2eG7A1A4A4S1G2S0G0G1S0S20SfScaS38A4S0S2cS25G11S2eGdA1A4A4S1G2S0G0G1S0S20SfScbS38A4S0S2cS25G11S2eGeA1A4A4S1G2S0G0G1S0S20SfSccS39A4S0S2cS25G11S2eGfA1A4A4S1G2S0G0G1S0S20SfS13cS39A4S0S2cS25G11S2eG10A1A4A4S1G2S0G0G1S0S20SfS13dS43A4S0S2cS25G11S2eZ2bA1A4A4S1G2S0G0G1S0S20SfS136S91A4GaA4S1G2S0G0G1S0S20SfS137S91A4GaA4S1G2S0G0G1S0S20SfS138S92A4GaA4S1G2S0G0G1S0S20SfS125S91A4S0S2cS25ZdS2dA4M12A4S1G2S0G0G1S0S20SfS126S92A4G12A4S1G2S0G0G1S0S20SfS12dS91A4S0S2cS25ZbS2dA4M13A4S1G2S0G0G1S0S20SfS12eS92A4G13A4S1G2S0G0G1S0S20SfS127S12fA4S0S2cS25Z0S2dA4M14A4S1G2S0G0G1S0S20SfS128S130A4G14A4S5G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Goal (length cutsF = 68%nat) /\ (length exitsF = 42%nat). Proof. split; reflexivity. Qed.
Lemma hdr_ok : ltac2:(tb__ "0|0|
S11eS2S148Se7S40A2SbA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cutpcs_hfF : list Z := cutpcs_hf5.
Definition TGT : list axst := etargets cutsF exitsF.
Definition NDS : list edescA := cutsF ++ exitsF.
Definition edge_dbg (e : edgeA) : nat * (bool * bool * bool * bool * bool * bool) := ltac2:(tb__ "0|e|
S4S10A1S3S9S3S3S3S3S3S2S2A2M0S2A2M1S2A2M2S2A2M3S2A2M4A2Lx;M5S114S10S3eS118Ve;A1A3S10G5S114S10S3eS11aVe;A1M6A3S10S1dR2A1M7SfG7SfS119Ve;A1S143S15R5A1S20S0S9G4G6S0G3S2S0G2S2S0G1S2S0G0S2S0S2S2S6S6S144R2Se7A2S14aSe7S2aS22R1A1A1M8A2A2S1fG8R4A2A2S147R2S1aR4A1S1aR3A1A3A4S1eR2S19R4A1S19R3A1A3A4S108S29S22S117Ve;A1A1A1M9S107R2S18R3A1A2S18R4A1A3A4S1bS1cR2S17R3A1A2S17R4A1A2A4S6S6S2bG8S16R6A1MaA2S14cZ0S14R5A1MbA2A2SeS14dGbS14R6A1McA2S6S14bGbGcA2S145G9S28S142R2S16R5A1A2GaA2A2A2A2A2A4A4TTi;Ts;Tndj;Tndi;Lnj;S0S9G4G6S0G3S2S0G2S2S0G1S2S0G0S2S0S2S2S7S7A4S7A4S7A4S7A4S7A4A4MdX4x2Lni;GdX4x2").
Definition cut_dbg (i : nat) : option (list (nat * (bool * bool * bool * bool * bool * bool))) * list (Z * stop_reason) := ltac2:(tb__ "0|c|
S4S10A1S3S4S8S3S9S3S3S3S3S3S2S2A2S2A2S2A2S2A2S2A2A2M0A1M1A1M2S8S3S2cS146A2M3A1M4A2M5Lx;S114S10S40Vi;A3S10S4S8S21A1M6A1G5Lx;S24S11fS76S47S15R1A1SbA5G6S0G2G4S4S8S116A1M7A1G2Lx;S11dSe7Vi;R1S3fA4G7SdG1S115S116G0S48R1A4A2Les;ScG1A1M8X4x2S115S21G3S120S14eS21G6S150S21A1S21S149S6SaS11cS23R1A1M9A1A1SaS11bSe7G9S3fA3A1A2MaA1LL;S21S14fGaA1Lx;R1A6A4A4Lleaves;S0G2G4G8S5G3A1A4MbX4x2Ln;GbX4x2").
