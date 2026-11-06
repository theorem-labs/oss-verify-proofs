(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "None"; "false"; "list"; "option"; "S"; "fst"; "length"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "SLit"; "sobj"; "SPUle"; "SAlu"; "SVar"; "SPUlt"; "mkObj"; "DUnknown"; "FcsrFrm0"; "mkSS"; "SPAlign"; "ss_objs"; "SPBranch"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "B32"; "vDp"; "spm"; "B_EW"; "two47"; "two40"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "tI"; "bd_vec"; "hF"; "O_data"; "V"; "tp"; "av_k"; "av_d"; "tE"; "vec_facts"; "hFL"; "PROG"; "O_cE"; "O_cP"; "av_nv"; "hG"; "tB"; "tL"; "xHASPRIM"; "HNEXT"; "NPH"; "O_text"; "P_cur"; "P_hdr"; "V120"; "av_c"; "avt_d"; "avt_k"; "h_fregs"; "h_xregs"; "handle_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "BI"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pQ"; "xbo"; "pA"; "room_r"; "fv_k"; "mi_k"; "mm_k"; "pT0"; "rp_k"; "sg_k"; "tr_k"; "ts_k"; "fv_d"; "mi_d"; "mm_d"; "pK2"; "rp_d"; "sg_d"; "tr_d"; "ts_d"; "pD2"; "co_k"; "co_d"; "fv_c"; "fv_n"; "mi_c"; "mi_n"; "mm_c"; "mm_n"; "pP"; "sg_c"; "sg_n"; "xfo"; "HC"; "co_n"; "lregsH"; "rp_n"; "shC"; "tr_n"; "ts_n"; "vec_facts0"; "BCUT"; "FUEL_hf"; "NCO"; "body_facts"; "cVF"; "cutpcs_hf"; "pDco"; "pKco"; "O_F"; "O_Wf"; "V496"; "V528"; "V560"; "V592"; "V752e"; "V784e"; "V816"; "X_body"; "X_hf"; "am1"; "am2"; "builderF"; "cA"; "cR"; "datasF"; "fr_hf"; "gB"; "gC"; "hf_facts"; "lregs0"; "lregsR"; "pHP"; "shB"; "tv_body"; "tv_hf"; "BAD"; "BANK"; "BIG"; "E_co"; "E_ms"; "E_sm0"; "F_cells"; "MAGIC3"; "O_flag"; "O_frame"; "P_caps"; "P_matf"; "Pre_ms"; "Pre_sm"; "T_cok"; "V216t"; "V720"; "V720e"; "avt_cnt"; "avt_t"; "bd_hf"; "bd_loop"; "cB"; "datas0"; "frame_factsF"; "ghostF_facts"; "hdr3"; "hf_cnt_facts"; "hf_room"; "hf_vecs"; "ndL"; "objs_body"; "objs_hf0"; "pairs7"; "pairs7e"; "prog_factF"; "sel_back"; "shF"; "slot"; "slot_facts"; "tv0"; "xMAT"; "xSMO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXSplit"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "FE"; "leafA"; "ax_setS"; "sym_runA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "piece"; "vb"; "vc"; "O_al"; "c4"; "vERR"; "vNC"; "P_alloc"; "P_st"; "V184"; "c1"; "vAL"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "FR"; "DW"; "hf_H"; "hf_K"; "hf_L1"; "hf_L2"; "f5_pc"; "hf_A"; "hf_C36"; "hf_EPI"; "hf_J"; "hf_K1"; "hf_K1X"; "hf_K2"; "hf_K3"; "hf_K3m"; "hf_L14"; "hf_REL"; "hf_RJ"; "hf_RW"; "hf_TS"; "hf_entry"; "memcpy_pc"; "memset_pc"; "pg_pc"; "sm3_pc"; "vr_ret_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "A_globals"; "leavesA_at"; "mkA"; "shb"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "@Stdlib.Lists.List"; "filter"; "flat_map"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN. End VN.
Module PG. Include Lib_tess_polygon_states. End PG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HFAddr.
  Definition hf_entry : Z := 0x9e888.
  Definition sm3_pc : Z := 0x47da8.
  Definition memset_pc : Z := 0x5cce8.
  Definition memcpy_pc : Z := 0x5c84c.
  Definition f5_pc : Z := 0x60390.
  Definition tss_pc : Z := 0xac5c0.
  Definition pg_pc : Z := 0xac5f4.
  Definition hf_H : Z := 0x9eb1c.
  Definition hf_L1 : Z := 0x9eb60.
  Definition hf_L2 : Z := 0x9ebcc.
  Definition hf_K : Z := 0x9ebf8.
  Definition hf_B : Z := 0x9eb00.
  Definition hf_A : Z := 0x9eef4.
  Definition hf_F2 : Z := 0x9eeb8.
  Definition hf_F7 : Z := 0x9ef64.
  Definition hf_RW : Z := 0x9f1bc.
  Definition hf_K1 : Z := 0x9f278.
  Definition hf_K2 : Z := 0x9f3c0.
  Definition hf_K3 : Z := 0x9f5e4.
  Definition hf_K3m : Z := 0x9f608.
  Definition hf_J : Z := 0x9f8cc.
  Definition hf_L14 : Z := 0x9f9e0.
  Definition hf_C36 : Z := 0x9ffc8.
  Definition hf_RJ : Z := 0xa0024.
  Definition hf_K1X : Z := 0x9f2c8.
  Definition hf_TS : Z := 0x9f75c.
  Definition hf_C4a : Z := 0xa01a4.
  Definition hf_C4b : Z := 0xa02b8.
  Definition hf_T4a : Z := 0x9fce0.
  Definition hf_T4b : Z := 0x9fdf0.
  Definition hf_EPI : Z := 0x9f0b0.
  Definition hf_REL : Z := 0x9f17c.
  Definition hf_ret : Z := 0xa07ec.
  Definition vr_ret_hf : Z := 0x9ec74.
  Definition DW : Z := 4704.
  Definition FR : Z := 352.
End HFAddr.
Import HFAddr.

Definition FUEL_hf : nat := 600%nat.

Definition cVF : Z := 768.

Definition mi_d : sv := SVar 100. Definition mi_c : sv := SVar 101. Definition mi_k : sv := SVar 102.
Definition fv_d : sv := SVar 103. Definition fv_c : sv := SVar 104. Definition fv_k : sv := SVar 105.
Definition mm_d : sv := SVar 106. Definition mm_c : sv := SVar 107. Definition mm_k : sv := SVar 113.
Definition sg_d : sv := SVar 114. Definition sg_c : sv := SVar 115. Definition sg_k : sv := SVar 120.
Definition co_d : sv := SVar 121. Definition co_k : sv := SVar 122. Definition co_n : sv := SVar 129.
Definition rp_d : sv := SVar 130. Definition rp_k : sv := SVar 131. Definition rp_n : sv := SVar 132.
Definition tr_d : sv := SVar 133. Definition tr_k : sv := SVar 134. Definition tr_n : sv := SVar 135.
Definition ts_d : sv := SVar 136. Definition ts_k : sv := SVar 137. Definition ts_n : sv := SVar 138.

Definition mi_n : sv := SVar 141. Definition fv_n : sv := SVar 142. Definition mm_n : sv := SVar 143. Definition sg_n : sv := SVar 149.

Definition xMAT : sv := SVar 139. Definition xSMO : sv := SVar 140.
Definition avt_t : sv := SVar 119.
Definition avt_cnt : sv := SAlu ALU_SLL avt_t (SLit 1).

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S16PaA1S12Sd8Se9A1A1S12Z0A1Vcells;S19A5").
Definition O_Wf : sobj := ltac2:(tb__ "0|0|
S18S27Se9A1S26S12Z0A1S3S11A1S19A5").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
SdbZ20M0Z60S0S11S24G0S12Sa2A1M1A2S0S11S24Z28G1A2S0S11S24Z30G1A2S0S11S24Z38S12Sd6Z2M2Z14A2A1A2S0S11S24Z40S12Sd6G2Z18A2A1M3A2S0S11S24Z48G3A2S0S11S24Z50G3A2S0S11S24Z58G1A2S3S11A1A3A3A3A3A3A3A3A3A3").
Definition V216t : sobj := ltac2:(tb__ "0|0|
S32Zd8S48Sb2S49Z4A5").
Definition V496 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z1f0Vd;Vc;Vk;ZcA5").
Definition V528 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z210Vd;Vc;Vk;Z4A5").
Definition V560 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z230Vd;Vc;Vk;Z4A5").
Definition V592 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z250Vd;Vc;Vk;Z4A5").

Definition V720e (d k : sv) : sobj := ltac2:(tb__ "0|1|
SdbZ2d0M0Z2f0S0S11S24G0Vd;A2S0S11S24Z2e0Vk;A2S0S11S24Z2e8S12ZcA1A2S3S11A1A3A3A3A3").
Definition V720 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z2d0Vd;Vc;Vk;ZcA5").
Definition V752e (d k : sv) : sobj := ltac2:(tb__ "0|1|
SdbZ2f0M0Z310S0S11S24G0Vd;A2S0S11S24Z300Vk;A2S0S11S24Z308S12Z4A1A2S3S11A1A3A3A3A3").
Definition V752 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z2f0Vd;Vc;Vk;Z4A5").
Definition V784e (d k : sv) : sobj := ltac2:(tb__ "0|1|
SdbZ310M0Z330S0S11S24G0Vd;A2S0S11S24Z320Vk;A2S0S11S24Z328S12Z4A1A2S3S11A1A3A3A3A3").
Definition V784 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z310Vd;Vc;Vk;Z4A5").
Definition V816 (d k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z330Vd;S12Z0A1Vk;Z1A5").
Definition P_matf : sobj := ltac2:(tb__ "0|1|
SdbZ4e8M0Z518S0S11SdfG0Sc9A2S0S11SdfZ4ecScaA2S0S11Se5Z4f0S12Z0A1A2S3S11A1A3A3A3A3").

Definition room_r (e r slack : Z) (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S14S15S51S2dVe;Vcnt;A2S2dSd9Vr;Ve;A2M0S36A2A3S15S51S12SdaS28Vslack;A2A1S2dG0Vcur;A2A3A2").
Definition hf_cnt_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S14S3cS12S2aA1M0A2S0S10S14Se1G0A2S0S10S14Sb3S12Sd6Z2Z1bA2A1A2S0S10S14S2dZ3S3cA2S34A2S3S10A1A3A3A3A3").
Definition hf_room : list sprop := ltac2:(tb__ "0|6|
S0S10S57ZcM0Z1M1G0S76S2eA5S0S10S57G0Z3M2Z24S6dS2eA5S0S10S57Z4M3G1Z8M4S6bS2eA5S0S10S57G3G1G4S6fS2eA5S0S10S57G3G1G4S72S2eA5S0S10S57G3G2G0S78S2eA5S0S10S57G3G2G0S7aS2eA5S0S10S57G1Z25M5G5S7bS2eA5S3S10A1A3A3A3A3A3A3A3A3").

Definition vec_facts0 (d k : sv) (e : Z) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S10S1cVdv;Z4A2S0S10S14Vd;S16P1eA1M0A2S0S10S14S15S51Vd;S2dVe;Vk;A2M1A3G0A2S0S10S14Vd;S12S29A1A2S0S10S14Vk;S12S25A1M2A2S0S10S14G1G2A2S3S10A1A3A3A3A3A3A3").
Definition hf_vecs : list sprop := ltac2:(tb__ "0|3|
S4S10S37S35S47S34Z4M0P6eA5S4S10S37S61S6dS59ZcM1P64A5S4S10S37S60S6bS58G0P67A5S4S10S37S62S6fS5aG0P6aA5S4S10S37S65S72S5dG0P72A5S4S10S7cS6aS69G1P79A4S4S10S7cS64S5cG0P82A4S4S10S7cS66S5eG0P85A4S4S10S37S67S12Z0A1S5fZ1P88A5S0S10S14S76S12S25A1M2A2S0S10S14S78G2A2S0S10S14S7aG2A2S0S10S14S7bG2A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition ghostF_facts : list sprop := ltac2:(tb__ "0|4|
S0S10S14S6dS6eA2S0S10S14S6eS12S25A1M0A2S0S10S57ZcZ3Z24S6eS2eA5S0S10S14S6bS6cA2S0S10S14S6cG0A2S0S10S57Z4M1Z1M2Z8M3S6cS2eA5S0S10S14S6fS70A2S0S10S14S70G0A2S0S10S57G1G2G3S70S2eA5S0S10S14S72S73A2S0S10S14S73G0A2S0S10S57G1G2G3S73S2eA5S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hf_facts : list sprop := ltac2:(tb__ "0|0|
S4S10S4cSe9SeaA2S4S10SbbS4S10S0S10S14S40S12Z1A1A2S3S10A1A3S4S10SbcS4S10SbdSb9A3A3A3A3A3").

Definition X_hf (dav dmi dfv dmm dsg dco drp dtr dts kav kmi kfv kmm ksg kco krp ktr kts : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S5SfSfA2M0S2SfSfSdcS12Z518A1A4S0G0S2SfSfSddS12Z10A1A4S0G0S2SfSfSe6S12Z30A1A4S0G0S2SfSfS3eS3fA4S0G0S2SfSfVdav;S2dZ4M1Vkav;A2A4S0G0S2SfSfVdmi;S2dZcM2Vkmi;A2A4S0G0S2SfSfVdfv;S2dG1Vkfv;A2A4S0G0S2SfSfVdmm;S2dG1Vkmm;A2A4S0G0S2SfSfVdsg;S2dG1Vksg;A2A4S0G0S2SfSfVdco;S2dG2Vkco;A2A4S0G0S2SfSfVdrp;S2dG1Vkrp;A2A4S0G0S2SfSfVdtr;S2dG1Vktr;A2A4S0G0S2SfSfVdts;S2dZ1Vkts;A2A4S0G0S2SfSfS27SeaA1S12SeaA1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_hf0 : list (sv * sv) := ltac2:(tb__ "0|0|
S8fS35S61S60S62S65S6aS64S66S67S34S59S58S5aS5dS69S5cS5eS5fA12").
Definition builderF (err hp : sv) (co : sobj) (rp tr : sobj) (mi fv mm sg ts : sobj) : list sobj := ltac2:(tb__ "0|0|
S0S13Se2S0S13S45S0S13SaaS0S13Se3Verr;A1S0S13S46S0S13Se4Se7Se1Se8A3S0S13SafS0S13S44Vhp;A1S0S13Vmi;S0S13Vfv;S0S13Vmm;S0S13Vsg;S0S13Vco;S0S13Vrp;S0S13Vtr;S0S13Vts;S0S13SabS3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition datasF (dav kav dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : list sobj := ltac2:(tb__ "0|2|
S0S13S31Vdav;Z4M0Vkav;A3S0S13S31Vdmi;ZcM1Vkmi;A3S0S13S31Vdfv;G0Vkfv;A3S0S13S31Vdmm;G0Vkmm;A3S0S13S31Vdsg;G0Vksg;A3S0S13S31Vdco;G1Vkco;A3S0S13S31Vdrp;G0Vkrp;A3S0S13S31Vdtr;G0Vktr;A3S0S13S31Vdts;Z1Vkts;A3S3S13A1A3A3A3A3A3A3A3A3A3").
Definition datas0 : list sobj := ltac2:(tb__ "0|0|
S95S35S34S61S59S60S58S62S5aS65S5dS6aS69S64S5cS66S5eS67S5fA12").
Definition objs_hf0 : list sobj := ltac2:(tb__ "0|1|
S4S13S0S13S85S3S11A1A1S0S13S86S3S13A1M0A3A3S4S13S92Se0S40Sb1S6aS69A2S8bS64S5cA2S8cS66S5eA2S87S61S6dS59A3S88S60S6bS58A3S89S62S6fS5aA3S8aS65S72S5dA3S8dS67S5fA2AaS4S13S0S13SdeS0S13S3bS2eA1S0S13S3aS0S13S43G0A3A3A3A3S4S13Sb7S109A3A3A3A3").
Definition Pre_hf_S : sstate := ltac2:(tb__ "0|0|
S1bSfeS128S127S1aS6SfA1Sc0S99S42S7A9").
Definition Pre_hf : axst := mkA Pre_hf_S X_hf0.

Definition tv_hf (dav kav dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S5SfSfA2M0S2SfSfVdav;S2dZ4M1Vkav;A2A4S0G0S2SfSfVdmi;S2dZcM2Vkmi;A2A4S0G0S2SfSfVdfv;S2dG1Vkfv;A2A4S0G0S2SfSfVdmm;S2dG1Vkmm;A2A4S0G0S2SfSfVdsg;S2dG1Vksg;A2A4S0G0S2SfSfVdco;S2dG2Vkco;A2A4S0G0S2SfSfVdrp;S2dG1Vkrp;A2A4S0G0S2SfSfVdtr;S2dG1Vktr;A2A4S0G0S2SfSfVdts;S2dZ1Vkts;A2A4S3G0A1A3A3A3A3A3A3A3A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|0|
S9fS35S34S61S59S60S58S62S5aS65S5dS6aS69S64S5cS66S5eS67S5fA12").
Definition bd_hf (cur nmi kmi nfv kfv nmm kmm nsg ksg nco kco nrp krp ntr ktr nts kts : sv) : list bitem := ltac2:(tb__ "0|2|
S4S4dS0S4dS39S81Vcur;A2S3S4dA1A3S4S4dS2fZcM0Vnmi;Vkmi;A3S4S4dS2fZ4M1Vnfv;Vkfv;A3S4S4dS2fG1Vnmm;Vkmm;A3S4S4dS2fG1Vnsg;Vksg;A3S4S4dS2fG0Vnco;Vkco;A3S4S4dS2fG1Vnrp;Vkrp;A3S4S4dS2fG1Vntr;Vktr;A3S2fZ1Vnts;Vkts;A3A3A3A3A3A3A3A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S105Sc8S3S5S5SfS2bA2SfA2A1Sb4S2eS6eS59S6cS58S70S5aS73S5dS76S69S78S5cS7aS5eS7bS5fA11A3").

Definition cutpcs_hf : list Z := ltac2:(tb__ "0|0|
S0S2bS102S0S2bSebS0S2bSedS0S2bSeeS0S2bSecS0S2bS115S0S2bS100S0S2bSffS0S2bS123S0S2bS118S0S2bSefS0S2bS101S0S2bSf0S0S2bSfcS0S2bSf4S0S2bSf6S0S2bSf7S0S2bSf8S0S2bSf3S0S2bSf9S0S2bSf1S0S2bSfbS0S2bSf5S0S2bSfdS0S2bSf2S0S2bSfaS3S2bA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S10bS1bZ0S3SfA1M0G0S1aS6SfA1S3S13A1S3S10A1P1S7A9S3S5SfSfA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S113Sd1Vk;S10aS7eS82VS;Vpc;A4Sa0A4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S9S8Sd3A1M0A1S8S5S2bS124A2M1A1Lx;Sd5S10dS7eS82VS;SeA5G0S111Sd3G1S10eR1A4Ll;S3G1A1X9x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hf sm3_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 3.
Definition L_sm : axst := L_stack_malloc AE_A 3.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S2cSfA2S2S2cSfS116S26A4S10fPaSd0Sa5A1Sd0SadA1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hf = [(sm3_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hf : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SfS2bA2M0SfA2M1S2G0SfS2SfS2bS30Z3A4S38A4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S1S112U0Vi;A2S4S1S112SaVi;A1M0S117ScS13S1dSd0VA;A1A1A2G0A2A2S0S1Vi;S3S1A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_hf0 ++ (hF, SLit 512) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 X_hf0 160 512.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_pro : axst := Eval vm_compute in leaf_at C_pro hf_H 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_pro)) O_Wf.
Definition objs_pro : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_pro)).
Goal lvs C_pro = [(hf_H, RsCut)] /\ sh_pro = shobj hG 0 64 (ob_cells sh_pro) DZero.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pre : axst := Eval vm_compute in shadow_release_stateA X_pro objs_pro 160 [].

Definition pP : sv := SVar 300. Definition pT0 : sv := SVar 301. Definition pQ : sv := SVar 302.
Definition pDco : sv := SVar 303. Definition pKco : sv := SVar 304. Definition pHP : sv := SVar 306.
Definition pA : sv := SVar 418.
Definition gB : positive := 191%positive. Definition gC : positive := 192%positive.
Definition shF : sv := ltac2:(tb__ "0|0|
S15S51S16S3dA1S12S108A1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S15S51S16S98A1S12Sd7S108Vk;A2A1A3").
Definition shB (k : Z) : sv := ltac2:(tb__ "0|0|
S15S51S16S97A1S12Sd7S108Vk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S15S51SdcS12Vo;A1A3").
Definition xfo (o : Z) : sv := ltac2:(tb__ "0|0|
S15S51S30S12Vo;A1A3").
Definition MAGIC3 : Z := 18446744072277895851.

Definition F_cells : list cell := ltac2:(tb__ "0|1|
S0S11S24Ne0S55Z38A1A2S0S11S24Na0S55Z2d0A1A2S0S11S24N108S12Sa7A1A2S0S11S24Nc0S79Z1A1A2S0S11S24N160S15S51SddS12Z8A1A3A2S0S11S24N110S55Z68A1A2S0S11S24N118S55Z10A1A2S0S11S24Nf0S55Z500A1A2S0S11S24N100S55Z4f8A1A2S0S11S24Ne8S55Ze0M0A1A2S0S11S24Nf8S55Z80A1A2S0S11S24Nd8S55Z4f0A1A2S0S11S24Nd0S55Z2e8A1A2S0S11S24N140S74Z130A1A2S0S11S24N128S30A2S0S11S24N138S74G0A1A2S0S11S24N150S74Za0A1A2S0S11S24N158S74Z30A1A2S0S11S24N148S74Z20A1A2S0S11S24N70S30A2S0S11S24N90S9dZ5bA1A2S0S11S24N120Sc5A2S0S11S24N88S55Z2d8A1A2S0S11S24N130S30A2S0S11S24N98S10cA2S0S11S24N68S16P2fA1A2S0S11S24N60S16P2eA1A2S0S11S24N58S16P2dA1A2S0S11S24N50S16P2cA1A2S0S11S24N48S16P2bA1A2S0S11S24N40S16P2aA1A2S0S11S24N38S16P29A1A2S0S11S24N30S16P28A1A2S0S11S24N28S16P27A1A2S0S11S24N20S16P26A1A2S0S11S24N18S16P1dA1A2S0S11S24N10S16P1cA1A2S0S11S24N8S16PbA1A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0S11S24Z10S12Z9e888A1A2S0S11S24Z8S12Z1e6c4A1A2S0S11S24Z0S12Z41b58ab3A1A2S3S11A1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S30S12Z0A1S12Z1f8A1Vcells;S19A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S18S30S12Z1f8M0A1S12Z200A1S0S11S24G0S38A2S3S11A1A3S19A5").

Definition objs_body (cur hp dco cco kco : sv) (fx fcells txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S13S0S13S86S0S13Sa9S4S11SbaVfcells;A3A1S0S13Sa8S3S13A1M0A3A3A3S4S13S109S4S13S0S13S85S4S11Sa6Vfx;A3A1G0A3S4S13S92Se0Vhp;Sb0Vdco;Vcco;Vkco;A3S8bS64S5cA2S8cS66S5eA2S87S61S6dS59A3S88S60S6bS58A3S89S62S6fS5aA3S8aS65S72S5dA3S8dS67S5fA2AaS4S13S0S13SdeS0S13S3bVcur;A1S0S13S3aS0S13S18S3eS12Z0A1S3fVtxt;S19A5G0A3A3A3A3S95S35S34S61S59S60S58S62S5aS65S5dVdco;Vkco;S64S5cS66S5eS67S5fA12A3A3A3A3A3").
Definition X_body (dco kco : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SfSfA2S2SfSfS30S12Z0A1A4S8fS35S61S60S62S65Vdco;S64S66S67S34S59S58S5aS5dVkco;S5cS5eS5fA12A3").
Definition tv_body (dco kco : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S9fS35S34S61S59S60S58S62S5aS65S5dVdco;Vkco;S64S5cS66S5eS67S5fA12").

Definition lregs0 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SfA2M0S2S1SfU2S27Se9A1M1A4S0G0S2S1SfU8S16PaA1A4S0G0S2S1SfU9G1A4S0G0S2S1SfU14S12Z20A1A4S0G0S2S1SfU16SddA4S0G0S2S1SfU19S12Z9A1A4S0G0S2S1SfU1aSdcA4S0G0S2S1SfU1bS55Z508A1A4S3G0A1A3A3A3A3A3A3A3A3").

Definition am2 : sv := SAlu ALU_ADD pA (SLit (-2)). Definition am1 : sv := SAlu ALU_ADD pA (SLit (-1)).
Definition lregsH : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SfA2M0S9aS0G0S2S1SfU5S55Z2d0A1A4S0G0S2S1SfU6S10cA4S0G0S2S1SfU7S55Z38A1A4S0G0S2S1SfU10S91A4S0G0S2S1SfU11S90A4S0G0S2S1SfU17S55Zc0A1A4S3G0A1A3A3A3A3A3A3A3").
Definition frame_factsF : list sprop := ltac2:(tb__ "0|1|
S4S10Sd2S98SddA2S4S10Sd2S97SdcA2S4S10Sd2S3dS30A2S0S10S1cPa0Z5A2S0S10S1fS1eS53S30S12Z0A1A3A1S0S10S14S12S110A1M0S30A2S0S10S14S15S51S30S12Z200A1A3S16P1eA1A2S0S10S14S30S12S29A1A2S0S10S14G0S38A2S0S10S14S15S51S38S12Z1A1A3S12Z7fffff800000A1A2S3S10A1A3A3A3A3A3A3A3A3A3A3").

Definition prog_factF (ar rcur : sv) : sprop := ltac2:(tb__ "0|0|
S14S15S51Var;S2eA3Vrcur;A2").

Definition body_facts (cur ar rcur dco kco : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4S10S0S10S14S9cS12Z1A1A2S0S10Sc3Var;Vrcur;A2S0S10S14S2eVrcur;A2S0S10S14Vrcur;Vcur;A2S0S10S14Vcur;S36A2S0S10S14Var;Vkco;A2S0S10S14Var;S12Sd6Z2Z14A2A1A2S3S10A1A3A3A3A3A3A3A3S4S10S7cVdco;Vkco;ZcVdv;A4S4S10Sb8S99A3A3A3").

Definition BANK (c : Z) (cur : sv) : bitem := ltac2:(tb__ "0|2|
S50Z1Z0M0S0S5S2bS4eA2M1S2S2bS4eVc;S4fVcur;A1A4S0G1S2S2bS4eSd8Vc;A1S4fS2eA1A4S3G1A1A3A3G0A4").
Definition cB : Z := 696.
Definition NCO (cur : sv) : sv := ltac2:(tb__ "0|0|
S15S51S76S15S52Vcur;S2eA3A3").
Definition pairs7 (nmi kmi nfv kfv nmm kmm nsg ksg nrp krp ntr ktr nts kts : sv) : list bitem := ltac2:(tb__ "0|1|
S4S4dS2fZcVnmi;Vkmi;A3S4S4dS2fZ4M0Vnfv;Vkfv;A3S4S4dS2fG0Vnmm;Vkmm;A3S4S4dS2fG0Vnsg;Vksg;A3S4S4dS2fG0Vnrp;Vkrp;A3S4S4dS2fG0Vntr;Vktr;A3S2fZ1Vnts;Vkts;A3A3A3A3A3A3A3").
Definition pairs7e : list bitem := ltac2:(tb__ "0|0|
Sc1S6eS59S6cS58S70S5aS73S5dS78S5cS7aS5eS7bS5fAe").
Definition bd_loop (cur kco : sv) : list bitem := ltac2:(tb__ "0|0|
S4S4dS0S4dS39S81Vcur;A2S0S4dSa1Sb6Vcur;A2S3S4dA1A3A3S4S4dS2fZcS7fVcur;A1Vkco;A3Sc2A3A3").
Definition ndL (cur dco kco : sv) : ndesc := ltac2:(tb__ "0|0|
S107S9eVdco;Vkco;A2S96Sb5Vcur;Vkco;A2S106A4").

Definition BCUT (pc : Z) (regs : list (nat * sv)) (cur dco cco kco : sv) (fx fcells txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S10bS1bVpc;S4bVregs;A1S4aS1aS6SfA1SbfVcur;S9cVdco;Vcco;Vkco;Vfx;Vfcells;Vtxt;A8Vfacts;S41S7A9S8eVdco;Vkco;A2A2").

Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur : sv) (fx : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S7dVpc;Vregs;Vcur;S83S56S84Vfx;S3S11A1M0G0S4S10Vfacts;S80Vcur;S56Vrcur;S83S84P12fA6A3Aa").

Definition H : axst := ltac2:(tb__ "0|0|
S75SebS77S71S71S3S11A1S3S10A1A6").
Goal leaf_matches1A NPH C_pre H = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs H = [(hf_A, RsCut); (hf_L1, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition L1 : axst := ltac2:(tb__ "0|2|
S75SedS4S5S1SfA2M0S77S0G0S2S1SfUaS33S54A1M1A4S0G0S2S1SfUbS79Z0A1A4S0G0S2S1SfUcS33S36A1A4S0G0S2S1SfU15G1A4S3G0A1A3A3A3A3A3S71S71S3S11A1S0S10S14S71S54A2S0S10S17S54S36A2S3S10A1A3A3A6").

Definition cA : list cell := [c8 (-168) pA].
Definition L2 : axst := ltac2:(tb__ "0|2|
S75SeeS4S5S1SfA2M0S77S0G0S2S1SfUaS33S54A1M1A4S0G0S2S1SfUbS79Z0A1A4S0G0S2S1SfUcS33S36A1A4S0G0S2S1SfUdG1A4S0G0S2S1SfU15S33S5bA1A4S3G0A1A3A3A3A3A3A3S54S5bS93S0S10S14S5bS54A2S0S10S17S54S36A2S3S10A1A3A3A6").

Definition K : axst := ltac2:(tb__ "0|1|
S75SecS4S5S1SfA2M0S77S0G0S2S1SfUbS79Z0A1A4S0G0S2S1SfUcS33S36A1A4S0G0S2S1SfU15S33S5bA1A4S3G0A1A3A3A3A3S54S5bS93S0S10S17S5bS54A2S3S10A1A3A6").
Goal lvs L1 = [(hf_A, RsCut); (hf_L1, RsCut); (hf_A, RsCut); (hf_L1, RsCut); (hf_L2, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs L2 = [(hf_K, RsCut); (hf_K, RsCut); (hf_L2, RsCut); (hf_K, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K = [(hf_EPI, RsCut); (hf_EPI, RsCut); (vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition leaves_at2 (Ss : list axst) (pc : Z) : list axst := ltac2:(tb__ "0|0|
S12aSd1Sd1Sd1S10aS7eS82R1Vpc;A4LS;VSs;A4").
Goal map (fun L => leaf_matches1A NPH L L1) (leaves_at2 [H; L1] hf_L1) = [true; true; true]
  /\ map (fun L => leaf_matches1A NPH L L2) (leaves_at2 [L1; L2] hf_L2) = [true; true]
  /\ map (fun L => leaf_matches1A NPH L K) (leaves_at2 [L2] hf_K) = [true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_co0 : axst := Eval vm_compute in leaf_at K vr_entry 0.
Definition xf_vr (i : nat) (o : Z) : list axform := ltac2:(tb__ "0|2|
S0ScbScdU0M0S12N40M1A1A2S0ScbSccG0G1A2S0ScbSccVi;Vo;A2S3ScbA1A3A3A3").

Definition co_need (cur : sv) : list sprop := ltac2:(tb__ "0|0|
S0S10S14S2dZcS7fVcur;A1A2S12S28A1A2S3S10A1A3").
Definition E_co : axst := Eval vm_compute in ax_add_facts (co_need pQ) (optAp (apply_axforms E_co0 (xf_vr 19 720))).
Definition s_co : wsub := ltac2:(tb__ "0|1|
S0S5S2cSfA2M0S2S2cSfP3bS7fS54A1A4S0G0S2S2cSfP13S15S51S26S12Z40A1A3A4S10fPaSd0Sa3A1Sd0S11cA1A3A3A3").
Definition R_co : list sobj := Eval vm_compute in optR (entails_frA E_co VN.Pre_vr s_co).
Definition PD_vn : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5Sd1S104A2M0S2Sd1S104S11bS11eA4S0G0S2Sd1S104S119S105S11fS3S5S5SfS2bA2SfA2A1M1S3S4dA1A3A4S0G0S2Sd1S104S11aS105S120G1S11dS122S121A2A3A4S3G0A1A3A3A3").
Goal entails_frA E_co VN.Pre_vr s_co = Some R_co /\ call_checkPA E_co VN.Pre_vr s_co R_co (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xkeep (dco : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S129S5SfSfA2M0G0SdS23SbSfSfR1A3Vdco;A2A1Lr;S8eVdco;S84A2A3").
Definition T_cok0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_keep (Xkeep pDco).
Definition T_cof0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_fail (Xkeep pDco).
Definition T_cog0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_grown (Xkeep pDco).

Definition sel_back : list nat := ltac2:(tb__ "0|0|
S0S1U1S0S1U0S0S1U7S0S1U8S0S1U5S0S1U6S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U2S0S1U16S0S1U17S0S1U18S0S1U19S0S1U3S0S1U1aS0S1U1bS0S1U1cS0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U4S0S1U22S0S1U23S0S1U24S3S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_back : list axform := ltac2:(tb__ "0|0|
S0ScbSccU1Z40A2S0ScbScfSc4A1S0ScbSceU0A1S0ScbSccU12N2d0A2S3ScbA1A3A3A3A3").
Definition T_cok : axst := Eval vm_compute in optAp (apply_axforms T_cok0 xf_back).
Definition T_cof : axst := Eval vm_compute in optAp (apply_axforms T_cof0 xf_back).
Definition T_cog : axst := Eval vm_compute in optAp (apply_axforms T_cog0 xf_back).
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S8S5S5SfSfA2SfA2A1") := ltac2:(tb__ "0|1|
S111S13S5S5SfSfA2M0SfA2S13S2G0SfS2SfSfS20R1A1S22R1A1A4S21R1A1A4Lo;S1dSd0VA;A1A1A4").

Definition pD2 : sv := SVar 307. Definition pK2 : sv := SVar 308.
Definition cR : list cell := ltac2:(tb__ "0|0|
S0S11S24Nc8S9dZ0A1A2S0S11S24Nb0S91A2S0S11S24Nb8S90A2S0S11S24Na8S56A2S3S11A1A3A3A3A3").
Definition lregsR (a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SfA2M0S9aS0G0S2S1SfU1S12S103A1A4S0G0S2S1SfUaVa0;A4S0G0S2S1SfU12S33S54A1A4S0G0S2S1SfU13S55Zc0A1A4S0G0S2S1SfU15S33S5bA1A4S0G0S2S1SfU17SdcA4S3G0A1A3A3A3A3A3A3A3").

Definition slot_facts (c k : sv) : list sprop := ltac2:(tb__ "0|3|
S0S10S14S15S51S2dZcM0Vc;A2M1S12G0A1A3S2dG0Vk;A2M2A2S0S10S14G1G2A2S0S10S14G1S12S25A1A2S3S10A1A3A3A3").
Definition JR_co : axst := ltac2:(tb__ "0|2|
S7dS114S9bS12Z1A1M0A1S54S68S56S63S94S3S11A1M1G1S4S10S0S10S17S5bS54A2S0S10S17S56S12Sd6Z2Z14A2A1A2S0S10S14S15S51S56G0A3S63A2S0S10S14S12S110A1S68A2S3S10A1A3A3A3A3S4S10Sc7S56S63A2S80S54S56S5bS68S63P133A6A3A3Aa").
Definition JF_co : axst := ltac2:(tb__ "0|1|
S7dS114S9bS12Z0A1A1S54S68S56S63S94S3S11A1M0G0S4S10S0S10S17S5bS54A2S0S10S17S56S12Sd6Z2Z14A2A1A2S3S10A1A3A3S80S54S56S5bS68S63P133A6A3Aa").
Definition ndR : ndesc := ltac2:(tb__ "0|0|
SbeS54S68S63A3").
Definition ndFc : ndesc := ltac2:(tb__ "0|0|
S107S9eS68S63A2S96S0S4dS39S81S54A2S3S4dA1A3S106A4").

Definition T_coks : axst := ltac2:(tb__ "0|0|
S125S0S10S14S12S110A1S83A2S3S10A1A3SaeA2").
Goal map (fun L => leaf_matches1A NPH L JR_co) [T_coks; T_cog] = [true; true] /\ leaf_matches1A NPH T_cof JF_co = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_co = [(memset_pc, RsCut)] /\ lvs JF_co = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition slot (d c : sv) : sv := ltac2:(tb__ "0|0|
S15S51Vd;S2dZcVc;A2A3").
Definition slot_obj (d c : sv) : sobj := ltac2:(tb__ "0|0|
S18Sc6Vd;Vc;A2S12Z0A1S12ZcA1S3S11A1S19A5").
Definition mid_slot (d c : sv) (dfl : odefault) : sobj := ltac2:(tb__ "0|2|
S18Vd;S2dZcM0Vc;A2M1S15S51G1S12G0A1A3S3S11A1Vdfl;A5").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
Sd4VA;S126Sd0VA;A1Vi;Vo;A3A2").
Definition xf_ms : list axform := ltac2:(tb__ "0|2|
S0ScbScdU20S2dZcM0S56A2M1A2S0ScbScdU21S15S51G1S12G0A1A3A2S3ScbA1A3A3").
Definition E_ms0 : axst := Eval vm_compute in leaf_at JR_co memset_pc 0.
Definition E_ms1 : axst := Eval vm_compute in optAp (apply_axforms E_ms0 xf_ms).
Definition E_ms : axst := Eval vm_compute in reshapeA E_ms1 33 (slot_obj pD2 pA).
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_ms : wsub := ltac2:(tb__ "0|1|
S0S5S2cSfA2M0S2S2cSfP35S68A4S0G0S2S2cSfP36S2dZcS63A2A4S0G0S2S2cSfS116S26A4S10fPaSd0Sa4A1Sd0SacA1A3A3A3A3").
Definition R_ms : list sobj := Eval vm_compute in optR (entails_frA E_ms Pre_ms s_ms).
Goal entails_frA E_ms Pre_ms s_ms = Some R_ms /\ call_checkPA E_ms Pre_ms s_ms R_ms [L_ms] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_ms0 : axst := Eval vm_compute in T_afterA Pre_ms E_ms s_ms R_ms L_ms.
