(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "None"; "false"; "list"; "option"; "S"; "fst"; "length"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "SLit"; "sobj"; "SPUle"; "SVar"; "SAlu"; "SPUlt"; "mkObj"; "DUnknown"; "FcsrFrm0"; "mkSS"; "SPAlign"; "ss_objs"; "SPBranch"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "B32"; "spm"; "vDp"; "B_EW"; "two47"; "two40"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "tI"; "bd_vec"; "hF"; "O_data"; "V"; "tp"; "av_k"; "av_d"; "tE"; "vec_facts"; "hFL"; "PROG"; "O_cE"; "O_cP"; "av_nv"; "hG"; "tB"; "tL"; "xHASPRIM"; "HNEXT"; "NPH"; "O_text"; "P_cur"; "P_hdr"; "V120"; "av_c"; "avt_d"; "avt_k"; "h_fregs"; "h_xregs"; "handle_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pQ"; "xbo"; "pA"; "room_r"; "fv_k"; "mi_k"; "mm_k"; "pT0"; "rp_k"; "sg_k"; "tr_k"; "ts_k"; "fv_d"; "mi_d"; "mm_d"; "rp_d"; "sg_d"; "tr_d"; "ts_d"; "pK2"; "pD2"; "co_k"; "co_d"; "fv_c"; "fv_n"; "mi_c"; "mi_n"; "mm_c"; "mm_n"; "pP"; "sg_c"; "sg_n"; "xfo"; "HC"; "co_n"; "lregsH"; "rp_n"; "tr_n"; "ts_n"; "vec_facts0"; "BCUT"; "FUEL_hf"; "NCO"; "body_facts"; "cVF"; "cutpcs_hf"; "pDco"; "pKco"; "O_F"; "O_Wf"; "V496"; "V528"; "V560"; "V592"; "V752e"; "V784e"; "V816"; "X_body"; "X_hf"; "am2"; "builderF"; "cA"; "cR"; "datasF"; "fr_hf"; "gB"; "gC"; "hf_facts"; "lregs0"; "lregsR"; "pHP"; "shB"; "shC"; "tv_body"; "tv_hf"; "BAD"; "BANK"; "BIG"; "E_co"; "E_sm0"; "F_cells"; "MAGIC3"; "O_flag"; "O_frame"; "P_caps"; "P_matf"; "Pre_sm"; "T_cok"; "V216t"; "V720"; "V720e"; "avt_cnt"; "avt_t"; "bd_hf"; "bd_loop"; "cB"; "datas0"; "frame_factsF"; "ghostF_facts"; "hdr3"; "hf_cnt_facts"; "hf_room"; "hf_vecs"; "ndL"; "objs_body"; "objs_hf0"; "pairs7"; "pairs7e"; "prog_factF"; "sel_back"; "shF"; "slot"; "slot_facts"; "tv0"; "xMAT"; "xSMO"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "FE"; "leafA"; "ax_setS"; "sym_runA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "piece"; "vb"; "vc"; "O_al"; "c4"; "vERR"; "vNC"; "P_alloc"; "P_st"; "V184"; "c1"; "vAL"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "FR"; "DW"; "hf_H"; "hf_K"; "hf_L1"; "hf_L2"; "bw_pc"; "f5_pc"; "hf_A"; "hf_C36"; "hf_EPI"; "hf_J"; "hf_K1"; "hf_K1X"; "hf_K2"; "hf_K3"; "hf_K3m"; "hf_L14"; "hf_MQ"; "hf_REL"; "hf_RJ"; "hf_RW"; "hf_T36X"; "hf_TFX"; "hf_TS"; "hf_ZX"; "hf_entry"; "memcpy_pc"; "memset_pc"; "pg_pc"; "sm3_pc"; "vr_ret_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.Lists.List"; "filter"; "flat_map"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN. End VN.
Module PG. Include Lib_tess_polygon_states. End PG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HFAddr.
  Definition hf_entry : Z := 0x9c8d8.
  Definition sm3_pc : Z := 0x47f3c.
  Definition memset_pc : Z := 0x5ce7c.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition f5_pc : Z := 0x60524.
  Definition tss_pc : Z := 0xa8e38.
  Definition pg_pc : Z := 0xa8e6c.
  Definition hf_H : Z := 0x9cb94.
  Definition hf_L1 : Z := 0x9cbd0.
  Definition hf_L2 : Z := 0x9cc48.
  Definition hf_K : Z := 0x9cc7c.
  Definition hf_B : Z := 0x9cb7c.
  Definition hf_A : Z := 0x9d000.
  Definition hf_F2 : Z := 0x9cfbc.
  Definition hf_F7 : Z := 0x9d078.
  Definition hf_RW : Z := 0x9d2f8.
  Definition hf_K1 : Z := 0x9d494.
  Definition hf_K2 : Z := 0x9d610.
  Definition hf_K3 : Z := 0x9d7f8.
  Definition hf_K3m : Z := 0x9d844.
  Definition hf_J : Z := 0x9db2c.
  Definition hf_L14 : Z := 0x9dca0.
  Definition hf_C36 : Z := 0x9e400.
  Definition hf_RJ : Z := 0x9e460.
  Definition hf_K1X : Z := 0x9d508.
  Definition hf_TS : Z := 0x9d9f8.
  Definition hf_C4a : Z := 0x9e660.
  Definition hf_C4b : Z := 0x9e790.
  Definition hf_T4a : Z := 0x9e0d8.
  Definition hf_T4b : Z := 0x9e200.
  Definition hf_EPI : Z := 0x9d1f0.
  Definition hf_REL : Z := 0x9d2b8.
  Definition hf_ret : Z := 0x9ee00.
  Definition vr_ret_hf : Z := 0x9ccf0.

  Definition hf_ZX : Z := 0x9cdb8.
  Definition hf_MQ : Z := 0x9e594.
  Definition hf_T36X : Z := 0x9defc.
  Definition hf_TFX : Z := 0x9e010.
  Definition bw_pc : Z := 0xa0394.
  Definition hf_trap : Z := 0x9ea68.
  Definition DW : Z := 4736.
  Definition FR : Z := 384.
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
S18S15PaA1S12Sd5Se6A1A1S12Z0A1Vcells;S19A5").
Definition O_Wf : sobj := ltac2:(tb__ "0|0|
S18S26Se6A1S27S12Z0A1S2S11A1S19A5").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
Sd8Z20M0Z60S0S11S24G0S12S9eA1M1A2S0S11S24Z28G1A2S0S11S24Z30G1A2S0S11S24Z38S12Sd3Z2M2Z14A2A1A2S0S11S24Z40S12Sd3G2Z18A2A1M3A2S0S11S24Z48G3A2S0S11S24Z50G3A2S0S11S24Z58G1A2S2S11A1A3A3A3A3A3A3A3A3A3").
Definition V216t : sobj := ltac2:(tb__ "0|0|
S32Zd8S48SacS49Z4A5").
Definition V496 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z1f0Vd;Vc;Vk;ZcA5").
Definition V528 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z210Vd;Vc;Vk;Z4A5").
Definition V560 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z230Vd;Vc;Vk;Z4A5").
Definition V592 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z250Vd;Vc;Vk;Z4A5").

Definition V720e (d k : sv) : sobj := ltac2:(tb__ "0|1|
Sd8Z2d0M0Z2f0S0S11S24G0Vd;A2S0S11S24Z2e0Vk;A2S0S11S24Z2e8S12ZcA1A2S2S11A1A3A3A3A3").
Definition V720 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z2d0Vd;Vc;Vk;ZcA5").
Definition V752e (d k : sv) : sobj := ltac2:(tb__ "0|1|
Sd8Z2f0M0Z310S0S11S24G0Vd;A2S0S11S24Z300Vk;A2S0S11S24Z308S12Z4A1A2S2S11A1A3A3A3A3").
Definition V752 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z2f0Vd;Vc;Vk;Z4A5").
Definition V784e (d k : sv) : sobj := ltac2:(tb__ "0|1|
Sd8Z310M0Z330S0S11S24G0Vd;A2S0S11S24Z320Vk;A2S0S11S24Z328S12Z4A1A2S2S11A1A3A3A3A3").
Definition V784 (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z310Vd;Vc;Vk;Z4A5").
Definition V816 (d k : sv) : sobj := ltac2:(tb__ "0|0|
S32Z330Vd;S12Z0A1Vk;Z1A5").
Definition P_matf : sobj := ltac2:(tb__ "0|1|
Sd8Z4e8M0Z518S0S11SdcG0Sc3A2S0S11SdcZ4ecSc4A2S0S11Se2Z4f0S12Z0A1A2S2S11A1A3A3A3A3").

Definition room_r (e r slack : Z) (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S14S16Sc5S2dVe;Vcnt;A2S2dSd6Vr;Ve;A2M0S36A2A3S16Sc5S12Sd7S28Vslack;A2A1S2dG0Vcur;A2A3A2").
Definition hf_cnt_facts : list sprop := ltac2:(tb__ "0|1|
S0S10S14S3cS12S2aA1M0A2S0S10S14SdeG0A2S0S10S14SadS12Sd3Z2Z1bA2A1A2S0S10S14S2dZ3S3cA2S34A2S2S10A1A3A3A3A3").
Definition hf_room : list sprop := ltac2:(tb__ "0|6|
S0S10S54ZcM0Z1M1G0S73S2eA5S0S10S54G0Z3M2Z24S6aS2eA5S0S10S54Z4M3G1Z8M4S68S2eA5S0S10S54G3G1G4S6cS2eA5S0S10S54G3G1G4S6fS2eA5S0S10S54G3G2G0S75S2eA5S0S10S54G3G2G0S76S2eA5S0S10S54G1Z25M5G5S77S2eA5S2S10A1A3A3A3A3A3A3A3A3").

Definition vec_facts0 (d k : sv) (e : Z) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S10S1cVdv;Z4A2S0S10S14Vd;S15P1eA1M0A2S0S10S14S16Sc5Vd;S2dVe;Vk;A2M1A3G0A2S0S10S14Vd;S12S29A1A2S0S10S14Vk;S12S25A1M2A2S0S10S14G1G2A2S2S10A1A3A3A3A3A3A3").
Definition hf_vecs : list sprop := ltac2:(tb__ "0|3|
S4S10S37S35S47S34Z4M0P6eA5S4S10S37S5eS6aS56ZcM1P64A5S4S10S37S5dS68S55G0P67A5S4S10S37S5fS6cS57G0P6aA5S4S10S37S61S6fS5aG0P72A5S4S10S78S67S66G1P79A4S4S10S78S60S59G0P82A4S4S10S78S62S5bG0P85A4S4S10S37S63S12Z0A1S5cZ1P88A5S0S10S14S73S12S25A1M2A2S0S10S14S75G2A2S0S10S14S76G2A2S0S10S14S77G2A2S2S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition ghostF_facts : list sprop := ltac2:(tb__ "0|4|
S0S10S14S6aS6bA2S0S10S14S6bS12S25A1M0A2S0S10S54ZcZ3Z24S6bS2eA5S0S10S14S68S69A2S0S10S14S69G0A2S0S10S54Z4M1Z1M2Z8M3S69S2eA5S0S10S14S6cS6dA2S0S10S14S6dG0A2S0S10S54G1G2G3S6dS2eA5S0S10S14S6fS70A2S0S10S14S70G0A2S0S10S54G1G2G3S70S2eA5S2S10A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hf_facts : list sprop := ltac2:(tb__ "0|0|
S4S10S4cSe6Se7A2S4S10Sb5S4S10S0S10S14S40S12Z1A1A2S2S10A1A3S4S10Sb6S4S10Sb7Sb3A3A3A3A3A3").

Definition X_hf (dav dmi dfv dmm dsg dco drp dtr dts kav kmi kfv kmm ksg kco krp ktr kts : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S5SfSfA2M0S3SfSfSd9S12Z518A1A4S0G0S3SfSfSdaS12Z10A1A4S0G0S3SfSfSe3S12Z30A1A4S0G0S3SfSfS3eS3fA4S0G0S3SfSfVdav;S2dZ4M1Vkav;A2A4S0G0S3SfSfVdmi;S2dZcM2Vkmi;A2A4S0G0S3SfSfVdfv;S2dG1Vkfv;A2A4S0G0S3SfSfVdmm;S2dG1Vkmm;A2A4S0G0S3SfSfVdsg;S2dG1Vksg;A2A4S0G0S3SfSfVdco;S2dG2Vkco;A2A4S0G0S3SfSfVdrp;S2dG1Vkrp;A2A4S0G0S3SfSfVdtr;S2dG1Vktr;A2A4S0G0S3SfSfVdts;S2dZ1Vkts;A2A4S0G0S3SfSfS26Se7A1S12Se7A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_hf0 : list (sv * sv) := ltac2:(tb__ "0|0|
S8bS35S5eS5dS5fS61S67S60S62S63S34S56S55S57S5aS66S59S5bS5cA12").
Definition builderF (err hp : sv) (co : sobj) (rp tr : sobj) (mi fv mm sg ts : sobj) : list sobj := ltac2:(tb__ "0|0|
S0S13SdfS0S13S45S0S13Sa5S0S13Se0Verr;A1S0S13S46S0S13Se1Se4SdeSe5A3S0S13Sa9S0S13S44Vhp;A1S0S13Vmi;S0S13Vfv;S0S13Vmm;S0S13Vsg;S0S13Vco;S0S13Vrp;S0S13Vtr;S0S13Vts;S0S13Sa6S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition datasF (dav kav dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : list sobj := ltac2:(tb__ "0|2|
S0S13S31Vdav;Z4M0Vkav;A3S0S13S31Vdmi;ZcM1Vkmi;A3S0S13S31Vdfv;G0Vkfv;A3S0S13S31Vdmm;G0Vkmm;A3S0S13S31Vdsg;G0Vksg;A3S0S13S31Vdco;G1Vkco;A3S0S13S31Vdrp;G0Vkrp;A3S0S13S31Vdtr;G0Vktr;A3S0S13S31Vdts;Z1Vkts;A3S2S13A1A3A3A3A3A3A3A3A3A3").
Definition datas0 : list sobj := ltac2:(tb__ "0|0|
S90S35S34S5eS56S5dS55S5fS57S61S5aS67S66S60S59S62S5bS63S5cA12").
Definition objs_hf0 : list sobj := ltac2:(tb__ "0|1|
S4S13S0S13S81S2S11A1A1S0S13S82S2S13A1M0A3A3S4S13S8dSddS40SabS67S66A2S87S60S59A2S88S62S5bA2S83S5eS6aS56A3S84S5dS68S55A3S85S5fS6cS57A3S86S61S6fS5aA3S89S63S5cA2AaS4S13S0S13SdbS0S13S3bS2eA1S0S13S3aS0S13S43G0A3A3A3A3S4S13Sb1S10bA3A3A3A3").
Definition Pre_hf_S : sstate := ltac2:(tb__ "0|0|
S1bS100S129S128S1aS6SfA1SbaS94S42S7A9").
Definition Pre_hf : axst := mkA Pre_hf_S X_hf0.

Definition tv_hf (dav kav dmi kmi dfv kfv dmm kmm dsg ksg dco kco drp krp dtr ktr dts kts : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S5SfSfA2M0S3SfSfVdav;S2dZ4M1Vkav;A2A4S0G0S3SfSfVdmi;S2dZcM2Vkmi;A2A4S0G0S3SfSfVdfv;S2dG1Vkfv;A2A4S0G0S3SfSfVdmm;S2dG1Vkmm;A2A4S0G0S3SfSfVdsg;S2dG1Vksg;A2A4S0G0S3SfSfVdco;S2dG2Vkco;A2A4S0G0S3SfSfVdrp;S2dG1Vkrp;A2A4S0G0S3SfSfVdtr;S2dG1Vktr;A2A4S0G0S3SfSfVdts;S2dZ1Vkts;A2A4S2G0A1A3A3A3A3A3A3A3A3A3").
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|0|
S9bS35S34S5eS56S5dS55S5fS57S61S5aS67S66S60S59S62S5bS63S5cA12").
Definition bd_hf (cur nmi kmi nfv kfv nmm kmm nsg ksg nco kco nrp krp ntr ktr nts kts : sv) : list bitem := ltac2:(tb__ "0|2|
S4S4dS0S4dS39S7dVcur;A2S2S4dA1A3S4S4dS2fZcM0Vnmi;Vkmi;A3S4S4dS2fZ4M1Vnfv;Vkfv;A3S4S4dS2fG1Vnmm;Vkmm;A3S4S4dS2fG1Vnsg;Vksg;A3S4S4dS2fG0Vnco;Vkco;A3S4S4dS2fG1Vnrp;Vkrp;A3S4S4dS2fG1Vntr;Vktr;A3S2fZ1Vnts;Vkts;A3A3A3A3A3A3A3A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S107Sc2S2S5S5SfS2bA2SfA2A1SaeS2eS6bS56S69S55S6dS57S70S5aS73S66S75S59S76S5bS77S5cA11A3").

Definition cutpcs_hf : list Z := ltac2:(tb__ "0|0|
S0S2bS104S0S2bSe8S0S2bSeaS0S2bSebS0S2bSe9S0S2bS116S0S2bS102S0S2bS101S0S2bS124S0S2bS119S0S2bSedS0S2bS103S0S2bSeeS0S2bSfbS0S2bSf2S0S2bSf4S0S2bSf5S0S2bSf6S0S2bSf1S0S2bSf7S0S2bSefS0S2bSfaS0S2bSf3S0S2bSfeS0S2bSf0S0S2bSf9S0S2bSffS0S2bSf8S0S2bSfcS0S2bSfdS0S2bSecS2S2bA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S10dS1bZ0S2SfA1M0G0S1aS6SfA1S2S13A1S2S10A1P1S7A9S2S5SfSfA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S114ScdVk;S10cS7aS7eVS;Vpc;A4S9cA4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S9S8Sd0A1M0A1S8S5S2bS125A2M1A1Lx;Sd2S10eS7aS7eVS;SeA5G0S112Sd0G1S110R1A4Ll;S2G1A1X9x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hf sm3_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 3.
Definition L_sm : axst := L_stack_malloc AE_A 3.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S2cSfA2S3S2cSfS12aS27A4S117PaSceSa0A1SceSa7A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hf = [(sm3_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hf : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SfS2bA2M0SfA2M1S3G0SfS3SfS2bS30Z3A4S38A4S2G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S1S113U0Vi;A2S4S1S113SaVi;A1M0S118ScS13S1dSceVA;A1A1A2G0A2A2S0S1Vi;S2S1A1A3A3A3").
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
S16Sc5S15S3dA1S12S10aA1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S16Sc5S15S93A1S12Sd4S10aVk;A2A1A3").
Definition shB (k : Z) : sv := ltac2:(tb__ "0|0|
S16Sc5S15S92A1S12Sd4S10aVk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S16Sc5Sd9S12Vo;A1A3").
Definition xfo (o : Z) : sv := ltac2:(tb__ "0|0|
S16Sc5S30S12Vo;A1A3").
Definition MAGIC3 : Z := 18446744072277895851.

Definition F_cells : list cell := ltac2:(tb__ "0|1|
S0S11S24Nf0S52Z38A1A2S0S11S24Na0Sd9A2S0S11S24Nb0S99Z1A1A2S0S11S24N100S12Sa2A1A2S0S11S24N160S16Sc5SdaS12Z8A1A3A2S0S11S24N118S52Z68A1A2S0S11S24N108S52Z10A1A2S0S11S24Ne8S52Z508A1A2S0S11S24Ne0S52Z500A1A2S0S11S24Nf8S52Z4f8A1A2S0S11S24Nd8S52Zc0A1A2S0S11S24Nd0S52Ze0M0A1A2S0S11S24Nc8S52Z80A1A2S0S11S24N140S52Z78A1A2S0S11S24Nb8S52Z4f0A1A2S0S11S24Nc0S52Z2e8A1A2S0S11S24N90S52Z2d0A1A2S0S11S24N138S71Z130A1A2S0S11S24N130S71G0A1A2S0S11S24N150S71Za0A1A2S0S11S24N158S71Z30A1A2S0S11S24N148S71Z20A1A2S0S11S24N88S98Z5bA1A2S0S11S24N120SbfA2S0S11S24N128S30A2S0S11S24N110S30A2S0S11S24N70S30A2S0S11S24N68S15P2fA1A2S0S11S24N60S15P2eA1A2S0S11S24N58S15P2dA1A2S0S11S24N50S15P2cA1A2S0S11S24N48S15P2bA1A2S0S11S24N40S15P2aA1A2S0S11S24N38S15P29A1A2S0S11S24N30S15P28A1A2S0S11S24N28S15P27A1A2S0S11S24N20S15P26A1A2S0S11S24N18S15P1dA1A2S0S11S24N10S15P1cA1A2S0S11S24N8S15PbA1A2S0S11S24N180S12Z0A1A2S2S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0S11S24Z10S12Z9c8d8A1A2S0S11S24Z8S12Z20a75A1A2S0S11S24Z0S12Z41b58ab3A1A2S2S11A1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S30S12Z0A1S12Z1f8A1Vcells;S19A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S18S30S12Z1f8M0A1S12Z200A1S0S11S24G0S38A2S2S11A1A3S19A5").

Definition objs_body (cur hp dco cco kco : sv) (fx fcells txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S13S0S13S82S0S13Sa4S4S11Sb4Vfcells;A3A1S0S13Sa3S2S13A1M0A3A3A3S4S13S10bS4S13S0S13S81S4S11Sa1Vfx;A3A1G0A3S4S13S8dSddVhp;SaaVdco;Vcco;Vkco;A3S87S60S59A2S88S62S5bA2S83S5eS6aS56A3S84S5dS68S55A3S85S5fS6cS57A3S86S61S6fS5aA3S89S63S5cA2AaS4S13S0S13SdbS0S13S3bVcur;A1S0S13S3aS0S13S18S3eS12Z0A1S3fVtxt;S19A5G0A3A3A3A3S90S35S34S5eS56S5dS55S5fS57S61S5aVdco;Vkco;S60S59S62S5bS63S5cA12A3A3A3A3A3").
Definition X_body (dco kco : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SfSfA2S3SfSfS30S12Z0A1A4S8bS35S5eS5dS5fS61Vdco;S60S62S63S34S56S55S57S5aVkco;S59S5bS5cA12A3").
Definition tv_body (dco kco : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S9bS35S34S5eS56S5dS55S5fS57S61S5aVdco;Vkco;S60S59S62S5bS63S5cA12").

Definition lregs0 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SfA2M0S3S1SfU2S26Se6A1M1A4S0G0S3S1SfU8S15PaA1A4S0G0S3S1SfU9G1A4S0G0S3S1SfU12S10fA4S0G0S3S1SfU15Sd9A4S0G0S3S1SfU17S12Z9A1A4S0G0S3S1SfU19SdaA4S0G0S3S1SfU1aS99Z0A1A4S0G0S3S1SfU1bS12Z20A1A4S2G0A1A3A3A3A3A3A3A3A3A3").

Definition am2 : sv := SAlu ALU_ADD pA (SLit (-2)). Definition am1 : sv := SAlu ALU_ADD pA (SLit (-1)).
Definition lregsH : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SfA2M0S95S0G0S3S1SfU5S12Z2A1A4S0G0S3S1SfUfS52Z2d8A1A4S0G0S3S1SfU10S8cA4S0G0S3S1SfU11S52Z38A1A4S0G0S3S1SfU13S53A4S2G0A1A3A3A3A3A3A3").
Definition frame_factsF : list sprop := ltac2:(tb__ "0|1|
S4S10ScfS93SdaA2S4S10ScfS92Sd9A2S4S10ScfS3dS30A2S0S10S1cPa0Z5A2S0S10S1fS1eSc7S30S12Z0A1A3A1S0S10S14S12S111A1M0S30A2S0S10S14S16Sc5S30S12Z200A1A3S15P1eA1A2S0S10S14S30S12S29A1A2S0S10S14G0S38A2S0S10S14S16Sc5S38S12Z1A1A3S12Z7fffff800000A1A2S2S10A1A3A3A3A3A3A3A3A3A3A3").

Definition prog_factF (ar rcur : sv) : sprop := ltac2:(tb__ "0|0|
S14S16Sc5Var;S2eA3Vrcur;A2").

Definition body_facts (cur ar rcur dco kco : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4S10S0S10S14S97S12Z1A1A2S0S10SbdVar;Vrcur;A2S0S10S14S2eVrcur;A2S0S10S14Vrcur;Vcur;A2S0S10S14Vcur;S36A2S0S10S14Var;Vkco;A2S0S10S14Var;S12Sd3Z2Z14A2A1A2S2S10A1A3A3A3A3A3A3A3S4S10S78Vdco;Vkco;ZcVdv;A4S4S10Sb2S94A3A3A3").

Definition BANK (c : Z) (cur : sv) : bitem := ltac2:(tb__ "0|2|
S50Z1Z0M0S0S5S2bS4eA2M1S3S2bS4eVc;S4fVcur;A1A4S0G1S3S2bS4eSd5Vc;A1S4fS2eA1A4S2G1A1A3A3G0A4").
Definition cB : Z := 696.
Definition NCO (cur : sv) : sv := ltac2:(tb__ "0|0|
S16Sc5S73S16Sc6Vcur;S2eA3A3").
Definition pairs7 (nmi kmi nfv kfv nmm kmm nsg ksg nrp krp ntr ktr nts kts : sv) : list bitem := ltac2:(tb__ "0|1|
S4S4dS2fZcVnmi;Vkmi;A3S4S4dS2fZ4M0Vnfv;Vkfv;A3S4S4dS2fG0Vnmm;Vkmm;A3S4S4dS2fG0Vnsg;Vksg;A3S4S4dS2fG0Vnrp;Vkrp;A3S4S4dS2fG0Vntr;Vktr;A3S2fZ1Vnts;Vkts;A3A3A3A3A3A3A3").
Definition pairs7e : list bitem := ltac2:(tb__ "0|0|
SbbS6bS56S69S55S6dS57S70S5aS75S59S76S5bS77S5cAe").
Definition bd_loop (cur kco : sv) : list bitem := ltac2:(tb__ "0|0|
S4S4dS0S4dS39S7dVcur;A2S0S4dS9dSb0Vcur;A2S2S4dA1A3A3S4S4dS2fZcS7bVcur;A1Vkco;A3SbcA3A3").
Definition ndL (cur dco kco : sv) : ndesc := ltac2:(tb__ "0|0|
S109S9aVdco;Vkco;A2S91SafVcur;Vkco;A2S108A4").

Definition BCUT (pc : Z) (regs : list (nat * sv)) (cur dco cco kco : sv) (fx fcells txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S10dS1bVpc;S4bVregs;A1S4aS1aS6SfA1Sb9Vcur;S97Vdco;Vcco;Vkco;Vfx;Vfcells;Vtxt;A8Vfacts;S41S7A9S8aVdco;Vkco;A2A2").

Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur : sv) (fx : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S79Vpc;Vregs;Vcur;S7fS53S80Vfx;S2S11A1M0G0S4S10Vfacts;S7cVcur;S53Vrcur;S7fS80P12fA6A3Aa").

Definition H : axst := ltac2:(tb__ "0|0|
S72Se8S74S6eS6eS2S11A1S2S10A1A6").
Goal leaf_matches1A NPH C_pre H = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs H = [(hf_A, RsCut); (hf_L1, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition L1 : axst := ltac2:(tb__ "0|2|
S72SeaS4S5S1SfA2M0S74S0G0S3S1SfUaS33S51A1M1A4S0G0S3S1SfUbS33S36A1A4S0G0S3S1SfU14G1A4S2G0A1A3A3A3A3S6eS6eS2S11A1S0S10S14S6eS51A2S0S10S17S51S36A2S2S10A1A3A3A6").

Definition cA : list cell := [].
Definition L2 : axst := ltac2:(tb__ "0|2|
S72SebS4S5S1SfA2M0S74S0G0S3S1SfUaS33S51A1M1A4S0G0S3S1SfUbS33S36A1A4S0G0S3S1SfUcG1A4S0G0S3S1SfU14S33S58A1A4S2G0A1A3A3A3A3A3S51S58S8eS0S10S14S58S51A2S0S10S17S51S36A2S2S10A1A3A3A6").

Definition K : axst := ltac2:(tb__ "0|1|
S72Se9S4S5S1SfA2M0S74S0G0S3S1SfUbS33S36A1A4S0G0S3S1SfU14S33S58A1A4S2G0A1A3A3A3S51S58S8eS0S10S17S58S51A2S2S10A1A3A6").
Goal lvs L1 = [(hf_A, RsCut); (hf_L1, RsCut); (hf_A, RsCut); (hf_L1, RsCut); (hf_L2, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs L2 = [(hf_K, RsCut); (hf_K, RsCut); (hf_L2, RsCut); (hf_K, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K = [(hf_EPI, RsCut); (hf_EPI, RsCut); (vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition leaves_at2 (Ss : list axst) (pc : Z) : list axst := ltac2:(tb__ "0|0|
S12cScdScdScdS10cS7aS7eR1Vpc;A4LS;VSs;A4").
Goal map (fun L => leaf_matches1A NPH L L1) (leaves_at2 [H; L1] hf_L1) = [true; true; true]
  /\ map (fun L => leaf_matches1A NPH L L2) (leaves_at2 [L1; L2] hf_L2) = [true; true]
  /\ map (fun L => leaf_matches1A NPH L K) (leaves_at2 [L2] hf_K) = [true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_co0 : axst := Eval vm_compute in leaf_at K vr_entry 0.
Definition xf_vr (i : nat) (o : Z) : list axform := ltac2:(tb__ "0|2|
S0Sc8SccU0M0S12N40M1A1A2S0Sc8Sc9G0G1A2S0Sc8Sc9Vi;Vo;A2S2Sc8A1A3A3A3").

Definition co_need (cur : sv) : list sprop := ltac2:(tb__ "0|0|
S0S10S14S2dZcS7bVcur;A1A2S12S28A1A2S2S10A1A3").
Definition E_co : axst := Eval vm_compute in ax_add_facts (co_need pQ) (optAp (apply_axforms E_co0 (xf_vr 19 720))).
Definition s_co : wsub := ltac2:(tb__ "0|1|
S0S5S2cSfA2M0S3S2cSfP3bS7bS51A1A4S0G0S3S2cSfP13S16Sc5S27S12Z40A1A3A4S117PaSceS9fA1SceS11dA1A3A3A3").
Definition R_co : list sobj := Eval vm_compute in optR (entails_frA E_co VN.Pre_vr s_co).
Definition PD_vn : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5ScdS106A2M0S3ScdS106S11cS11fA4S0G0S3ScdS106S11aS107S120S2S5S5SfS2bA2SfA2A1M1S2S4dA1A3A4S0G0S3ScdS106S11bS107S121G1S11eS123S122A2A3A4S2G0A1A3A3A3").
Goal entails_frA E_co VN.Pre_vr s_co = Some R_co /\ call_checkPA E_co VN.Pre_vr s_co R_co (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xkeep (dco : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S12bS5SfSfA2M0G0SdS23SbSfSfR1A3Vdco;A2A1Lr;S8aVdco;S80A2A3").
Definition T_cok0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_keep (Xkeep pDco).
Definition T_cof0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_fail (Xkeep pDco).
Definition T_cog0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_co s_co R_co VN.P_grown (Xkeep pDco).

Definition sel_back : list nat := ltac2:(tb__ "0|0|
S0S1U1S0S1U0S0S1U7S0S1U8S0S1U5S0S1U6S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U2S0S1U16S0S1U17S0S1U18S0S1U19S0S1U3S0S1U1aS0S1U1bS0S1U1cS0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U4S0S1U22S0S1U23S0S1U24S2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_back : list axform := ltac2:(tb__ "0|0|
S0Sc8Sc9U1Z40A2S0Sc8ScbSbeA1S0Sc8ScaU0A1S0Sc8Sc9U12N2d0A2S2Sc8A1A3A3A3A3").
Definition T_cok : axst := Eval vm_compute in optAp (apply_axforms T_cok0 xf_back).
Definition T_cof : axst := Eval vm_compute in optAp (apply_axforms T_cof0 xf_back).
Definition T_cog : axst := Eval vm_compute in optAp (apply_axforms T_cog0 xf_back).
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S8S5S5SfSfA2SfA2A1") := ltac2:(tb__ "0|1|
S112S13S5S5SfSfA2M0SfA2S13S3G0SfS3SfSfS20R1A1S22R1A1A4S21R1A1A4Lo;S1dSceVA;A1A1A4").

Definition pD2 : sv := SVar 307. Definition pK2 : sv := SVar 308.
Definition cR : list cell := ltac2:(tb__ "0|0|
S0S11S24N98S8cA2S0S11S24Na8S98Z0A1A2S2S11A1A3A3").
Definition lregsR (a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SfA2M0S95S0G0S3S1SfU1S12S105A1A4S0G0S3S1SfUaVa0;A4S0G0S3S1SfU13S33S51A1A4S0G0S3S1SfU14S33S58A1A4S0G0S3S1SfU16S52Z2d8A1A4S0G0S3S1SfU18S53A4S2G0A1A3A3A3A3A3A3A3").

Definition slot_facts (c k : sv) : list sprop := ltac2:(tb__ "0|3|
S0S10S14S16Sc5S2dZcM0Vc;A2M1S12G0A1A3S2dG0Vk;A2M2A2S0S10S14G1G2A2S0S10S14G1S12S25A1A2S2S10A1A3A3A3").
Definition JR_co : axst := ltac2:(tb__ "0|2|
S79S115S96S12Z1A1M0A1S51S65S53S64S8fS2S11A1M1G1S4S10S0S10S17S58S51A2S0S10S17S53S12Sd3Z2Z14A2A1A2S0S10S14S16Sc5S53G0A3S64A2S0S10S14S12S111A1S65A2S2S10A1A3A3A3A3S4S10Sc1S53S64A2S7cS51S53S58S65S64P133A6A3A3Aa").
Definition JF_co : axst := ltac2:(tb__ "0|1|
S79S115S96S12Z0A1A1S51S65S53S64S8fS2S11A1M0G0S4S10S0S10S17S58S51A2S0S10S17S53S12Sd3Z2Z14A2A1A2S2S10A1A3A3S7cS51S53S58S65S64P133A6A3Aa").
Definition ndR : ndesc := ltac2:(tb__ "0|0|
Sb8S51S65S64A3").
Definition ndFc : ndesc := ltac2:(tb__ "0|0|
S109S9aS65S64A2S91S0S4dS39S7dS51A2S2S4dA1A3S108A4").

Definition T_coks : axst := ltac2:(tb__ "0|0|
S126S0S10S14S12S111A1S7fA2S2S10A1A3Sa8A2").
Goal map (fun L => leaf_matches1A NPH L JR_co) [T_coks; T_cog] = [true; true] /\ leaf_matches1A NPH T_cof JF_co = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_co = [(hf_ZX, RsCut)] /\ lvs JF_co = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition slot (d c : sv) : sv := ltac2:(tb__ "0|0|
S16Sc5Vd;S2dZcVc;A2A3").
Definition slot_obj (d c : sv) : sobj := ltac2:(tb__ "0|0|
S18Sc0Vd;Vc;A2S12Z0A1S12ZcA1S2S11A1S19A5").
Definition mid_slot (d c : sv) (dfl : odefault) : sobj := ltac2:(tb__ "0|2|
S18Vd;S2dZcM0Vc;A2M1S16Sc5G1S12G0A1A3S2S11A1Vdfl;A5").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
Sd1VA;S127SceVA;A1Vi;Vo;A3A2").

Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).

