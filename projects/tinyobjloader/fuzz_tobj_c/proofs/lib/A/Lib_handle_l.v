(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "None"; "false"; "option"; "list"; "length"; "true"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "SLit"; "sobj"; "SPUle"; "SAlu"; "SVar"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPUlt"; "mkSS"; "SPAlign"; "SPBranch"; "SPNot"; "ss_facts"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "B32"; "vDp"; "spm"; "B_EW"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXRebase"; "apply_axforms"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l"; "xbo"; "pQ"; "pC"; "li_n"; "pD"; "pK"; "pT0"; "HC"; "lregs1"; "pP"; "X_hl"; "cmul12"; "lc_n"; "FUEL_hl"; "O_F"; "O_Wl"; "builderL"; "cutpcs_hl"; "pHP"; "room4_fact"; "room_fact"; "F_cells"; "O_flag"; "body_facts"; "gB"; "gC"; "ghostL_facts"; "hdr3"; "lregs0"; "optAp"; "pN"; "pX"; "reshapeA"; "shC"; "slot_facts"; "xfo"; "BAD"; "BIG"; "C24"; "E_da"; "E_pc"; "E_sm0"; "E_vr"; "JC"; "NA"; "O_frame"; "P_caps"; "P_matl"; "Pre_hl_S"; "Pre_mc"; "Pre_sm"; "T_grown0"; "T_keep0"; "V624"; "V656"; "X_tok"; "bd_hl"; "dst_obj"; "frame_factsH"; "hl_facts"; "idx_obj"; "lregs"; "mid_dst"; "objs_body"; "objs_hl"; "objs_tok"; "pC1"; "prog_fact"; "sel_body"; "shB"; "shF"; "tv_hl"; "vKg"; "xMATl"; "xSMOl"; "xf_cm"; "xf_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hF"; "lc_k"; "lc_d"; "kb"; "lc_c"; "li_c"; "tE"; "tI"; "tp"; "O_data"; "li_k"; "hFL"; "li_d"; "vec_facts"; "O_cE"; "O_cP"; "hG"; "tB"; "tL"; "HNEXT"; "bd_vec"; "cnt_facts"; "h_fregs"; "h_xregs"; "handle_facts"; "xHASPRIM"; "NPH"; "O_text"; "PROG"; "P_cur"; "P_hdr"; "V120"; "V216"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "FE"; "sym_runA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.HLAddr"; "FR"; "DW"; "hl_H"; "hl_J"; "hl_K"; "hl_L1"; "hl_L2"; "hl_N"; "hl_EPI"; "hl_FP"; "hl_OK"; "hl_PRO"; "hl_REL"; "hl_REP"; "hl_REP2"; "hl_RP8"; "hl_UNP"; "hl_entry"; "memcpy_pc"; "sm1_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "SHB"; "segs"; "leavesA_at"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "vc"; "O_al"; "vERR"; "c4"; "piece"; "P_alloc"; "P_st"; "V184"; "c1"; "vAL"; "vNC"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Corelib.Init.Nat"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "xlocal"].
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN. End VN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HLAddr.
  Definition hl_entry : Z := 0xa07f0.
  Definition sm1_pc : Z := 0x47a7c.
  Definition memcpy_pc : Z := 0x5c84c.
  Definition hl_PRO : Z := 0xa0910.
  Definition hl_H : Z := 0xa09e0.
  Definition hl_L1 : Z := 0xa0a0c.
  Definition hl_L2 : Z := 0xa0a70.
  Definition hl_K : Z := 0xa0a98.
  Definition hl_UNP : Z := 0xa0abc.
  Definition hl_J : Z := 0xa0c24.
  Definition hl_REP : Z := 0xa0ce0.
  Definition hl_REP2 : Z := 0xa0cec.
  Definition hl_FP : Z := 0xa0d3c.
  Definition hl_N : Z := 0xa0d60.
  Definition hl_OK : Z := 0xa0e7c.
  Definition hl_RP8 : Z := 0xa0f98.
  Definition hl_EPI : Z := 0xa0e2c.
  Definition hl_REL : Z := 0xa0fe4.
  Definition hl_ret : Z := 0xa1020.
  Definition hl_ra_pc : Z := 0xa0bc4.
  Definition hl_ra_da : Z := 0xa0c24.
  Definition hl_ra_da2 : Z := 0xa0dd0.
  Definition hl_ra_vr : Z := 0xa0c5c.
  Definition hl_ra_vr2 : Z := 0xa0ee0.
  Definition hl_ra_mc : Z := 0xa0cbc.
  Definition hl_ra_mc2 : Z := 0xa0f30.
  Definition DW : Z := 4640.
  Definition FR : Z := 288.
End HLAddr.
Import HLAddr.

Definition FUEL_hl : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S14PaA1S10Sd7Sa9A1A1S10Z0A1Vcells;S15A5").
Definition O_Wl : sobj := ltac2:(tb__ "0|0|
S16S22Sa9A1S21S10Z0A1S2SfA1S15A5").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
ScaZ20M0Z60S0SfS1fG0S10S56A1M1A2S0SfS1fZ28G1A2S0SfS1fZ30G1A2S0SfS1fZ38S10Sd5Z2M2Z14A2A1A2S0SfS1fZ40S10Sd5G2Z18A2A1M3A2S0SfS1fZ48G3A2S0SfS1fZ50G3A2S0SfS1fZ58G1A2S2SfA1A3A3A3A3A3A3A3A3A3").
Definition V624 (d c k : sv) : sobj := V 624 d c k 12.
Definition V656 (d c k : sv) : sobj := V 656 d c k 4.

Definition room_e (e : Z) (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S12S13S2eS81Ve;Vcnt;A2S81Ve;S84A2A3S13S2eS10Sd8S23Ve;A2A1S81Ve;Vcur;A2A3A2").
Definition room_fact (cnt cur : sv) : sprop := room_e 12 cnt cur.

Definition prog_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S12S13S2eVcnt;S85A3S13S2eS83Vcur;A3A2").

Definition li_n : sv := SVar 129.
Definition NA (cur : sv) : sv := ltac2:(tb__ "0|0|
S13S2eS34S13S2fVcur;S85A3A3").
Definition PHIN (cur k : sv) : bitem := PHIe 12 (NA cur) k.

Definition room4_fact (cnt : sv) : sprop := room_e 4 cnt tI.

Definition lc_n : sv := SVar 130.
Definition ghostL_facts : list sprop := ltac2:(tb__ "0|0|
S0SeS12S82S3dA2S0SeS12S3dS10S20A1A2S0SeS44S3dA1S2SeA1A3A3A3").
Definition hl_facts : list sprop := ltac2:(tb__ "0|0|
S4SeS96Sa9SaaA2S4SeS93S4SeS0SeS12S97S10Z1A1A2S0SeS12S83S34A2S0SeS12S34S10S20A1A2S0SeS45S34S85A2S0SeS44S82A1S2SeA1A3A3A3A3A3S4SeS4bS4SeS8bS8aS83S88ZcP7bA5S8bS80S82S7fZ4P7eA5A3A3A3A3A3").
Definition X_hl (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdSc5S10Z518A1A4S0G0S3SdSdSc6S10Z10A1A4S0G0S3SdSdScfS10Z30A1A4S0G0S3SdSdS8fS90A4S0G0S3SdSdVd;S81ZcVk;A2A4S0G0S3SdSdVd2;S81Z4Vk2;A2A4S0G0S3SdSdS22SaaA1S10SaaA1A4S2G0A1A3A3A3A3A3A3A3").

Definition xMATl : sv := SVar 139. Definition xSMOl : sv := SVar 140.
Definition P_matl : sobj := ltac2:(tb__ "0|1|
ScaZ4e8M0Z518S0SfSc9G0S7aA2S0SfSc9Z4ecS7bA2S0SfSceZ4f0S10Z0A1A2S2SfA1A3A3A3A3").
Definition builderL (err hp : sv) (d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|0|
S0S11ScbS0S11S9cS0S11S5fS0S11SccVerr;A1S0S11S9dS0S11ScdSd1Sd0Sd2A3S0S11S9eS0S11S66Vd;Vc;Vk;A3S0S11S67Vd2;Vc2;Vk2;A3S0S11S9bVhp;A1S0S11S60S2S11A1A3A3A3A3A3A3A3A3A3A3A3").
Definition objs_hl (cur err hp d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S3fS2SfA1A1S0S11S40S2S11A1M0A3A3S4S11S41Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S4S11S0S11Sc7S0S11S8dVcur;A1S0S11S8cS0S11S99S0S11S87Vd;ZcVk;A3S0S11S87Vd2;Z4Vk2;A3G0A3A3A3A3A3A3SbfA3A3A3").
Definition Pre_hl_S : sstate := ltac2:(tb__ "0|0|
S19SbaSf0SefS17S6SdA1S71S85Sc8S97S8aS83S88S80S82S7fA9S6cS98S7A9").
Definition Pre_hl : axst := ltac2:(tb__ "0|0|
SbeS61S3bS8aS88S80S7fA4A2").

Definition C24 : bitem := BIc 1 0 24.

Definition bd_hl (n k c2 k2 cur : sv) : list bitem := ltac2:(tb__ "0|1|
S4Sa5S0Sa5S9aZ48Vcur;A2S2Sa5A1M0A3S4Sa5S92ZcVn;Vk;A3S4Sa5S92Z4Vc2;Vk2;A3S0Sa5S57G0A3A3A3A3").
Definition tv_hl (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdVd;S81ZcVk;A2A4S0G0S3SdSdVd2;S81Z4Vk2;A2A4S2G0A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
Sd4S78S8aS88S80S7fA4S2S5S5SdS2cA2SdA2A1S69S34S88S3dS7fS85A5A3").

Definition tvI (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdVd2;S81Z4Vk2;A2A4S0G0S3SdSdVd;S81ZcVk;A2A4S2G0A1A3A3").

Definition cutpcs_hl : list Z := ltac2:(tb__ "0|0|
S0S2cSbcS0S2cSb4S0S2cSabS0S2cSaeS0S2cSafS0S2cSadS0S2cSb9S0S2cSe9S0S2cSddS0S2cSacS0S2cSebS0S2cSbbS0S2cSb6S0S2cSb7S0S2cSb2S0S2cSb0S0S2cSb3S0S2cSb8S0S2cSb1S0S2cSb5S2S2cA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
SbeS19Z0S2SdA1M0G0S17S6SdA1S2S11A1S2SeA1P1S7A9S2S5SdSdA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa8Sa0Vk;Sc2S3eS42VS;Vpc;A4S55A4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SaSa1S8S9Sa1A1M0A1G0Lx;Sa3Sc1S3eS42VS;SbA5G0R1Ll;S2Sa1A1X8x2A2").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S8S9Sa1A1M0A1S9S5S2cSecA2M1A1Lx;Sa3Sc1S3eS42VS;SbA5G0Sa7Sa1G1Sc4R1A4Ll;S2G1A1X8x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hl sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S2dSdA2S3S2dSdSdbS21A4SbdPaS9fS5aA1S9fS63A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hl = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hl : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SdS2cA2M0SdA2M1S3G0SdS3SdS2cS7eZ1A4S89A4S2G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S1Sa6U0Vi;A2S4S1Sa6ScVi;A1M0SdcSaS11S1eS9fVA;A1A1A2G0A2A2S0S1Vi;S2S1A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_hl li_d li_k lc_d lc_k ++ (hF, SLit 128) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 (X_hl li_d li_k lc_d lc_k) 160 128.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_pro : axst := Eval vm_compute in leaf_at C_pro hl_PRO 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_pro)) O_Wl.
Definition objs_pro : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_pro)).
Goal lvs C_pro = [(hl_PRO, RsCut)] /\ sh_pro = shobj hG 0 16 (ob_cells sh_pro) DZero.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_pre : axst := Eval vm_compute in shadow_release_stateA X_pro objs_pro 160 [].
Definition X_H0 : axst := Eval vm_compute in leaf_at C_pre hl_H 0.
Goal lvs C_pre = [(hl_H, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition pP : sv := SVar 300. Definition pT0 : sv := SVar 301. Definition pQ : sv := SVar 302.
Definition pD : sv := SVar 303. Definition pC : sv := SVar 304. Definition pK : sv := SVar 305. Definition pHP : sv := SVar 306.
Definition pN : sv := SVar 418.
Definition gB : positive := 191%positive.
Definition gC : positive := 192%positive.
Definition shF : sv := ltac2:(tb__ "0|0|
S13S2eS14S8eA1S10Sc0A1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S13S2eS14S4aA1S10Sd6Sc0Vk;A2A1A3").
Definition shB (k : Z) : sv := ltac2:(tb__ "0|0|
S13S2eS14S49A1S10Sd6Sc0Vk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S13S2eSc5S10Vo;A1A3").
Definition xfo (o : Z) : sv := ltac2:(tb__ "0|0|
S13S2eS7eS10Vo;A1A3").

Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0SfS1fN120S13S2eSc6S10Z8A1A3A2S0SfS1fN118S83A2S0SfS1fN110S54Z40A1A2S0SfS1fN108S7eA2S0SfS1fN100S7eA2S0SfS1fNf8S31Z10A1A2S0SfS1fNf0S31Z68A1A2S0SfS1fNe8S10ZffffffffaaaaaaabA1A2S0SfS1fNe0S31Z508A1A2S0SfS1fNd8S31Z500A1A2S0SfS1fNd0S31Z4f8A1A2S0SfS1fNc8S31Zc0A1A2S0SfS1fNc0S31Ze0A1A2S0SfS1fNb8S31Z80A1A2S0SfS1fNb0S31Z4f0A1A2S0SfS1fNa8S52Z1A1A2S0SfS1fNa0S31Z38A1A2S0SfS1fN98S54Z20A1A2S0SfS1fN90S31Z270A1A2S0SfS1fN88S76Z4fA1A2S0SfS1fN70S7eA2S0SfS1fN68S14P2fA1A2S0SfS1fN60S14P2eA1A2S0SfS1fN58S14P2dA1A2S0SfS1fN50S14P2cA1A2S0SfS1fN48S14P2bA1A2S0SfS1fN40S14P2aA1A2S0SfS1fN38S14P29A1A2S0SfS1fN30S14P28A1A2S0SfS1fN28S14P27A1A2S0SfS1fN20S14P26A1A2S0SfS1fN18S14P1dA1A2S0SfS1fN10S14P1cA1A2S0SfS1fN8S14PbA1A2S2SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0SfS1fZ0S10Z41b58ab3A1A2S0SfS1fZ8S10Z160beA1A2S0SfS1fZ10S10Za07f0A1A2S2SfA1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S7eS10Z0A1S10Z78A1Vcells;S15A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S16S7eS10Z78M0A1S10Z80A1S0SfS1fG0S89A2S2SfA1A3S15A5").

Definition objs_body (cur hp d c k : sv) (fcells txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S40S0S11S5eS4SfS4cVfcells;A3A1S0S11S47S2S11A1M0A3A3A3S4S11SbfS4S11S0S11S3fS46A1G0A3S4S11S41Sc8Vhp;Vd;Vc;Vk;S80S82S7fA8S0S11Sc7S0S11S8dVcur;A1S0S11S8cS0S11S16S8fS10Z0A1S90Vtxt;S15A5S0S11S87Vd;ZcVk;A3S0S11S87S80Z4S7fA3G0A3A3A3A3A3A3A3A3A3A3").
Definition lregs0 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SdA2M0S3S1SdU2S22Sa9A1M1A4S0G0S3S1SdU8S14PaA1A4S0G0S3S1SdU9G1A4S0G0S3S1SdU13Sc5A4S0G0S3S1SdU14Sc6A4S0G0S3S1SdU15S10Z20A1A4S0G0S3S1SdU16S31Z278A1A4S0G0S3S1SdU17S77A4S0G0S3S1SdU18Sc3A4S0G0S3S1SdU19S52Z0A1A4S0G0S3S1SdU1aS10Z9A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition lregs1 : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SdA2M0S4dS0G0S3S1SdU10S31Z38A1A4S2G0A1A3A3").
Definition lregs : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SdA2M0S39S0G0S3S1SdUbS31Z288A1A4S2G0A1A3A3").
Definition frame_factsH : list sprop := ltac2:(tb__ "0|1|
S4SeSa2S4aSc6A2S4SeSa2S49Sc5A2S4SeSa2S8eS7eA2S0SeS1aPa0Z5A2S0SeS1cS1bS30S7eS10Z0A1A3A1S0SeS12S10SdaA1M0S7eA2S0SeS12S13S2eS7eS10Z80A1A3S14P1eA1A2S0SeS12S7eS10S24A1A2S0SeS12G0S89A2S0SeS12S13S2eS89S10Z1A1A3S10Z7fffff800000A1A2S2SeA1A3A3A3A3A3A3A3A3A3A3").

Definition body_facts (cur rc rcur d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4SeS96Sa9SaaA2S4SeS93S4SeS0SeS12S43S10Z1A1A2S0SeS45S34S85A2S0SeS45Vrc;Vrcur;A2S0SeS74Vrc;Vrcur;A2S0SeS12S83Vc;A2S0SeS12S83S34A2S0SeS12S34S10S20A1M0A2S0SeS12S83G0A2S0SeS12S85Vrcur;A2S0SeS12Vrcur;Vcur;A2S0SeS12Vcur;S84A2S0SeS44S82A1S0SeS12S4fS10Sd5Z2Z14A2A1A2S2SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3S4SeS4bS4SeS8bVd;Vc;Vk;ZcVdv;A5S4SeS8bS80S82S7fZ4P7eA5S6bA3A3A3A3A3A3").
Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur d c k : sv) (dv : positive) (fcells txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SbeS19Vpc;S95Vregs;A1S94S17S6SdA1S70Vcur;S43Vd;Vc;Vk;Vfcells;Vtxt;A7S4SeVfacts;S48Vcur;Vc;Vrcur;Vd;Vc;Vk;Vdv;A7A3S91S7A9S3bVd;Vk;S80S7fA4A2").

Definition H : axst := ltac2:(tb__ "0|1|
S38SabS6eS3aS3aS35S33S36P12fS2SfA1M0G0S2SeA1Ab").

Definition L1 : axst := ltac2:(tb__ "0|3|
S38SaeS4S5S1SdA2M0S39S0G0S3S1SdUaS86S32A1M1A4S0G0S3S1SdUbG1A4S0G0S3S1SdUcS86S84A1A4S0G0S3S1SdU1bS31Z288A1A4S2G0A1A3A3A3A3A3S3aS3aS35S33S36P12fS2SfA1M2G2S0SeS12S3aS32A2S0SeS18S32S84A2S2SeA1A3A3Ab").

Definition L2 : axst := ltac2:(tb__ "0|3|
S38SafS4S5S1SdA2M0S39S0G0S3S1SdUaS86S37A1A4S0G0S3S1SdUbS86S32A1M1A4S0G0S3S1SdUdG1A4S0G0S3S1SdUcS86S84A1A4S0G0S3S1SdU1bS31Z288A1A4S2G0A1A3A3A3A3A3A3S32S37S35S33S36P12fS2SfA1M2G2S0SeS12S37S32A2S0SeS18S32S84A2S2SeA1A3A3Ab").

Definition K : axst := ltac2:(tb__ "0|2|
S38SadS4S5S1SdA2M0S39S0G0S3S1SdUaS86S37A1A4S0G0S3S1SdUcS86S84A1A4S0G0S3S1SdU1bS31Z288A1A4S2G0A1A3A3A3A3S32S37S35S33S36P12fS2SfA1M1G1S0SeS18S37S32A2S2SeA1A3Ab").

Definition pX : sv := SVar 307.
Definition XN : axst := ltac2:(tb__ "0|1|
S38Sb0S39S50S50S35S33S36P12fS2SfA1M0G0S2SeA1Ab").
Goal lvs H = [(hl_N, RsCut); (hl_L1, RsCut)] /\ lvs L1 = [(hl_N, RsCut); (hl_L1, RsCut); (hl_N, RsCut); (hl_L1, RsCut); (hl_L2, RsCut)]
  /\ lvs L2 = [(hl_K, RsCut); (hl_K, RsCut); (hl_L2, RsCut); (hl_K, RsCut)] /\ lvs K = [(hl_EPI, RsCut); (hl_EPI, RsCut); (hl_UNP, RsCut)]
  /\ lvs XN = [(hl_OK, RsCut); (da_entry, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_unp0 : axst := Eval vm_compute in leaf_at K hl_UNP 0.
Definition C_unp : axst := Eval vm_compute in shadow_reopen_stateA E_unp0 (ax_X E_unp0) hG 4 6.

Definition E_pc0 : axst := Eval vm_compute in leaf_at C_unp pc_entry 0.
Goal lvs C_unp = [(pc_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sh_unp : sobj := Eval vm_compute in last (ss_objs (ax_S E_pc0)) O_Wl.
Definition objs_pc0 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_pc0)).
Goal sh_unp = shobj hG 4 6 (ob_cells sh_unp) DUnknown /\ local_ok (ob_cells sh_unp) DUnknown 4 6 (32, 12) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_pc1 : axst := Eval vm_compute in shadow_release_stateA E_pc0 objs_pc0 160 [(32, 12)].
Definition idx_obj (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S7eS10Z20A1S10Z2cA1Vcells;S15A5").

Definition xf_pc : list axform := ltac2:(tb__ "0|2|
S0S25S26U0S10N40A1A2S0S25S26U2S10Z20M0A1A2S0S25S26U3M1S10Z2cA1A2S0S25S27G1G0A2S2S25A1A3A3A3A3").
Definition E_pc : axst := Eval vm_compute in optAp (apply_axforms E_pc1 xf_pc).
Definition s_pc : wsub := ltac2:(tb__ "0|0|
SbdPaS9fS59A1S9fSeaA1A3").
Definition R_pc : list sobj := Eval vm_compute in optR (entails_frA E_pc Pre_pc s_pc).
Goal entails_frA E_pc Pre_pc s_pc = Some R_pc /\ call_checkA E_pc Pre_pc s_pc R_pc (map la_state Posts_pc) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
Sd9S1dS9fVCl;A1A1SedVs;VPre;VL;VCl;VR;A5A2").
Definition T_pc0 : axst := Eval vm_compute in T_pure Pre_pc E_pc s_pc R_pc P_ret.

Definition xf_tpc : list axform := ltac2:(tb__ "0|2|
S0S25S29S4S1S0S1U5S0S1U0M0S0S1U1S0S1U2M1S0S1U3S0S1U4S2S1A1A3A3A3A3A3A3Sa6U6U14A2A3A1S0S25S28G0A1S0S25S2aG1A1S2S25A1A3A3A3").
Definition T_pc : axst := Eval vm_compute in optAp (apply_axforms T_pc0 xf_tpc).

Definition E_da0 : axst := Eval vm_compute in leaf_at T_pc da_entry 0.
Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
SbdPaS9fS58A1S9fSdeA1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0S25S29S4S1S0S1U3S0S1U0M0S0S1U4S0S1U5S0S1U1S0S1U2S2S1A1A3A3A3A3A3A3Sa6U6U14A2A3A1S0S25S28G0A1S2S25A1A3A3").
Definition T_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).

Definition objs_tok (cur hp d c k : sv) (idxc : list cell) : list sobj := ltac2:(tb__ "0|3|
S4S11S0S11S40S0S11S16S8fS10Z0A1M0S90S2SfA1M1S15A5S0S11S6dVidxc;A1S2S11A1M2A3A3A3S4S11SbfS4S11S0S11S16S7eG0S10Z20A1S4cS15A5S0S11S16S7eS10Z2cA1S10Z78A1G1S15A5S0S11S47S0S11S3fS46A1G2A3A3A3A3S4S11S41Sc8Vhp;Vd;Vc;Vk;S80S82S7fA8S0S11Sc7S0S11S8dVcur;A1S0S11S8cS0S11S87Vd;ZcVk;A3S0S11S87S80Z4S7fA3G2A3A3A3A3A3A3A3A3A3").
Definition X_tok (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SdSdA2Sf2Pa0S3S2cS2cZ20ZcA4A2S3bVd;Vk;S80S7fA4A3").

Definition pC1 : sv := SAlu ALU_ADD pC (SLit 1).
Definition JC (pc : Z) (regs : list (nat * sv)) (cur d c k : sv) (dv : positive) (idxc : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SbeS19Vpc;S95Vregs;A1S94S17S6SdA1S72Vcur;S43Vd;Vc;Vk;Vidxc;A6S4SeVfacts;S48Vcur;S73Vcur;Vd;Vc;Vk;Vdv;A7A3S91S7A9S68Vd;Vk;A2A2").
Definition J : axst := ltac2:(tb__ "0|1|
S5cSacS4S5S1SdA2M0S4dS0G0S3S1SdU1bS31Z288A1A4S2G0A1A3A3S32S35S33S36P12fS2SfA1S0SeS18S4fS10Sd5Z2Z14A2A1A2S2SeA1A3A9").
Goal lvs T_pc = [(hl_J, RsCut); (hl_J, RsCut); (da_entry, RsCut)] /\ lvs T_da = [(hl_J, RsCut)]
  /\ map (fun L => leaf_matchesA NPH L [J]) (leavesA_at FUEL_hl cutpcs_hl T_pc hl_J ++ leavesA_at FUEL_hl cutpcs_hl T_da hl_J) = [true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at J vr_entry 0.
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S25S26U0M0S10N40M1A1A2S0S25S27G0G1A2S0S25S27U11Z270A2S2S25A1A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).
Definition s_v : wsub := ltac2:(tb__ "0|1|
S0S5S2dSdA2M0S3S2dSdP3bS5dS32A1A4S0G0S3S2dSdP13S13S2eS21S10Z40A1A3A4SbdPaS9fS5bA1S9fSe2A1A3A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr VN.Pre_vr s_v).
Definition PD_vn : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5Sa0Sd3A2M0S3Sa0Sd3Se1Se4A4S0G0S3Sa0Sd3SdfSd4Se5S2S5S5SdS2cA2SdA2A1M1S2Sa5A1A3A4S0G0S3Sa0Sd3Se0Sd4Se6G1Se3Se8Se7A2A3A4S2G0A1A3A3A3").
Goal lvs J = [(vr_entry, RsCut)] /\ entails_frA E_vr VN.Pre_vr s_v = Some R_v /\ call_checkPA E_vr VN.Pre_vr s_v R_v (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) pD)) (X_tok pD pK).
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_grown Xk_v.

Definition cmul12 (c : sv) : sv := SMd M_MUL c (SLit 12).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0SeS12S13S2eS3cS33A1M0S10ZcM1A1A3S81G1Vk;A2M2A2S0SeS12G0G2A2S0SeS12G0S10S20A1A2S2SeA1A3A3A3").
Definition vDg : sv := SVar 520.
Definition vKg : sv := SVar 521.
Definition T_keep : axst := ltac2:(tb__ "0|0|
Sd9S4SeS53S36A1S0SeS12S10SdaA1S35A2S2SeA1A3A3S65A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
Sd9S53S79A1S64A2").
Definition E_mk0 : axst := Eval vm_compute in leaf_at T_keep memcpy_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leaf_at T_grown memcpy_pc 0.
Goal lvs T_keep = [(memcpy_pc, RsCut)] /\ lvs T_grown = [(memcpy_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S16S13S2eVd;S3cS33A1A3S10Z0A1S10ZcA1S2SfA1S15A5").
Definition xf_mc : list axform := ltac2:(tb__ "0|3|
S0S25S27U1M0Z40A2S0S25S27U8Z20A2S0S25S29S4S1S0S1G0S0S1U0M1S2S1A1A3A3Sa6U2U18A2A3A1S0S25S28G1A1S0S25S26U3S3cS33A1M2A2S0S25S26U4S13S2eG2S10ZcA1A3A2S2S25A1A3A3A3A3A3A3").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
Sa4VA;SeeS9fVA;A1Vi;Vo;A3A2").
Definition E_mc (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S51S4eS2bVE0;S7dA2A1U4S6aVd;A1A3").
Definition E_mk : axst := Eval vm_compute in E_mc E_mk0 pD.
Definition E_mg : axst := Eval vm_compute in E_mc E_mg0 vDg.
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|2|
S0S5S2dSdA2M0S3S2dSdP35Vd;A4S0G0S3S2dSdP36S81ZcM1Vk;A2A4S0G0S3S2dSdP37S13S2eS7eS10Z20A1A3A4S0G0S3S2dSdP38S10G1A1A4S0G0S3S2dSdSdbS21A4SbdPaS9fVE;A1S9fS62A1A3A3A3A3A3A3").
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_mk Pre_mc (s_mc E_mk pD pK)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg)).
Goal entails_frA E_mk Pre_mc (s_mc E_mk pD pK) = Some R_mk /\ call_checkPA E_mk Pre_mc (s_mc E_mk pD pK) R_mk [L_mc1; L_mc1] = true
  /\ entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg) = Some R_mg /\ call_checkPA E_mg Pre_mc (s_mc E_mg vDg vKg) R_mg [L_mc1; L_mc1] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_mck : axst := Eval vm_compute in T_afterA Pre_mc E_mk (s_mc E_mk pD pK) R_mk L_mc1.
Definition T_mcg : axst := Eval vm_compute in T_afterA Pre_mc E_mg (s_mc E_mg vDg vKg) R_mg L_mc1.

Definition X_rpk : axst := Eval vm_compute in leaf_at T_mck hl_REP 0.
Definition X_rpg : axst := Eval vm_compute in leaf_at T_mcg hl_REP 0.
Goal lvs T_mck = [(hl_REP, RsCut)] /\ lvs T_mcg = [(hl_REP, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition mid_dst (d : sv) : sobj := ltac2:(tb__ "0|1|
S16Vd;S3cS33A1M0S13S2eG0S10ZcA1A3S2SfA1S15A5").
Definition sel_body : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1UaS0S1U2S0S1UbS0S1UcS0S1U3S0S1U4S0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U5S0S1U15S0S1U16S0S1U17S0S1U6S0S1U18S0S1U19S0S1U9S0S1U7S0S1U1S0S1U8S0S1U1aS2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_cm : list axform := ltac2:(tb__ "0|2|
S0S25S2aU2A1S0S25S27U5N270A2S0S25S29S75A1S0S25S28U1A1M0S0S25G0S0S25S28U15A1M1S0S25G1S2S25A1A3A3A3A3A3A3A3").
Definition canon_mc (A : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
S51VA;U1S6fVd;A1A3Sa0S4eS2bR1S7cA2A1Sa0Sf1R1S3bVd;Vk;S80S7fA4S8eZ4Z6A5TA2;TA1;").
Definition C_mk : axst := Eval vm_compute in canon_mc X_rpk pD pK.
Definition C_mg : axst := Eval vm_compute in canon_mc X_rpg vDg vKg.
Goal shape C_mg = shape (ax_setS C_mk (set_objs (ax_S C_mk) (firstn 21 (ss_objs (ax_S C_mk)) ++ [O_data vDg 12 vKg; O_data lc_d 4 lc_k; shobj hG 4 6 [] DUnknown])))
  /\ map (fun o => (ob_base o, ob_lo o, ob_hi o)) (firstn 23 (ss_objs (ax_S C_mk))) = map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pQ pHP pD pC1 pK [] []).
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_r2k : axst := Eval vm_compute in leaf_at C_mk hl_REP2 0.
Definition X_r2g : axst := Eval vm_compute in leaf_at C_mg hl_REP2 0.
Definition C_rlk : axst := Eval vm_compute in shadow_release_stateA X_r2k (removelast (ss_objs (ax_S X_r2k))) 160 [].
Definition C_rlg : axst := Eval vm_compute in shadow_release_stateA X_r2g (removelast (ss_objs (ax_S X_r2g))) 160 [].
Goal lvs C_mk = [(hl_REP2, RsCut)] /\ lvs C_mg = [(hl_REP2, RsCut)] /\ lvs C_rlk = [(hl_H, RsCut)] /\ lvs C_rlg = [(hl_H, RsCut)]
  /\ map (fun L => leaf_matchesA NPH L [H]) (leavesA_at FUEL_hl cutpcs_hl C_rlk hl_H ++ leavesA_at FUEL_hl cutpcs_hl C_rlg hl_H) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
