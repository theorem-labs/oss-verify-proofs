(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "list"; "option"; "true"; "S"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "cell"; "SPUle"; "SVar"; "SAlu"; "DUnknown"; "mkObj"; "mkSS"; "FcsrFrm0"; "SPBranch"; "ss_objs"; "SMd"; "ss_facts"; "ss_next"; "SExt"; "SPAlign"; "SPNot"; "ob_base"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXRebase"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "leafA"; "FE"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt"; "z0"; "aw_k"; "tv_vt"; "aw_d"; "yK"; "yK2"; "avt_cnt2"; "ndP"; "qK"; "qK2"; "cm4"; "ndF"; "ndG"; "ndK"; "qD"; "qD2"; "yD"; "yD2"; "X_vt"; "vKg"; "Wp1"; "avt_t"; "aw_c"; "bd_fin"; "optAp"; "qC2"; "qCUR"; "vDg"; "O_F"; "O_Wv"; "V248"; "base_vt"; "bdK"; "reshapeA"; "tvI"; "yC2"; "yCUR"; "Cb1"; "E_B"; "E_sm0"; "FUEL_vt"; "P_fail"; "P_ok"; "YC"; "bd_vt"; "cutpcs_vt"; "fail_facts"; "gD"; "gK"; "nd0"; "ndEf"; "ndEo"; "ndO"; "ndX"; "nd_fail"; "nd_ok"; "oD"; "oK"; "objs_post"; "ok_facts"; "qC1"; "qERR"; "slot_facts"; "yC1"; "yERR"; "BAD"; "C_Ef"; "C_Eo"; "C_L"; "C_Wg"; "C_Wk"; "C_pro"; "C_rlf"; "C_rlo"; "E_A"; "E_Dg"; "E_Dgc"; "E_Dk"; "E_Dkc"; "E_mg0"; "E_mk0"; "E_opg"; "E_opgc"; "E_opk"; "E_opkc"; "E_vr"; "E_vr0"; "F_saved"; "NZ32"; "O_flag"; "O_fr0"; "Pre_mc"; "Pre_sm"; "Pre_vt"; "Pre_vt_S"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_Dg0"; "T_Dg1"; "T_Dk0"; "T_Dk1"; "T_fl"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "T_mcg"; "T_mck"; "T_opg0"; "T_opg1"; "T_opk0"; "T_opk1"; "T_pure"; "V216t"; "X_A"; "X_body"; "X_rlf"; "X_rlo"; "Xk_op"; "avt_cnt"; "bdFl"; "dst_obj"; "epi_regs"; "epi_state"; "fr_vt"; "frame_factsV"; "havoc_freg"; "havoc_reg_le1"; "mid_dst"; "ndEf'"; "ndEo'"; "ndFl"; "objs_epi"; "objs_vt"; "sel_D"; "sel_op"; "sel_rel"; "sel_vr"; "src_obj"; "tvP"; "vt_facts"; "xf_D"; "xf_mc"; "xf_opb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "avt_k"; "hF"; "avt_d"; "kb"; "bd_vec"; "O_data"; "vec_facts"; "hFL"; "hG"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "h_fregs"; "tI"; "V"; "handle_facts"; "tB"; "tE"; "tL"; "NPH"; "h_xregs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "M_MUL"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "vDp"; "spm"; "B_EW"; "B32"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "two47"; "vKn"; "vW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Lists.ListDef"; "seq"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt.HVTAddr"; "DW"; "FR"; "vt_EPI"; "vt_ret"; "memcpy_pc";
"op_pc"; "sm1_pc"; "vt_L"; "vt_REL"; "vt_W"; "vt_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "SHB"; "leavesA_at"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "Pre_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xlocal"; "shadow_reopen_stateA"; "flag_carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "O_al"; "P_alloc"; "P_st"; "vERR"; "vAL"; "vb"; "vc"; "havoc_reg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt.OP"; "Pre_op"; "P_op0"; "P_op1"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
Module OP. Include Lib_opt_push1. End OP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HVTAddr.
  Definition vt_entry : Z := 0x9e3e4.
  Definition sm1_pc : Z := 0x47a7c.
  Definition memcpy_pc : Z := 0x5c84c.
  Definition op_pc : Z := 0xa5d68.
  Definition vt_L : Z := 0x9e568.
  Definition vt_W : Z := 0x9e700.
  Definition vt_FP : Z := 0x9e694.
  Definition vt_P2 : Z := 0x9e768.
  Definition vt_EPI : Z := 0x9e6ac.
  Definition vt_REL : Z := 0x9e7bc.
  Definition vt_ret : Z := 0x9e7f8.
  Definition vt_ra_A : Z := 0x9e530. Definition vt_ra_B : Z := 0x9e558. Definition vt_ra_vr : Z := 0x9e5bc. Definition vt_ra_mc : Z := 0x9e614.
  Definition vt_ra_D : Z := 0x9e648. Definition vt_ra_op : Z := 0x9e734.
  Definition DW : Z := 4544.
  Definition FR : Z := 160.
End HVTAddr.
Import HVTAddr.

Definition FUEL_vt : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S13PaA1SeS12fS103A1A1SeZ0A1Vcells;S15A5").
Definition O_Wv : sobj := ltac2:(tb__ "0|0|
S16SeeS103A1SedSeZ0A1S3S11A1S15A5").

Definition avt_t : sv := SVar 119.
Definition avt_cnt : sv := SAlu ALU_SLL avt_t (SLit 1).
Definition avt_cnt2 : sv := SAlu ALU_ADD avt_cnt (SLit 2).
Definition aw_d : sv := SVar 120. Definition aw_c : sv := SVar 121. Definition aw_k : sv := SVar 122.
Definition Wp1 : sv := ltac2:(tb__ "0|1|
S14Se7S1bSe9SeZ1A1M0S54A3G0A3").
Definition Cb1 : sv := ltac2:(tb__ "0|0|
S14Se7S1bSe9SeZ1A1S54A3SeZ0A1A3").
Definition V216t (d k : sv) : sobj := V 216 d avt_cnt k 4.
Definition V248 (d c k : sv) : sobj := V 248 d c k 4.
Definition vt_facts : list sprop := ltac2:(tb__ "0|1|
S5S10Se1S103S102A2S5S10S0S10S19Se8SeN1120A1SedA3S0S10S12S54SeS12eZ2Z1bA2A1A2S0S10S12S55S64A2S0S10S12Sd4Z4M0S45A2SeSefA1A2S3S10A1A3A3A3A3S5S10Sd7Sd3Sb8Sd1G0P74A5Sd7S42S55S40G0P78A5A3A3A3").
Definition X_vt (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SdSdA2M0S1SdSdS11dSeZ518A1A4S0G0S1SdSdS11eSeZ10A1A4S0G0S1SdSdS11cSeZ30A1A4S0G0S1SdSdSe2Se4A4S0G0S1SdSdSeS125A1SeZb8A1A4S0G0S1SdSdVd;Sd4Z4M1Vk;A2A4S0G0S1SdSdVd2;Sd4G1Vk2;A2A4S0G0S1SdSdSeeS102A1SeS102A1A4S3G0A1A3A3A3A3A3A3A3A3").
Definition objs_vt (cur err : sv) (d k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S5SfS0SfS5bS3S11A1A1S0SfS5cS0SfS119S0SfS11aVerr;A1S0SfSb2Vd;Vk;A2S0SfS5dVd2;Vc2;Vk2;A3S0SfS118S0SfSdcVcur;A1S0SfSdbS0SfSddS0SfSd6Vd;Z4M0Vk;A3S0SfSd6Vd2;G0Vk2;A3S3SfA1A3A3A3A3A3A3A3A3A3A3A3A3S10eA3").
Definition Pre_vt_S : sstate := ltac2:(tb__ "0|0|
S17S10cS12aS129S18S6SdA1Sc6SdfS11bSd3Sd1S42S55S40A7ScdSe5S7A9").
Definition Pre_vt : axst := ltac2:(tb__ "0|0|
S10dS9dS51Sd3Sd1S42S40A4A2").

Definition bd_vt (k k2 : sv) : list bitem := ltac2:(tb__ "0|1|
S5S101Sd5Z4M0S45Vk;A3Sd5G0S53Vk2;A3A3").
Definition tv_vt (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SdSdA2M0S1SdSdVd;Sd4Z4M1Vk;A2A4S0G0S1SdSdVd2;Sd4G1Vk2;A2A4S3G0A1A3A3").
Definition tvI (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SdSdA2M0S1SdSdVd2;Sd4Z4M1Vk2;A2A4S0G0S1SdSdVd;Sd4G1Vk;A2A4S3G0A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S3aS41Sd3Sd1S42S40A4S3S4S4SdS3dA2SdA2A1S6bSd1S40A2A3").
Definition nd0' : ndesc := ltac2:(tb__ "0|0|
S3aS61Sd3Sd1S42S40A4S3S4S4SdS3dA2SdA2A1S6bSd1S40A2A3").

Definition cutpcs_vt : list Z := ltac2:(tb__ "0|0|
S0S3dS108S0S3dS126S0S3dS109S0S3dS131S0S3dS106S0S3dS10bS0S3dS107S0S3dS104S0S3dS10aS3S3dA1A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S10dS17Z0S3SdA1M0G0S18S6SdA1S3SfA1S3S10A1P1S7A9S3S4SdSdA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S100S32Vk;S110S67S6cVS;Vpc;A4S80A4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S9S8S36A1M0A1S8S4S3dS133A2M1A1Lx;S38S111S67S6cVS;SaA5G0SfeS36G1S112R1A4Ll;S3G1A1X9x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_vt sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S4S3eSdA2S1S3eSdS12dSedA4SfcPaS33S66A1S33S9bA1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_vt = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.
Definition fr_vt : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S4S4SdS3dA2M0SdA2M1S1G0SdS1SdS3dSd2Z1A4Sd8A4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S2SfdU0Vi;A2S5S2SfdSbVi;A1M0S130ScSfS1aS33VA;A1A1A2G0A2A2S0S2Vi;S3S2A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_vt avt_d avt_k aw_d aw_k ++ (hF, SLit 128) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 (X_vt avt_d avt_k aw_d aw_k) 160 128.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_A : axst := Eval vm_compute in leaf_at C_pro sd_entry 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_A)) O_Wv.
Definition objs_A : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_A)).
Goal lvs C_pro = [(sd_entry, RsCut)] /\ sh_pro = shobj hG 0 16 (ob_cells sh_pro) DZero /\ local_ok (ob_cells sh_pro) DZero 0 16 (32, 8) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition E_A1 : axst := Eval vm_compute in shadow_release_stateA X_A objs_A 160 [(32, 8)].

Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
S34VA;S135S33VA;A1Vi;Vo;A3A2").
Definition O_fr0 : sobj := ltac2:(tb__ "0|0|
S16Sd2SeZ0A1SeZ78A1S3S11A1S15A5").
Definition E_A2 : axst := Eval vm_compute in reshapeA E_A1 1 O_fr0.
Definition xf_sd : list axform := ltac2:(tb__ "0|2|
S0S2bS2cU0SeN30A1A2S0S2bS2cU6SeN70M0A1A2S0S2bS2cU7M1SeN68A1A2S0S2bS2dG1G0A2S3S2bA1A3A3A3A3").
Definition E_A : axst := Eval vm_compute in optAp (apply_axforms E_A2 xf_sd).
Definition s_A : wsub := ltac2:(tb__ "0|0|
SfcPaS33S89A1S33S113A1A3").
Definition R_A : list sobj := Eval vm_compute in optR (entails_frA E_A Pre_sd s_A).
Goal entails_frA E_A Pre_sd s_A = Some R_A /\ call_checkA E_A Pre_sd s_A R_A [P_none; P_num] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S114S1cS33VCl;A1A1S134Vs;VPre;VL;VCl;VR;A5A2").
Definition T_A0 : axst := Eval vm_compute in T_pure Pre_sd E_A s_A R_A P_none.
Definition T_A1 : axst := Eval vm_compute in T_pure Pre_sd E_A s_A R_A P_num.

Definition X_body (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S115Pa0S1S3dS3dZ20Z8A4A2S0G0S1SdSdSd2SeZ0A1A4S51Vd;Vk;Vd2;Vk2;A4A3A3").
Definition XB : list (sv * sv) := ltac2:(tb__ "0|0|
Sb4Sd3Sd1S42S40A4").
Definition E_B : axst := Eval vm_compute in ax_setX (leaf_at T_A1 sd_entry 0) XB.
Definition s_B : wsub := ltac2:(tb__ "0|0|
SfcPaS33S65A1S33S113A1A3").
Definition R_B : list sobj := Eval vm_compute in optR (entails_frA E_B Pre_sd s_B).
Definition T_B0 : axst := Eval vm_compute in T_pure Pre_sd E_B s_B R_B P_none.
Definition T_B1 : axst := Eval vm_compute in T_pure Pre_sd E_B s_B R_B P_num.

Definition O_sdf : sobj := ltac2:(tb__ "0|0|
S16SeeS103A1SeN30A1SeZ0A1S3S11A1S15A5").
Definition forget0 (A : axst) : axst := reshapeA A 0 O_sdf.
Definition C_L : axst := Eval vm_compute in ax_setX (havoc_reg (havoc_reg (forget0 (leaf_at T_A0 vt_L 0)) 10) 1) XB.
Goal lvs T_A0 = [(vt_L, RsCut)] /\ lvs T_A1 = [(sd_entry, RsCut)] /\ entails_frA E_B Pre_sd s_B = Some R_B /\ call_checkA E_B Pre_sd s_B R_B [P_none; P_num] = true
  /\ lvs T_B0 = [(vt_L, RsCut)] /\ lvs T_B1 = [(vt_L, RsCut)]
  /\ map (fun L => leaf_matches1A NPH L C_L) (leavesA_at FUEL_vt cutpcs_vt T_A0 vt_L ++ leavesA_at FUEL_vt cutpcs_vt T_B0 vt_L ++ leavesA_at FUEL_vt cutpcs_vt T_B1 vt_L) = [true; true; true].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at C_L vr_entry 0.
Definition sel_vr : list nat := ltac2:(tb__ "0|0|
S5S2S0S2U6S0S2U0S3S2A1A3A3S5S2SfdU1U5A2SfdU7UcA2A3A3").
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S2bS2fScaA1S0S2bS2eU0M0A1S0S2bS2cG0SeN40M1A1A2S0S2bS2dG0G1A2S0S2bS2dUdZd8A2S3S2bA1A3A3A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S3eSdA2S1S3eSdP13S14Se7SedSeZ40A1A3A4SfcPaS33S94A1S33Sf4A1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S32S39A2M0S1S32S39Sf3Sf6A4S0G0S1S32S39Sf1S3aSf7S3S4S4SdS3dA2SdA2A1M1S3S101A1A3A4S0G0S1S32S39Sf2S3aSf8G1Sf5SfbSfaA2A3A4S3G0A1A3A3A3").
Goal lvs C_L = [(vr_entry, RsCut)] /\ entails_frA E_vr Pre_vr s_v = Some R_v /\ call_checkPA E_vr Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) avt_d)) XB.
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v Lib_vec_reserve.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_grown Xk_v.

Definition cm4 : sv := SMd M_MUL avt_cnt (SLit 4).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S0S10S12S14Se7S49SeZ8A1A3Sd4Z4Vk;A2M0A2S0S10S12S49G0A2S0S10S12S49SeSf0A1A2S3S10A1A3A3A3").
Definition vDg : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_vr)) + 40)).
Definition vKg : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_vr)) + 41)).
Definition T_keep : axst := ltac2:(tb__ "0|0|
S114S5S10S7dSd1A1S0S10S12SeS12cA1Sd3A2S3S10A1A3A3SaaA2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
S114S7dS52A1Sa8A2").
Definition E_mk0 : axst := Eval vm_compute in leaf_at T_keep memcpy_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leaf_at T_grown memcpy_pc 0.
Goal lvs T_keep = [(memcpy_pc, RsCut)] /\ lvs T_grown = [(memcpy_pc, RsCut)]
  /\ map SymState.c_val (ob_cells (nth 2 (ss_objs (ax_S T_grown0)) O_Wv)) = [vDg; avt_cnt; vKg; SLit 4].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S16S14Se7Vd;S49A3SeZ0A1SeZ8A1S3S11A1S15A5").
Definition src_obj : sobj := ltac2:(tb__ "0|0|
S16S14Se7Sd2SeZ20A1A3SeZ0A1SeZ8A1S3S11A1S15A5").
Definition xf_mc : list axform := ltac2:(tb__ "0|2|
S0S2bS2dU1M0Z40A2S0S2bS2fS5S2S0S2G0S0S2U0M1S3S2A1A3A3SfdU2U11A2A3A1S0S2bS2eG1A1S0S2bS2cU3S49A2S0S2bS2cU4S14Se7S49SeZ8A1A3A2S0S2bS2cUbSeZ20A1A2S0S2bS2cUcSeZ28A1A2S3S2bA1A3A3A3A3A3A3A3").
Definition E_mc (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S60S60S57S31VE0;ScfA2A1U4SbaVd;A1A3UcScbA3").
Definition E_mk : axst := Eval vm_compute in E_mc E_mk0 avt_d.
Definition E_mg : axst := Eval vm_compute in E_mc E_mg0 vDg.
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S3eSdA2M0S1S3eSdP35Vd;A4S0G0S1S3eSdP36Sd4Z4Vk;A2A4S0G0S1S3eSdP37S14Se7Sd2SeZ20A1A3A4S0G0S1S3eSdP38SeZ8A1A4S0G0S1S3eSdS12dSedA4SfcPaS33VE;A1S33S9aA1A3A3A3A3A3A3").
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_mk Pre_mc (s_mc E_mk avt_d avt_k)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg)).
Definition T_mck : axst := Eval vm_compute in T_afterA Pre_mc E_mk (s_mc E_mk avt_d avt_k) R_mk L_mc1.
Definition T_mcg : axst := Eval vm_compute in T_afterA Pre_mc E_mg (s_mc E_mg vDg vKg) R_mg L_mc1.

Definition E_Dk : axst := Eval vm_compute in leaf_at T_mck sd_entry 0.
Definition E_Dg : axst := Eval vm_compute in leaf_at T_mcg sd_entry 0.
Goal entails_frA E_mk Pre_mc (s_mc E_mk avt_d avt_k) = Some R_mk /\ call_checkPA E_mk Pre_mc (s_mc E_mk avt_d avt_k) R_mk [L_mc1; L_mc1] = true
  /\ entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg) = Some R_mg /\ call_checkPA E_mg Pre_mc (s_mc E_mg vDg vKg) R_mg [L_mc1; L_mc1] = true
  /\ lvs T_mck = [(sd_entry, RsCut)] /\ lvs T_mcg = [(sd_entry, RsCut)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition mid_dst (d : sv) : sobj := ltac2:(tb__ "0|0|
S16Vd;S49S14Se7S49SeZ8A1A3S3S11A1S15A5").
Definition sel_D : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2UcS0S2U2S0S2UdS0S2UeS0S2U3S0S2U4S0S2UfS0S2UbS0S2U10S0S2U11S0S2U12S0S2U5S0S2U13S0S2U6S0S2U9S0S2U14S0S2UaS0S2U7S0S2U1S0S2U8S0S2U15S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_D : list axform := ltac2:(tb__ "0|2|
S0S2bS30U2A1S0S2bS2dU5Nd8A2S0S2bS2fSc7A1S0S2bS2eU1A1M0S0S2bG0S0S2bS2eU10A1M1S0S2bG1S0S2bS2cU0SeN30A1A2S3S2bA1A3A3A3A3A3A3A3A3").
Definition canon_D (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S57S31S60VA;U1Sc1Vd;A1A3SceA2A1").
Definition E_Dkc : axst := Eval vm_compute in canon_D E_Dk avt_d.
Definition E_Dgc : axst := Eval vm_compute in canon_D E_Dg vDg.
Definition s_Dk : wsub := ltac2:(tb__ "0|0|
SfcPaS33S8dA1S33S113A1A3").
Definition s_Dg : wsub := ltac2:(tb__ "0|0|
SfcPaS33S8bA1S33S113A1A3").
Definition R_Dk : list sobj := Eval vm_compute in optR (entails_frA E_Dkc Pre_sd s_Dk).
Definition R_Dg : list sobj := Eval vm_compute in optR (entails_frA E_Dgc Pre_sd s_Dg).
Goal entails_frA E_Dkc Pre_sd s_Dk = Some R_Dk /\ call_checkA E_Dkc Pre_sd s_Dk R_Dk [P_none; P_num] = true
  /\ entails_frA E_Dgc Pre_sd s_Dg = Some R_Dg /\ call_checkA E_Dgc Pre_sd s_Dg R_Dg [P_none; P_num] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition T_D (E : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
Sb1S113VE;Vs;VR;VL;A5S32S116R1S35R1A1Sd9Z8ZbA5TT;").
Definition T_Dk0 : axst := Eval vm_compute in T_D E_Dkc s_Dk R_Dk P_none.
Definition T_Dk1 : axst := Eval vm_compute in T_D E_Dkc s_Dk R_Dk P_num.
Definition T_Dg0 : axst := Eval vm_compute in T_D E_Dgc s_Dg R_Dg P_none.
Definition T_Dg1 : axst := Eval vm_compute in T_D E_Dgc s_Dg R_Dg P_num.
Goal map lvs [T_Dk0; T_Dk1; T_Dg0; T_Dg1] = [[(vt_W, RsCut)]; [(vt_W, RsCut)]; [(vt_W, RsCut)]; [(vt_W, RsCut)]].
Proof. vm_compute. reflexivity. Qed.

Definition havoc_freg (A : axst) (r : nat) : axst := ltac2:(tb__ "0|2|
S33VA;A1S2aS34VA;S17S27R1A1S28R1A1S12bS25R1A1S0S4S2SdA2M0S1S2SdVr;S13S1dR1A1M1A1A4S3G0A1A3A2S24R1A1S29R1A1S1aR1A1S1cR1A1S137G1A1S26R1A1A9A2TS;").
Definition havoc_reg_le1 (A : axst) (r : nat) : axst := ltac2:(tb__ "0|0|
S1dS33VA;A1A1S3eS114S0S10S12S13R1A1SeZ1A1A2S3S10A1A3S11fVA;Vr;A2A2Tv;").
Definition joinW (A : axst) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S127SbfSc0VA;UfM0A2G0A2VX;A2").
Definition C_Wk : axst := Eval vm_compute in joinW (leaf_at T_Dk0 vt_W 0) (X_body avt_d avt_k aw_d aw_k).
Definition C_Wg : axst := Eval vm_compute in joinW (leaf_at T_Dg0 vt_W 0) (X_body vDg vKg aw_d aw_k).
Goal map (fun L => leaf_matches1A NPH L C_Wk) (leavesA_at FUEL_vt cutpcs_vt T_Dk0 vt_W ++ leavesA_at FUEL_vt cutpcs_vt T_Dk1 vt_W) = [true; true]
  /\ map (fun L => leaf_matches1A NPH L C_Wg) (leavesA_at FUEL_vt cutpcs_vt T_Dg0 vt_W ++ leavesA_at FUEL_vt cutpcs_vt T_Dg1 vt_W) = [true; true].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition E_opk : axst := Eval vm_compute in leaf_at C_Wk op_pc 0.
Definition E_opg : axst := Eval vm_compute in leaf_at C_Wg op_pc 0.
Goal lvs C_Wk = [(op_pc, RsCut)] /\ lvs C_Wg = [(op_pc, RsCut)] /\ nth 12 (ss_regs (ax_S E_opk)) (SLit 0) = avt_t. Proof. vm_compute. repeat split; reflexivity. Qed.

Definition sh_op : sobj := Eval vm_compute in last (ss_objs (ax_S E_opk)) O_Wv.
Definition objs_opk : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_opk)).
Definition objs_opg : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_opg)).
Goal sh_op = shobj hG 8 11 (ob_cells sh_op) DUnknown /\ last (ss_objs (ax_S E_opg)) O_Wv = sh_op
  /\ local_ok (ob_cells sh_op) DUnknown 8 11 (64, 4) = true /\ local_ok (ob_cells sh_op) DUnknown 8 11 (80, 4) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition E_opk1 : axst := Eval vm_compute in shadow_release_stateA E_opk objs_opk 160 [(64, 4); (80, 4)].
Definition E_opg1 : axst := Eval vm_compute in shadow_release_stateA E_opg objs_opg 160 [(64, 4); (80, 4)].
Definition xf_op : list axform := ltac2:(tb__ "0|7|
S0S2bS2fS5S2S0S2U6S0S2U0M0S0S2U1S0S2U2S0S2U3S0S2U4S0S2U5S3S2A1A3A3A3A3A3A3A3SfdU7M1UcA2A3A1S0S2bS2eG0A1S0S2bS2cG0SeN80M2A1A2S0S2bS2dG0G2A2S0S2bS2dUeZf8A2S0S2bS2cG1SeZ40M3A1A2S0S2bS2cU8M4SeZ44A1A2S0S2bS2cU9SeZ50M5A1A2S0S2bS2cUaM6SeZ54A1A2S0S2bS2dG4G3A2S0S2bS2dG6G5A2S3S2bA1A3A3A3A3A3A3A3A3A3A3A3").
Definition E_opkc : axst := Eval vm_compute in optAp (apply_axforms E_opk1 xf_op).
Definition E_opgc : axst := Eval vm_compute in optAp (apply_axforms E_opg1 xf_op).
Definition s_opk : wsub := ltac2:(tb__ "0|0|
S0S4S3eSdA2S1S3eSdP13S14Se7SedSeZ80A1A3A4SfcPaS33S93A1S33S120A1A3A3").
Definition s_opg : wsub := ltac2:(tb__ "0|0|
S0S4S3eSdA2S1S3eSdP13S14Se7SedSeZ80A1A3A4SfcPaS33S91A1S33S120A1A3A3").
Definition R_opk : list sobj := Eval vm_compute in optR (entails_frA E_opkc OP.Pre_op s_opk).
Definition R_opg : list sobj := Eval vm_compute in optR (entails_frA E_opgc OP.Pre_op s_opg).
Definition PD_op : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S32S39A2M0S1S32S39S122S124A4S0G0S1S32S39S121S123A4S3G0A1A3A3").
Goal entails_frA E_opkc OP.Pre_op s_opk = Some R_opk /\ call_checkPA E_opkc OP.Pre_op s_opk R_opk (map fst PD_op) = true
  /\ entails_frA E_opgc OP.Pre_op s_opg = Some R_opg /\ call_checkPA E_opgc OP.Pre_op s_opg R_opg (map fst PD_op) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition Xk_op (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S4SdSdA2M0S115Pa0M1S1S3dS3dZ40Z4M2A4A2S0G0S115G1S1S3dS3dZ50G2A4A2S0G0S115G1S1S3dS3dZ20Z8A4A2S0G0S1SdSdSd2SeZ0A1A4S0G0S1SdSdS11dSeZ518A1A4S0G0S1SdSdS11eSeZ10A1A4S0G0S1SdSdS11cSeZ30A1A4S0G0S1SdSdSe2Se4A4S0G0S1SdSdSeS125A1SeZb8A1A4S0G0S1SdSdVd;Sd4G2Vk;A2A4S0G0S1SdSdSeeS102A1SeS102A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Goal Xk_op avt_d avt_k = List.filter (fun r => negb (sv_eqb (fst r) aw_d)) (ax_X E_opkc) /\ Xk_op vDg vKg = List.filter (fun r => negb (sv_eqb (fst r) aw_d)) (ax_X E_opgc).
Proof. vm_compute. split; reflexivity. Qed.
Definition sel_op : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2UcS0S2U4S0S2UdS0S2U5S0S2UeS0S2UfS0S2U7S0S2U8S0S2U10S0S2UbS0S2U11S0S2U12S0S2U13S0S2U14S0S2U2S0S2U3S0S2U9S0S2U15S0S2UaS0S2U16S0S2U6S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_opb : list axform := ltac2:(tb__ "0|4|
S0S2bS2dU1M0Z80A2S0S2bS30U4A1S0S2bS30U5M1A1S0S2bS2dU2Nf8A2S0S2bS30UbA1S0S2bS2fSc8A1S0S2bS2eU0A1S0S2bS2eG0A1M2S0S2bG2S0S2bG2S0S2bG2S0S2bS2eG1A1M3S0S2bG3S3S2bA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
S117S116VY;S35VY;A1Sd9Z0Z10A5PaaA2").
Definition cont_op (E : axst) (s : wsub) (R : list sobj) (P : axst) (d k d2 k2 : sv) : axst := ltac2:(tb__ "0|0|
SbcS127S57S31S136S120VE;Vs;VR;VP;Sb7Vd;Vk;A2A6Sd0A2A1S51Vd;Vk;Vd2;Vk2;A4A2A1").
Definition oD : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opkc)) + 40)).
Definition oC : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opkc)) + 41)).
Definition oK : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opkc)) + 42)).
Definition gD : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opgc)) + 40)).
Definition gC : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opgc)) + 41)).
Definition gK : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_opgc)) + 42)).
Definition T_opk1 : axst := Eval vm_compute in cont_op E_opkc s_opk R_opk OP.P_op1 avt_d avt_k oD oK.
Definition T_opk0 : axst := Eval vm_compute in cont_op E_opkc s_opk R_opk OP.P_op0 avt_d avt_k oD oK.
Definition T_opg1 : axst := Eval vm_compute in cont_op E_opgc s_opg R_opg OP.P_op1 vDg vKg gD gK.
Definition T_opg0 : axst := Eval vm_compute in cont_op E_opgc s_opg R_opg OP.P_op0 vDg vKg gD gK.
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S8S4S4SdSdA2SdA2A1") := ltac2:(tb__ "0|1|
SfeSfS4S4SdSdA2M0SdA2SfS1G0SdS1SdSdS21R1A1S23R1A1A4S22R1A1A4Lo;S1aS33VA;A1A1A4").
Goal firstn 16 (shape T_opk1) = shape (mkA (mkSS 0 [] [] FcsrFrm0 None ([O_Wv; O_fr0; mkObj hF (SLit 120) (SLit 128) [] DUnknown] ++ A_globals ++ [O_F []; P_alloc; P_st vERR; V216t avt_d avt_k; V248 oD oC oK; O_al; O_cP tI; O_cE; O_text; O_data avt_d 4 avt_k; O_data oD 4 oK]) [] NPH false) [])
  /\ map lvs [T_opk1; T_opk0; T_opg1; T_opg0] = [[(vt_EPI, RsCut)]; [(vt_EPI, RsCut); (vt_EPI, RsCut)]; [(vt_EPI, RsCut)]; [(vt_EPI, RsCut); (vt_EPI, RsCut)]].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition xf_fl : list axform := ltac2:(tb__ "0|6|
S0S2bS2dU1M0Z40A2S0S2bS2dU2M1Nd8A2S0S2bS30U9M2A1S0S2bS2fS0S2G0S0S2U0M3S0S2UaS0S2UbS0S2U5M4S0S2U6S0S2UcS0S2G2S0S2UdS0S2UeS0S2UfS0S2G1S0S2U10S0S2U3S0S2U7S0S2U11S0S2U8S0S2U4S0S2U12S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S2bS2eG3A1S0S2bS2eG4A1M5S0S2bG5S3S2bA1A3A3A3A3A3A3A3").
Definition Y_fl : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_fail0 xf_fl)) (X_vt avt_d avt_k aw_d aw_k).
Definition T_fl : axst := Eval vm_compute in epi_state Y_fl.
Goal firstn 15 (shape T_fl) = firstn 15 (shape T_opk1) /\ nth 15 (shape T_fl) (vb, vb, vb) = (aw_d, SLit 0, kb 4 aw_k) /\ lvs T_fl = [(vt_EPI, RsCut); (vt_EPI, RsCut)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition yCUR : sv := SVar 320. Definition yD : sv := SVar 321. Definition yC1 : sv := SVar 322. Definition yK : sv := SVar 323.
Definition yD2 : sv := SVar 324. Definition yC2 : sv := SVar 325. Definition yK2 : sv := SVar 326. Definition yERR : sv := SVar 328.
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S19SebS1eSaQ20Ve;A3SeZ0A1A3").
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S11SecN68S13P2fA1A2S0S11SecN60S13P2eA1A2S0S11SecN58S13P2dA1A2S0S11SecN50S13P2cA1A2S0S11SecN48S13P2bA1A2S0S11SecN40S13P2aA1A2S0S11SecN38S13P29A1A2S0S11SecN30S13P28A1A2S0S11SecN28S13P27A1A2S0S11SecN20S13P26A1A2S0S11SecN18S13P1dA1A2S0S11SecN10S13P1cA1A2S0S11SecN8S13PbA1A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S16Sd2SeZ78M0A1SeZ80A1S0S11SecG0Sd8A2S3S11A1A3S15A5").
Definition objs_epi (err cnt cur d k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|2|
S5SfS0SfS5cS0SfS99S0SfS98S3SfA1M0A3A3A3S5SfS10eS0SfS5bS96A1S0SfS119S0SfS11aVerr;A1S0SfSe0Zd8Vd;Vcnt;Vk;Z4M1A5S0SfS5dVd2;Vc2;Vk2;A3S0SfS118S0SfSdcVcur;A1S0SfSdbS0SfSddS0SfSd6Vd;G1Vk;A3S0SfSd6Vd2;G1Vk2;A3G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition base_vt : list sprop := ltac2:(tb__ "0|0|
S5S10Se1S103S102A2S0S10S19Se8SeN1120A1SedA3S0S10S12S54SeS12eZ2Z1bA2A1A2S0S10S12S55S64A2S0S10S12Sd4Z4S45A2SeSefA1A2S3S10A1A3A3A3A3A3").
Definition frame_factsV : list sprop := ltac2:(tb__ "0|1|
S5S10S37Sd9Sd2A2S0S10S1fPa0Z5A2S0S10S20S19SeaSd2SeZ0A1A3A1S0S10S12SeS12cA1M0Sd2A2S0S10S12S14Se7Sd2SeZ80A1A3S13P1eA1A2S0S10S12Sd2SeSf9A1A2S0S10S12G0Sd8A2S0S10S12S14Se7Sd8SeZ1A1A3SeZ7fffff800000A1A2S3S10A1A3A3A3A3A3A3A3A3").
Definition ok_facts (cur d k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|1|
S5S10S0S10S12Vc2;S53A2S0S10S12SdfVcur;A2S0S10S12Vcur;Se3A2S3S10A1A3A3A3S5S10Sd7Vd;S45Vk;Z4M0Vdv;A5Sd7Vd2;Vc2;Vk2;G0Vdv2;A5A3A3").
Definition fail_facts (err cur d c1 k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|1|
S5S10S0S10S97Verr;A1S0S10S12SdfVcur;A2S0S10S12Vcur;Se3A2S3S10A1A3A3A3S5S10Sd7Vd;Vc1;Vk;Z4M0Vdv;A5Sd7Vd2;Vc2;Vk2;G0Vdv2;A5A3A3").
Definition epi_regs : list sv := ltac2:(tb__ "0|1|
Se6S0S4S2SdA2M0S1S2SdU8S13PaA1A4S0G0S1S2SdUdSd2A4S0G0S1S2SdU19S14Se7S13Sd9A1SeS10fA1A3A4S3G0A1A3A3A3A1").
Definition YC (err cnt : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S10dS17S104SbbSdeS18S6SdA1Sc5Verr;Vcnt;S63S4fS43S50S62S44A8S5S10Vfacts;S5S10S5eSbeA3A3SdaS7A9S51S4fS43S50S44A4A2").
Definition Y_ok : axst := ltac2:(tb__ "0|0|
S6aS11bS45S7aS63S4fS43S50S62S44P141P144A8A3").
Definition Y_fail : axst := ltac2:(tb__ "0|0|
S6aS7fS7eS6dS7fS63S4fS7eS43S50S62S44P141P144AaA3").
Definition C_Eo : axst := Eval vm_compute in epi_state Y_ok.
Definition C_Ef : axst := Eval vm_compute in epi_state Y_fail.
Goal map (fun C => map (fun L => (leaf_matches1A NPH L C_Ef, leaf_matches1A NPH L C_Eo)) (leavesA_at FUEL_vt cutpcs_vt C vt_EPI)) [T_opk1; T_opg1; T_opk0; T_opg0; T_fl]
  = [[(false, true)]; [(false, true)]; [(true, false); (true, false)]; [(true, false); (true, false)]; [(true, false); (true, false)]].
Proof. vm_compute. reflexivity. Qed.

Definition X_rlo : axst := Eval vm_compute in leaf_at C_Eo vt_REL 0.
Definition X_rlf : axst := Eval vm_compute in leaf_at C_Ef vt_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U0S3S2A1M0A3S5S2SfdU3UdA2S0S2U1S0S2U2S0S2U10S0S2U11G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S57S31VX;S0S2bS2fSc9A1S3S2bA1A3A2A1S32S34R1S132S33R1A1M0SffSfUeS1aG0A1A3A2A2TX1;").
Definition C_rlo : axst := Eval vm_compute in rel_state X_rlo.
Definition C_rlf : axst := Eval vm_compute in rel_state X_rlf.
Definition X_reto : axst := Eval vm_compute in leaf_at C_rlo vt_ret 0.
Definition X_retf : axst := Eval vm_compute in leaf_at C_rlf vt_ret 0.
Goal lvs C_Eo = [(vt_REL, RsCut)] /\ lvs C_Ef = [(vt_REL, RsCut)]
  /\ map (fun X => release_objs_ok 160 170 hG 1 (skipn 14 (ss_objs (ax_S (optAp (apply_axforms X [AXSelect sel_rel])))))) [X_rlo; X_rlf] = [true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rlo; C_rlf] = [14; 14]%nat /\ lvs C_rlo = [(vt_ret, RsSymJump)] /\ lvs C_rlf = [(vt_ret, RsSymJump)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition qCUR : sv := SVar 310. Definition qD : sv := SVar 311. Definition qC1 : sv := SVar 312. Definition qK : sv := SVar 313.
Definition qERR : sv := SVar 315. Definition qD2 : sv := SVar 316. Definition qC2 : sv := SVar 317. Definition qK2 : sv := SVar 318.
Definition objs_post (err cnt cur d k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|2|
S5SfS0SfS5cS3SfA1M0A3S5SfS10eS0SfS5bS3S11A1A1S0SfS119S0SfS11aVerr;A1S0SfSe0Zd8Vd;Vcnt;Vk;Z4M1A5S0SfS5dVd2;Vc2;Vk2;A3S0SfS118S0SfSdcVcur;A1S0SfSdbS0SfSddS0SfSd6Vd;G1Vk;A3S0SfSd6Vd2;G1Vk2;A3G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S10dS17S105S128P190A1SdeS18S6SdA1S79S11bS45S59S4dS47S4eS58S48A8S5S10S7aS59S4dS47S4eS58S48P137P13cA8S5eA3SdaS7A9S51S4dS47S4eS48A4A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S10dS17S105S128P190A1SdeS18S6SdA1S79S7cS7bS59S4dS47S4eS58S48A8S5S10S6dS7cS59S4dS7bS47S4eS58S48P137P13cAaS5eA3SdaS7A9S51S4dS47S4eS48A4A2").

Definition bd_fin (k k2 : sv) : list bitem := ltac2:(tb__ "0|1|
S5S101Sd5Z4M0S53Vk2;A3Sd5G0S45Vk;A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S3aS41S4dS47S4eS48A4S3S4S4SdS3dA2SdA2A1S56S47S48A2A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S3aS41S4dS47S4eS48A4S3S4S4SdS3dA2SdA2A1S3S101A1A3").
Definition Posts_vt : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S32S39A2M0S1S32S39S68S75A4S0G0S1S32S39S69S76A4S3G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S3cVtv;SbdVbd;S3bA4").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|0|
S61Sd3Sd1S42S40A4").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
S61S5aS52S42S40A4").
Definition bdPre : list bitem := bd_vt avt_k aw_k.
Definition bdK (k : sv) : list bitem := ltac2:(tb__ "0|1|
S5S101Sd5Z4M0S45Vk;A3Sd5G0S53S40A3A3").
Definition bdFl : list bitem := bd_vec 4 Wp1 aw_k.
Definition ndP : ndesc := ndF tvP bdPre.
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S4aSccS5fSd1A1A2").
Definition ndG : ndesc := ndF tvG (bdK vKg).
Definition ndKs : ndesc := ltac2:(tb__ "0|0|
S4aS41Sd3Sd1S42S40A4S5fSd1A1A2").
Definition ndGs : ndesc := ltac2:(tb__ "0|0|
S4aS41S5aS52S42S40A4S5fS52A1A2").
Definition ndFl : ndesc := ltac2:(tb__ "0|0|
S4aS41Sd3Sd1S42S40A4Sb9A2").
Definition ndO (d k d2 k2 : sv) : ndesc := ltac2:(tb__ "0|0|
S4aS41Vd;Vk;Vd2;Vk2;A4S56Vk;Vk2;A2A2").
Definition ndX (d k d2 k2 : sv) : ndesc := ltac2:(tb__ "0|0|
S4aS41Vd;Vk;Vd2;Vk2;A4Sd5Z4S45Vk;A3A2").
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
S4aS41S4fS43S50S44A4S56S43S44A2A2").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
S4aS41S4fS43S50S44A4S3S101A1A2").
Definition ndEo' : ndesc := ltac2:(tb__ "0|0|
S3aS41S4fS43S50S44A4S3S4S4SdS3dA2SdA2A1S56S43S44A2A3").
Definition ndEf' : ndesc := ltac2:(tb__ "0|0|
S3aS41S4fS43S50S44A4S3S4S4SdS3dA2SdA2A1S3S101A1A3").
Definition z0 : sv := SLit 0.
Definition cutsV : list edescA := ltac2:(tb__ "0|c|
S0S4S4S32S39A2M0S4S3dSdA2M1A2M2S1G0G1S1S32S39S9cS70A4S1S3dSdZ64S3fA4A4S0G2S1G0G1S1S32S39S86S46A4S1S3dSdZ60S3fA4A4S0G2S1G0G1S1S32S39S9eS46A4S1S3dSdZ5aS3fA4M3A4S0G2S1G0G1S1S32S39S9fS46A4G3A4S0G2S1G0G1S1S32S39Sa0S46A4S1S3dSdZ56S3fA4M4A4S0G2S1G0G1S1S32S39Sa1S46A4G4A4S0G2S1G0G1S1S32S39S83S46A4S1S3dSdZ50S3fA4A4S0G2S1G0G1S1S32S39Sa9S4cA4S1S3dSdZ4aS3fA4M5A4S0G2S1G0G1S1S32S39Sa7S4bA4G5A4S0G2S1G0G1S1S32S39Sa6Sc4A4G5A4S0G2S1G0G1S1S32S39SacS4cA4S1S3dSdZ46S3fA4M6A4S0G2S1G0G1S1S32S39SabS4bA4G6A4S0G2S1G0G1S1S32S39Sa4S4cA4S1S3dSdZ42S3fA4M7A4S0G2S1G0G1S1S32S39Sa5S4cA4G7A4S0G2S1G0G1S1S32S39Sa2S4bA4G7A4S0G2S1G0G1S1S32S39Sa3S4bA4G7A4S0G2S1G0G1S1S32S39S85S4cA4S1S3dSdZ40S3fA4M8A4S0G2S1G0G1S1S32S39S84S4bA4G8A4S0G2S1G0G1S1S32S39Sb0S73Sd3Sd1S77S78A4A4S1S3dSdZ3aS3fA4M9A4S0G2S1G0G1S1S32S39SafS74Sd3Sd1S77S78A4A4G9A4S0G2S1G0G1S1S32S39SaeS73S5aS52S6eS6fA4A4G9A4S0G2S1G0G1S1S32S39SadS74S5aS52S6eS6fA4A4G9A4S0G2S1G0G1S1S32S39S81S71A4S1S3dSdZ32S3fA4MaA4S0G2S1G0G1S1S32S39S82S72A4GaA4S0G2S1G0G1S1S32S39S87Sc2A4S1S3dSdZ1eS3fA4MbA4S0G2S1G0G1S1S32S39S88Sc3A4GbA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsV : list edescA := ltac2:(tb__ "0|8|
S0S4S4S32S39A2M0S4S3dSdA2M1A2M2S1G0G1S1S32S39S66S70A4S1S3dSdZ62S3fA4A4S0G2S1G0G1S1S32S39Sb3S46A4S1S3dSdZ5eS3fA4A4S0G2S1G0G1S1S32S39S65S46A4S1S3dSdZ58S3fA4A4S0G2S1G0G1S1S32S39S95S46A4S1S3dSdZ4eS3fA4A4S0G2S1G0G1S1S32S39S8fS4cA4S1S3dSdZ48S3fA4M3A4S0G2S1G0G1S1S32S39S8eS4bA4G3A4S0G2S1G0G1S1S32S39S8cS4cA4S1S3dSdZ44S3fA4M4A4S0G2S1G0G1S1S32S39S8aS4bA4G4A4S0G2S1G0G1S1S32S39S92S4cA4S1S3dSdZ3eS3fA4M5A4S0G2S1G0G1S1S32S39S90S4bA4G5A4S0G2S1G0G1S1S32S39Sb5S71A4S1S3dSdZ28S3fA4M6A4S0G2S1G0G1S1S32S39Sb6S72A4G6A4S0G2S1G0G1S1S32S39S68S75A4S1S3dSdZ0S3fA4M7A4S0G2S1G0G1S1S32S39S69S76A4G7A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
