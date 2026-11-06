(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "list"; "option"; "true"; "S"; "bool"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "cell"; "SAlu"; "SPUle"; "SVar"; "DUnknown"; "mkObj"; "mkSS"; "FcsrFrm0"; "ss_objs"; "SPBranch"; "SMd"; "SExt"; "ss_facts"; "ss_next"; "SAluW"; "SLBytes"; "SMdW"; "SPAlign"; "SPNot"; "c_val"; "ob_base"; "ob_cells"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXRebase"; "apply_axforms"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "leafA"; "FE"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt"; "z0"; "aw_k"; "tv_vt"; "aw_d"; "yK"; "yK2"; "avt_cnt2"; "ndP"; "qK"; "qK2"; "cm4"; "ndF"; "qD"; "qD2"; "yD"; "yD2"; "ndG"; "ndK"; "X_vt"; "vKg"; "Wp1"; "avt_t"; "aw_c"; "bd_fin"; "optAp"; "qC2"; "qCUR"; "vDg"; "O_F"; "O_Wv"; "V248"; "base_vt"; "bdK"; "tvI"; "yC2"; "yCUR"; "Cb1"; "E_B"; "E_sm0"; "FUEL_vt"; "P_fail"; "P_ok"; "YC"; "bd_vt"; "cutpcs_vt"; "fail_facts"; "gD"; "gK"; "nd0"; "ndEf"; "ndEo"; "ndO"; "ndX"; "nd_fail"; "nd_ok"; "oD"; "oK"; "objs_post"; "ok_facts"; "qC1"; "qERR"; "reshapeA"; "slot_facts"; "yC1"; "yERR"; "BAD"; "BADO"; "C_Ef"; "C_Eo"; "C_L"; "C_Wg"; "C_Wk"; "C_cg"; "C_ck"; "C_pro"; "C_rlf"; "C_rlo"; "E_A"; "E_Dg"; "E_Dgc"; "E_Dk"; "E_Dkc"; "E_opg"; "E_opgc"; "E_opk"; "E_opkc"; "E_vr"; "E_vr0"; "F_saved"; "NZ32"; "O_flag"; "O_fr0"; "Pre_mc"; "Pre_sm"; "Pre_vt"; "Pre_vt_S"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_Dg0"; "T_Dg1"; "T_Dk0"; "T_Dk1"; "T_fl"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "T_opg0"; "T_opg1"; "T_opk0"; "T_opk1"; "T_pure"; "V216t"; "X_A"; "X_body"; "X_rlf"; "X_rlo"; "Xk_op"; "avt_cnt"; "bdFl"; "cg_var"; "ck_var"; "dst_obj"; "epi_regs"; "epi_state"; "fr_vt"; "frame_factsV"; "havoc_freg"; "havoc_reg_le1"; "ndEf'"; "ndEo'"; "ndFl"; "objs_epi"; "objs_vt"; "sel_op"; "sel_rel"; "sel_vr"; "src_obj"; "tvP"; "vt_facts"; "xf_D"; "xf_mc"; "xf_opb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "avt_k"; "hF"; "avt_d"; "kb"; "bd_vec"; "O_data"; "vec_facts"; "hFL"; "hG"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "h_fregs"; "tI"; "V"; "handle_facts"; "tB"; "tE"; "tL"; "NPH"; "h_xregs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "BC_GE"; "M_MUL"; "mulop"; "ALU_AND"; "ALU_OR"; "ALU_SLL"; "ALU_SLT"; "ALU_SLTU"; "ALU_SRA"; "ALU_SRL"; "ALU_SUB"; "ALU_XOR"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "vDp"; "spm"; "B_EW"; "B32"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "two47"; "vKn"; "vW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth";
"firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt.HVTAddr"; "DW"; "FR"; "vt_EPI"; "vt_ret"; "memcpy_pc"; "op_pc"; "sm1_pc"; "vt_L"; "vt_REL"; "vt_W"; "vt_cp"; "vt_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "SHB"; "leavesA_at"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xlocal"; "shadow_reopen_stateA"; "flag_carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "P_alloc"; "P_st"; "vERR"; "vAL"; "vb"; "vc"; "havoc_reg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt.OP"; "Pre_op"; "P_op0"; "P_op1"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
Module OP. Include Lib_opt_push1. End OP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HVTAddr.
  Definition vt_entry : Z := 0x9c3a0.
  Definition sm1_pc : Z := 0x47c10.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition vt_cp : Z := 0x9c5f8.
  Definition op_pc : Z := 0xa3f44.
  Definition vt_L : Z := 0x9c52c.
  Definition vt_W : Z := 0x9c748.
  Definition vt_FP : Z := 0x9c688.
  Definition vt_P2 : Z := 0x9c7b0.
  Definition vt_EPI : Z := 0x9c6a0.
  Definition vt_REL : Z := 0x9c804.
  Definition vt_ret : Z := 0x9c840.
  Definition vt_ra_A : Z := 0x9c4f4. Definition vt_ra_B : Z := 0x9c51c. Definition vt_ra_vr : Z := 0x9c588. Definition vt_ra_mc : Z := 0x9c6f0.
  Definition vt_ra_D : Z := 0x9c728. Definition vt_ra_op : Z := 0x9c77c.
  Definition DW : Z := 4544.
  Definition FR : Z := 160.
End HVTAddr.
Import HVTAddr.

Definition FUEL_vt : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S15PaA1SfS141S114A1A1SfZ0A1Vcells;S16A5").
Definition O_Wv : sobj := ltac2:(tb__ "0|0|
S17SffS114A1SfeSfZ0A1S3S12A1S16A5").

Definition avt_t : sv := SVar 119.
Definition avt_cnt : sv := SAlu ALU_SLL avt_t (SLit 1).
Definition avt_cnt2 : sv := SAlu ALU_ADD avt_cnt (SLit 2).
Definition aw_d : sv := SVar 120. Definition aw_c : sv := SVar 121. Definition aw_k : sv := SVar 122.
Definition Wp1 : sv := ltac2:(tb__ "0|1|
S13SedS1cSf0SfZ1A1M0S5bA3G0A3").
Definition Cb1 : sv := ltac2:(tb__ "0|0|
S13SedS1cSf0SfZ1A1S5bA3SfZ0A1A3").
Definition V216t (d k : sv) : sobj := V 216 d avt_cnt k 4.
Definition V248 (d c k : sv) : sobj := V 248 d c k 4.
Definition vt_facts : list sprop := ltac2:(tb__ "0|1|
S5S11Se7S114S113A2S5S11S0S11S1bSefSfN1120A1SfeA3S0S11S14S5bSfS140Z2Z1bA2A1A2S0S11S14S5cS6aA2S0S11S14SdaZ4M0S4cA2SfS100A1A2S3S11A1A3A3A3A3S5S11SddSd9SbeSd7G0P74A5SddS49S5cS47G0P78A5A3A3A3").
Definition X_vt (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S1SeSeS12fSfZ518A1A4S0G0S1SeSeS130SfZ10A1A4S0G0S1SeSeS12eSfZ30A1A4S0G0S1SeSeSe8SeaA4S0G0S1SeSeSfS137A1SfZb8A1A4S0G0S1SeSeVd;SdaZ4M1Vk;A2A4S0G0S1SeSeVd2;SdaG1Vk2;A2A4S0G0S1SeSeSffS113A1SfS113A1A4S3G0A1A3A3A3A3A3A3A3A3").
Definition objs_vt (cur err : sv) (d k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S5S10S0S10S62S3S12A1A1S0S10S63S0S10S12bS0S10S12cVerr;A1S0S10Sb8Vd;Vk;A2S0S10S64Vd2;Vc2;Vk2;A3S0S10S12aS0S10Se2Vcur;A1S0S10Se1S0S10Se3S0S10SdcVd;Z4M0Vk;A3S0S10SdcVd2;G0Vk2;A3S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3S120A3").
Definition Pre_vt_S : sstate := ltac2:(tb__ "0|0|
S18S11eS13cS13bS19S6SeA1ScdSe5S12dSd9Sd7S49S5cS47A7Sd3SebS7A9").
Definition Pre_vt : axst := ltac2:(tb__ "0|0|
S11fSa5S58Sd9Sd7S49S47A4A2").

Definition bd_vt (k k2 : sv) : list bitem := ltac2:(tb__ "0|1|
S5S112SdbZ4M0S4cVk;A3SdbG0S5aVk2;A3A3").
Definition tv_vt (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S1SeSeVd;SdaZ4M1Vk;A2A4S0G0S1SeSeVd2;SdaG1Vk2;A2A4S3G0A1A3A3").
Definition tvI (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S1SeSeVd2;SdaZ4M1Vk2;A2A4S0G0S1SeSeVd;SdaG1Vk;A2A4S3G0A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S43S48Sd9Sd7S49S47A4S3S4S4SeS38A2SeA2A1S71Sd7S47A2A3").
Definition nd0' : ndesc := ltac2:(tb__ "0|0|
S43S67Sd9Sd7S49S47A4S3S4S4SeS38A2SeA2A1S71Sd7S47A2A3").

Definition cutpcs_vt : list Z := ltac2:(tb__ "0|0|
S0S38S119S0S38S138S0S38S11aS0S38S143S0S38S117S0S38S11cS0S38S118S0S38S115S0S38S11bS0S38S11dS3S38A1A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S11fS18Z0S3SeA1M0G0S19S6SeA1S3S10A1S3S11A1P1S7A9S3S4SeSeA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S110S3bVk;S122S6dS72VS;Vpc;A4S87A4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S9S8S3fA1M0A1S8S4S38S145A2M1A1Lx;S41S123S6dS72VS;SaA5G0S10fS3fG1S124R1A4Ll;S3G1A1X9x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_vt sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S4S39SeA2S1S39SeS13fSfeA4S10dPaS3cS6cA1S3cSa3A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_vt = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.
Definition fr_vt : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S4S4SeS38A2M0SeA2M1S1G0SeS1SeS38Sd8Z1A4SdeA4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S2S10eU0Vi;A2S5S2S10eSbVi;A1M0S142SdS10S1aS3cVA;A1A1A2G0A2A2S0S2Vi;S3S2A1A3A3A3").
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
S3dVA;S147S3cVA;A1Vi;Vo;A3A2").
Definition O_fr0 : sobj := ltac2:(tb__ "0|0|
S17Sd8SfZ0A1SfZ78A1S3S12A1S16A5").
Definition E_A2 : axst := Eval vm_compute in reshapeA E_A1 1 O_fr0.
Definition xf_sd : list axform := ltac2:(tb__ "0|2|
S0S31S32U0SfN30A1A2S0S31S32U6SfN70M0A1A2S0S31S32U7M1SfN68A1A2S0S31S33G1G0A2S3S31A1A3A3A3A3").
Definition E_A : axst := Eval vm_compute in optAp (apply_axforms E_A2 xf_sd).
Definition s_A : wsub := ltac2:(tb__ "0|0|
S10dPaS3cS93A1S3cS125A1A3").
Definition R_A : list sobj := Eval vm_compute in optR (entails_frA E_A Pre_sd s_A).
Goal entails_frA E_A Pre_sd s_A = Some R_A /\ call_checkA E_A Pre_sd s_A R_A [P_none; P_num] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S126S1eS3cVCl;A1A1S146Vs;VPre;VL;VCl;VR;A5A2").
Definition T_A0 : axst := Eval vm_compute in T_pure Pre_sd E_A s_A R_A P_none.
Definition T_A1 : axst := Eval vm_compute in T_pure Pre_sd E_A s_A R_A P_num.

Definition X_body (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SeSeA2M0S127Pa0S1S38S38Z20Z8A4A2S0G0S1SeSeSd8SfZ0A1A4S58Vd;Vk;Vd2;Vk2;A4A3A3").
Definition XB : list (sv * sv) := ltac2:(tb__ "0|0|
SbaSd9Sd7S49S47A4").
Definition E_B : axst := Eval vm_compute in ax_setX (leaf_at T_A1 sd_entry 0) XB.
Definition s_B : wsub := ltac2:(tb__ "0|0|
S10dPaS3cS6bA1S3cS125A1A3").
Definition R_B : list sobj := Eval vm_compute in optR (entails_frA E_B Pre_sd s_B).
Definition T_B0 : axst := Eval vm_compute in T_pure Pre_sd E_B s_B R_B P_none.
Definition T_B1 : axst := Eval vm_compute in T_pure Pre_sd E_B s_B R_B P_num.

Definition O_sdf : sobj := ltac2:(tb__ "0|0|
S17SffS114A1SfN30A1SfZ0A1S3S12A1S16A5").
Definition forget0 (A : axst) : axst := reshapeA A 0 O_sdf.
Definition C_L : axst := Eval vm_compute in ax_setX (havoc_reg (havoc_reg (forget0 (leaf_at T_A0 vt_L 0)) 10) 1) XB.
Goal lvs T_A0 = [(vt_L, RsCut)] /\ lvs T_A1 = [(sd_entry, RsCut)] /\ entails_frA E_B Pre_sd s_B = Some R_B /\ call_checkA E_B Pre_sd s_B R_B [P_none; P_num] = true
  /\ lvs T_B0 = [(vt_L, RsCut)] /\ lvs T_B1 = [(vt_L, RsCut)]
  /\ map (fun L => leaf_matches1A NPH L C_L) (leavesA_at FUEL_vt cutpcs_vt T_A0 vt_L ++ leavesA_at FUEL_vt cutpcs_vt T_B0 vt_L ++ leavesA_at FUEL_vt cutpcs_vt T_B1 vt_L) = [true; true; true].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at C_L vr_entry 0.
Definition sel_vr : list nat := ltac2:(tb__ "0|0|
S5S2S0S2U6S0S2U0S3S2A1A3A3S5S2S10eU1U5A2S10eU7UcA2A3A3").
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S31S35Sd0A1S0S31S34U0M0A1S0S31S32G0SfN40M1A1A2S0S31S33G0G1A2S0S31S33UdZd8A2S3S31A1A3A3A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S39SeA2S1S39SeP13S13SedSfeSfZ40A1A3A4S10dPaS3cS9cA1S3cS105A1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S4S3bS42A2M0S1S3bS42S104S107A4S0G0S1S3bS42S102S43S108S3S4S4SeS38A2SeA2A1M1S3S112A1A3A4S0G0S1S3bS42S103S43S109G1S106S10cS10bA2A3A4S3G0A1A3A3A3").
Goal lvs C_L = [(vr_entry, RsCut)] /\ entails_frA E_vr Pre_vr s_v = Some R_v /\ call_checkPA E_vr Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) avt_d)) XB.
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v Lib_vec_reserve.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_grown Xk_v.

Definition cm4 : sv := SMd M_MUL avt_cnt (SLit 4).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|1|
S0S11S14S13SedS50SfZ8A1A3SdaZ4Vk;A2M0A2S0S11S14S50G0A2S0S11S14S50SfS101A1A2S3S11A1A3A3A3").
Definition vDg : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_vr)) + 40)).
Definition vKg : sv := Eval vm_compute in SVar (Pos.of_nat (Pos.to_nat (ss_next (ax_S E_vr)) + 41)).
Definition T_keep : axst := ltac2:(tb__ "0|0|
S126S5S11S84Sd7A1S0S11S14SfS13eA1Sd9A2S3S11A1A3A3Sb2A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
S126S84S59A1Sb0A2").

Definition BADO : sobj := ltac2:(tb__ "0|1|
S17SfZ0A1M0G0G0S3S12A1S16A5").
Definition L_ck : axst := Eval vm_compute in leaf_at T_keep vt_cp 0.
Definition L_cg : axst := Eval vm_compute in leaf_at T_grown vt_cp 0.

Definition cur_off (L : axst) : sv := ltac2:(tb__ "0|1|
S8S12A1M0SeLx;S27S110S10U7S1aS3cVL;A1A1S88A4A1SfZ0A1S12G0SeSeLx;S25R2A1S38SfR1A1Lz;S39S15R1A1Li;SeeSeSeSeeSeLop;R3R1S13Sf9R2R1A3S13Sf4R2R1A3S13Sf5R2R1A3S13Sf6R2R1A3S13SfaR2R1A3S13Sf8R2R1A3S13Sf7R2R1A3S13Sf3R2R1A3S13Sf2R2R1A3XeexaLo;La;Lop;SeeSeSeS20R3R2R1A3Lb;La;Lop;Sf1SeSeS1cR3R2R1A3Lb;La;Lop;Sf1SeSeS22R3R2R1A3Lb;La;Lop;ScS3aSeS1dR3R2R1A3La;Lw;Lsgn;S39SeS38S21R3R2R1A3Lk;Li;Ll;Xex8Ll;Lc;X8x2").
Definition C_ck : axst := Eval vm_compute in bl_cut L_ck 13 (SLit 8) [10; 11; 16; 17]%nat [SPUle tI (cur_off L_ck)].
Definition C_cg : axst := Eval vm_compute in bl_cut L_cg 13 (SLit 8) [10; 11; 16; 17]%nat [SPUle tI (cur_off L_cg)].
Definition ck_var : sv := Eval vm_compute in bl_var L_ck (SLit 8).
Definition cg_var : sv := Eval vm_compute in bl_var L_cg (SLit 8).
Goal lvs T_keep = [(vt_cp, RsCut)] /\ lvs T_grown = [(vt_cp, RsCut)]
  /\ map SymState.c_val (ob_cells (nth 2 (ss_objs (ax_S T_grown0)) O_Wv)) = [vDg; avt_cnt; vKg; SLit 4].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S17S13SedVd;S50A3SfZ0A1SfZ8A1S3S12A1S16A5").
Definition src_obj : sobj := ltac2:(tb__ "0|0|
S17S13SedSd8SfZ20A1A3SfZ0A1SfZ8A1S3S12A1S16A5").
Definition xf_mc : list axform := ltac2:(tb__ "0|2|
S0S31S33U1M0Z40A2S0S31S35S5S2S0S2G0S0S2U0M1S3S2A1A3A3S10eU2U11A2A3A1S0S31S34G1A1S0S31S32U3S50A2S0S31S32U4S13SedS50SfZ8A1A3A2S0S31S32UbSfZ20A1A2S0S31S32UcSfZ28A1A2S3S31A1A3A3A3A3A3A3A3").
Definition E_mc (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S83S83S5eS37VE0;Sd5A2A1U4Sc2Vd;A1A3UcSd1A3").
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S39SeA2M0S1S39SeP35Vd;A4S0G0S1S39SeP36SdaZ4Vk;A2A4S0G0S1S39SeP37S13SedSd8SfZ20A1A3A4S0G0S1S39SeP38SfZ8A1A4S0G0S1S39SeS13fSfeA4S10dPaS3cVE;A1S3cSa2A1A3A3A3A3A3A3").

Definition E_Dk : axst := Eval vm_compute in bl_forget (bl_junk (leaf_at C_ck sd_entry 0) [16; 17]%nat) [4; 10]%nat.
Definition E_Dg : axst := Eval vm_compute in bl_forget (bl_junk (leaf_at C_cg sd_entry 0) [16; 17]%nat) [4; 10]%nat.

Definition mid_dst (d : sv) : sobj := ltac2:(tb__ "0|0|
S17Vd;S50S13SedS50SfZ8A1A3S3S12A1S16A5").
Definition sel_D : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2UcS0S2U2S0S2UdS0S2UeS0S2U3S0S2U4S0S2UfS0S2UbS0S2U10S0S2U11S0S2U12S0S2U5S0S2U13S0S2U6S0S2U9S0S2U14S0S2UaS0S2U7S0S2U1S0S2U8S0S2U15S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition xf_D : list axform := ltac2:(tb__ "0|3|
S0S31S33U1M0Z40A2S0S31S33U2M1Nd8A2S0S31S35S0S2G0S0S2U0M2S0S2UaS0S2UbS0S2U5S0S2U6S0S2UcS0S2U9S0S2UdS0S2UeS0S2UfS0S2G1S0S2U10S0S2U3S0S2U7S0S2U11S0S2U8S0S2U4S0S2U12S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S31S34G2A1S0S31S32G2SfN30A1A2S3S31A1A3A3A3A3A3").
Definition canon_D (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S5eS37VA;Sd4A2A1").
Definition E_Dkc : axst := Eval vm_compute in canon_D E_Dk avt_d.
Definition E_Dgc : axst := Eval vm_compute in canon_D E_Dg vDg.
Definition s_Dk : wsub := ltac2:(tb__ "0|0|
S10dPaS3cS97A1S3cS125A1A3").
Definition s_Dg : wsub := ltac2:(tb__ "0|0|
S10dPaS3cS95A1S3cS125A1A3").
Definition R_Dk : list sobj := Eval vm_compute in optR (entails_frA E_Dkc Pre_sd s_Dk).
Definition R_Dg : list sobj := Eval vm_compute in optR (entails_frA E_Dgc Pre_sd s_Dg).
Goal entails_frA E_Dkc Pre_sd s_Dk = Some R_Dk /\ call_checkA E_Dkc Pre_sd s_Dk R_Dk [P_none; P_num] = true
  /\ entails_frA E_Dgc Pre_sd s_Dg = Some R_Dg /\ call_checkA E_Dgc Pre_sd s_Dg R_Dg [P_none; P_num] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition T_D (E : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
Sb7S125VE;Vs;VR;VL;A5S3bS128R1S3eR1A1SdfZ8ZbA5TT;").
Definition T_Dk0 : axst := Eval vm_compute in T_D E_Dkc s_Dk R_Dk P_none.
Definition T_Dk1 : axst := Eval vm_compute in T_D E_Dkc s_Dk R_Dk P_num.
Definition T_Dg0 : axst := Eval vm_compute in T_D E_Dgc s_Dg R_Dg P_none.
Definition T_Dg1 : axst := Eval vm_compute in T_D E_Dgc s_Dg R_Dg P_num.
Goal map lvs [T_Dk0; T_Dk1; T_Dg0; T_Dg1] = [[(vt_W, RsCut)]; [(vt_W, RsCut)]; [(vt_W, RsCut)]; [(vt_W, RsCut)]].
Proof. vm_compute. reflexivity. Qed.

Definition havoc_freg (A : axst) (r : nat) : axst := ltac2:(tb__ "0|2|
S3cVA;A1S30S3dVA;S18S2dR1A1S2eR1A1S13dS2bR1A1S0S4S2SeA2M0S1S2SeVr;S15S1fR1A1M1A1A4S3G0A1A3A2S2aR1A1S2fR1A1S1aR1A1S1eR1A1S149G1A1S2cR1A1A9A2TS;").
Definition havoc_reg_le1 (A : axst) (r : nat) : axst := ltac2:(tb__ "0|0|
S1fS3cVA;A1A1S39S126S0S11S14S15R1A1SfZ1A1A2S3S11A1A3S131VA;Vr;A2A2Tv;").
Definition joinW (A : axst) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|1|
S139Sc7Sc8VA;UfM0A2G0A2VX;A2").
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
S0S31S35S5S2S0S2U6S0S2U0M0S0S2U1S0S2U2S0S2U3S0S2U4S0S2U5S3S2A1A3A3A3A3A3A3A3S10eU7M1UcA2A3A1S0S31S34G0A1S0S31S32G0SfN80M2A1A2S0S31S33G0G2A2S0S31S33UeZf8A2S0S31S32G1SfZ40M3A1A2S0S31S32U8M4SfZ44A1A2S0S31S32U9SfZ50M5A1A2S0S31S32UaM6SfZ54A1A2S0S31S33G4G3A2S0S31S33G6G5A2S3S31A1A3A3A3A3A3A3A3A3A3A3A3").
Definition E_opkc : axst := Eval vm_compute in optAp (apply_axforms E_opk1 xf_op).
Definition E_opgc : axst := Eval vm_compute in optAp (apply_axforms E_opg1 xf_op).
Definition s_opk : wsub := ltac2:(tb__ "0|0|
S0S4S39SeA2S1S39SeP13S13SedSfeSfZ80A1A3A4S10dPaS3cS9bA1S3cS132A1A3A3").
Definition s_opg : wsub := ltac2:(tb__ "0|0|
S0S4S39SeA2S1S39SeP13S13SedSfeSfZ80A1A3A4S10dPaS3cS99A1S3cS132A1A3A3").
Definition R_opk : list sobj := Eval vm_compute in optR (entails_frA E_opkc OP.Pre_op s_opk).
Definition R_opg : list sobj := Eval vm_compute in optR (entails_frA E_opgc OP.Pre_op s_opg).
Definition PD_op : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S3bS42A2M0S1S3bS42S134S136A4S0G0S1S3bS42S133S135A4S3G0A1A3A3").
Goal entails_frA E_opkc OP.Pre_op s_opk = Some R_opk /\ call_checkPA E_opkc OP.Pre_op s_opk R_opk (map fst PD_op) = true
  /\ entails_frA E_opgc OP.Pre_op s_opg = Some R_opg /\ call_checkPA E_opgc OP.Pre_op s_opg R_opg (map fst PD_op) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition Xk_op (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|3|
S0S4SeSeA2M0S127Pa0M1S1S38S38Z40Z4M2A4A2S0G0S127G1S1S38S38Z50G2A4A2S0G0S127G1S1S38S38Z20Z8A4A2S0G0S1SeSeSd8SfZ0A1A4S0G0S1SeSeS12fSfZ518A1A4S0G0S1SeSeS130SfZ10A1A4S0G0S1SeSeS12eSfZ30A1A4S0G0S1SeSeSe8SeaA4S0G0S1SeSeSfS137A1SfZb8A1A4S0G0S1SeSeVd;SdaG2Vk;A2A4S0G0S1SeSeSffS113A1SfS113A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Goal Xk_op avt_d avt_k = List.filter (fun r => negb (sv_eqb (fst r) aw_d)) (ax_X E_opkc) /\ Xk_op vDg vKg = List.filter (fun r => negb (sv_eqb (fst r) aw_d)) (ax_X E_opgc).
Proof. vm_compute. split; reflexivity. Qed.
Definition sel_op : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2UcS0S2U4S0S2UdS0S2U5S0S2UeS0S2UfS0S2U7S0S2U8S0S2U10S0S2UbS0S2U11S0S2U12S0S2U13S0S2U14S0S2U2S0S2U3S0S2U9S0S2U15S0S2UaS0S2U16S0S2U6S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_opb : list axform := ltac2:(tb__ "0|4|
S0S31S33U1M0Z80A2S0S31S36U4A1S0S31S36U5M1A1S0S31S33U2Nf8A2S0S31S36UbA1S0S31S35SceA1S0S31S34U0A1S0S31S34G0A1M2S0S31G2S0S31G2S0S31G2S0S31S34G1A1M3S0S31G3S3S31A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
S129S128VY;S3eVY;A1SdfZ0Z10A5PaaA2").
Definition cont_op (E : axst) (s : wsub) (R : list sobj) (P : axst) (d k d2 k2 : sv) : axst := ltac2:(tb__ "0|0|
Sc4S139S5eS37S148S132VE;Vs;VR;VP;SbdVd;Vk;A2A6Sd6A2A1S58Vd;Vk;Vd2;Vk2;A4A2A1").
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
S8S4S4SeSeA2SeA2A1") := ltac2:(tb__ "0|1|
S10fS10S4S4SeSeA2M0SeA2S10S1G0SeS1SeSeS26R1A1S29R1A1A4S28R1A1A4Lo;S1aS3cVA;A1A1A4").
Goal firstn 16 (shape T_opk1) = shape (mkA (mkSS 0 [] [] FcsrFrm0 None ([O_Wv; O_fr0; mkObj hF (SLit 120) (SLit 128) [] DUnknown] ++ A_globals ++ [O_F []; P_alloc; P_st vERR; V216t avt_d avt_k; V248 oD oC oK; O_al; O_cP tI; O_cE; O_text; O_data avt_d 4 avt_k; O_data oD 4 oK]) [] NPH false) [])
  /\ map lvs [T_opk1; T_opk0; T_opg1; T_opg0] = [[(vt_EPI, RsCut)]; [(vt_EPI, RsCut); (vt_EPI, RsCut)]; [(vt_EPI, RsCut)]; [(vt_EPI, RsCut); (vt_EPI, RsCut)]].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition xf_fl : list axform := ltac2:(tb__ "0|6|
S0S31S33U1M0Z40A2S0S31S33U2M1Nd8A2S0S31S36U9M2A1S0S31S35S0S2G0S0S2U0M3S0S2UaS0S2UbS0S2U5M4S0S2U6S0S2UcS0S2G2S0S2UdS0S2UeS0S2UfS0S2G1S0S2U10S0S2U3S0S2U7S0S2U11S0S2U8S0S2U4S0S2U12S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S31S34G3A1S0S31S34G4A1M5S0S31G5S3S31A1A3A3A3A3A3A3A3").
Definition Y_fl : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_fail0 xf_fl)) (X_vt avt_d avt_k aw_d aw_k).
Definition T_fl : axst := Eval vm_compute in epi_state Y_fl.
Goal firstn 15 (shape T_fl) = firstn 15 (shape T_opk1) /\ nth 15 (shape T_fl) (vb, vb, vb) = (aw_d, SLit 0, kb 4 aw_k) /\ lvs T_fl = [(vt_EPI, RsCut); (vt_EPI, RsCut)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition yCUR : sv := SVar 320. Definition yD : sv := SVar 321. Definition yC1 : sv := SVar 322. Definition yK : sv := SVar 323.
Definition yD2 : sv := SVar 324. Definition yC2 : sv := SVar 325. Definition yK2 : sv := SVar 326. Definition yERR : sv := SVar 328.
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1bSfcS1dSaQ20Ve;A3SfZ0A1A3").
Definition F_saved : list cell := ltac2:(tb__ "0|0|
S0S12SfdN68S15P2fA1A2S0S12SfdN60S15P2eA1A2S0S12SfdN58S15P2dA1A2S0S12SfdN50S15P2cA1A2S0S12SfdN48S15P2bA1A2S0S12SfdN40S15P2aA1A2S0S12SfdN38S15P29A1A2S0S12SfdN30S15P28A1A2S0S12SfdN28S15P27A1A2S0S12SfdN20S15P26A1A2S0S12SfdN18S15P1dA1A2S0S12SfdN10S15P1cA1A2S0S12SfdN8S15PbA1A2S3S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S17Sd8SfZ78M0A1SfZ80A1S0S12SfdG0SdeA2S3S12A1A3S16A5").
Definition objs_epi (err cnt cur d k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|2|
S5S10S0S10S63S0S10Sa1S0S10Sa0S3S10A1M0A3A3A3S5S10S120S0S10S62S9eA1S0S10S12bS0S10S12cVerr;A1S0S10Se6Zd8Vd;Vcnt;Vk;Z4M1A5S0S10S64Vd2;Vc2;Vk2;A3S0S10S12aS0S10Se2Vcur;A1S0S10Se1S0S10Se3S0S10SdcVd;G1Vk;A3S0S10SdcVd2;G1Vk2;A3G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition base_vt : list sprop := ltac2:(tb__ "0|0|
S5S11Se7S114S113A2S0S11S1bSefSfN1120A1SfeA3S0S11S14S5bSfS140Z2Z1bA2A1A2S0S11S14S5cS6aA2S0S11S14SdaZ4S4cA2SfS100A1A2S3S11A1A3A3A3A3A3").
Definition frame_factsV : list sprop := ltac2:(tb__ "0|1|
S5S11S40SdfSd8A2S0S11S23Pa0Z5A2S0S11S24S1bSfbSd8SfZ0A1A3A1S0S11S14SfS13eA1M0Sd8A2S0S11S14S13SedSd8SfZ80A1A3S15P1eA1A2S0S11S14Sd8SfS10aA1A2S0S11S14G0SdeA2S0S11S14S13SedSdeSfZ1A1A3SfZ7fffff800000A1A2S3S11A1A3A3A3A3A3A3A3A3").
Definition ok_facts (cur d k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|1|
S5S11S0S11S14Vc2;S5aA2S0S11S14Se5Vcur;A2S0S11S14Vcur;Se9A2S3S11A1A3A3A3S5S11SddVd;S4cVk;Z4M0Vdv;A5SddVd2;Vc2;Vk2;G0Vdv2;A5A3A3").
Definition fail_facts (err cur d c1 k d2 c2 k2 : sv) (dv dv2 : positive) : list sprop := ltac2:(tb__ "0|1|
S5S11S0S11S9fVerr;A1S0S11S14Se5Vcur;A2S0S11S14Vcur;Se9A2S3S11A1A3A3A3S5S11SddVd;Vc1;Vk;Z4M0Vdv;A5SddVd2;Vc2;Vk2;G0Vdv2;A5A3A3").
Definition epi_regs : list sv := ltac2:(tb__ "0|1|
SecS0S4S2SeA2M0S1S2SeU8S15PaA1A4S0G0S1S2SeUdSd8A4S0G0S1S2SeU18S13SedS15SdfA1SfS121A1A3A4S3G0A1A3A3A3A1").
Definition YC (err cnt : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S11fS18S115Sc3Se4S19S6SeA1SccVerr;Vcnt;S69S54S4aS55S68S4bA8S5S11Vfacts;S5S11S65Sc6A3A3Se0S7A9S58S54S4aS55S4bA4A2").
Definition Y_ok : axst := ltac2:(tb__ "0|0|
S70S12dS4cS80S69S54S4aS55S68S4bP141P144A8A3").
Definition Y_fail : axst := ltac2:(tb__ "0|0|
S70S86S85S73S86S69S54S85S4aS55S68S4bP141P144AaA3").
Definition C_Eo : axst := Eval vm_compute in epi_state Y_ok.
Definition C_Ef : axst := Eval vm_compute in epi_state Y_fail.
Goal map (fun C => map (fun L => (leaf_matches1A NPH L C_Ef, leaf_matches1A NPH L C_Eo)) (leavesA_at FUEL_vt cutpcs_vt C vt_EPI)) [T_opk1; T_opg1; T_opk0; T_opg0; T_fl]
  = [[(false, true)]; [(false, true)]; [(true, false); (true, false)]; [(true, false); (true, false)]; [(true, false); (true, false)]].
Proof. vm_compute. reflexivity. Qed.

Definition X_rlo : axst := Eval vm_compute in leaf_at C_Eo vt_REL 0.
Definition X_rlf : axst := Eval vm_compute in leaf_at C_Ef vt_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U0S3S2A1M0A3S5S2S10eU3UdA2S0S2U1S0S2U2S0S2U10S0S2U11G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S5eS37VX;S0S31S35ScfA1S3S31A1A3A2A1S3bS3dR1S144S3cR1A1M0S111S10UeS1aG0A1A3A2A2TX1;").
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
S5S10S0S10S63S3S10A1M0A3S5S10S120S0S10S62S3S12A1A1S0S10S12bS0S10S12cVerr;A1S0S10Se6Zd8Vd;Vcnt;Vk;Z4M1A5S0S10S64Vd2;Vc2;Vk2;A3S0S10S12aS0S10Se2Vcur;A1S0S10Se1S0S10Se3S0S10SdcVd;G1Vk;A3S0S10SdcVd2;G1Vk2;A3G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S11fS18S116S13aP190A1Se4S19S6SeA1S7fS12dS4cS60S52S4eS53S5fS4fA8S5S11S80S60S52S4eS53S5fS4fP137P13cA8S65A3Se0S7A9S58S52S4eS53S4fA4A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S11fS18S116S13aP190A1Se4S19S6SeA1S7fS82S81S60S52S4eS53S5fS4fA8S5S11S73S82S60S52S81S4eS53S5fS4fP137P13cAaS65A3Se0S7A9S58S52S4eS53S4fA4A2").

Definition bd_fin (k k2 : sv) : list bitem := ltac2:(tb__ "0|1|
S5S112SdbZ4M0S5aVk2;A3SdbG0S4cVk;A3A3").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S43S48S52S4eS53S4fA4S3S4S4SeS38A2SeA2A1S5dS4eS4fA2A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S43S48S52S4eS53S4fA4S3S4S4SeS38A2SeA2A1S3S112A1A3").
Definition Posts_vt : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S3bS42A2M0S1S3bS42S6eS7bA4S0G0S1S3bS42S6fS7cA4S3G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S45Vtv;Sc5Vbd;S44A4").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|0|
S67Sd9Sd7S49S47A4").
Definition tvG : list (sv * sv) := ltac2:(tb__ "0|0|
S67S61S59S49S47A4").
Definition bdPre : list bitem := bd_vt avt_k aw_k.
Definition bdK (k : sv) : list bitem := ltac2:(tb__ "0|1|
S5S112SdbZ4M0S4cVk;A3SdbG0S5aS47A3A3").
Definition bdFl : list bitem := bd_vec 4 Wp1 aw_k.
Definition ndP : ndesc := ndF tvP bdPre.
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S51Sd2S66Sd7A1A2").
Definition ndG : ndesc := ndF tvG (bdK vKg).
Definition ndKs : ndesc := ltac2:(tb__ "0|0|
S51S48Sd9Sd7S49S47A4S66Sd7A1A2").
Definition ndGs : ndesc := ltac2:(tb__ "0|0|
S51S48S61S59S49S47A4S66S59A1A2").
Definition ndFl : ndesc := ltac2:(tb__ "0|0|
S51S48Sd9Sd7S49S47A4SbfA2").
Definition ndO (d k d2 k2 : sv) : ndesc := ltac2:(tb__ "0|0|
S51S48Vd;Vk;Vd2;Vk2;A4S5dVk;Vk2;A2A2").
Definition ndX (d k d2 k2 : sv) : ndesc := ltac2:(tb__ "0|0|
S51S48Vd;Vk;Vd2;Vk2;A4SdbZ4S4cVk;A3A2").
Definition ndEo : ndesc := ltac2:(tb__ "0|0|
S51S48S54S4aS55S4bA4S5dS4aS4bA2A2").
Definition ndEf : ndesc := ltac2:(tb__ "0|0|
S51S48S54S4aS55S4bA4S3S112A1A2").
Definition ndEo' : ndesc := ltac2:(tb__ "0|0|
S43S48S54S4aS55S4bA4S3S4S4SeS38A2SeA2A1S5dS4aS4bA2A3").
Definition ndEf' : ndesc := ltac2:(tb__ "0|0|
S43S48S54S4aS55S4bA4S3S4S4SeS38A2SeA2A1S3S112A1A3").
Definition z0 : sv := SLit 0.
Definition cutsV : list edescA := ltac2:(tb__ "0|c|
S0S4S4S3bS42A2M0S4S38SeA2M1A2M2S1G0G1S1S3bS42Sa4S76A4S1S38SeZ64S46A4A4S0G2S1G0G1S1S3bS42S90S4dA4S1S38SeZ60S46A4A4S0G2S1G0G1S1S3bS42Sa6S4dA4S1S38SeZ5aS46A4M3A4S0G2S1G0G1S1S3bS42Sa7S4dA4G3A4S0G2S1G0G1S1S3bS42Sa8S4dA4S1S38SeZ56S46A4M4A4S0G2S1G0G1S1S3bS42Sa9S4dA4G4A4S0G2S1G0G1S1S3bS42S8bS4dA4S1S38SeZ50S46A4A4S0G2S1G0G1S1S3bS42Sb1S57A4S1S38SeZ4aS46A4M5A4S0G2S1G0G1S1S3bS42SafS56A4G5A4S0G2S1G0G1S1S3bS42SaeScbA4G5A4S0G2S1G0G1S1S3bS42S8fS57A4S1S38SeZ46M6Sc1A4A4S0G2S1G0G1S1S3bS42S8eS56A4S1S38SeG6Sc0A4A4S0G2S1G0G1S1S3bS42SacS57A4S1S38SeZ42S46A4M7A4S0G2S1G0G1S1S3bS42SadS57A4G7A4S0G2S1G0G1S1S3bS42SaaS56A4G7A4S0G2S1G0G1S1S3bS42SabS56A4G7A4S0G2S1G0G1S1S3bS42S8dS57A4S1S38SeZ40S46A4M8A4S0G2S1G0G1S1S3bS42S8cS56A4G8A4S0G2S1G0G1S1S3bS42Sb6S79Sd9Sd7S7dS7eA4A4S1S38SeZ3aS46A4M9A4S0G2S1G0G1S1S3bS42Sb5S7aSd9Sd7S7dS7eA4A4G9A4S0G2S1G0G1S1S3bS42Sb4S79S61S59S74S75A4A4G9A4S0G2S1G0G1S1S3bS42Sb3S7aS61S59S74S75A4A4G9A4S0G2S1G0G1S1S3bS42S89S77A4S1S38SeZ32S46A4MaA4S0G2S1G0G1S1S3bS42S8aS78A4GaA4S0G2S1G0G1S1S3bS42S91Sc9A4S1S38SeZ1eS46A4MbA4S0G2S1G0G1S1S3bS42S92ScaA4GbA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsV : list edescA := ltac2:(tb__ "0|7|
S0S4S4S3bS42A2M0S4S38SeA2M1A2M2S1G0G1S1S3bS42S6cS76A4S1S38SeZ62S46A4A4S0G2S1G0G1S1S3bS42Sb9S4dA4S1S38SeZ5eS46A4A4S0G2S1G0G1S1S3bS42S6bS4dA4S1S38SeZ58S46A4A4S0G2S1G0G1S1S3bS42S9dS4dA4S1S38SeZ4eS46A4A4S0G2S1G0G1S1S3bS42S96S57A4S1S38SeZ44S46A4M3A4S0G2S1G0G1S1S3bS42S94S56A4G3A4S0G2S1G0G1S1S3bS42S9aS57A4S1S38SeZ3eS46A4M4A4S0G2S1G0G1S1S3bS42S98S56A4G4A4S0G2S1G0G1S1S3bS42SbbS77A4S1S38SeZ28S46A4M5A4S0G2S1G0G1S1S3bS42SbcS78A4G5A4S0G2S1G0G1S1S3bS42S6eS7bA4S1S38SeZ0S46A4M6A4S0G2S1G0G1S1S3bS42S6fS7cA4G6A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
