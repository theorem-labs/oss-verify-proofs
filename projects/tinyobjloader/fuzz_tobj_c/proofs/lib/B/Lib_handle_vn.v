(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "bool"; "option"; "true"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SAlu"; "SPUle"; "DUnknown"; "cell"; "mkObj"; "FcsrFrm0"; "SVar"; "mkSS"; "ss_facts"; "SExt"; "SMd"; "SPBranch"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "sym_runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXSplit"; "AXMerge"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "z0"; "vDp"; "spm"; "B32"; "B_EW"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vNK"; "vNC"; "vND"; "kb4"; "cb4"; "O_al"; "O_c0"; "O_c8"; "O_dat"; "P_alloc"; "P_st"; "V184"; "bd_cnt"; "vE"; "vERR"; "vec4_facts"; "builder_facts"; "vAL"; "vb"; "vc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn"; "ndp"; "vF"; "ndf"; "tv_hvn"; "bd_hvn"; "pCUR"; "X_hvn"; "ndg"; "ndk"; "pK"; "E_B"; "E_C"; "ndF"; "optAh"; "pD"; "E_A"; "hvn_facts"; "vKg"; "C_ms1"; "E_sm0"; "FUEL_hvn"; "O_F"; "O_Wh"; "Pre_hvn"; "T_ms0"; "cutpcs_hvn"; "nd0"; "ndf'"; "objs_post"; "pERR"; "post_fregs_hvn"; "slot_facts"; "tvG"; "C_F"; "C_J"; "C_body"; "C_cg"; "C_ck"; "C_epf0"; "C_epf1"; "C_epg"; "C_epk"; "C_pro"; "C_rlf0"; "C_rlf1"; "C_rlg"; "C_rlk"; "E_A0"; "E_ms"; "E_vr"; "E_vr0"; "NZ32"; "P_fail"; "P_ok"; "Pre_hvn_S"; "Pre_mc"; "Pre_ms"; "Pre_sm"; "R_A"; "R_B"; "R_C"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_C0"; "T_C1"; "T_fail0"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "X_epf0"; "X_epf1"; "X_epg"; "X_epi"; "X_epk"; "X_rel"; "X_rlf0"; "X_rlf1"; "X_rlg"; "X_rlk"; "cg_var"; "ck_var"; "dst_obj"; "fcallee_saved"; "fr_hvn"; "gF"; "mid_xyz"; "nd_fail"; "nd_ok"; "ndg'"; "ndk'"; "objs_hvn"; "post_facts"; "s_A"; "s_B"; "s_C"; "sel_rel"; "sel_vr"; "src_obj"; "vFL"; "xf_mc"; "xyz_obj"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "vI"; "O_txt"; "vB"; "vL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn.HVNAddr"; "DW"; "hvn_ret"; "hvn_EPI"; "hvn_F"; "hvn_J"; "hvn_REL"; "hvn_cp"; "hvn_entry"; "memcpy_pc"; "memset_pc"; "sm0_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH";
"@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "flag_carve_stateA"; "shadow_reopen_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HVNAddr.
  Definition hvn_entry : Z := 0x9bf74.
  Definition sm0_pc : Z := 0x47a9c.
  Definition memset_pc : Z := 0x5ce7c.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition hvn_cp : Z := 0x9c218.
  Definition hvn_A : Z := 0x9c0b4.
  Definition hvn_B : Z := 0x9c0dc.
  Definition hvn_C : Z := 0x9c104.
  Definition hvn_J : Z := 0x9c120.
  Definition hvn_F : Z := 0x9c194.
  Definition hvn_EPI : Z := 0x9c28c.
  Definition hvn_REL : Z := 0x9c2f8.
  Definition hvn_ret : Z := 0x9c330.
  Definition DW : Z := 4480.
End HVNAddr.
Import HVNAddr.

Definition FUEL_hvn : nat := 300%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S15S17PaA1SeN80A1SeZ0A1Vcells;S13A5").
Definition O_Wh : sobj := ltac2:(tb__ "0|0|
S15S31Z80A1S30SeZ0A1S3S14A1S13A5").

Definition hvn_facts : list sprop := ltac2:(tb__ "0|0|
S5S10S45Sc4A1S5S10S0S10S12S38S11S49S36SeZ3A1A3A1SeS33A1A2S3S10A1A3S44S37S36S35P36A4A3A3").
Definition X_hvn (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0S1SdSdS47SeZ518A1A4S0G0S1SdSdS48SeZ10A1A4S0G0S1SdSdS46SeZ30A1A4S0G0S1SdSdSbcSbdA4S0G0S1SdSdSeSd8A1SeZb8A1A4S0G0S1SdSdVd;S38Vk;A1A4S0G0S1SdSdS31Sc4A1SeSc4A1A4S3G0A1A3A3A3A3A3A3A3").
Definition objs_hvn (cur err d c k : sv) : list sobj := ltac2:(tb__ "0|1|
S5SfS0SfS61S3S14A1M0A1S0SfS62S0SfS3eS0SfS3fVerr;A1S0SfS40Vd;Vc;Vk;A3S0SfS3aS0SfS3bVcur;A1S0SfS3cS0SfSbbG0A1S0SfS3dVd;Vk;A2S3SfA1A3A3A3A3A3A3A3A3A3A3Sc1A3").
Definition Pre_hvn_S : sstate := ltac2:(tb__ "0|0|
S18ScbSd3Sd2S16S6SdA1Sa9SbaS43S37S36S35A5S5cSd0S7A9").
Definition Pre_hvn : axst := ltac2:(tb__ "0|0|
Sc0S82S52S37S35A2A2").

Definition bd_hvn (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S41S11S49Vc;SeZ3A1A3Vk;A2").
Definition tv_hvn (d k : sv) : list (sv * sv) := tv_vec d k.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S26S4fS37S35A2S3S4S4SdS23A2SdA2A1S50S36S35A2A3").

Definition cutpcs_hvn : list Z := ltac2:(tb__ "0|0|
S0S23SceS0S23ScdS0S23SccS0S23Sd9S0S23SdaS0S23Sc8S0S23Sc7S0S23Sc6S0S23Sc9S0S23ScaS3S23A1A3A3A3A3A3A3A3A3A3A3").
Definition optAh (x : option axst) : axst := match x with Some s => s | None => Pre_hvn end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sb7S1eVk;Sc2S60S65VS;Vpc;A4S63A4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SbS21S9ScS21A1M0A1G0Lx;S22Sc3S60S65VS;SaA5G0R1Ll;S3S21A1X9x2A2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hvn sm0_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 0.
Definition L_sm : axst := L_stack_malloc AE_A 0.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S4S24SdA2S1S24SdSd5S30A4Sb8PaS1fS5fA1S1fS85A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal nleaves Pre_hvn = 1%nat /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition vF : sv := SVar 110. Definition vFL : sv := SVar 120. Definition gF : positive := 140%positive.
Definition fr_hvn : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S4S4SdS23A2M0SdA2M1S1G0SdS1SdS23S4dZ0A4Sb1A4S3G1A1A3").
Definition sel_sm : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U0S0S2U1S0S2U2S3S2A1M0A3A3A3S5S2Sb4U4UbA2S0S2U3G0A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAh (apply_axforms T_sm [AXSelect sel_sm]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj vFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_hvn vND vNK ++ (vF, SLit 64) :: [] /\ ss_next (ax_S T_sm1) = gF.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 (X_hvn vND vNK) 110 64.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((vF, SLit 0) :: ax_X C_pro0).

Definition X_rel : axst := Eval vm_compute in leaf_at C_pro memset_pc 0.
Definition sh_rel : sobj := Eval vm_compute in last (ss_objs (ax_S X_rel)) O_Wh.
Definition objs_rel : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_rel)).
Goal nleaves C_pro = 1%nat /\ sh_rel = shobj gF 0 8 (ob_cells sh_rel) DZero /\ local_ok (ob_cells sh_rel) DZero 0 8 (32, 12) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_ms : axst := Eval vm_compute in shadow_release_stateA X_rel objs_rel 110 [(32, 12)].

Definition xyz_obj (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S15S11S49S4dSeZ20A1A3SeZ0A1SeZcA1Vcells;S13A5").
Definition C_ms1 : axst := Eval vm_compute in optAh (apply_axforms C_ms [AXSplit 1 (SLit 32); AXSplit 2 (SLit 44)]).
Definition E_ms : axst := ltac2:(tb__ "0|0|
S20S5eSbeS1fS5eA1U2Sb3S3S14A1A1A3A2").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_ms : wsub := ltac2:(tb__ "0|1|
S0S4S24SdA2M0S1S24SdP35S11S49S4dSeZ20A1A3A4S0G0S1S24SdP36SeZcA1A4S0G0S1S24SdSd5S30A4Sb8PaS1fS7cA1S1fS84A1A3A3A3A3").
Definition R_ms : list sobj := Eval vm_compute in optR (entails_frA E_ms Pre_ms s_ms).
Goal entails_frA E_ms Pre_ms s_ms = Some R_ms /\ call_checkPA E_ms Pre_ms s_ms R_ms [L_ms] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_ms0 : axst := Eval vm_compute in T_afterA Pre_ms E_ms s_ms R_ms L_ms.

Definition mid_xyz : sobj := ltac2:(tb__ "0|0|
S15S4dSeZ20A1SeZ2cA1S3S14A1S13A5").
Definition T_ms1 : axst := ltac2:(tb__ "0|0|
S20S64SbeS1fS64A1U1Sa4A3A2").
Definition sel_ms : list nat := ltac2:(tb__ "0|0|
S5S2S0S2U0S0S2U4S0S2U1S0S2U5S0S2U6S0S2U2S0S2U3S3S2A1A3A3A3A3A3A3A3Sb4U7U9A2A3").
Definition C_body : axst := Eval vm_compute in optAh (apply_axforms T_ms1 [AXSelect sel_ms; AXMerge 1; AXMerge 1]).
Goal map (fun o => (ob_base o, ob_lo o, ob_hi o)) (firstn 3 (ss_objs (ax_S C_body))) = [(spm 128, vDp, SLit 0); (vF, SLit 0, SLit 56); (vF, SLit 56, SLit 64)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition xf_sd : list axform := ltac2:(tb__ "0|2|
S0S29S2bU0SeN30A1A2S0S29S2bU6SeN68M0A1A2S0S29S2bU7M1SeN60A1A2S0S29S2aG1G0A2S3S29A1A3A3A3A3").
Definition E_A0 : axst := Eval vm_compute in leaf_at C_body sd_entry 0.
Definition E_A : axst := Eval vm_compute in optAh (apply_axforms E_A0 xf_sd).
Definition s_A : wsub := ltac2:(tb__ "0|0|
Sb8PaS1fS5bA1S1fSb9A1A3").
Definition R_A : list sobj := Eval vm_compute in optR (entails_frA E_A Pre_sd s_A).
Goal nleaves C_body = 1%nat /\ entails_frA E_A Pre_sd s_A = Some R_A /\ call_checkA E_A Pre_sd s_A R_A [P_none; P_num] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition TA (L : axst) : axst := ltac2:(tb__ "0|0|
SbfS19S1fS5bA1A1ScfSabSb9VL;S5bS86A5A2").
Definition T_A0 : axst := Eval vm_compute in TA P_none.
Definition T_A1 : axst := Eval vm_compute in TA P_num.
Definition E_B0a : axst := Eval vm_compute in leaf_at T_A0 sd_entry 0.
Definition E_B1a : axst := Eval vm_compute in leaf_at T_A1 sd_entry 0.

Definition X_body : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4SdSdA2M0SdeP6eS1S23S23Z20ZcA4A2S0G0S1SdSdS4dSeZ0A1A4S52S37S35A2A3A3").
Definition E_B : axst := ax_setX E_B0a X_body.
Definition s_B : wsub := ltac2:(tb__ "0|0|
Sb8PaS1fS56A1S1fSb9A1A3").
Definition R_B : list sobj := Eval vm_compute in optR (entails_frA E_B Pre_sd s_B).
Definition TB (L : axst) : axst := ltac2:(tb__ "0|0|
SbfS19S1fS56A1A1ScfSacSb9VL;S56S87A5A2").
Definition T_B0 : axst := Eval vm_compute in TB P_none.
Definition T_B1 : axst := Eval vm_compute in TB P_num.
Definition E_C : axst := Eval vm_compute in ax_setX (leaf_at T_B0 sd_entry 0) X_body.
Definition E_C1a : axst := Eval vm_compute in leaf_at T_B1 sd_entry 0.
Definition s_C : wsub := ltac2:(tb__ "0|0|
Sb8PaS1fS57A1S1fSb9A1A3").
Definition R_C : list sobj := Eval vm_compute in optR (entails_frA E_C Pre_sd s_C).
Definition TC (L : axst) : axst := ltac2:(tb__ "0|0|
SbfS19S1fS57A1A1ScfSadSb9VL;S57S88A5A2").
Definition T_C0 : axst := Eval vm_compute in TC P_none.
Definition T_C1 : axst := Eval vm_compute in TC P_num.

Definition C_J : axst := Eval vm_compute in ax_setX (havoc_reg (leaf_at T_C0 hvn_J 0) 10) X_body.
Definition C_J1a : axst := Eval vm_compute in leaf_at T_C1 hvn_J 0.
Goal entails_frA E_B Pre_sd s_B = Some R_B /\ call_checkA E_B Pre_sd s_B R_B [P_none; P_num] = true
  /\ entails_frA E_C Pre_sd s_C = Some R_C /\ call_checkA E_C Pre_sd s_C R_C [P_none; P_num] = true
  /\ leaf_matches1A NF E_B1a E_B = true /\ leaf_matches1A NF E_C1a E_C = true /\ leaf_matches1A NF C_J1a C_J = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at C_J vr_entry 0.
Definition sel_vr : list nat := ltac2:(tb__ "0|0|
S5S2S0S2U6S0S2U0S3S2A1A3A3S5S2Sb4U1U5A2Sb4U7UaA2A3A3").
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S29S2dSafA1S0S29S2cU0M0A1S0S29S2bG0SeN40M1A1A2S0S29S2aG0G1A2S0S29S2aUdZb8A2S3S29A1A3A3A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAh (apply_axforms E_vr0 xf_vr).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S24SdA2S1S24SdP13S11S49S30SeZ40A1A3A4Sb8PaS1fS7dA1S1fS34A1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr Pre_vr s_v).
Goal nleaves C_J = 1%nat /\ entails_frA E_vr Pre_vr s_v = Some R_v /\ call_checkPA E_vr Pre_vr s_v R_v [P_keep; P_fail; P_grown] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) vND)) X_body.
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vr s_v R_v P_grown Xk_v.

Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|2|
S0S10S12S11S49S1bS4bS36SeZ4A1A3M0SeZcA1A3S38Vk;A1M1A2S0S10S12G0G1A2S0S10S12G0SeS32A1A2S3S10A1A3A3A3").
Definition vDg : sv := SVar 446.
Definition vKg : sv := SVar 447.
Definition T_keep : axst := ltac2:(tb__ "0|0|
SbfS5S10S6bS35A1S0S10S12SeSdfA1S37A2S3S10A1A3A3S93A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
SbfS6bS5dA1S91A2").

Goal length (ax_X T_keep0) = 11%nat /\ nleaves T_keep = 1%nat /\ nleaves T_grown = 1%nat /\ nleaves T_fail0 = 1%nat
  /\ map SymState.c_val (ob_cells (nth 2 (ss_objs (ax_S T_grown0)) O_Wh)) = [vDg; vNC; vKg; SLit 4].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition L_ck : axst := Eval vm_compute in leaf_at T_keep hvn_cp 0.
Definition L_cg : axst := Eval vm_compute in leaf_at T_grown hvn_cp 0.
Definition C_ck : axst := Eval vm_compute in bl_cut L_ck 13 (SLit 12) [10; 11; 16; 17]%nat [].
Definition C_cg : axst := Eval vm_compute in bl_cut L_cg 13 (SLit 12) [10; 11; 16; 17]%nat [].
Definition ck_var : sv := Eval vm_compute in bl_var L_ck (SLit 12).
Definition cg_var : sv := Eval vm_compute in bl_var L_cg (SLit 12).

Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S15S11S49Vd;S39S36A1A3SeZ0A1SeZcA1S3S14A1S13A5").
Definition src_obj : sobj := ltac2:(tb__ "0|0|
S15S11S49S4dSeZ20A1A3SeZ0A1SeZcA1S3S14A1S13A5").
Definition xf_mc : list axform := ltac2:(tb__ "0|3|
S0S29S2aU1M0Z40A2S0S29S2dS5S2S0S2G0S0S2U0M1S3S2A1A3A3Sb4U2UfA2A3A1S0S29S2cG1A1S0S29S2bU3S39S36A1M2A2S0S29S2bU4S11S49G2SeZcA1A3A2S0S29S2bUbSeZ20A1A2S0S29S2bUcSeZ2cA1A2S3S29A1A3A3A3A3A3A3A3").
Definition E_mc (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|1|
S59S2eVE0;Sb2A2A1S1eS20R1SbeS1fR1A1M0U4Sa0Vd;A1A3A2S1eS20R1SbeG0UcSb0A3A2TE2;TE1;").
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S24SdA2M0S1S24SdP35Vd;A4S0G0S1S24SdP36S38Vk;A1A4S0G0S1S24SdP37S11S49S4dSeZ20A1A3A4S0G0S1S24SdP38SeZcA1A4S0G0S1S24SdSd5S30A4Sb8PaS1fVE;A1S1fS83A1A3A3A3A3A3A3").

Definition X_epk : axst := Eval vm_compute in bl_junk (leaf_at C_ck hvn_EPI 0) [16; 17]%nat.
Definition X_epg : axst := Eval vm_compute in bl_junk (leaf_at C_cg hvn_EPI 0) [16; 17]%nat.

Definition C_F : axst := Eval vm_compute in leaf_at T_fail0 hvn_F 0.
Definition X_epf0 : axst := Eval vm_compute in leaf_at C_F hvn_EPI 0.
Definition X_epf1 : axst := Eval vm_compute in leaf_at C_F hvn_EPI 1.
Goal nleaves C_F = 2%nat
  /\ map (fun A => ss_pc (ax_S A)) [X_epk; X_epg; X_epf0; X_epf1] = [hvn_EPI; hvn_EPI; hvn_EPI; hvn_EPI].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition canon_mc (A : axst) (d : sv) : axst := ltac2:(tb__ "0|a|
S20VA;SbeS1fVA;A1U1M0S15Vd;S39S36A1M1S11S49G1SeZcA1A3S3S14A1M2S13A5A3A2S1eS20R1SbeS1fR1A1U2M3S15S4dSeZ20A1SeZ2cA1G2S13A5A3A2S1eS59S2eR1S0S29S2aUbM4Z68A2S0S29S2aU5M5Nb8A2S0S29S2dS0S2U0S0S2UcS0S2G3S0S2UdM6S0S2UeS0S2U3S0S2U4S0S2UfS0S2G4S0S2U10S0S2U11S0S2U12S0S2G5S0S2U6S0S2U9S0S2U13S0S2UaS0S2U7S0S2G0S0S2U8S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S29S2cG0A1M7S0S29G7S0S29S2cG5A1M8S0S29G8S0S29S2cG6A1M9S0S29G9S3S29A1A3A3A3A3A3A3A3A3A3A2A1TA2;TA1;").

Definition canon_f (A : axst) : axst := ltac2:(tb__ "0|6|
S59S2eVA;S0S29S2aU1M0Z40A2S0S29S2aU9M1Z68A2S0S29S2aU2M2Nb8A2S0S29S2dS0S2G0S0S2U0M3S0S2UaS0S2UbS0S2U5M4S0S2U6S0S2UcS0S2G1S0S2UdS0S2UeS0S2UfS0S2G2S0S2U3S0S2U7S0S2U10S0S2U8S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S29S2cG3A1S0S29S2cG4A1M5S0S29G5S3S29A1A3A3A3A3A3A3A3A2A1").
Definition Y_epk : axst := Eval vm_compute in canon_f X_epk.
Definition Y_epg : axst := Eval vm_compute in canon_f X_epg.
Definition Y_epf0 : axst := Eval vm_compute in canon_f X_epf0.
Definition Y_epf1 : axst := Eval vm_compute in canon_f X_epf1.
Goal shape Y_epg = shape (ax_setS Y_epk (set_objs (ax_S Y_epk) (firstn 13 (ss_objs (ax_S Y_epk)) ++ [O_dat vDg vKg])))
  /\ shape Y_epf1 = shape Y_epf0 /\ shape Y_epf0 = shape Y_epk.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_epi (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S4SdSdA2S1SdSdS4dSeZ0A1A4S52Vd;Vk;A2A3").
Definition epi_state (Y : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
SdcSddVY;S97Vd;Vk;A2Sa3Z0Z8A5P78A2").
Definition C_epk : axst := Eval vm_compute in epi_state Y_epk vND vNK.
Definition C_epg : axst := Eval vm_compute in epi_state Y_epg vDg vKg.
Definition C_epf0 : axst := Eval vm_compute in epi_state Y_epf0 vND vNK.
Definition C_epf1 : axst := Eval vm_compute in epi_state Y_epf1 vND vNK.

Definition X_rlk : axst := Eval vm_compute in leaf_at C_epk hvn_REL 0.
Definition X_rlg : axst := Eval vm_compute in leaf_at C_epg hvn_REL 0.
Definition X_rlf0 : axst := Eval vm_compute in leaf_at C_epf0 hvn_REL 0.
Definition X_rlf1 : axst := Eval vm_compute in leaf_at C_epf1 hvn_REL 0.

Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S5S2S0S2U0S3S2A1M0A3S5S2Sb4U3UbA2S0S2U1S0S2U2S0S2UeS0S2UfG0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S59S2eVX;S0S29S2dSaeA1S3S29A1A3A2A1S1eS20R1SdbS1fR1A1M0Sb5SfUcS1dG0A1A3A2A2TX1;").
Definition C_rlk : axst := Eval vm_compute in rel_state X_rlk.
Definition C_rlg : axst := Eval vm_compute in rel_state X_rlg.
Definition C_rlf0 : axst := Eval vm_compute in rel_state X_rlf0.
Definition C_rlf1 : axst := Eval vm_compute in rel_state X_rlf1.
Goal map nleaves [C_epk; C_epg; C_epf0; C_epf1] = [1; 1; 1; 1]%nat
  /\ map (fun X => release_objs_ok 110 120 gF 0 (skipn 12 (ss_objs (ax_S (optAh (apply_axforms X [AXSelect sel_rel])))))) [X_rlk; X_rlg; X_rlf0; X_rlf1] = [true; true; true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rlk; C_rlg; C_rlf0; C_rlf1] = [12; 12; 12; 12]%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_retk : axst := Eval vm_compute in leaf_at C_rlk hvn_ret 0.
Definition X_retg : axst := Eval vm_compute in leaf_at C_rlg hvn_ret 0.
Definition X_retf0 : axst := Eval vm_compute in leaf_at C_rlf0 hvn_ret 0.
Definition X_retf1 : axst := Eval vm_compute in leaf_at C_rlf1 hvn_ret 0.

Definition pCUR : sv := SVar 172. Definition pD : sv := SVar 173. Definition pK : sv := SVar 174. Definition pERR : sv := SVar 175.
Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition post_fregs_hvn : list sv := ltac2:(tb__ "0|0|
Sb6S2SdS2S8SdL_;Sa1R1A1S17Sd7Sd6U3cR1A2A1A1S17Sd7Sd6Ub4R1A2A1A1X8x2Lr;Sb4U0U20A2A4").

Definition objs_post (cnt err d k cur : sv) : list sobj := ltac2:(tb__ "0|2|
S5SfS0SfS62S3SfA1M0A3S5SfSc1S0SfS61S3S14A1M1A1S0SfS3eS0SfS3fVerr;A1S0SfS40Vd;Vcnt;Vk;A3S0SfS3aS0SfS3bVcur;A1S0SfS3cS0SfSbbG1A1S0SfS3dVd;Vk;A2G0A3A3A3A3A3A3A3A3A3A3A3").
Definition post_facts (d k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S5S10S0S10S12SbaS51A2S0S10S12S51S42A2S3S10A1A3A3S5S10S44Vd;S11S49S36SeZ3A1A3Vk;Vdv;A4S5cA3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
Sc0S18Sc5Sd1Sd0A1S6aS16S6SdA1S68S11S49S36SeZ3A1A3S43S5aS55S51A5SaaS5aS55PadA3Pd4S7A9S52S5aS55A2A2").

Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1cS4aS1aSaQ20Ve;A3SeZ0A1A3").
Definition P_fail : axst := ltac2:(tb__ "0|0|
Sc0S18Sc5Sd1Sd0A1S6aS16S6SdA1S68S36S69S37S35S51A5S5S10S0S10S7fS69A1S0S10S12SbaS51A2S0S10S12S51S42A2S3S10A1A3A3A3S5cA3Pd4S7A9S52S37S35A2A2").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S26S4fS5aS55A2S3S4S4SdS23A2SdA2A1S41S11S49S36SeZ3A1A3S55A2A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S26S4fS37S35A2S3S4S4SdS23A2SdA2A1S3Sd4A1A3").
Goal map (fun L => leaf_matches1A NF L P_ok) [X_retk; X_retg] = [true; true] /\ map (fun L => leaf_matches1A NF L P_fail) [X_retf0; X_retf1] = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S28Vtv;Sa2Vbd;S27A4").
Definition tvG : list (sv * sv) := tv_hvn vDg vKg.
Definition ndp : ndesc := ltac2:(tb__ "0|0|
S58S4fS37S35A2S50S36S35A2A2").
Definition ndk : ndesc := ltac2:(tb__ "0|0|
S58S4fS37S35A2S50S36S35A2A2").
Definition ndg : ndesc := ltac2:(tb__ "0|0|
S58S6cS50S36S5dA2A2").
Definition ndf : ndesc := ltac2:(tb__ "0|0|
S58S4fS37S35A2S3Sd4A1A2").
Definition ndk' : ndesc := ltac2:(tb__ "0|0|
S26S4fS37S35A2S3S4S4SdS23A2SdA2A1S50S36S35A2A3").
Definition ndg' : ndesc := ltac2:(tb__ "0|0|
S26S6cS3S4S4SdS23A2SdA2A1S50S36S5dA2A3").
Definition ndf' : ndesc := ltac2:(tb__ "0|0|
S26S4fS37S35A2S3S4S4SdS23A2SdA2A1S3Sd4A1A3").

Definition cutsH : list edescA := ltac2:(tb__ "0|a|
S0S4S4S1eS25A2M0S4S23SdA2M1A2M2S1G0G1S1S1eS25S63S66A4S1S23SdZ64S2fA4A4S0G2S1G0G1S1S1eS25S76S4cA4S1S23SdZ60S2fA4A4S0G2S1G0G1S1S1eS25S6fS4cA4S1S23SdZ5cS2fA4A4S0G2S1G0G1S1S1eS25S89S4cA4S1S23SdZ58S2fA4M3A4S0G2S1G0G1S1S1eS25S8aS4cA4G3A4S0G2S1G0G1S1S1eS25S8bS4cA4S1S23SdZ54S2fA4M4A4S0G2S1G0G1S1S1eS25S8cS4cA4G4A4S0G2S1G0G1S1S1eS25S8dS4cA4S1S23SdZ50S2fA4M5A4S0G2S1G0G1S1S1eS25S8eS4cA4G5A4S0G2S1G0G1S1S1eS25S6eS4cA4S1S23SdZ4cS2fA4A4S0G2S1G0G1S1S1eS25S92S54A4S1S23SdZ46S2fA4M6A4S0G2S1G0G1S1S1eS25S90S53A4G6A4S0G2S1G0G1S1S1eS25S8fS4eA4G6A4S0G2S1G0G1S1S1eS25S6dS4eA4S1S23SdZ42S2fA4A4S0G2S1G0G1S1S1eS25S71S54A4S1S23SdZ3aM7S9fA4A4S0G2S1G0G1S1S1eS25S70S53A4S1S23SdG7S9eA4A4S0G2S1G0G1S1S1eS25S75S54A4S1S23SdZ32S2fA4M8A4S0G2S1G0G1S1S1eS25S74S53A4G8A4S0G2S1G0G1S1S1eS25S72S4eA4G8A4S0G2S1G0G1S1S1eS25S73S4eA4G8A4S0G2S1G0G1S1S1eS25S7aSa8A4S1S23SdZ28S2fA4M9A4S0G2S1G0G1S1S1eS25S79Sa7A4G9A4S0G2S1G0G1S1S1eS25S77S67A4G9A4S0G2S1G0G1S1S1eS25S78S67A4G9A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsH : list edescA := ltac2:(tb__ "0|6|
S0S4S4S1eS25A2M0S4S23SdA2M1A2M2S1G0G1S1S1eS25S5fS66A4S1S23SdZ62S2fA4A4S0G2S1G0G1S1S1eS25S99S4cA4S1S23SdZ5eS2fA4A4S0G2S1G0G1S1S1eS25S7bS4cA4S1S23SdZ5aS2fA4A4S0G2S1G0G1S1S1eS25S56S4cA4S1S23SdZ56S2fA4A4S0G2S1G0G1S1S1eS25S57S4cA4S1S23SdZ52S2fA4A4S0G2S1G0G1S1S1eS25S7eS4cA4S1S23SdZ4aS2fA4A4S0G2S1G0G1S1S1eS25S98S54A4S1S23SdZ37S2fA4M3A4S0G2S1G0G1S1S1eS25S96S53A4G3A4S0G2S1G0G1S1S1eS25S94S4eA4G3A4S0G2S1G0G1S1S1eS25S95S4eA4G3A4S0G2S1G0G1S1S1eS25S9dS54A4S1S23SdZ2dS2fA4M4A4S0G2S1G0G1S1S1eS25S9cS53A4G4A4S0G2S1G0G1S1S1eS25S9aS4eA4G4A4S0G2S1G0G1S1S1eS25S9bS4eA4G4A4S0G2S1G0G1S1S1eS25S81Sa6A4S1S23SdZ0S2fA4M5A4S0G2S1G0G1S1S1eS25S80Sa5A4G5A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Goal ejcertA segs NF FUEL_hvn cutpcs_hvn 100 cutsH exitsH = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
