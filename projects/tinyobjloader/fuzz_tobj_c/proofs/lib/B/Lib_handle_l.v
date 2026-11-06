(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "None"; "false"; "option"; "list"; "length"; "true"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "SLit"; "sobj"; "SPUle"; "SVar"; "SAlu"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPUlt"; "mkSS"; "SPAlign"; "SPBranch"; "SPNot"; "ss_facts"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "B32"; "spm"; "vDp"; "B_EW"; "two47"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSplit"; "AXSelect"; "AXRebase"; "apply_axforms"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hF"; "lc_k"; "lc_d"; "kb"; "lc_c"; "li_c"; "tE"; "tI"; "tp"; "O_data"; "li_k"; "hFL"; "li_d"; "vec_facts"; "O_cE"; "O_cP"; "hG"; "tB"; "tL"; "HNEXT"; "bd_vec"; "cnt_facts"; "h_fregs"; "h_xregs"; "handle_facts"; "xHASPRIM"; "NPH"; "O_text"; "PROG"; "P_cur"; "P_hdr"; "V120"; "V216"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l"; "xbo"; "pQ"; "li_n"; "pC"; "pD"; "pK"; "pT0"; "HC"; "pP"; "X_hl"; "lc_n"; "lregs1"; "FUEL_hl"; "O_F"; "O_Wl"; "builderL"; "cutpcs_hl"; "pHP"; "room4_fact"; "room_fact"; "F_cells"; "O_flag"; "body_facts"; "gB"; "gC"; "ghostL_facts"; "hdr3"; "lregs0"; "pN"; "pX"; "shC"; "slot_facts"; "xfo"; "BAD"; "BIG"; "C24"; "E_da"; "E_pc"; "E_sm0"; "E_vr"; "JC"; "NA"; "O_frame"; "P_caps"; "P_matl"; "Pre_hl_S"; "Pre_sm"; "T_grown0"; "T_keep0"; "V624"; "V656"; "X_tok"; "bd_hl"; "cmul12"; "frame_factsH"; "hl_facts"; "idx_obj"; "lregs"; "objs_body"; "objs_hl"; "objs_tok"; "optAp"; "pC1"; "prog_fact"; "sel_cm"; "shB"; "shF"; "tv_hl"; "vKg"; "xMATl"; "xSMOl"; "xf_cm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "FE"; "sym_runA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "vc"; "O_al"; "vERR"; "c4"; "piece"; "P_alloc"; "P_st"; "V184"; "c1"; "vAL"; "vNC"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.HLAddr"; "FR"; "DW"; "hl_H"; "hl_J"; "hl_K"; "hl_L1"; "hl_L2"; "hl_N"; "hl_EPI"; "hl_FP"; "hl_OK"; "hl_PRO"; "hl_REL"; "hl_REP"; "hl_REP2"; "hl_RP8"; "hl_UNP"; "hl_cp"; "hl_cp2"; "hl_entry"; "sm1_pc"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "SHB"; "segs"; "leavesA_at"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops"; "bl_vi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.DiagAppendAddr"; "da_entry";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN. End VN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HLAddr.
  Definition hl_entry : Z := 0x9ee04.
  Definition sm1_pc : Z := 0x47c10.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition hl_cp : Z := 0x9f31c.
  Definition hl_cp2 : Z := 0x9f608.
  Definition hl_PRO : Z := 0x9ef40.
  Definition hl_H : Z := 0x9f014.
  Definition hl_L1 : Z := 0x9f040.
  Definition hl_L2 : Z := 0x9f0a8.
  Definition hl_K : Z := 0x9f0d4.
  Definition hl_UNP : Z := 0x9f0f8.
  Definition hl_J : Z := 0x9f25c.
  Definition hl_REP : Z := 0x9f398.
  Definition hl_REP2 : Z := 0x9f3a4.
  Definition hl_FP : Z := 0x9f3f4.
  Definition hl_N : Z := 0x9f418.
  Definition hl_OK : Z := 0x9f538.
  Definition hl_RP8 : Z := 0x9f6d0.
  Definition hl_EPI : Z := 0x9f4e8.
  Definition hl_REL : Z := 0x9f71c.
  Definition hl_ret : Z := 0x9f758.
  Definition hl_ra_pc : Z := 0x9f1f8.
  Definition hl_ra_da : Z := 0x9f25c.
  Definition hl_ra_da2 : Z := 0x9f48c.
  Definition hl_ra_vr : Z := 0x9f29c.
  Definition hl_ra_vr2 : Z := 0x9f59c.
  Definition hl_ra_mc : Z := 0x9f378.
  Definition hl_ra_mc2 : Z := 0x9f69c.
  Definition DW : Z := 4672.
  Definition FR : Z := 320.
End HLAddr.
Import HLAddr.

Definition FUEL_hl : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S13PaA1S10Sd3SafA1A1S10Z0A1Vcells;S15A5").
Definition O_Wl : sobj := ltac2:(tb__ "0|0|
S16S21SafA1S22S10Z0A1S2SfA1S15A5").
Definition BIG : Z := 288230376151711743.
Definition P_caps : sobj := ltac2:(tb__ "0|4|
Sa6Z20M0Z60S0SfS1fG0S10S74A1M1A2S0SfS1fZ28G1A2S0SfS1fZ30G1A2S0SfS1fZ38S10Sd1Z2M2Z14A2A1A2S0SfS1fZ40S10Sd1G2Z18A2A1M3A2S0SfS1fZ48G3A2S0SfS1fZ50G3A2S0SfS1fZ58G1A2S2SfA1A3A3A3A3A3A3A3A3A3").
Definition V624 (d c k : sv) : sobj := V 624 d c k 12.
Definition V656 (d c k : sv) : sobj := V 656 d c k 4.

Definition room_e (e : Z) (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S12S14S2eS34Ve;Vcnt;A2S34Ve;S37A2A3S14S2eS10Sd4S23Ve;A2A1S34Ve;Vcur;A2A3A2").
Definition room_fact (cnt cur : sv) : sprop := room_e 12 cnt cur.

Definition prog_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S12S14S2eVcnt;S38A3S14S2eS36Vcur;A3A2").

Definition li_n : sv := SVar 129.
Definition NA (cur : sv) : sv := ltac2:(tb__ "0|0|
S14S2eS54S14S2fVcur;S38A3A3").
Definition PHIN (cur k : sv) : bitem := PHIe 12 (NA cur) k.

Definition room4_fact (cnt : sv) : sprop := room_e 4 cnt tI.

Definition lc_n : sv := SVar 130.
Definition ghostL_facts : list sprop := ltac2:(tb__ "0|0|
S0SeS12S35S5cA2S0SeS12S5cS10S20A1A2S0SeS64S5cA1S2SeA1A3A3A3").
Definition hl_facts : list sprop := ltac2:(tb__ "0|0|
S4SeS49SafSb0A2S4SeS46S4SeS0SeS12S4aS10Z1A1A2S0SeS12S36S54A2S0SeS12S54S10S20A1A2S0SeS65S54S38A2S0SeS64S35A1S2SeA1A3A3A3A3A3S4SeS6bS4SeS3eS3dS36S3bZcP7bA5S3eS33S35S32Z4P7eA5A3A3A3A3A3").
Definition X_hl (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdSa1S10Z518A1A4S0G0S3SdSdSa2S10Z10A1A4S0G0S3SdSdSabS10Z30A1A4S0G0S3SdSdS42S43A4S0G0S3SdSdVd;S34ZcVk;A2A4S0G0S3SdSdVd2;S34Z4Vk2;A2A4S0G0S3SdSdS21Sb0A1S10Sb0A1A4S2G0A1A3A3A3A3A3A3A3").

Definition xMATl : sv := SVar 139. Definition xSMOl : sv := SVar 140.
Definition P_matl : sobj := ltac2:(tb__ "0|1|
Sa6Z4e8M0Z518S0SfSa5G0S97A2S0SfSa5Z4ecS98A2S0SfSaaZ4f0S10Z0A1A2S2SfA1A3A3A3A3").
Definition builderL (err hp : sv) (d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|0|
S0S11Sa7S0S11S4fS0S11S7dS0S11Sa8Verr;A1S0S11S50S0S11Sa9SadSacSaeA3S0S11S51S0S11S83Vd;Vc;Vk;A3S0S11S84Vd2;Vc2;Vk2;A3S0S11S4eVhp;A1S0S11S7eS2S11A1A3A3A3A3A3A3A3A3A3A3A3").
Definition objs_hl (cur err hp d c k d2 c2 k2 : sv) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S5fS2SfA1A1S0S11S60S2S11A1M0A3A3S4S11S61Verr;Vhp;Vd;Vc;Vk;Vd2;Vc2;Vk2;A8S4S11S0S11Sa3S0S11S40Vcur;A1S0S11S3fS0S11S4cS0S11S3aVd;ZcVk;A3S0S11S3aVd2;Z4Vk2;A3G0A3A3A3A3A3A3Sc8A3A3A3").
Definition Pre_hl_S : sstate := ltac2:(tb__ "0|0|
S19Sc2SecSebS17S6SdA1S8dS38Sa4S4aS3dS36S3bS33S35S32A9S89S4bS7A9").
Definition Pre_hl : axst := ltac2:(tb__ "0|0|
Sc7S7fS5bS3dS3bS33S32A4A2").

Definition C24 : bitem := BIc 1 0 24.

Definition bd_hl (n k c2 k2 cur : sv) : list bitem := ltac2:(tb__ "0|1|
S4Sa0S0Sa0S4dZ48Vcur;A2S2Sa0A1M0A3S4Sa0S45ZcVn;Vk;A3S4Sa0S45Z4Vc2;Vk2;A3S0Sa0S75G0A3A3A3A3").
Definition tv_hl (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdVd;S34ZcVk;A2A4S0G0S3SdSdVd2;S34Z4Vk2;A2A4S2G0A1A3A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
Sd0S95S3dS3bS33S32A4S2S5S5SdS25A2SdA2A1S86S54S3bS5cS32S38A5A3").

Definition tvI (d k d2 k2 : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S3SdSdVd2;S34Z4Vk2;A2A4S0G0S3SdSdVd;S34ZcVk;A2A4S2G0A1A3A3").

Definition cutpcs_hl : list Z := ltac2:(tb__ "0|0|
S0S25Sc3S0S25SbaS0S25Sb1S0S25Sb4S0S25Sb5S0S25Sb3S0S25SbfS0S25Se5S0S25Sd9S0S25Sb2S0S25Se7S0S25Sc0S0S25Sc1S0S25SbcS0S25SbdS0S25Sb8S0S25Sb6S0S25Sb9S0S25SbeS0S25Sb7S0S25SbbS2S25A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
Sc7S19Z0S2SdA1M0G0S17S6SdA1S2S11A1S2SeA1P1S7A9S2S5SdSdA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sc6S9bVk;ScbS5eS62VS;Vpc;A4S73A4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SaS9cS8S9S9cA1M0A1G0Lx;S9eScaS5eS62VS;SbA5G0R1Ll;S2S9cA1X8x2A2").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S8S9S9cA1M0A1S9S5S25Se8A2M1A1Lx;S9eScaS5eS62VS;SbA5G0Sc5S9cG1ScdR1A4Ll;S2G1A1X8x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hl sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S26SdA2S3S26SdSefS22A4ScePaS9aS78A1S9aS80A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hl = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hl : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SdS25A2M0SdA2M1S3G0SdS3SdS25S31Z1A4S3cA4S2G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S1Sc4U0Vi;A2S4S1Sc4ScVi;A1M0Sd7SaS11S1eS9aVA;A1A1A2G0A2A2S0S1Vi;S2S1A1A3A3A3").
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
Definition pN : sv := SVar 426.
Definition gB : positive := 191%positive.
Definition gC : positive := 192%positive.
Definition shF : sv := ltac2:(tb__ "0|0|
S14S2eS13S41A1S10Sc9A1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S14S2eS13S6aA1S10Sd2Sc9Vk;A2A1A3").
Definition shB (k : Z) : sv := ltac2:(tb__ "0|0|
S14S2eS13S69A1S10Sd2Sc9Vk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S14S2eSa1S10Vo;A1A3").
Definition xfo (o : Z) : sv := ltac2:(tb__ "0|0|
S14S2eS31S10Vo;A1A3").

Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0SfS1fN140S10Z0A1A2S0SfS1fN128S14S2eSa2S10Z8A1A3A2S0SfS1fN120S36A2S0SfS1fN118S72Z40A1A2S0SfS1fN110S31A2S0SfS1fN108S52Z68A1A2S0SfS1fN100S31A2S0SfS1fNf8S52Z10A1A2S0SfS1fNf0S10ZffffffffaaaaaaabA1A2S0SfS1fNe8S52Z508A1A2S0SfS1fNe0S52Z500A1A2S0SfS1fNd8S52Z4f8A1A2S0SfS1fNd0S52Zc0A1A2S0SfS1fNc8S52Ze0A1A2S0SfS1fNc0S52Z80A1A2S0SfS1fNb8S52Z4f0A1A2S0SfS1fNb0S52Z38A1A2S0SfS1fNa8S70Z1A1A2S0SfS1fNa0Sa1A2S0SfS1fN98S52Z270A1A2S0SfS1fN90S93Z4fA1A2S0SfS1fN88S52Z278A1A2S0SfS1fN70S31A2S0SfS1fN68S13P2fA1A2S0SfS1fN60S13P2eA1A2S0SfS1fN58S13P2dA1A2S0SfS1fN50S13P2cA1A2S0SfS1fN48S13P2bA1A2S0SfS1fN40S13P2aA1A2S0SfS1fN38S13P29A1A2S0SfS1fN30S13P28A1A2S0SfS1fN28S13P27A1A2S0SfS1fN20S13P26A1A2S0SfS1fN18S13P1dA1A2S0SfS1fN10S13P1cA1A2S0SfS1fN8S13PbA1A2S2SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0SfS1fZ0S10Z41b58ab3A1A2S0SfS1fZ8S10Z160edA1A2S0SfS1fZ10S10Z9ee04A1A2S2SfA1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S31S10Z0A1S10Z78A1Vcells;S15A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S16S31S10Z78M0A1S10Z80A1S0SfS1fG0S3cA2S2SfA1A3S15A5").

Definition objs_body (cur hp d c k : sv) (fcells txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S60S0S11S7cS4SfS6cVfcells;A3A1S0S11S67S2S11A1M0A3A3A3S4S11Sc8S4S11S0S11S5fS66A1G0A3S4S11S61Sa4Vhp;Vd;Vc;Vk;S33S35S32A8S0S11Sa3S0S11S40Vcur;A1S0S11S3fS0S11S16S42S10Z0A1S43Vtxt;S15A5S0S11S3aVd;ZcVk;A3S0S11S3aS33Z4S32A3G0A3A3A3A3A3A3A3A3A3A3").
Definition lregs0 : list (nat * sv) := ltac2:(tb__ "0|3|
S0S5S1SdA2M0S3S1SdU2S21SafA1M1A4S0G0S3S1SdU8S13PaA1A4S0G0S3S1SdU9G1A4S0G0S3S1SdU12S10Z2A1A4S0G0S3S1SdU13S10Z9A1A4S0G0S3S1SdU14Sa2A4S0G0S3S1SdU15S52Z288A1A4S0G0S3S1SdU16SccA4S0G0S3S1SdU17S94A4S0G0S3S1SdU18S70Z0A1A4S0G0S3S1SdU19S72Z20M2A1A4S0G0S3S1SdU1bS10G2A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition lregs1 : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1SdA2M0S6dS0G0S3S1SdU5Sa1A4S0G0S3S1SdU7S52Z38A1A4S0G0S3S1SdU1cS52Z4f0A1A4S2G0A1A3A3A3A3").
Definition lregs : list (nat * sv) := lregs1.
Definition frame_factsH : list sprop := ltac2:(tb__ "0|1|
S4SeS9dS6aSa2A2S4SeS9dS69Sa1A2S4SeS9dS41S31A2S0SeS1aPa0Z5A2S0SeS1cS1bS30S31S10Z0A1A3A1S0SeS12S10Sd6A1M0S31A2S0SeS12S14S2eS31S10Z80A1A3S13P1eA1A2S0SeS12S31S10S24A1A2S0SeS12G0S3cA2S0SeS12S14S2eS3cS10Z1A1A3S10Z7fffff800000A1A2S2SeA1A3A3A3A3A3A3A3A3A3A3").

Definition body_facts (cur rc rcur d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4SeS49SafSb0A2S4SeS46S4SeS0SeS12S63S10Z1A1A2S0SeS65S54S38A2S0SeS65Vrc;Vrcur;A2S0SeS91Vrc;Vrcur;A2S0SeS12S36Vc;A2S0SeS12S36S54A2S0SeS12S54S10S20A1M0A2S0SeS12S36G0A2S0SeS12S38Vrcur;A2S0SeS12Vrcur;Vcur;A2S0SeS12Vcur;S37A2S0SeS64S35A1S0SeS12S6eS10Sd1Z2Z14A2A1A2S2SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3S4SeS6bS4SeS3eVd;Vc;Vk;ZcVdv;A5S4SeS3eS33S35S32Z4P7eA5S88A3A3A3A3A3A3").
Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur d c k : sv) (dv : positive) (fcells txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sc7S19Vpc;S48Vregs;A1S47S17S6SdA1S8cVcur;S63Vd;Vc;Vk;Vfcells;Vtxt;A7S4SeVfacts;S68Vcur;Vc;Vrcur;Vd;Vc;Vk;Vdv;A7A3S44S7A9S5bVd;Vk;S33S32A4A2").

Definition H : axst := ltac2:(tb__ "0|1|
S59Sb1S8bS5aS5aS56S55S57P12fS2SfA1M0G0S2SeA1Ab").

Definition L1 : axst := ltac2:(tb__ "0|3|
S59Sb4S4S5S1SdA2M0S5dS0G0S3S1SdUaS39S53A1M1A4S0G0S3S1SdUbG1A4S0G0S3S1SdUcS39S37A1A4S2G0A1A3A3A3A3S5aS5aS56S55S57P12fS2SfA1M2G2S0SeS12S5aS53A2S0SeS18S53S37A2S2SeA1A3A3Ab").

Definition L2 : axst := ltac2:(tb__ "0|3|
S59Sb5S4S5S1SdA2M0S5dS0G0S3S1SdUaS39S58A1A4S0G0S3S1SdUbS39S53A1M1A4S0G0S3S1SdUdG1A4S0G0S3S1SdUcS39S37A1A4S2G0A1A3A3A3A3A3S53S58S56S55S57P12fS2SfA1M2G2S0SeS12S58S53A2S0SeS18S53S37A2S2SeA1A3A3Ab").

Definition K : axst := ltac2:(tb__ "0|2|
S59Sb3S4S5S1SdA2M0S5dS0G0S3S1SdUaS39S58A1A4S0G0S3S1SdUcS39S37A1A4S2G0A1A3A3A3S53S58S56S55S57P12fS2SfA1M1G1S0SeS18S58S53A2S2SeA1A3Ab").

Definition pX : sv := SVar 307.
Definition XN : axst := ltac2:(tb__ "0|1|
S59Sb6S5dS6fS6fS56S55S57P12fS2SfA1M0G0S2SeA1Ab").
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
S16S31S10Z20A1S10Z2cA1Vcells;S15A5").

Definition xf_pc : list axform := ltac2:(tb__ "0|2|
S0S27S2aU0S10N70A1A2S0S27S2aU2S10Z20M0A1A2S0S27S2aU3M1S10Z2cA1A2S0S27S28G1G0A2S2S27A1A3A3A3A3").
Definition E_pc : axst := Eval vm_compute in optAp (apply_axforms E_pc1 xf_pc).
Definition s_pc : wsub := ltac2:(tb__ "0|0|
ScePaS9aS77A1S9aSe6A1A3").
Definition R_pc : list sobj := Eval vm_compute in optR (entails_frA E_pc Pre_pc s_pc).
Goal entails_frA E_pc Pre_pc s_pc = Some R_pc /\ call_checkA E_pc Pre_pc s_pc R_pc (map la_state Posts_pc) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
Sd5S1dS9aVCl;A1A1Se9Vs;VPre;VL;VCl;VR;A5A2").
Definition T_pc0 : axst := Eval vm_compute in T_pure Pre_pc E_pc s_pc R_pc P_ret.

Definition xf_tpc : list axform := ltac2:(tb__ "0|2|
S0S27S2bS4S1S0S1U5S0S1U0M0S0S1U1S0S1U2M1S0S1U3S0S1U4S2S1A1A3A3A3A3A3A3Sc4U6U14A2A3A1S0S27S29G0A1S0S27S2cG1A1S2S27A1A3A3A3").
Definition T_pc : axst := Eval vm_compute in optAp (apply_axforms T_pc0 xf_tpc).

Definition E_da0 : axst := Eval vm_compute in leaf_at T_pc da_entry 0.
Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
ScePaS9aS76A1S9aSdaA1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0S27S2bS4S1S0S1U3S0S1U0M0S0S1U4S0S1U5S0S1U1S0S1U2S2S1A1A3A3A3A3A3A3Sc4U6U14A2A3A1S0S27S29G0A1S2S27A1A3A3").
Definition T_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).

Definition objs_tok (cur hp d c k : sv) (idxc : list cell) : list sobj := ltac2:(tb__ "0|3|
S4S11S0S11S60S0S11S16S42S10Z0A1M0S43S2SfA1M1S15A5S0S11S8aVidxc;A1S2S11A1M2A3A3A3S4S11Sc8S4S11S0S11S16S31G0S10Z20A1S6cS15A5S0S11S16S31S10Z2cA1S10Z78A1G1S15A5S0S11S67S0S11S5fS66A1G2A3A3A3A3S4S11S61Sa4Vhp;Vd;Vc;Vk;S33S35S32A8S0S11Sa3S0S11S40Vcur;A1S0S11S3fS0S11S3aVd;ZcVk;A3S0S11S3aS33Z4S32A3G2A3A3A3A3A3A3A3A3A3").
Definition X_tok (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SdSdA2SeePa0S3S25S25Z20ZcA4A2S5bVd;Vk;S33S32A4A3").

Definition pC1 : sv := SAlu ALU_ADD pC (SLit 1).
Definition JC (pc : Z) (regs : list (nat * sv)) (cur d c k : sv) (dv : positive) (idxc : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sc7S19Vpc;S48Vregs;A1S47S17S6SdA1S8eVcur;S63Vd;Vc;Vk;Vidxc;A6S4SeVfacts;S68Vcur;S90Vcur;Vd;Vc;Vk;Vdv;A7A3S44S7A9S85Vd;Vk;A2A2").
Definition J : axst := ltac2:(tb__ "0|0|
S7aSb2S6dS53S56S55S57P12fS2SfA1S0SeS18S6eS10Sd1Z2Z14A2A1A2S2SeA1A3A9").
Goal lvs T_pc = [(hl_J, RsCut); (hl_J, RsCut); (da_entry, RsCut)] /\ lvs T_da = [(hl_J, RsCut)]
  /\ map (fun L => leaf_matchesA NPH L [J]) (leavesA_at FUEL_hl cutpcs_hl T_pc hl_J ++ leavesA_at FUEL_hl cutpcs_hl T_da hl_J) = [true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at J vr_entry 0.
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S27S2aU0M0S10N40M1A1A2S0S27S28G0G1A2S0S27S28U11Z270A2S2S27A1A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).
Definition s_v : wsub := ltac2:(tb__ "0|1|
S0S5S26SdA2M0S3S26SdP3bS7bS53A1A4S0G0S3S26SdP13S14S2eS22S10Z40A1A3A4ScePaS9aS79A1S9aSdeA1A3A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr VN.Pre_vr s_v).
Definition PD_vn : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5S9bScfA2M0S3S9bScfSddSe0A4S0G0S3S9bScfSdbSd0Se1S2S5S5SdS25A2SdA2A1M1S2Sa0A1A3A4S0G0S3S9bScfSdcSd0Se2G1SdfSe4Se3A2A3A4S2G0A1A3A3A3").
Goal lvs J = [(vr_entry, RsCut)] /\ entails_frA E_vr VN.Pre_vr s_v = Some R_v /\ call_checkPA E_vr VN.Pre_vr s_v R_v (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) pD)) (X_tok pD pK).
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_grown Xk_v.

Definition cmul12 (c : sv) : sv := SMd M_MUL c (SLit 12).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0SeS12S14S2eS87S55A1M0S10ZcM1A1A3S34G1Vk;A2M2A2S0SeS12G0G2A2S0SeS12G0S10S20A1A2S2SeA1A3A3A3").
Definition vDg : sv := SVar 520.
Definition vKg : sv := SVar 521.
Definition T_keep : axst := ltac2:(tb__ "0|0|
Sd5S4SeS71S57A1S0SeS12S10Sd6A1S56A2S2SeA1A3A3S82A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
Sd5S71S96A1S81A2").

Definition L_ck : axst := Eval vm_compute in leaf_at T_keep hl_cp 0.
Definition L_cg : axst := Eval vm_compute in leaf_at T_grown hl_cp 0.
Definition C_ck : axst := Eval vm_compute in bl_cut L_ck 14 (SLit 12) [10; 11; 16; 17]%nat [].
Definition C_cg : axst := Eval vm_compute in bl_cut L_cg 14 (SLit 12) [10; 11; 16; 17]%nat [].
Definition cp_var (L : axst) : sv := ltac2:(tb__ "0|0|
S14S2eS34Z40S14S2fS37S53A3A2S14S2fS10Z2bA1S13Sd8VL;A1A1A3A3").
Definition ck_var : sv := Eval vm_compute in cp_var L_ck.
Definition cg_var : sv := Eval vm_compute in cp_var L_cg.
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
S9fVA;SeaS9aVA;A1Vi;Vo;A3A2").

Definition X_rpk : axst := Eval vm_compute in bl_junk (leaf_at C_ck hl_REP 0) [16; 17]%nat.
Definition X_rpg : axst := Eval vm_compute in bl_junk (leaf_at C_cg hl_REP 0) [16; 17]%nat.
Goal lvs T_keep = [(hl_cp, RsCut)] /\ lvs T_grown = [(hl_cp, RsCut)] /\ lvs C_ck = [(hl_cp, RsCut); (hl_REP, RsCut); (hl_cp, RsCut); (hl_REP, RsCut)] /\ lvs C_cg = lvs C_ck.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition sel_cm : list nat := ltac2:(tb__ "0|0|
S0S1U1S0S1U0S0S1U9S0S1U8S0S1UaS0S1UbS0S1U5S0S1U6S0S1UcS0S1UdS0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U2S0S1U14S0S1U15S0S1U16S0S1U3S0S1U17S0S1U18S0S1U7S0S1U4S0S1U19S2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_cm : list axform := ltac2:(tb__ "0|2|
S0S27S28U1M0Z40A2S0S27S28U2N270A2S0S27S2bS92A1S0S27S29U0A1S0S27S29G0A1M1S0S27G1S2S27A1A3A3A3A3A3A3").
Definition canon_mc (A : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
SedS8fS2dVA;S99A2A1S5bVd;Vk;S33S32A4S41Z4Z6A5").
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
