(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "None"; "false"; "option"; "list"; "true"; "length"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "cell"; "SPUle"; "SAlu"; "SVar"; "DUnknown"; "mkObj"; "FcsrFrm0"; "mkSS"; "SPUlt"; "SPBranch"; "ss_objs"; "SExt"; "SPAlign"; "SPNot"; "ss_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "FE"; "ax_setS"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "B32"; "vDp"; "spm"; "B_EW"; "KLG"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p"; "pQ"; "VR"; "z0"; "ndJ"; "pK"; "xbo"; "pC"; "qCUR"; "ndX"; "qK"; "X_hp"; "pD"; "qC"; "qD"; "bd_hpN"; "ndF"; "ndG"; "pP"; "pT0"; "tvL"; "pi_n"; "HC"; "O_F"; "O_Wp"; "builderP"; "cmul12"; "optAp"; "pX"; "qHP"; "room_fact"; "tv_hp"; "FUEL_hp"; "cutpcs_hp"; "ghost_facts"; "ndN"; "ndP"; "pHP"; "E_sm0"; "F_cells"; "NA"; "O_flag"; "P_fail"; "P_ok"; "bd_hp"; "body_facts"; "gB"; "gC"; "hdr3"; "lregs"; "nd0"; "ndH"; "ndT"; "ndX'"; "nd_fail"; "nd_ok"; "objs_post"; "post_base_facts"; "prog_fact"; "prog_factP"; "qERR"; "reshapeA"; "shC"; "shF"; "slot_facts"; "vKg"; "BAD"; "C_epf0"; "C_epf1"; "C_epn"; "C_fp0"; "C_fp1"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlf0"; "C_rlf1"; "C_rlg"; "C_rlk"; "C_rln"; "C_unp"; "E_da"; "E_da0"; "E_mg0"; "E_mk0"; "E_pc"; "E_pc0"; "E_unp0"; "E_vr"; "E_vr0"; "H"; "J"; "JC"; "K"; "L1"; "L2"; "NZ32"; "O_frame"; "PHIN"; "P_matp"; "Pre_hp"; "Pre_hp_S"; "Pre_mc"; "Pre_sm"; "T_da"; "T_fail0"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "T_mcg"; "T_mck"; "T_pc"; "V688"; "XN"; "X_fp0"; "X_fp1"; "X_pro"; "X_r2g"; "X_r2k"; "X_rlf0"; "X_rlf1"; "X_rln"; "X_rpg"; "X_rpk"; "X_tok"; "dst_obj"; "fr_hp"; "frame_factsH"; "hp_facts"; "idx_obj"; "mid_dst"; "ndN'"; "objs_body"; "objs_hp"; "objs_tok"; "pC1"; "sel_body"; "sel_f"; "sel_rel"; "tvG"; "xMATp"; "xSMOp"; "xf_mc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hF"; "kb"; "tI"; "tE"; "pi_c"; "pi_k"; "tp"; "PROG"; "pi_d"; "HNEXT"; "O_cE"; "O_cP"; "O_data"; "hFL"; "hG"; "h_fregs"; "vec_facts"; "cnt_facts"; "handle_facts"; "tB"; "tL"; "O_text"; "h_xregs"; "xHASPRIM"; "NPH"; "P_cur"; "P_hdr"; "V120"; "V216"; "bd_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "SHB"; "segs"; "leavesA_at"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.HPAddr"; "FR"; "DW"; "hp_EPI"; "hp_H"; "hp_J"; "hp_K"; "hp_L1"; "hp_L2"; "hp_ret"; "hp_FP"; "hp_PRO"; "hp_REL"; "hp_REP"; "hp_REP2"; "hp_UNP"; "hp_entry";
"memcpy_pc"; "sm0_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "O_al"; "vERR"; "vb"; "vc"; "c4"; "P_alloc"; "P_st"; "V184"; "c1"; "piece"; "vAL"; "vNC"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "flag_carve_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "sub"].
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

Module HPAddr.
  Definition hp_entry : Z := 0xa1190.
  Definition sm0_pc : Z := 0x47908.
  Definition memcpy_pc : Z := 0x5c84c.
  Definition hp_PRO : Z := 0xa1314.
  Definition hp_H : Z := 0xa1344.
  Definition hp_L1 : Z := 0xa136c.
  Definition hp_L2 : Z := 0xa13d0.
  Definition hp_K : Z := 0xa13f8.
  Definition hp_UNP : Z := 0xa1404.
  Definition hp_J : Z := 0xa1570.
  Definition hp_REP : Z := 0xa1654.
  Definition hp_REP2 : Z := 0xa1660.
  Definition hp_F : Z := 0xa1690.
  Definition hp_FP : Z := 0xa16c4.
  Definition hp_EPI : Z := 0xa16d0.
  Definition hp_REL : Z := 0xa1738.
  Definition hp_ret : Z := 0xa1774.
  Definition hp_ra_pc : Z := 0xa1508.
  Definition hp_ra_da : Z := 0xa1570.
  Definition hp_ra_vr : Z := 0xa15bc.
  Definition hp_ra_mc : Z := 0xa161c.
  Definition DW : Z := 4640.
  Definition FR : Z := 288.
End HPAddr.
Import HPAddr.

Definition FUEL_hp : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S14PaA1S10S138Sf8A1A1S10Z0A1Vcells;S15A5").
Definition O_Wp : sobj := ltac2:(tb__ "0|0|
S16S36Sf8A1S35S10Z0A1S3S11A1S15A5").
Definition V688 (d c k : sv) : sobj := V 688 d c k 12.

Definition room_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S12S13ScaScfZcM0Vcnt;A2ScfG0Sd1A2A3S13ScaS10S139S37G0A2A1ScfG0Vcur;A2A3A2").

Definition prog_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S12S13ScaScfZcM0Vcnt;A2ScfG0Sd0A2A3S13ScaScfG0Sd2A2ScfG0Vcur;A2A3A2").

Definition pi_n : sv := SVar 149.
Definition NA (cur : sv) : sv := ltac2:(tb__ "0|0|
S13ScaS4eS13ScbVcur;Sd0A3A3").
Definition PHIN (cur k : sv) : bitem := PHIe 12 (NA cur) k.
Definition prog_factP (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S12S13ScaVcnt;Sd0A3S13ScaSd2Vcur;A3A2").
Definition ghost_facts : list sprop := ltac2:(tb__ "0|0|
S0SeS12Sd2S4eA2S0SeS12S4eS10S34A1A2S0SeS57S4eSd0A2S3SeA1A3A3A3").
Definition hp_facts : list sprop := ltac2:(tb__ "0|0|
S4SeSe0Sf8Sf9A2S4SeSdfS4SeS0SeS12Se5S10Z1A1A2S0SeS57Sd2Sd0A2S3SeA1A3A3S4SeS5bSdeSd6Sd2Sd3ZcP92A5A3A3A3A3").
Definition X_hp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS10dS10Z518A1A4S0G0S1SdSdS10eS10Z10A1A4S0G0S1SdSdS115S10Z30A1A4S0G0S1SdSdSe1Se2A4S0G0S1SdSdVd;ScfZcVk;A2A4S0G0S1SdSdS36Sf9A1S10Sf9A1A4S3G0A1A3A3A3A3A3A3").

Definition xMATp : sv := SVar 139. Definition xSMOp : sv := SVar 140.
Definition P_matp : sobj := ltac2:(tb__ "0|1|
S114Z4e8M0Z518S0S11S10fG0Sc7A2S0S11S10fZ4ecSc8A2S0S11S113Z4f0S10Z0A1A2S3S11A1A3A3A3A3").
Definition builderP (err hp : sv) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0SfS110S0SfSe8S0SfS111Verr;A1S0SfSe9S0SfS112S117S116S118A3S0SfSeaS0SfSe7Vhp;A1S0SfSabVd;Vc;Vk;A3S0SfS9dS3SfA1A3A3A3A3A3A3A3A3A3").
Definition objs_hp (cur err hp d c k : sv) : list sobj := ltac2:(tb__ "0|1|
S4SfS0SfS50S3S11A1A1S0SfS51S3SfA1M0A3A3S4SfS52Verr;Vhp;Vd;Vc;Vk;A5S4SfS0SfS10bS0SfSd9Vcur;A1S0SfSd8S0SfSe3S0SfSdaVd;ZcVk;A3G0A3A3A3A3A3Sf2A3A3A3").
Definition Pre_hp_S : sstate := ltac2:(tb__ "0|0|
S18S107S11cS11bS17S6SdA1Sc0Sd0S10cSe5Sd6Sd2Sd3A6SbbSe6S7A9").
Definition Pre_hp : axst := ltac2:(tb__ "0|0|
Sf1S9fS44Sd6Sd3A2A2").

Definition bd_hp (c k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S4SecSebZcVc;Vk;A3S0SecSd5Z48Vcur;A2S3SecA1A3A3").

Definition bd_hpN (k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S0SecS9cVcur;Vk;A2S0SecS38Vk;A1S0SecSd5Z48Vcur;A2S3SecA1A3A3A3").
Definition tv_hp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdVd;ScfZcVk;A2A4S3G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S29S58Sd6Sd3A2S3S5S5SdS20A2SdA2A1S65S4eSd3Sd0A3A3").

Definition cutpcs_hp : list Z := ltac2:(tb__ "0|0|
S0S20S109S0S20S102S0S20SfbS0S20SfeS0S20SffS0S20SfdS0S20S106S0S20S12fS0S20S123S0S20SfcS0S20S131S0S20S108S0S20S104S0S20S105S0S20S101S0S20SfaS0S20S103S3S20A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
Sf1S18Z0S3SdA1M0G0S17S6SdA1S3SfA1S3SeA1P1S7A9S3S5SdSdA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sf0S22Vk;Sf5S59S5aVS;Vpc;A4S7bA4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SbS24S8S9S24A1M0A1G0Lx;S27Sf4S59S5aVS;SaA5G0R1Ll;S3S24A1X8x2A2").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S8S9S24A1M0A1S9S5S20S133A2M1A1Lx;S27Sf4S59S5aVS;SaA5G0SefS24G1Sf7R1A4Ll;S3G1A1X8x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hp sm0_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 0.
Definition L_sm : axst := L_stack_malloc AE_A 0.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S21SdA2S1S21SdS121S35A4S10aPaS23S5fA1S23Sa1A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hp = [(sm0_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hp : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SdS20A2M0SdA2M1S1G0SdS1SdS20SceZ0A4SdbA4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S2SedU0Vi;A2S4S2SedScVi;A1M0S122SbSfS1bS23VA;A1A1A2G0A2A2S0S2Vi;S3S2A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_hp pi_d pi_k ++ (hF, SLit 64) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 (X_hp pi_d pi_k) 160 64.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_pro : axst := Eval vm_compute in leaf_at C_pro hp_PRO 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_pro)) O_Wp.
Definition objs_pro : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_pro)).
Goal lvs C_pro = [(hp_PRO, RsCut)] /\ sh_pro = shobj hG 0 8 (ob_cells sh_pro) DZero.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_pre : axst := Eval vm_compute in shadow_release_stateA X_pro objs_pro 160 [].
Definition X_H0 : axst := Eval vm_compute in leaf_at C_pre hp_H 0.
Goal lvs C_pre = [(hp_H, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition pP : sv := SVar 300. Definition pT0 : sv := SVar 301. Definition pQ : sv := SVar 302.
Definition pD : sv := SVar 303. Definition pC : sv := SVar 304. Definition pK : sv := SVar 305. Definition pHP : sv := SVar 306.
Definition gC : positive := 191%positive.
Definition shF : sv := ltac2:(tb__ "0|0|
S13ScaS14SdcA1S10Sf3A1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S13ScaS14S68A1S10S137Sf3Vk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S13ScaS10dS10Vo;A1A3").

Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S11S33N120S10Z0A1A2S0S11S33N110S13ScaS10eS10Z8A1A3A2S0S11S33N108SceA2S0S11S33N100SceA2S0S11S33Nf8S3fZ68A1A2S0S11S33Nf0S3fZ10A1A2S0S11S33Ne8S10ZffffffffaaaaaaabA1A2S0S11S33Ne0S3fZ1e8A1A2S0S11S33Nd8S3fZ2c8A1A2S0S11S33Nd0S78A2S0S11S33Nc8S3fZ500A1A2S0S11S33Nc0S3fZ4f8A1A2S0S11S33Nb8S3fZe0A1A2S0S11S33Nb0S3fZ80A1A2S0S11S33Na8S77Z1A1A2S0S11S33Na0S13ScaSceS10Z20A1A3A2S0S11S33N98S3fZ2b0A1A2S0S11S33N90S10dA2S0S11S33N88S3fZ2b8A1A2S0S11S33N70SceA2S0S11S33N68S14P2fA1A2S0S11S33N60S14P2eA1A2S0S11S33N58S14P2dA1A2S0S11S33N50S14P2cA1A2S0S11S33N48S14P2bA1A2S0S11S33N40S14P2aA1A2S0S11S33N38S14P29A1A2S0S11S33N30S14P28A1A2S0S11S33N28S14P27A1A2S0S11S33N20S14P26A1A2S0S11S33N18S14P1dA1A2S0S11S33N10S14P1cA1A2S0S11S33N8S14PbA1A2S3S11A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0S11S33Z0S10Z41b58ab3A1A2S0S11S33Z8S10Z1b054A1A2S0S11S33Z10S10Za1190A1A2S3S11A1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16SceS10Z0A1S10Z38A1Vcells;S15A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S16SceS10Z38M0A1S10Z40A1S0S11S33G0SdbA2S3S11A1A3S15A5").

Definition objs_body (cur hp d c k : sv) (txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4SfS0SfS51S0SfS9bS69A1S0SfS62S3SfA1M0A3A3A3S4SfSf2S4SfS0SfS50S60A1G0A3S4SfS52S10cVhp;Vd;Vc;Vk;A5S0SfS10bS0SfSd9Vcur;A1S0SfSd8S0SfS16Se1S10Z0A1Se2Vtxt;S15A5S0SfSdaVd;ZcVk;A3G0A3A3A3A3A3A3A3A3A3").
Definition lregs : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SdA2M0S1S2SdU2S36Sf8A1M1A4S0G0S1S2SdU8S14PaA1A4S0G0S1S2SdU9G1A4S0G0S1S2SdU12S3fZ508A1A4S0G0S1S2SdU13S10eA4S0G0S1S2SdU14S3fZc0A1A4S0G0S1S2SdU15S77Z0A1A4S0G0S1S2SdU16Sf6A4S0G0S1S2SdU17S3fZ4f0A1A4S0G0S1S2SdU19S78A4S0G0S1S2SdU1aS10Z20A1A4S0G0S1S2SdU1bS10Z9A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition frame_factsH : list sprop := ltac2:(tb__ "0|1|
S4SeS25S68S10eA2S4SeS25SdcSceA2S0SeS1dPa0Z5A2S0SeS1eS1aSccSceS10Z0A1A3A1S0SeS12S10S120A1M0SceA2S0SeS12S13ScaSceS10Z40A1A3S14P1eA1A2S0SeS12SceS10S39A1A2S0SeS12G0SdbA2S0SeS12S13ScaSdbS10Z1A1A3S10Z7fffff800000A1A2S3SeA1A3A3A3A3A3A3A3A3A3").

Definition body_facts (cur rc rcur d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4SeSe0Sf8Sf9A2S4SeSdfS4SeS0SeS12S5eS10Z1A1A2S0SeS57Vrc;Vrcur;A2S0SeS73Vrc;Vrcur;A2S0SeS74Vrc;Vrcur;A2S0SeS12Sd2S10S34A1A2S0SeS12Sd0Vrcur;A2S0SeS12Vrcur;Vcur;A2S0SeS12Vcur;Sd1A2S3SeA1A3A3A3A3A3A3A3A3S4SeS5bS4SeSdeVd;Vc;Vk;ZcVdv;A5SbaA3A3A3A3A3").
Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur d c k : sv) (dv : positive) (txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sf1S18Vpc;Se4S4S5S2SdA2S6aVregs;A3A1SddS17S6SdA1SbfVcur;S5eVd;Vc;Vk;Vtxt;A6S4SeVfacts;S66Vcur;Vc;Vrcur;Vd;Vc;Vk;Vdv;A7A3Sd7S7A9S44Vd;Vk;A2A2").

Definition H : axst := ltac2:(tb__ "0|0|
S4fSfbS3S5S2SdA2A1S4bS4bS45S40S3eP12fS3S11A1S3SeA1Aa").

Definition L1 : axst := ltac2:(tb__ "0|2|
S4fSfeS0S5S2SdA2M0S1S2SdUaSd4S3aA1M1A4S0G0S1S2SdUbG1A4S0G0S1S2SdUcSd4Sd1A1A4S3G0A1A3A3A3S4bS4bS45S40S3eP12fS3S11A1S0SeS12S4bS3aA2S0SeS19S3aSd1A2S3SeA1A3A3Aa").

Definition L2 : axst := ltac2:(tb__ "0|2|
S4fSffS0S5S2SdA2M0S1S2SdUaSd4S4cA1A4S0G0S1S2SdUbSd4S3aA1M1A4S0G0S1S2SdUdG1A4S0G0S1S2SdUcSd4Sd1A1A4S3G0A1A3A3A3A3S3aS4cS45S40S3eP12fS3S11A1S0SeS12S4cS3aA2S0SeS19S3aSd1A2S3SeA1A3A3Aa").

Definition K : axst := ltac2:(tb__ "0|1|
S4fSfdS0S5S2SdA2M0S1S2SdUaSd4S4cA1A4S0G0S1S2SdUcSd4Sd1A1A4S3G0A1A3A3S3aS4cS45S40S3eP12fS3S11A1S0SeS19S4cS3aA2S3SeA1A3Aa").

Definition pX : sv := SVar 307.
Definition XN : axst := ltac2:(tb__ "0|0|
S4fSfaS3S5S2SdA2A1S55S55S45S40S3eP12fS3S11A1S3SeA1Aa").

Definition E_unp0 : axst := Eval vm_compute in leaf_at K hp_UNP 0.
Definition C_unp : axst := Eval vm_compute in shadow_reopen_stateA E_unp0 (ax_X E_unp0) hG 4 6.

Definition E_pc0 : axst := Eval vm_compute in leaf_at C_unp pc_entry 0.
Goal lvs K = [(hp_UNP, RsCut)] /\ lvs C_unp = [(pc_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition sh_unp : sobj := Eval vm_compute in last (ss_objs (ax_S E_pc0)) O_Wp.
Definition objs_pc0 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S E_pc0)).
Goal sh_unp = shobj hG 4 6 (ob_cells sh_unp) DUnknown /\ local_ok (ob_cells sh_unp) DUnknown 4 6 (32, 12) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_pc1 : axst := Eval vm_compute in shadow_release_stateA E_pc0 objs_pc0 160 [(32, 12)].
Definition idx_obj (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16SceS10Z20A1S10Z2cA1Vcells;S15A5").
Definition xf_pc : list axform := ltac2:(tb__ "0|2|
S0S2cS30U0S10N40A1A2S0S2cS30U2S10Z20M0A1A2S0S2cS30U3M1S10Z2cA1A2S0S2cS2dG1G0A2S3S2cA1A3A3A3A3").
Definition E_pc : axst := Eval vm_compute in optAp (apply_axforms E_pc1 xf_pc).
Definition s_pc : wsub := ltac2:(tb__ "0|0|
S10aPaS23S8fA1S23S130A1A3").
Definition R_pc : list sobj := Eval vm_compute in optR (entails_frA E_pc Pre_pc s_pc).
Goal entails_frA E_pc Pre_pc s_pc = Some R_pc /\ call_checkA E_pc Pre_pc s_pc R_pc (map la_state Posts_pc) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S119S1fS23VCl;A1A1S135Vs;VPre;VL;VCl;VR;A5A2").
Definition T_pc0 : axst := Eval vm_compute in T_pure Pre_pc E_pc s_pc R_pc P_ret.

Definition xf_tpc : list axform := ltac2:(tb__ "0|2|
S0S2cS2fS4S2S0S2U5S0S2U0M0S0S2U1S0S2U2M1S0S2U3S0S2U4S3S2A1A3A3A3A3A3A3SedU6U11A2A3A1S0S2cS2eG0A1S0S2cS32G1A1S3S2cA1A3A3A3").
Definition T_pc : axst := Eval vm_compute in optAp (apply_axforms T_pc0 xf_tpc).

Definition E_da0 : axst := Eval vm_compute in leaf_at T_pc da_entry 0.
Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
S10aPaS23S8bA1S23S124A1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0S2cS2fS4S2S0S2U3S0S2U0M0S0S2U4S0S2U5S0S2U1S0S2U2S3S2A1A3A3A3A3A3A3SedU6U11A2A3A1S0S2cS2eG0A1S3S2cA1A3A3").
Definition T_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).

Definition gB : positive := 308%positive.
Definition objs_tok (cur hp d c k : sv) (idxc : list cell) : list sobj := ltac2:(tb__ "0|3|
S4SfS0SfS51S0SfS16Se1S10Z0A1M0Se2S3S11A1M1S15A5S0SfSbcVidxc;A1S3SfA1M2A3A3A3S4SfSf2S4SfS0SfS16SceG0S10Z20A1S69S15A5S0SfS16SceS10Z2cA1S10Z38A1G1S15A5S0SfS62S0SfS50S60A1G2A3A3A3A3S4SfS52S10cVhp;Vd;Vc;Vk;A5S0SfS10bS0SfSd9Vcur;A1S0SfSd8S0SfSdaVd;ZcVk;A3G2A3A3A3A3A3A3A3A3").
Definition X_tok (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SdSdA2S11fPa0S1S20S20Z20ZcA4A2S44Vd;Vk;A2A3").

Definition pC1 : sv := SAlu ALU_ADD pC (SLit 1).
Definition JC (pc : Z) (regs : list (nat * sv)) (cur d c k : sv) (dv : positive) (idxc : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
Sf1S18Vpc;Se4S4S5S2SdA2S6aVregs;A3A1SddS17S6SdA1Sc1Vcur;S5eVd;Vc;Vk;Vidxc;A6S4SeVfacts;S66Vcur;Sc2Vcur;Vd;Vc;Vk;Vdv;A7A3Sd7S7A9Sb7Vd;Vk;A2A2").
Definition J : axst := ltac2:(tb__ "0|1|
S96SfcS0S5S2SdA2M0S1S2SdU19S14S67A1A4S3G0A1A3S3aS45S40S3eP12fS3S11A1S25S67S10dA2A9").
Goal lvs T_pc = [(hp_J, RsCut); (hp_J, RsCut); (da_entry, RsCut)] /\ lvs T_da = [(hp_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at J vr_entry 0.
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0S2cS30U0M0S10N40M1A1A2S0S2cS2dG0G1A2S0S2cS2dU11Z2b0A2S3S2cA1A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).

Definition s_v : wsub := ltac2:(tb__ "0|1|
S0S5S21SdA2M0S1S21SdP3bS61S3aA1A4S0G0S1S21SdP13S13ScaS35S10Z40A1A3A4S10aPaS23S92A1S23S128A1A3A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr VN.Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5S22S28A2M0S1S22S28S127S12aA4S0G0S1S22S28S125S29S12bS3S5S5SdS20A2SdA2A1M1S3SecA1A3A4S0G0S1S22S28S126S29S12cG1S129S12eS12dA2A3A4S3G0A1A3A3A3").
Goal entails_frA E_vr VN.Pre_vr s_v = Some R_v /\ call_checkPA E_vr VN.Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) pD)) (X_tok pD pK).
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_grown Xk_v.

Definition cmul12 (c : sv) : sv := SMd M_MUL c (SLit 12).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0SeS12S13ScaS53S40A1M0S10ZcM1A1A3ScfG1Vk;A2M2A2S0SeS12G0G2A2S0SeS12G0S10S34A1A2S3SeA1A3A3A3").
Definition vDg : sv := SVar 520.
Definition vKg : sv := SVar 521.
Definition T_keep : axst := ltac2:(tb__ "0|0|
S119S4SeS79S3eA1S0SeS12S10S120A1S45A2S3SeA1A3A3Sa7A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
S119S79S7aA1Sa5A2").
Definition E_mk0 : axst := Eval vm_compute in leaf_at T_keep memcpy_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leaf_at T_grown memcpy_pc 0.

Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S16S13ScaVd;S53S40A1A3S10Z0A1S10ZcA1S3S11A1S15A5").
Definition xf_mc : list axform := ltac2:(tb__ "0|3|
S0S2cS2dU1M0Z40A2S0S2cS2dU8Z20A2S0S2cS2fS4S2S0S2G0S0S2U0M1S3S2A1A3A3SedU2U15A2A3A1S0S2cS2eG1A1S0S2cS30U3S53S40A1M2A2S0S2cS30U4S13ScaG2S10ZcA1A3A2S3S2cA1A3A3A3A3A3A3").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
S26VA;S136S23VA;A1Vi;Vo;A3A2").
Definition E_mc (E0 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S76S54S31VE0;Sc9A2A1U4Sb8Vd;A1A3").
Definition E_mk : axst := Eval vm_compute in E_mc E_mk0 pD.
Definition E_mg : axst := Eval vm_compute in E_mc E_mg0 vDg.
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|2|
S0S5S21SdA2M0S1S21SdP35Vd;A4S0G0S1S21SdP36ScfZcM1Vk;A2A4S0G0S1S21SdP37S13ScaSceS10Z20A1A3A4S0G0S1S21SdP38S10G1A1A4S0G0S1S21SdS121S35A4S10aPaS23VE;A1S23Sa0A1A3A3A3A3A3A3").
Definition R_mk : list sobj := Eval vm_compute in optR (entails_frA E_mk Pre_mc (s_mc E_mk pD pK)).
Definition R_mg : list sobj := Eval vm_compute in optR (entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg)).
Goal entails_frA E_mk Pre_mc (s_mc E_mk pD pK) = Some R_mk /\ call_checkPA E_mk Pre_mc (s_mc E_mk pD pK) R_mk [L_mc1; L_mc1] = true
  /\ entails_frA E_mg Pre_mc (s_mc E_mg vDg vKg) = Some R_mg /\ call_checkPA E_mg Pre_mc (s_mc E_mg vDg vKg) R_mg [L_mc1; L_mc1] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_mck : axst := Eval vm_compute in T_afterA Pre_mc E_mk (s_mc E_mk pD pK) R_mk L_mc1.
Definition T_mcg : axst := Eval vm_compute in T_afterA Pre_mc E_mg (s_mc E_mg vDg vKg) R_mg L_mc1.

Definition X_rpk : axst := Eval vm_compute in leaf_at T_mck hp_REP 0.
Definition X_rpg : axst := Eval vm_compute in leaf_at T_mcg hp_REP 0.
Goal lvs T_mck = [(hp_REP, RsCut)] /\ lvs T_mcg = [(hp_REP, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition mid_dst (d : sv) : sobj := ltac2:(tb__ "0|1|
S16Vd;S53S40A1M0S13ScaG0S10ZcA1A3S3S11A1S15A5").
Definition sel_body : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2UaS0S2U2S0S2UbS0S2UcS0S2U3S0S2U4S0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U14S0S2U5S0S2U15S0S2U6S0S2U16S0S2U17S0S2U9S0S2U7S0S2U1S0S2U8S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition canon_mc (A : axst) (d k : sv) : axst := ltac2:(tb__ "0|3|
S76VA;U1M0SbdVd;A1A3S22S54S31R1S0S2cS32U2A1S0S2cS2dU5N2b0A2S0S2cS2fSc3A1S0S2cS2eG0A1M1S0S2cG1S0S2cS2eU13A1M2S0S2cG2S3S2cA1A3A3A3A3A3A3A3A2A1S22S11dR1S44Vd;Vk;A2SdcZ4Z6A5TA2;TA1;").
Definition C_mk : axst := Eval vm_compute in canon_mc X_rpk pD pK.
Definition C_mg : axst := Eval vm_compute in canon_mc X_rpg vDg vKg.
Goal shape C_mg = shape (ax_setS C_mk (set_objs (ax_S C_mk) (firstn 19 (ss_objs (ax_S C_mk)) ++ [O_data vDg 12 vKg; shobj hG 4 6 [] DUnknown])))
  /\ map (fun o => (ob_base o, ob_lo o, ob_hi o)) (firstn 20 (ss_objs (ax_S C_mk))) = map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pQ pHP pD pC1 pK []).
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_r2k : axst := Eval vm_compute in leaf_at C_mk hp_REP2 0.
Definition X_r2g : axst := Eval vm_compute in leaf_at C_mg hp_REP2 0.
Definition C_rlk : axst := Eval vm_compute in shadow_release_stateA X_r2k (removelast (ss_objs (ax_S X_r2k))) 160 [].
Definition C_rlg : axst := Eval vm_compute in shadow_release_stateA X_r2g (removelast (ss_objs (ax_S X_r2g))) 160 [].
Goal lvs C_mk = [(hp_REP2, RsCut)] /\ lvs C_mg = [(hp_REP2, RsCut)] /\ lvs C_rlk = [(hp_H, RsCut)] /\ lvs C_rlg = [(hp_H, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition epi_state (Y : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
S11eS11dVY;S44Vd;Vk;A2SdcZ0Z8A5PaaA2").
Definition C_epn : axst := Eval vm_compute in epi_state XN pD pK.
Definition X_rln : axst := Eval vm_compute in leaf_at C_epn hp_REL 0.

Definition X_fp0 : axst := Eval vm_compute in leaf_at T_fail0 hp_FP 0.
Definition X_fp1 : axst := Eval vm_compute in leaf_at T_fail0 hp_FP 1.
Definition sel_f : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U9S0S2U8S0S2UaS0S2UbS0S2U5S0S2U6S0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U2S0S2U14S0S2U3S0S2U15S0S2U16S0S2U7S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition canon_f (A : axst) : axst := ltac2:(tb__ "0|2|
S134S54S31VA;S0S2cS2dU1M0Z40A2S0S2cS2dU2N2b0A2S0S2cS2fSc4A1S0S2cS2eU0A1S0S2cS2eG0A1M1S0S2cG1S3S2cA1A3A3A3A3A3A3A2A1S44S45S3eA2A2").
Definition Y_fp0 : axst := Eval vm_compute in canon_f X_fp0.
Definition Y_fp1 : axst := Eval vm_compute in canon_f X_fp1.
Definition C_fp0 : axst := Eval vm_compute in epi_state Y_fp0 pD pK.
Definition C_fp1 : axst := Eval vm_compute in epi_state Y_fp1 pD pK.
Goal lvs T_fail0 = [(hp_FP, RsCut); (hp_FP, RsCut)] /\ shape Y_fp1 = shape Y_fp0
  /\ map (fun o => (ob_base o, ob_lo o, ob_hi o)) (ss_objs (ax_S Y_fp0)) = map (fun o => (ob_base o, ob_lo o, ob_hi o)) (objs_body pQ pHP pD pC pK []).
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_epf0 : axst := Eval vm_compute in leaf_at C_fp0 hp_EPI 0.
Definition C_epf1 : axst := Eval vm_compute in leaf_at C_fp1 hp_EPI 0.
Definition X_rlf0 : axst := Eval vm_compute in leaf_at C_epf0 hp_REL 0.
Definition X_rlf1 : axst := Eval vm_compute in leaf_at C_epf1 hp_REL 0.
Goal lvs C_epn = [(hp_REL, RsCut)] /\ lvs C_fp0 = [(hp_EPI, RsCut)] /\ lvs C_fp1 = [(hp_EPI, RsCut)] /\ lvs C_epf0 = [(hp_REL, RsCut)] /\ lvs C_epf1 = [(hp_REL, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S4S2S0S2U0S3S2A1M0A3S4S2SedU3U11A2S0S2U1S0S2U2S0S2U14S0S2U15G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S54S31VX;S0S2cS2fSc5A1S3S2cA1A3A2A1S22S26R1S132S23R1A1M0SeeSfU12S1bG0A1A3A2A2TX1;").
Definition C_rln : axst := Eval vm_compute in rel_state X_rln.
Definition C_rlf0 : axst := Eval vm_compute in rel_state X_rlf0.
Definition C_rlf1 : axst := Eval vm_compute in rel_state X_rlf1.
Goal map (fun X => release_objs_ok 160 170 hG 0 (skipn 18 (ss_objs (ax_S (optAp (apply_axforms X [AXSelect sel_rel])))))) [X_rln; X_rlf0; X_rlf1] = [true; true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rln; C_rlf0; C_rlf1] = [18; 18; 18]%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_retn : axst := Eval vm_compute in leaf_at C_rln hp_ret 0.
Definition X_retf0 : axst := Eval vm_compute in leaf_at C_rlf0 hp_ret 0.
Definition X_retf1 : axst := Eval vm_compute in leaf_at C_rlf1 hp_ret 0.
Goal lvs C_rln = [(hp_ret, RsSymJump)] /\ lvs C_rlf0 = [(hp_ret, RsSymJump)] /\ lvs C_rlf1 = [(hp_ret, RsSymJump)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition qCUR : sv := SVar 310. Definition qD : sv := SVar 311. Definition qC : sv := SVar 312. Definition qK : sv := SVar 313.
Definition qHP : sv := SVar 314. Definition qERR : sv := SVar 315.
Definition objs_post (err hp d c k cur : sv) : list sobj := ltac2:(tb__ "0|1|
S4SfS0SfS51S3SfA1M0A3S4SfSf2S4SfS0SfS50S3S11A1A1G0A3S4SfS52Verr;Vhp;Vd;Vc;Vk;A5S0SfS10bS0SfSd9Vcur;A1S0SfSd8S0SfSe3S0SfSdaVd;ZcVk;A3G0A3A3A3A3A3A3A3A3A3").
Definition post_base_facts (cur hp : sv) : list sprop := ltac2:(tb__ "0|0|
S4SeSe0Sf8Sf9A2S4SeSdfS4SeS0SeS12Vhp;S10Z1A1A2S0SeS12Sd2S10S34A1A2S0SeS12Sd0Vcur;A2S0SeS12Vcur;Sd1A2S3SeA1A3A3A3A3S5bA3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
Sf1S18S100S11aP190A1SddS17S6SdA1S71S10cS56S47S46S43S41A6S4SeS0SeS57S46S41A2S0SeS73S46S41A2S0SeS74S46S41A2S0SeS12S46S61S41A1A2S3SeA1A3A3A3A3S4SeSdeS47S46S43ZcP137A5S72S41S56A2A3A3Sd7S7A9S44S47S43A2A2").
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1aScdS1cSaQ20Ve;A3S10Z0A1A3").
Definition P_fail : axst := ltac2:(tb__ "0|0|
Sf1S18S100S11aP190A1SddS17S6SdA1S71S75S56S47S46S43S41A6S4SeS0SeS9aS75A1S3SeA1A3S4SeSdeS47S46S43ZcP137A5S72S41S56A2A3A3Sd7S7A9S44S47S43A2A2").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S29S58S47S43A2S3S5S5SdS20A2SdA2A1S48S43S41A2A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S29S58S47S43A2S3S5S5SdS20A2SdA2A1S0SecSd5Z48S41A2S3SecA1A3A3").
Definition Posts_hp : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S5S22S28A2M0S1S22S28S63S6fA4S0G0S1S22S28S64S70A4S3G0A1A3A3").

Goal leaf_matches1A NPH X_retn P_ok = true /\ map (fun L => leaf_matches1A NPH L P_fail) [X_retf0; X_retf1] = [true; true]
  /\ leaf_matches1A NPH X_retn P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S2bVtv;Sb9Vbd;S2aA4").
Definition tvL : list (sv * sv) := tv_hp pD pK.
Definition tvG : list (sv * sv) := tv_hp vDg vKg.
Definition ndP : ndesc := ltac2:(tb__ "0|0|
S49S58Sd6Sd3A2S65S4eSd3Sd0A3A2").
Definition ndH : ndesc := ltac2:(tb__ "0|0|
S49S4dS48S3eS4bA2A2").
Definition ndT : ndesc := ltac2:(tb__ "0|0|
S49S4dS48S3eS4cA2A2").
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S49S4dS48S3eS3aA2A2").
Definition ndG : ndesc := ltac2:(tb__ "0|0|
S49Sc6S48S7aS3aA2A2").
Definition ndX : ndesc := ltac2:(tb__ "0|0|
S49S4dS0SecSd5Z48S3aA2S3SecA1A3A2").
Definition ndN : ndesc := ltac2:(tb__ "0|0|
S49S4dS48S3eS55A2A2").
Definition ndX' : ndesc := ltac2:(tb__ "0|0|
S29S4dS3S5S5SdS20A2SdA2A1S0SecSd5Z48S3aA2S3SecA1A3A3").
Definition ndN' : ndesc := ltac2:(tb__ "0|0|
S29S4dS3S5S5SdS20A2SdA2A1S48S3eS55A2A3").

Definition VR (cur : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S13ScaScfZ40S13ScbSd1Vcur;A3A2S10Vpos;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsH : list edescA := ltac2:(tb__ "0|b|
S0S5S5S22S28A2M0S5S20SdA2M1A2M2S1G0G1S1S22S28S9eS6bA4S1S20SdZ64S3cA4A4S0G2S1G0G1S1S22S28S84S5dA4S1S20SdZ60S3cA4A4S0G2S1G0G1S1S22S28S83S5dA4S1S20SdZ5cS3cA4A4S0G2S1G0G1S1S22S28S94S6cA4S1S20SdZ50M3S3bS4bZ2A2A4A4S0G2S1G0G1S1S22S28S98S6cA4S1S20SdG3S3bS3aZ1A2A4A4S0G2S1G0G1S1S22S28S99S6dA4S1S20SdG3S3bS3aZ0A2A4A4S0G2S1G0G1S1S22S28S97S6dA4S1S20SdG3S3bS3aZ3cA2A4A4S0G2S1G0G1S1S22S28S8aS3dA4S1S20SdG3S3bS3aZ3aA2A4A4S0G2S1G0G1S1S22S28SaaS3dA4S1S20SdG3S3bS3aZ38A2A4A4S0G2S1G0G1S1S22S28Sa2S3dA4S1S20SdG3S3bS3aZ36A2A4A4S0G2S1G0G1S1S22S28S95S3dA4S1S20SdG3S3bS3aZ35A2A4A4S0G2S1G0G1S1S22S28Sa6S3dA4S1S20SdG3S3bS3aZ33A2A4M4A4S0G2S1G0G1S1S22S28Sa4S4aA4G4A4S0G2S1G0G1S1S22S28Sa3S42A4S1S20SdZ1eS3cA4A4S0G2S1G0G1S1S22S28Sa9S3dA4S1S20SdG3S3bS3aZ31A2A4M5A4S0G2S1G0G1S1S22S28Sa8S4aA4G5A4S0G2S1G0G1S1S22S28S82S3dA4S1S20SdG3S3bS3aZ2fA2A4M6A4S0G2S1G0G1S1S22S28S81S4aA4G6A4S0G2S1G0G1S1S22S28S88S3dA4S1S20SdG3S3bS3aZ2dA2A4M7A4S0G2S1G0G1S1S22S28S87S4aA4G7A4S0G2S1G0G1S1S22S28S7cS42A4S1S20SdZ18S3cA4M8A4S0G2S1G0G1S1S22S28S7dS42A4G8A4S0G2S1G0G1S1S22S28S7eS5cA4S1S20SdZ26S3cA4A4S0G2S1G0G1S1S22S28S7fS42A4S1S20SdZ1aS3cA4M9A4S0G2S1G0G1S1S22S28S80S42A4G9A4S0G2S1G0G1S1S22S28S89SbeA4S1S20SdZ22S3cA4A4S0G2S1G0G1S1S22S28S85S6eA4S1S20SdZ14S3cA4MaA4S0G2S1G0G1S1S22S28S86S6eA4GaA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsH : list edescA := ltac2:(tb__ "0|a|
S0S5S5S22S28A2M0S5S20SdA2M1A2M2S1G0G1S1S22S28S5fS6bA4S1S20SdZ62S3cA4A4S0G2S1G0G1S1S22S28SafS5dA4S1S20SdZ5eS3cA4A4S0G2S1G0G1S1S22S28S91S3dA4S1S20SdZ50M3S3bS3aZ3bA2A4A4S0G2S1G0G1S1S22S28S90S3dA4S1S20SdG3S3bS3aZ39A2A4A4S0G2S1G0G1S1S22S28S8cS3dA4S1S20SdG3S3bS3aZ37A2A4A4S0G2S1G0G1S1S22S28S93S3dA4S1S20SdG3S3bS3aZ34A2A4A4S0G2S1G0G1S1S22S28S8eS3dA4S1S20SdG3S3bS3aZ32A2A4M4A4S0G2S1G0G1S1S22S28S8dS4aA4G4A4S0G2S1G0G1S1S22S28Sb6S3dA4S1S20SdG3S3bS3aZ30A2A4M5A4S0G2S1G0G1S1S22S28Sb5S4aA4G5A4S0G2S1G0G1S1S22S28Sb1S3dA4S1S20SdG3S3bS3aZ2eA2A4M6A4S0G2S1G0G1S1S22S28Sb0S4aA4G6A4S0G2S1G0G1S1S22S28SacS5cA4S1S20SdZ28S3cA4A4S0G2S1G0G1S1S22S28Sb4S5cA4S1S20SdZ24S3cA4A4S0G2S1G0G1S1S22S28SadS42A4S1S20SdZ1cS3cA4M7A4S0G2S1G0G1S1S22S28SaeS42A4G7A4S0G2S1G0G1S1S22S28Sb2S42A4S1S20SdZ16S3cA4M8A4S0G2S1G0G1S1S22S28Sb3S42A4G8A4S0G2S1G0G1S1S22S28S63S6fA4S1S20SdZ0S3cA4M9A4S0G2S1G0G1S1S22S28S64S70A4G9A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
