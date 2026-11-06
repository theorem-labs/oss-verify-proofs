(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "None"; "false"; "list"; "option"; "true"; "length"; "S"; "fst"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "cell"; "SPUle"; "SAlu"; "SVar"; "DUnknown"; "mkObj"; "FcsrFrm0"; "mkSS"; "SPUlt"; "SPBranch"; "ss_objs"; "SExt"; "SPAlign"; "SPNot"; "ss_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "FE"; "sym_runA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "B32"; "spm"; "vDp"; "B_EW"; "KLG"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p"; "pQ"; "VR"; "z0"; "ndJ"; "xbo"; "pK"; "qCUR"; "ndX"; "qK"; "X_hp"; "pD"; "qC"; "qD"; "bd_hpN"; "ndF"; "pC"; "pP"; "pT0"; "tvL"; "ndG"; "pi_n"; "HC"; "O_F"; "O_Wp"; "builderP"; "pX"; "qHP"; "room_fact"; "tv_hp"; "FUEL_hp"; "cutpcs_hp"; "ghost_facts"; "ndN"; "ndP"; "optAp"; "pHP"; "E_sm0"; "F_cells"; "NA"; "O_flag"; "P_fail"; "P_ok"; "bd_hp"; "body_facts"; "gB"; "gC"; "hdr3"; "lregs"; "nd0"; "ndH"; "ndT"; "ndX'"; "nd_fail"; "nd_ok"; "objs_post"; "post_base_facts"; "prog_fact"; "prog_factP"; "qERR"; "shC"; "shF"; "slot_facts"; "vKg"; "xf_f"; "BAD"; "C_cg"; "C_ck"; "C_epf0"; "C_epf1"; "C_epn"; "C_fp0"; "C_fp1"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlf0"; "C_rlf1"; "C_rlg"; "C_rlk"; "C_rln"; "C_unp"; "E_da"; "E_da0"; "E_pc"; "E_pc0"; "E_unp0"; "E_vr"; "E_vr0"; "H"; "J"; "JC"; "K"; "L1"; "L2"; "NZ32"; "O_frame"; "PHIN"; "P_matp"; "Pre_hp"; "Pre_hp_S"; "Pre_sm"; "T_da"; "T_fail0"; "T_grown"; "T_grown0"; "T_keep"; "T_keep0"; "T_pc"; "V688"; "XN"; "X_fp0"; "X_fp1"; "X_pro"; "X_r2g"; "X_r2k"; "X_rlf0"; "X_rlf1"; "X_rln"; "X_rpg"; "X_rpk"; "X_tok"; "cg_var"; "ck_var"; "cmul12"; "fr_hp"; "frame_factsH"; "hp_facts"; "idx_obj"; "lregsJ"; "ndN'"; "objs_body"; "objs_hp"; "objs_tok"; "pC1"; "sel_f"; "sel_rel"; "tvG"; "xMATp"; "xSMOp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "AXRebase"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hF"; "kb"; "tE"; "tI"; "pi_c"; "pi_k"; "tp"; "PROG"; "pi_d"; "HNEXT"; "O_cE"; "O_cP"; "O_data"; "hFL"; "hG"; "h_fregs"; "vec_facts"; "cnt_facts"; "handle_facts"; "tB"; "tL"; "O_text"; "h_xregs"; "xHASPRIM"; "NPH"; "P_cur"; "P_hdr"; "V120"; "V216"; "bd_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "SHB"; "segs"; "leavesA_at"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.HPAddr"; "FR"; "DW"; "hp_EPI"; "hp_H"; "hp_J"; "hp_K"; "hp_L1"; "hp_L2"; "hp_ret"; "hp_FP"; "hp_PRO"; "hp_REL"; "hp_REP"; "hp_REP2"; "hp_UNP"; "hp_cp"; "hp_entry"; "sm0_pc"; "@Corelib.Lists.ListDef"; "seq"; "firstn"; "map"; "nth";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "vERR"; "vb"; "vc"; "c4"; "P_alloc"; "P_st"; "V184"; "c1"; "piece"; "vAL"; "vNC"; "vND"; "vNK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "flag_carve_stateA"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops"; "bl_vi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.VN"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "bdP"; "nd0"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner.ParseCornerAddr"; "pc_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "sub"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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

Module HPAddr.
  Definition hp_entry : Z := 0x9f8e8.
  Definition sm0_pc : Z := 0x47a9c.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition hp_cp : Z := 0x9fe14.
  Definition hp_PRO : Z := 0x9f9ec.
  Definition hp_H : Z := 0x9fb28.
  Definition hp_L1 : Z := 0x9fb54.
  Definition hp_L2 : Z := 0x9fbbc.
  Definition hp_K : Z := 0x9fbe8.
  Definition hp_UNP : Z := 0x9fbf4.
  Definition hp_J : Z := 0x9fd5c.
  Definition hp_REP : Z := 0x9fea8.
  Definition hp_REP2 : Z := 0x9feb4.
  Definition hp_F : Z := 0x9fee4.
  Definition hp_FP : Z := 0x9ff14.
  Definition hp_EPI : Z := 0x9ff38.
  Definition hp_REL : Z := 0x9ffa0.
  Definition hp_ret : Z := 0x9ffdc.
  Definition hp_ra_pc : Z := 0x9fcfc.
  Definition hp_ra_da : Z := 0x9fd5c.
  Definition hp_ra_vr : Z := 0x9fd9c.
  Definition hp_ra_mc : Z := 0x9fe70.
  Definition DW : Z := 4640.
  Definition FR : Z := 288.
End HPAddr.
Import HPAddr.

Definition FUEL_hp : nat := 400%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18S16PaA1S12S139Sf2A1A1S12Z0A1Vcells;S17A5").
Definition O_Wp : sobj := ltac2:(tb__ "0|0|
S18S30Sf2A1S31S12Z0A1S3S13A1S17A5").
Definition V688 (d c k : sv) : sobj := V 688 d c k 12.

Definition room_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S14S15Sc8ScdZcM0Vcnt;A2ScdG0SceA2A3S15Sc8S12S13aS32G0A2A1ScdG0Vcur;A2A3A2").

Definition prog_fact (cnt cur : sv) : sprop := ltac2:(tb__ "0|1|
S14S15Sc8ScdZcM0Vcnt;A2ScdG0ScfA2A3S15Sc8ScdG0Sd0A2ScdG0Vcur;A2A3A2").

Definition pi_n : sv := SVar 149.
Definition NA (cur : sv) : sv := ltac2:(tb__ "0|0|
S15Sc8S49S15Sc9Vcur;ScfA3A3").
Definition PHIN (cur k : sv) : bitem := PHIe 12 (NA cur) k.
Definition prog_factP (cnt cur : sv) : sprop := ltac2:(tb__ "0|0|
S14S15Sc8Vcnt;ScfA3S15Sc8Sd0Vcur;A3A2").
Definition ghost_facts : list sprop := ltac2:(tb__ "0|0|
S0S10S14Sd0S49A2S0S10S14S49S12S2fA1A2S0S10S50S49ScfA2S3S10A1A3A3A3").
Definition hp_facts : list sprop := ltac2:(tb__ "0|0|
S4S10SdeSf2Sf3A2S4S10SddS4S10S0S10S14Se3S12Z1A1A2S0S10S50Sd0ScfA2S3S10A1A3A3S4S10S54SdcSd4Sd0Sd1ZcP92A5A3A3A3A3").
Definition X_hp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SfSfA2M0S1SfSfS10aS12Z518A1A4S0G0S1SfSfS10bS12Z10A1A4S0G0S1SfSfS112S12Z30A1A4S0G0S1SfSfSdfSe0A4S0G0S1SfSfVd;ScdZcVk;A2A4S0G0S1SfSfS30Sf3A1S12Sf3A1A4S3G0A1A3A3A3A3A3A3").

Definition xMATp : sv := SVar 139. Definition xSMOp : sv := SVar 140.
Definition P_matp : sobj := ltac2:(tb__ "0|1|
S111Z4e8M0Z518S0S13S10cG0SbfA2S0S13S10cZ4ecSc0A2S0S13S110Z4f0S12Z0A1A2S3S13A1A3A3A3A3").
Definition builderP (err hp : sv) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S0S11S10dS0S11Se6S0S11S10eVerr;A1S0S11Se7S0S11S10fS114S113S115A3S0S11Se8S0S11Se5Vhp;A1S0S11Sa2Vd;Vc;Vk;A3S0S11S97S3S11A1A3A3A3A3A3A3A3A3A3").
Definition objs_hp (cur err hp d c k : sv) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S4bS3S13A1A1S0S11S4cS3S11A1M0A3A3S4S11S4dVerr;Vhp;Vd;Vc;Vk;A5S4S11S0S11S108S0S11Sd7Vcur;A1S0S11Sd6S0S11Se1S0S11Sd8Vd;ZcVk;A3G0A3A3A3A3A3SecA3A3A3").
Definition Pre_hp_S : sstate := ltac2:(tb__ "0|0|
S1aS102S11aS119S19S6SfA1Sb9ScfS109Se3Sd4Sd0Sd1A6Sb4Se4S7A9").
Definition Pre_hp : axst := ltac2:(tb__ "0|0|
SebS99S3eSd4Sd1A2A2").

Definition bd_hp (c k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S4SeaSe9ZcVc;Vk;A3S0SeaSd3Z48Vcur;A2S3SeaA1A3A3").

Definition bd_hpN (k cur : sv) : list bitem := ltac2:(tb__ "0|0|
S0SeaS96Vcur;Vk;A2S0SeaS33Vk;A1S0SeaSd3Z48Vcur;A2S3SeaA1A3A3A3").
Definition tv_hp (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SfSfA2M0S1SfSfVd;ScdZcVk;A2A4S3G0A1A3").
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S2bS51Sd4Sd1A2S3S5S5SfS22A2SfA2A1S5fS49Sd1ScfA3A3").

Definition cutpcs_hp : list Z := ltac2:(tb__ "0|0|
S0S22S103S0S22SfcS0S22Sf5S0S22Sf8S0S22Sf9S0S22Sf7S0S22S100S0S22S12dS0S22S121S0S22Sf6S0S22S12fS0S22S101S0S22SfeS0S22SffS0S22SfbS0S22Sf4S0S22SfdS3S22A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
SebS1aZ0S3SfA1M0G0S19S6SfA1S3S11A1S3S10A1P1S7A9S3S5SfSfA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S107S24Vk;SefS52S53VS;Vpc;A4S75A4").
Definition nleaves (S : axst) : nat := ltac2:(tb__ "0|1|
SbS26S9S8S26A1M0A1G0Lx;S28SeeS52S53VS;SaA5G0R1Ll;S3S26A1X9x2A2").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S9S8S26A1M0A1S8S5S22S131A2M1A1Lx;S28SeeS52S53VS;SaA5G0S106S26G1Sf1R1A4Ll;S3G1A1X9x2").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_hp sm0_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 0.
Definition L_sm : axst := L_stack_malloc AE_A 0.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S5S23SfA2S1S23SfS134S31A4S116PaS25S59A1S25S9aA1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_hp = [(sm0_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_hp : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S5S5SfS22A2M0SfA2M1S1G0SfS1SfS22SccZ0A4Sd9A4S3G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S4S2S104U0Vi;A2S4S2S104ScVi;A1M0S11fSbS11S1dS25VA;A1A1A2G0A2A2S0S2Vi;S3S2A1A3A3A3").
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
S15Sc8S16SdaA1S12SedA1A3").
Definition shC (k : Z) : sv := ltac2:(tb__ "0|0|
S15Sc8S16S62A1S12S138SedVk;A2A1A3").
Definition xbo (o : Z) : sv := ltac2:(tb__ "0|0|
S15Sc8S10aS12Vo;A1A3").

Definition F_cells : list cell := ltac2:(tb__ "0|0|
S0S13S2eN120S12Z0A1A2S0S13S2eN108S15Sc8S10bS12Z8A1A3A2S0S13S2eN100S39Z68A1A2S0S13S2eNf8S39Z10A1A2S0S13S2eNf0SccA2S0S13S2eNe8S12ZffffffffaaaaaaabA1A2S0S13S2eNe0SccA2S0S13S2eNd8S39Z1e8A1A2S0S13S2eNd0S39Z508A1A2S0S13S2eNc8S39Z2c8A1A2S0S13S2eNc0S71A2S0S13S2eNb8S39Z500A1A2S0S13S2eNb0S39Z4f8A1A2S0S13S2eNa8S39Ze0A1A2S0S13S2eNa0S39Z80A1A2S0S13S2eN98S70Z1A1A2S0S13S2eN90S39Z2b8A1A2S0S13S2eN88S39Z2b0A1A2S0S13S2eN70SccA2S0S13S2eN68S16P2fA1A2S0S13S2eN60S16P2eA1A2S0S13S2eN58S16P2dA1A2S0S13S2eN50S16P2cA1A2S0S13S2eN48S16P2bA1A2S0S13S2eN40S16P2aA1A2S0S13S2eN38S16P29A1A2S0S13S2eN30S16P28A1A2S0S13S2eN28S16P27A1A2S0S13S2eN20S16P26A1A2S0S13S2eN18S16P1dA1A2S0S13S2eN10S16P1cA1A2S0S13S2eN8S16PbA1A2S3S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hdr3 : list cell := ltac2:(tb__ "0|0|
S0S13S2eZ0S12Z41b58ab3A1A2S0S13S2eZ8S12Z1afeeA1A2S0S13S2eZ10S12Z9f8e8A1A2S3S13A1A3A3A3").
Definition O_frame (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S18SccS12Z0A1S12Z38A1Vcells;S17A5").
Definition O_flag : sobj := ltac2:(tb__ "0|1|
S18SccS12Z38M0A1S12Z40A1S0S13S2eG0Sd9A2S3S13A1A3S17A5").

Definition objs_body (cur hp d c k : sv) (txt : list cell) : list sobj := ltac2:(tb__ "0|1|
S4S11S0S11S4cS0S11S95S63A1S0S11S5cS3S11A1M0A3A3A3S4S11SecS4S11S0S11S4bS5aA1G0A3S4S11S4dS109Vhp;Vd;Vc;Vk;A5S0S11S108S0S11Sd7Vcur;A1S0S11Sd6S0S11S18SdfS12Z0A1Se0Vtxt;S17A5S0S11Sd8Vd;ZcVk;A3G0A3A3A3A3A3A3A3A3A3").
Definition lregs : list (nat * sv) := ltac2:(tb__ "0|3|
S0S5S2SfA2M0S1S2SfU2S30Sf2A1M1A4S0G0S1S2SfU8S16PaA1A4S0G0S1S2SfU9G1A4S0G0S1S2SfU5S12Z1A1A4S0G0S1S2SfU6S12Z2A1A4S0G0S1S2SfU10S39Z508A1A4S0G0S1S2SfU11S12Z9A1A4S0G0S1S2SfU12S10bA4S0G0S1S2SfU14S10aA4S0G0S1S2SfU15Sf0A4S0G0S1S2SfU16S39Zc0A1A4S0G0S1S2SfU17S71A4S0G0S1S2SfU18S15Sc8SccS12Z20A1M2A3A4S0G0S1S2SfU19S39Z4f0A1A4S0G0S1S2SfU1aS70Z0A1A4S0G0S1S2SfU1bG2A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition frame_factsH : list sprop := ltac2:(tb__ "0|1|
S4S10S27S62S10bA2S4S10S27SdaSccA2S0S10S1fPa0Z5A2S0S10S20S1cScaSccS12Z0A1A3A1S0S10S14S12S11eA1M0SccA2S0S10S14S15Sc8SccS12Z40A1A3S16P1eA1A2S0S10S14SccS12S34A1A2S0S10S14G0Sd9A2S0S10S14S15Sc8Sd9S12Z1A1A3S12Z7fffff800000A1A2S3S10A1A3A3A3A3A3A3A3A3A3").

Definition body_facts (cur rc rcur d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4S10SdeSf2Sf3A2S4S10SddS4S10S0S10S14S58S12Z1A1A2S0S10S50Vrc;Vrcur;A2S0S10S6dVrc;Vrcur;A2S0S10S6eVrc;Vrcur;A2S0S10S14Sd0S12S2fA1A2S0S10S14ScfVrcur;A2S0S10S14Vrcur;Vcur;A2S0S10S14Vcur;SceA2S3S10A1A3A3A3A3A3A3A3A3S4S10S54S4S10SdcVd;Vc;Vk;ZcVdv;A5Sb3A3A3A3A3A3").
Definition HC (pc : Z) (regs : list (nat * sv)) (cur rcur d c k : sv) (dv : positive) (txt : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SebS1aVpc;Se2S4S5S2SfA2S64Vregs;A3A1SdbS19S6SfA1Sb8Vcur;S58Vd;Vc;Vk;Vtxt;A6S4S10Vfacts;S60Vcur;Vc;Vrcur;Vd;Vc;Vk;Vdv;A7A3Sd5S7A9S3eVd;Vk;A2A2").

Definition H : axst := ltac2:(tb__ "0|0|
S4aSf5S3S5S2SfA2A1S45S45S3fS44S3aP12fS3S13A1S3S10A1Aa").

Definition L1 : axst := ltac2:(tb__ "0|2|
S4aSf8S0S5S2SfA2M0S1S2SfUaSd2S35A1M1A4S0G0S1S2SfUbG1A4S0G0S1S2SfUcSd2SceA1A4S3G0A1A3A3A3S45S45S3fS44S3aP12fS3S13A1S0S10S14S45S35A2S0S10S1bS35SceA2S3S10A1A3A3Aa").

Definition L2 : axst := ltac2:(tb__ "0|2|
S4aSf9S0S5S2SfA2M0S1S2SfUaSd2S46A1A4S0G0S1S2SfUbSd2S35A1M1A4S0G0S1S2SfUdG1A4S0G0S1S2SfUcSd2SceA1A4S3G0A1A3A3A3A3S35S46S3fS44S3aP12fS3S13A1S0S10S14S46S35A2S0S10S1bS35SceA2S3S10A1A3A3Aa").

Definition K : axst := ltac2:(tb__ "0|1|
S4aSf7S0S5S2SfA2M0S1S2SfUaSd2S46A1A4S0G0S1S2SfUcSd2SceA1A4S3G0A1A3A3S35S46S3fS44S3aP12fS3S13A1S0S10S1bS46S35A2S3S10A1A3Aa").

Definition pX : sv := SVar 307.
Definition XN : axst := ltac2:(tb__ "0|0|
S4aSf4S3S5S2SfA2A1S4eS4eS3fS44S3aP12fS3S13A1S3S10A1Aa").

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
S18SccS12Z20A1S12Z2cA1Vcells;S17A5").
Definition xf_pc : list axform := ltac2:(tb__ "0|2|
S0Sc1Sc5U0S12N70A1A2S0Sc1Sc5U2S12Z20M0A1A2S0Sc1Sc5U3M1S12Z2cA1A2S0Sc1Sc2G1G0A2S3Sc1A1A3A3A3A3").
Definition E_pc : axst := Eval vm_compute in optAp (apply_axforms E_pc1 xf_pc).
Definition s_pc : wsub := ltac2:(tb__ "0|0|
S116PaS25S89A1S25S12eA1A3").
Definition R_pc : list sobj := Eval vm_compute in optR (entails_frA E_pc Pre_pc s_pc).
Goal entails_frA E_pc Pre_pc s_pc = Some R_pc /\ call_checkA E_pc Pre_pc s_pc R_pc (map la_state Posts_pc) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S117S21S25VCl;A1A1S133Vs;VPre;VL;VCl;VR;A5A2").
Definition T_pc0 : axst := Eval vm_compute in T_pure Pre_pc E_pc s_pc R_pc P_ret.

Definition xf_tpc : list axform := ltac2:(tb__ "0|2|
S0Sc1Sc4S4S2S0S2U5S0S2U0M0S0S2U1S0S2U2M1S0S2U3S0S2U4S3S2A1A3A3A3A3A3A3S104U6U11A2A3A1S0Sc1Sc3G0A1S0Sc1Sc7G1A1S3Sc1A1A3A3A3").
Definition T_pc : axst := Eval vm_compute in optAp (apply_axforms T_pc0 xf_tpc).

Definition E_da0 : axst := Eval vm_compute in leaf_at T_pc da_entry 0.
Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
S116PaS25S87A1S25S122A1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0Sc1Sc4S4S2S0S2U3S0S2U0M0S0S2U4S0S2U5S0S2U1S0S2U2S3S2A1A3A3A3A3A3A3S104U6U11A2A3A1S0Sc1Sc3G0A1S3Sc1A1A3A3").
Definition T_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).

Definition gB : positive := 308%positive.
Definition objs_tok (cur hp d c k : sv) (idxc : list cell) : list sobj := ltac2:(tb__ "0|3|
S4S11S0S11S4cS0S11S18SdfS12Z0A1M0Se0S3S13A1M1S17A5S0S11Sb5Vidxc;A1S3S11A1M2A3A3A3S4S11SecS4S11S0S11S18SccG0S12Z20A1S63S17A5S0S11S18SccS12Z2cA1S12Z38A1G1S17A5S0S11S5cS0S11S4bS5aA1G2A3A3A3A3S4S11S4dS109Vhp;Vd;Vc;Vk;A5S0S11S108S0S11Sd7Vcur;A1S0S11Sd6S0S11Sd8Vd;ZcVk;A3G2A3A3A3A3A3A3A3A3").
Definition X_tok (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S0S5SfSfA2S11dPa0S1S22S22Z20ZcA4A2S3eVd;Vk;A2A3").

Definition pC1 : sv := SAlu ALU_ADD pC (SLit 1).

Definition lregsJ : list (nat * sv) := ltac2:(tb__ "0|2|
S13bS5S2SfA2M0S8G0A1S13dG0A1G0S136SeS137S2S135SdS2SfR1A3A1S0S2U5S0S2U6S0S2U10S0S2U11S3S2A1A3A3A3A3A3A1M1A1Lp;G0S13cG1A1Lx;S64A6").
Definition JC (pc : Z) (regs : list (nat * sv)) (cur d c k : sv) (dv : positive) (idxc : list cell) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SebS1aVpc;Se2S4S5S2SfA2Sb6Vregs;A3A1SdbS19S6SfA1SbaVcur;S58Vd;Vc;Vk;Vidxc;A6S4S10Vfacts;S60Vcur;SbbVcur;Vd;Vc;Vk;Vdv;A7A3Sd5S7A9SaeVd;Vk;A2A2").
Definition J : axst := ltac2:(tb__ "0|1|
S90Sf6S0S5S2SfA2M0S1S2SfU13S16S61A1A4S3G0A1A3S35S3fS44S3aP12fS3S13A1S27S61S10aA2A9").
Goal lvs T_pc = [(hp_J, RsCut); (hp_J, RsCut); (da_entry, RsCut)] /\ lvs T_da = [(hp_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_vr0 : axst := Eval vm_compute in leaf_at J vr_entry 0.
Definition xf_vr : list axform := ltac2:(tb__ "0|2|
S0Sc1Sc5U0M0S12N40M1A1A2S0Sc1Sc2G0G1A2S0Sc1Sc2U11Z2b0A2S3Sc1A1A3A3A3").
Definition E_vr : axst := Eval vm_compute in optAp (apply_axforms E_vr0 xf_vr).

Definition s_v : wsub := ltac2:(tb__ "0|1|
S0S5S23SfA2M0S1S23SfP3bS5bS35A1A4S0G0S1S23SfP13S15Sc8S31S12Z40A1A3A4S116PaS25S8cA1S25S126A1A3A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vr VN.Pre_vr s_v).
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S0S5S24S2aA2M0S1S24S2aS125S128A4S0G0S1S24S2aS123S2bS129S3S5S5SfS22A2SfA2A1M1S3SeaA1A3A4S0G0S1S24S2aS124S2bS12aG1S127S12cS12bA2A3A4S3G0A1A3A3A3").
Goal entails_frA E_vr VN.Pre_vr s_v = Some R_v /\ call_checkPA E_vr VN.Pre_vr s_v R_v (map fst PD_vr) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xk_v : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) pD)) (X_tok pD pK).
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_vr s_v R_v VN.P_grown Xk_v.

Definition cmul12 (c : sv) : sv := SMd M_MUL c (SLit 12).
Definition slot_facts (k : sv) : list sprop := ltac2:(tb__ "0|3|
S0S10S14S15Sc8Sb1S44A1M0S12ZcM1A1A3ScdG1Vk;A2M2A2S0S10S14G0G2A2S0S10S14G0S12S2fA1A2S3S10A1A3A3A3").
Definition vDg : sv := SVar 520.
Definition vKg : sv := SVar 521.
Definition T_keep : axst := ltac2:(tb__ "0|0|
S117S4S10S72S3aA1S0S10S14S12S11eA1S3fA2S3S10A1A3A3Sa0A2").
Definition T_grown : axst := ltac2:(tb__ "0|0|
S117S72S73A1S9eA2").

Definition L_ck : axst := Eval vm_compute in leaf_at T_keep hp_cp 0.
Definition L_cg : axst := Eval vm_compute in leaf_at T_grown hp_cp 0.
Definition C_ck : axst := Eval vm_compute in bl_cut L_ck 14 (SLit 12) [10; 11; 16; 17]%nat [].
Definition C_cg : axst := Eval vm_compute in bl_cut L_cg 14 (SLit 12) [10; 11; 16; 17]%nat [].
Definition cp_var (L : axst) : sv := ltac2:(tb__ "0|0|
S15Sc8ScdZ40S15Sc9SceS35A3A2S15Sc9S12Z2bA1S16S120VL;A1A1A3A3").
Definition ck_var : sv := Eval vm_compute in cp_var L_ck.
Definition cg_var : sv := Eval vm_compute in cp_var L_cg.

Definition X_rpk : axst := Eval vm_compute in bl_junk (leaf_at C_ck hp_REP 0) [16; 17]%nat.
Definition X_rpg : axst := Eval vm_compute in bl_junk (leaf_at C_cg hp_REP 0) [16; 17]%nat.
Goal lvs T_keep = [(hp_cp, RsCut)] /\ lvs T_grown = [(hp_cp, RsCut)] /\ lvs C_ck = [(hp_cp, RsCut); (hp_REP, RsCut); (hp_cp, RsCut); (hp_REP, RsCut)] /\ lvs C_cg = lvs C_ck.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition sel_f : list nat := ltac2:(tb__ "0|0|
S0S2U1S0S2U0S0S2U9S0S2U8S0S2UaS0S2UbS0S2U5S0S2U6S0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S0S2U11S0S2U12S0S2U13S0S2U2S0S2U14S0S2U3S0S2U15S0S2U16S0S2U7S0S2U4S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_f : list axform := ltac2:(tb__ "0|2|
S0Sc1Sc2U1M0Z40A2S0Sc1Sc2U2N2b0A2S0Sc1Sc4SbcA1S0Sc1Sc3U0A1S0Sc1Sc3G0A1M1S0Sc1G1S3Sc1A1A3A3A3A3A3A3").
Definition canon_mc (A : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
S11bS57Sc6VA;S74A2A1S3eVd;Vk;A2SdaZ4Z6A5").
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
S11cS11bVY;S3eVd;Vk;A2SdaZ0Z8A5PaaA2").
Definition C_epn : axst := Eval vm_compute in epi_state XN pD pK.
Definition X_rln : axst := Eval vm_compute in leaf_at C_epn hp_REL 0.

Definition X_fp0 : axst := Eval vm_compute in leaf_at T_fail0 hp_FP 0.
Definition X_fp1 : axst := Eval vm_compute in leaf_at T_fail0 hp_FP 1.

Definition canon_f (A : axst) : axst := ltac2:(tb__ "0|0|
S132S57Sc6VA;S74A2A1S3eS3fS3aA2A2").
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
S4S2S0S2U0S3S2A1M0A3S4S2S104U3U11A2S0S2U1S0S2U2S0S2U14S0S2U15G0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S57Sc6VX;S0Sc1Sc4SbdA1S3Sc1A1A3A2A1S24S29R1S130S25R1A1M0S105S11U12S1dG0A1A3A2A2TX1;").
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
S4S11S0S11S4cS3S11A1M0A3S4S11SecS4S11S0S11S4bS3S13A1A1G0A3S4S11S4dVerr;Vhp;Vd;Vc;Vk;A5S0S11S108S0S11Sd7Vcur;A1S0S11Sd6S0S11Se1S0S11Sd8Vd;ZcVk;A3G0A3A3A3A3A3A3A3A3A3").
Definition post_base_facts (cur hp : sv) : list sprop := ltac2:(tb__ "0|0|
S4S10SdeSf2Sf3A2S4S10SddS4S10S0S10S14Vhp;S12Z1A1A2S0S10S14Sd0S12S2fA1A2S0S10S14ScfVcur;A2S0S10S14Vcur;SceA2S3S10A1A3A3A3A3S54A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
SebS1aSfaS118P190A1SdbS19S6SfA1S6bS109S4fS41S40S3dS3bA6S4S10S0S10S50S40S3bA2S0S10S6dS40S3bA2S0S10S6eS40S3bA2S0S10S14S40S5bS3bA1A2S3S10A1A3A3A3A3S4S10SdcS41S40S3dZcP137A5S6cS3bS4fA2A3A3Sd5S7A9S3eS41S3dA2A2").
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1cScbS1eSaQ20Ve;A3S12Z0A1A3").
Definition P_fail : axst := ltac2:(tb__ "0|0|
SebS1aSfaS118P190A1SdbS19S6SfA1S6bS6fS4fS41S40S3dS3bA6S4S10S0S10S94S6fA1S3S10A1A3S4S10SdcS41S40S3dZcP137A5S6cS3bS4fA2A3A3Sd5S7A9S3eS41S3dA2A2").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S2bS51S41S3dA2S3S5S5SfS22A2SfA2A1S42S3dS3bA2A3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S2bS51S41S3dA2S3S5S5SfS22A2SfA2A1S0SeaSd3Z48S3bA2S3SeaA1A3A3").
Definition Posts_hp : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S5S24S2aA2M0S1S24S2aS5dS69A4S0G0S1S24S2aS5eS6aA4S3G0A1A3A3").

Goal leaf_matches1A NPH X_retn P_ok = true /\ map (fun L => leaf_matches1A NPH L P_fail) [X_retf0; X_retf1] = [true; true]
  /\ leaf_matches1A NPH X_retn P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndF (tv : list (sv * sv)) (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S2dVtv;Sb2Vbd;S2cA4").
Definition tvL : list (sv * sv) := tv_hp pD pK.
Definition tvG : list (sv * sv) := tv_hp vDg vKg.
Definition ndP : ndesc := ltac2:(tb__ "0|0|
S43S51Sd4Sd1A2S5fS49Sd1ScfA3A2").
Definition ndH : ndesc := ltac2:(tb__ "0|0|
S43S47S42S3aS45A2A2").
Definition ndT : ndesc := ltac2:(tb__ "0|0|
S43S47S42S3aS46A2A2").
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S43S47S42S3aS35A2A2").
Definition ndG : ndesc := ltac2:(tb__ "0|0|
S43SbeS42S73S35A2A2").
Definition ndX : ndesc := ltac2:(tb__ "0|0|
S43S47S0SeaSd3Z48S35A2S3SeaA1A3A2").
Definition ndN : ndesc := ltac2:(tb__ "0|0|
S43S47S42S3aS4eA2A2").
Definition ndX' : ndesc := ltac2:(tb__ "0|0|
S2bS47S3S5S5SfS22A2SfA2A1S0SeaSd3Z48S35A2S3SeaA1A3A3").
Definition ndN' : ndesc := ltac2:(tb__ "0|0|
S2bS47S3S5S5SfS22A2SfA2A1S42S3aS4eA2A3").

Definition VR (cur : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S15Sc8ScdZ40S15Sc9SceVcur;A3A2S12Vpos;A1A3").
Definition z0 : sv := SLit 0.
Definition cutsH : list edescA := ltac2:(tb__ "0|a|
S0S5S5S24S2aA2M0S5S22SfA2M1A2M2S1G0G1S1S24S2aS98S65A4S1S22SfZ64S37A4A4S0G2S1G0G1S1S24S2aS80S56A4S1S22SfZ60S37A4A4S0G2S1G0G1S1S24S2aS7fS56A4S1S22SfZ5cS37A4A4S0G2S1G0G1S1S24S2aS8eS66A4S1S22SfZ50M3S36S45Z2A2A4A4S0G2S1G0G1S1S24S2aS92S66A4S1S22SfG3S36S35Z1A2A4A4S0G2S1G0G1S1S24S2aS93S67A4S1S22SfG3S36S35Z0A2A4A4S0G2S1G0G1S1S24S2aS91S67A4S1S22SfG3S36S35Z3cA2A4A4S0G2S1G0G1S1S24S2aS86S38A4S1S22SfG3S36S35Z3aA2A4A4S0G2S1G0G1S1S24S2aSa1S38A4S1S22SfG3S36S35Z38A2A4A4S0G2S1G0G1S1S24S2aS9bS38A4S1S22SfG3S36S35Z36A2A4A4S0G2S1G0G1S1S24S2aS8fS38A4S1S22SfG3S36S35Z35A2A4A4S0G2S1G0G1S1S24S2aS9fS38A4S1S22SfG3S36S35Z33A2A4M4A4S0G2S1G0G1S1S24S2aS9dS48A4G4A4S0G2S1G0G1S1S24S2aS9cS3cA4S1S22SfZ1eS37A4A4S0G2S1G0G1S1S24S2aS77S38A4S1S22SfG3Sb0A4A4S0G2S1G0G1S1S24S2aS76S48A4S1S22SfG3SafA4A4S0G2S1G0G1S1S24S2aS7eS38A4S1S22SfG3S36S35Z1dA2A4M5A4S0G2S1G0G1S1S24S2aS7dS48A4G5A4S0G2S1G0G1S1S24S2aS84S38A4S1S22SfG3S36S35Z1bA2A4M6A4S0G2S1G0G1S1S24S2aS83S48A4G6A4S0G2S1G0G1S1S24S2aS78S3cA4S1S22SfZ18S37A4M7A4S0G2S1G0G1S1S24S2aS79S3cA4G7A4S0G2S1G0G1S1S24S2aS7aS55A4S1S22SfZ26S37A4A4S0G2S1G0G1S1S24S2aS7bS3cA4S1S22SfZ1aS37A4M8A4S0G2S1G0G1S1S24S2aS7cS3cA4G8A4S0G2S1G0G1S1S24S2aS85Sb7A4S1S22SfZ22S37A4A4S0G2S1G0G1S1S24S2aS81S68A4S1S22SfZ14S37A4M9A4S0G2S1G0G1S1S24S2aS82S68A4G9A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsH : list edescA := ltac2:(tb__ "0|a|
S0S5S5S24S2aA2M0S5S22SfA2M1A2M2S1G0G1S1S24S2aS59S65A4S1S22SfZ62S37A4A4S0G2S1G0G1S1S24S2aSa6S56A4S1S22SfZ5eS37A4A4S0G2S1G0G1S1S24S2aS8bS38A4S1S22SfZ50M3S36S35Z3bA2A4A4S0G2S1G0G1S1S24S2aS8aS38A4S1S22SfG3S36S35Z39A2A4A4S0G2S1G0G1S1S24S2aS88S38A4S1S22SfG3S36S35Z37A2A4A4S0G2S1G0G1S1S24S2aS8dS38A4S1S22SfG3S36S35Z34A2A4A4S0G2S1G0G1S1S24S2aSadS38A4S1S22SfG3S36S35Z1eA2A4M4A4S0G2S1G0G1S1S24S2aSacS48A4G4A4S0G2S1G0G1S1S24S2aSa8S38A4S1S22SfG3S36S35Z1cM5A2A4M6A4S0G2S1G0G1S1S24S2aSa7S48A4G6A4S0G2S1G0G1S1S24S2aSa3S55A4S1S22SfZ28S37A4A4S0G2S1G0G1S1S24S2aSabS55A4S1S22SfZ24S37A4A4S0G2S1G0G1S1S24S2aSa4S3cA4S1S22SfG5S37A4M7A4S0G2S1G0G1S1S24S2aSa5S3cA4G7A4S0G2S1G0G1S1S24S2aSa9S3cA4S1S22SfZ16S37A4M8A4S0G2S1G0G1S1S24S2aSaaS3cA4G8A4S0G2S1G0G1S1S24S2aS5dS69A4S1S22SfZ0S37A4M9A4S0G2S1G0G1S1S24S2aS5eS6aA4G9A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
