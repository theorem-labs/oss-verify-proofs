(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "false"; "true"; "option"; "nat"; "Some"; "bool"; "list"; "None"; "app"; "prod"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "SVar"; "sprop"; "SPUle"; "SAlu"; "sobj"; "mkObj"; "SPBranch"; "DUnknown"; "SExt"; "DImage"; "SPAlign"; "sstate"; "SPNot"; "ss_next"; "ss_facts"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPEq"; "SPUlt"; "mkSS"; "ss_objs"; "ss_lenient"; "reg_sv"; "ss_pc"; "swf"; "DRom"; "sprop_below"; "DList"; "dflt_writable"; "is_arr"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_wf"; "sprop_eqb"; "valuation"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "ALU_OR"; "ALU_SLL"; "BC_NE"; "BC_LT"; "instr"; "Ecall"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "set_objs"; "RsEcall"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XRebase"; "XMerge"; "XSplit"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx2_states"; "E_fl2"; "C_2x"; "XB22"; "T_2Bt"; "C_2"; "E_fl2c"; "T_2f"; "s_fb2"; "s_ff2"; "s_fl2"; "XA20"; "T_2fS"; "R_fb2"; "R_ff2"; "T_2BS"; "T_fl2E"; "ECUTS"; "E_x2"; "R_fl2"; "T_fl2D"; "XA2a"; "XA2a2"; "XA2b"; "XA2b2"; "XB2a"; "XB2b"; "E_fl22"; "E_fl23"; "O10_fl2"; "XB2r"; "C_2m"; "E_fl21"; "T_2B"; "XA2a1"; "XA2a3"; "XA2a4"; "XA2b1"; "XA2b3"; "XA2b4"; "XB20"; "XB21"; "XB2a4"; "XB2b4"; "xs_xa"; "O_payB"; "s_CAa2"; "s_CAb2"; "s_CBa2"; "s_CBb2"; "BL_fl2"; "xs_fl2"; "xs_fo"; "MEMO_1"; "MEMO_12"; "MEMO_18"; "MEMO_25"; "O_b2z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "app_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states"; "X_2"; "NX1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "reshape_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "tvK"; "PreF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_free"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "leb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "tv_sub_eqb"; "robjs_check"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "beval"; "cells_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states.LAddr"; "stdout_buf"; "stdout_fdo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "O_payL"; "robj_inwi"; "tvL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLoutS"; "D"; "Pre_wl2"; "wl_ecallA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG";
"add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_checkP"; "call_check"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "to_nat"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "zeros"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue ObjXform ObjUnbase ListObj MuslWL DrvGlue DrvGlue2 TobjJV DataWin DrvStatics DrvPristine DrvLoop SysRead FuzzOneIface DrvWins.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code Drv_wins.
Require Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Drv_hl0_states Drv_hl1_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr TAddr LAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECUTS : list Z := [free_entry].

Lemma X_2_objs : ltac2:(tb__ "0|1|
S44S43S9S15A1S26S92A1M0SbS15Sb7S15UdG0A3S90S8bS93A2A3A3S44S43S5S15A1Sb2S15G0U2A3S7S15Sa7A2A3S44S43S8S27S92A1S3A3S44S43S10S28S92ZaA2S11Pf1A1A3S43S42S29S92A1SaaA3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition XA20 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc X_2) (list_set (ss_regs X_2) 10 (SLit 0)) (ss_fregs X_2) (ss_fcsr X_2) (ss_resv X_2) (ss_objs X_2) (ss_facts X_2) (ss_next X_2) false) in exact x).
Lemma diff_XA20 : ltac2:(tb__ "0|4|
S44S43S5ScS9ScS10S10A2M0A1M1S9S12A1M2A2M3A1SbbS92S5cA2S7G3S1G1G2S0G0S1S10S10S11Pf1A1SdZ0A1A4S2G0A1A3S2S12A1A4A2A3S44S43S8S2aS5cA1S4A3S44S43S8S27S5cA1S3A3S43S41S1eS5cA1S1eS92A1A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some ([(SVar 241, SLit 0)], @nil sprop))) | split; [vm_cast_no_check (@eq_refl bool true) | split; reflexivity]]. Qed.
Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S5S9S45A1A1") := ltac2:(tb__ "0|0|
S48S8cS8fS62S5cS4A5").
Definition LVA2 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_1 with Some l => l | None => [] end) in exact x).
Definition XA2a : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVA2 (mkLeaf XA20 RsFuel))) in exact x).
Definition XA2b : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVA2 (mkLeaf XA20 RsFuel))) in exact x).
Local Lemma MEMO_1_c : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S86S7G0S0S45S46S66S47A2S0S45S46S68S47A2S2S45A1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS62S5cS4A5S7G0S0S45S46S66S47A2S0S45S46S68S47A2S2S45A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL ECUTS XA20 true) MEMO_1 (Some [mkLeaf XA2a RsCut; mkLeaf XA2b RsCut]) (@eq_refl _ (sym_run segs FUEL ECUTS XA20 true)) MEMO_1_c). Qed.
Lemma run_XA20 : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS62S5cS4A5S7G0S0S45S46S66S47A2S0S45S46S68S47A2S2S45A1A3A3A2A3").
Proof. exact MEMO_1_e. Qed.

Definition xs_xa : list xform := ltac2:(tb__ "0|11|
S0S4cS51S0S6U0M0S0S6U1M1S0S6U3M2S0S6U4M3S0S6U5M4S0S6U6M5S0S6U7M6S0S6U8M7S0S6U9M8S0S6UaM9S0S6UbMaS0S6UcMbS0S6UdMcS0S6UeMdS0S6UfMeS0S6U2MfS2S6A1M10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S4cS4eG0A1S0S4cS4eG1A1S0S4cS51S0S6G1S0S6G0S0S6GfS0S6G2S0S6G3S0S6G4S0S6G5S0S6G6S0S6G7S0S6G8S0S6G9S0S6GaS0S6GbS0S6GcS0S6GdS0S6GeG10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S4cS4fG0A1S2S4cA1A3A3A3A3A3").
Local Definition MEMO_2 := apply_xforms XA2a xs_xa.
Definition XA2a1 : sstate := ltac:(let x := eval vm_compute in (xget XA2a (MEMO_2)) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = Some XA2a1. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS66S7dA2S7S1cS73A2A3").
Proof. exact (@eq_trans _ (apply_xforms XA2a xs_xa) MEMO_2 (Some XA2a1) (@eq_refl _ (apply_xforms XA2a xs_xa)) MEMO_2_c). Qed.
Lemma xs_XA2a_ok : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS66S7dA2S7S1cS73A2A3"). Proof. exact MEMO_2_e. Qed.
Local Definition MEMO_3 := unbase_obj_at XA2a1 0 (-208).
Definition XA2a2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_3 with Some s => s | None => XA2a1 end) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = Some XA2a2. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S43S5S1cA1S94S73U0Nd0A3S7S1cS67A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XA2a1 0 (-208)) MEMO_3 (Some XA2a2) (@eq_refl _ (unbase_obj_at XA2a1 0 (-208))) MEMO_3_c). Qed.
Lemma unb_XA2a : ltac2:(tb__ "0|0|
S43S5S1cA1S94S73U0Nd0A3S7S1cS67A2A3"). Proof. exact MEMO_3_e. Qed.
Definition XA2a3 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc XA2a2) (ss_regs XA2a2) (ss_fregs XA2a2) (ss_fcsr XA2a2) (ss_resv XA2a2) (firstn 14 (ss_objs XA2a2)) (ss_facts XA2a2) (ss_next XA2a2) (ss_lenient XA2a2)) in exact x).
Definition XA2a4 : sstate := ltac:(let x := eval vm_compute in (set_objs XA2a3 (firstn 11 (ss_objs XA2a3))) in exact x).
Lemma XA2a_sets : ltac2:(tb__ "0|5|
S44S43S9S15A1M0S26S67A1SbS15S26S74A1M1S0S15Sa7S2S15A1A3A3A3S44S43S8S2aS74A1S4A3S44S43G0G1SbS15S26S75A1M2S90S8bS93A2A3A3S44S43S41S1eS67A1S1eS5cA1A3S44S43S9S12A1M3S1fS75A1S1fS66A1M4A3S44S43G3S1fS67A1G4A3S44S43S1cS75S49S74G2A2A3S43S1cS74S49S67G1A2A3A2A2A2A2A2A2A2").
Proof. split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | repeat split; reflexivity]]. Qed.
Local Definition MEMO_4 := apply_xforms XA2b xs_xa.
Definition XA2b1 : sstate := ltac:(let x := eval vm_compute in (xget XA2b (MEMO_4)) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = Some XA2b1. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS68S7dA2S7S1cS76A2A3").
Proof. exact (@eq_trans _ (apply_xforms XA2b xs_xa) MEMO_4 (Some XA2b1) (@eq_refl _ (apply_xforms XA2b xs_xa)) MEMO_4_c). Qed.
Lemma xs_XA2b_ok : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS68S7dA2S7S1cS76A2A3"). Proof. exact MEMO_4_e. Qed.
Local Definition MEMO_5 := unbase_obj_at XA2b1 0 (-208).
Definition XA2b2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_5 with Some s => s | None => XA2b1 end) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some XA2b2. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S43S5S1cA1S94S76U0Nd0A3S7S1cS69A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XA2b1 0 (-208)) MEMO_5 (Some XA2b2) (@eq_refl _ (unbase_obj_at XA2b1 0 (-208))) MEMO_5_c). Qed.
Lemma unb_XA2b : ltac2:(tb__ "0|0|
S43S5S1cA1S94S76U0Nd0A3S7S1cS69A2A3"). Proof. exact MEMO_5_e. Qed.
Definition XA2b3 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc XA2b2) (ss_regs XA2b2) (ss_fregs XA2b2) (ss_fcsr XA2b2) (ss_resv XA2b2) (firstn 14 (ss_objs XA2b2)) (ss_facts XA2b2) (ss_next XA2b2) (ss_lenient XA2b2)) in exact x).
Definition XA2b4 : sstate := ltac:(let x := eval vm_compute in (set_objs XA2b3 (firstn 11 (ss_objs XA2b3))) in exact x).
Lemma XA2b_sets : ltac2:(tb__ "0|5|
S44S43S9S15A1M0S26S69A1SbS15S26S77A1M1S0S15Sa7S2S15A1A3A3A3S44S43S8S2aS77A1S4A3S44S43G0G1SbS15S26S78A1M2S90S8bS93A2A3A3S44S43S41S1eS69A1S1eS5cA1A3S44S43S9S12A1M3S1fS78A1S1fS68A1M4A3S44S43G3S1fS69A1G4A3S44S43S1cS78S49S77G2A2A3S43S1cS77S49S69G1A2A3A2A2A2A2A2A2A2").
Proof. split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | repeat split; reflexivity]]. Qed.

Definition XB2r : sstate := ltac:(let x := eval vm_compute in (set_objs X_2 (firstn 13 (ss_objs X_2))) in exact x).
Lemma XB2r_eq : ltac2:(tb__ "0|0|
S43S1cS49S92Sb7S15UdS26S92A1A3A2S6fA3"). Proof. reflexivity. Qed.
Definition O_payB : sobj := ltac2:(tb__ "0|0|
S16S11Pf1A1SdZ0A1S11P9eA1S2SeA1S18A5").
Local Definition MEMO_6 := reshape_obj_at XB2r 2 O_payB.
Definition XB20 : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = XB20. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S43S1cS95S6fU2S7eA3S79A3").
Proof. exact (@eq_trans _ (reshape_obj_at XB2r 2 O_payB) MEMO_6 (XB20) (@eq_refl _ (reshape_obj_at XB2r 2 O_payB)) MEMO_6_c). Qed.
Lemma XB20_eq : ltac2:(tb__ "0|2|
S44S43S1cS95S6fU2M0S7eA3S79A3S44S43S5S15A1Sb2S15S26S6fA1G0A3S7S15Sa7A2A3S44S43S8S34S1eS6fA1M1S7eA2S4A3S43S41G1S1eS92A1A3A2A2A2").
Proof. split; [exact MEMO_6_e | split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]]]. Qed.
Definition xs_fo : list xform := ltac2:(tb__ "0|2|
S0S4cS4eU0M0A1S0S4cS4eU1M1A1S0S4cS51S0S6G1S0S6G0S0S6U2S0S6U3S0S6U4S0S6U5S0S6U6S0S6U7S0S6U8S0S6U9S0S6UaS0S6UbS0S6UcS2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S4cS4fG0A1S2S4cA1A3A3A3A3").
Local Definition MEMO_7 := apply_xforms XB20 xs_fo.
Definition XB21 : sstate := ltac:(let x := eval vm_compute in (xget XB20 (MEMO_7)) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some XB21. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS79S85A2S7S1cS7aA2A3").
Proof. exact (@eq_trans _ (apply_xforms XB20 xs_fo) MEMO_7 (Some XB21) (@eq_refl _ (apply_xforms XB20 xs_fo)) MEMO_7_c). Qed.
Lemma xs_fo2_ok : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS79S85A2S7S1cS7aA2A3"). Proof. exact MEMO_7_e. Qed.
Local Definition MEMO_8 := unbase_obj_at XB21 0 (-208).
Definition XB22 : sstate := ltac:(let x := eval vm_compute in (match MEMO_8 with Some s => s | None => XB21 end) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some XB22. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S43S5S1cA1S94S7aU0Nd0A3S7S1cS54A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XB21 0 (-208)) MEMO_8 (Some XB22) (@eq_refl _ (unbase_obj_at XB21 0 (-208))) MEMO_8_c). Qed.
Lemma unb_fo2 : ltac2:(tb__ "0|0|
S43S5S1cA1S94S7aU0Nd0A3S7S1cS54A2A3"). Proof. exact MEMO_8_e. Qed.
Definition s_fb2 : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-208))) :: (15%positive, SLit (-1048368)) :: (13%positive, SVar 158) :: infer_sub 1 XB22 PreF) in exact x).
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S5S9S15A1A1") := ltac2:(tb__ "0|0|
S98S54S97S59A3").
Definition R_fb2 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_9 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some R_fb2. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S54S97S59A3S7G0S5eA2A3").
Proof. exact (@eq_trans _ (entails_fr XB22 PreF s_fb2) MEMO_9 (Some R_fb2) (@eq_refl _ (entails_fr XB22 PreF s_fb2)) MEMO_9_c). Qed.
Lemma efr_fb2 : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S54S97S59A3S7G0S5eA2A3"). Proof. exact MEMO_9_e. Qed.
Lemma chk_fb2 : ltac2:(tb__ "0|0|
S44S43S8Sb0S54S97S59S5eS0S1cS9bS9aA1S2S1cA1A3A5S4A3S43S8Sa0S1fS54A1Sa9S7S6U0A2Sa8S5eA5S4A3A2").
Proof. split; [vm_cast_no_check (@eq_refl _ true) | vm_cast_no_check (@eq_refl _ true)]. Qed.
Lemma s_fb2_vals : ltac2:(tb__ "0|0|
S44S43S10S8dS59PcA2S11Pf1A1A3S44S43S10S8dS59PdA2S11P9eA1A3S44S43S10S8dS59PaA2S14S37S11P1A1SdNd0A1A3A3S43S10S8dS59PfA2SdNfff30A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma XB22_shape : ltac2:(tb__ "0|0|
S44S43S42S29S54A1SaaA3S44S43S41S1eS54A1S1eS92A1A3S44S43S9S12A1S1fS54A1S1fS92A1A3S43S8S27S54A1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
S9eS54S59S5eS9bS9aA1A4").
Definition T_2B : sstate := ltac:(let x := eval vm_compute in (MEMO_10) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = T_2B. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S43S1cS9eS54S59S5eS9bS9aA1A4S72A3").
Proof. exact (@eq_trans _ (T_after XB22 s_fb2 R_fb2 (L_free EC_U)) MEMO_10 (T_2B) (@eq_refl _ (T_after XB22 s_fb2 R_fb2 (L_free EC_U))) MEMO_10_c). Qed.
Lemma T_2B_eq : ltac2:(tb__ "0|0|
S43S1cS9eS54S59S5eS9bS9aA1A4S72A3"). Proof. exact MEMO_10_e. Qed.

Definition T_2Bt : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc T_2B) (ss_regs T_2B) (ss_fregs T_2B) (ss_fcsr T_2B) (ss_resv T_2B) (ss_objs T_2B) L_facts (ss_next T_2B) false) in exact x).
Lemma ent_T2Bt : ltac2:(tb__ "0|0|
S44S43S8S99S72S55S2ScS41S10A2A1A3S4A3S43S41S1eS55A1S1eS72A1A3A2"). Proof. split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]. Qed.
Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|1|
S91S55S90S8bS1eS55A1M0A2S9cG0A1A3").
Definition T_2BS : sstate := ltac:(let x := eval vm_compute in (MEMO_11) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = T_2BS. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|1|
S43S1cS91S55S90S8bS1eS55A1M0A2S9cG0A1A3S60A3").
Proof. exact (@eq_trans _ (app_objs T_2Bt (statics_objs C_U (ss_next T_2Bt)) (Pos.succ (ss_next T_2Bt))) MEMO_11 (T_2BS) (@eq_refl _ (app_objs T_2Bt (statics_objs C_U (ss_next T_2Bt)) (Pos.succ (ss_next T_2Bt)))) MEMO_11_c). Qed.
Lemma T_2BS_eq : ltac2:(tb__ "0|1|
S43S1cS91S55S90S8bS1eS55A1M0A2S9cG0A1A3S60A3"). Proof. exact MEMO_11_e. Qed.
Lemma swf_T_2BS : swf T_2BS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_T2B : ltac2:(tb__ "0|0|
S43S8SbaS8bS1fS55A1S96S26S55A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_2BS_shape : ltac2:(tb__ "0|0|
S44S43S41S1eS60A1S9cS1eS55A1A1A3S43S8S27S60A1S3A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S5S9S45A1A1") := ltac2:(tb__ "0|0|
S48S8cS8fS62S60S4A5").
Definition LVB2 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_12 with Some l => l | None => [] end) in exact x).
Definition XB2a : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVB2 (mkLeaf T_2BS RsFuel))) in exact x).
Definition XB2b : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVB2 (mkLeaf T_2BS RsFuel))) in exact x).
Local Lemma MEMO_12_c : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S87S7G0S0S45S46S6aS47A2S0S45S46S6bS47A2S2S45A1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS62S60S4A5S7G0S0S45S46S6aS47A2S0S45S46S6bS47A2S2S45A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL ECUTS T_2BS true) MEMO_12 (Some [mkLeaf XB2a RsCut; mkLeaf XB2b RsCut]) (@eq_refl _ (sym_run segs FUEL ECUTS T_2BS true)) MEMO_12_c). Qed.
Lemma run_T2B : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS62S60S4A5S7G0S0S45S46S6aS47A2S0S45S46S6bS47A2S2S45A1A3A3A2A3").
Proof. exact MEMO_12_e. Qed.

Definition XB2a4 : sstate := ltac:(let x := eval vm_compute in (set_objs XB2a (firstn 11 (ss_objs XB2a))) in exact x).
Lemma XB2a_sets : ltac2:(tb__ "0|1|
S44S43S9S15A1S26S6aA1SbS15S26S7bA1M0S90S8bS1eS55A1A2A3A3S44S43S9S12A1S1fS7bA1S1fS6aA1A3S43S1cS7bS49S6aG0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition XB2b4 : sstate := ltac:(let x := eval vm_compute in (set_objs XB2b (firstn 11 (ss_objs XB2b))) in exact x).
Lemma XB2b_sets : ltac2:(tb__ "0|1|
S44S43S9S15A1S26S6bA1SbS15S26S7cA1M0S90S8bS1eS55A1A2A3A3S44S43S9S12A1S1fS7cA1S1fS6bA1A3S43S1cS7cS49S6bG0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition rc2_rng (o : sobj) : option (Z * Z) :=
  match ob_base o, ob_lo o, ob_hi o with
  | SLit 0, SLit lo, SLit hi => Some (lo, hi)
  | _, _, _ => None
  end.
Local Definition rc2_inside (o : sobj) (c : cell) : bool :=
  match rc2_rng o, c_off c with
  | Some (lo, hi), SLit a => Z.leb lo a && Z.ltb a hi
  | _, _ => true
  end.
Local Definition rc2_regroup (S : sstate) : sstate :=
  let stray := List.concat (List.map (fun o => List.filter (fun c => negb (rc2_inside o c)) (ob_cells o))
                                     (ss_objs S)) in
  let os := List.map (fun o =>
    mkObj (ob_base o) (ob_lo o) (ob_hi o)
      (List.filter (rc2_inside o) (ob_cells o) ++
       match rc2_rng o with Some _ => List.filter (rc2_inside o) stray | None => nil end)
      (ob_dflt o)) (ss_objs S) in
  mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) os (ss_facts S) (ss_next S) (ss_lenient S).
Definition C_2_raw : sstate := ltac2:(tb__ "0|47|
S25Z2042cS0S10S11P1a4A1S0S10SdZ13680A1S0S10S14S37S11P1M0A1M1SdN80A1M2A3M3S0S10SdZ10800A1S0S10SdZ3a0d0A1S0S10S11P1ccA1S0S10S11P1cdA1S0S10S11P1ceA1S0S10SdZ0A1M4S0S10S11P66M5A1M6S0S10G6S0S10S11P1cfA1S0S10S11P1d0A1S0S10S11P1d1A1S0S10S11P1d2A1S0S10S11P1d3A1S0S10S11P1d4A1S0S10S11P1d5A1S0S10S11P9dA1M7S0S10S14S37G6S14S37G7SdZ6A1A3M8A3M9S0S10S11P9eA1MaS0S10S19S4Q8MbS14S39S11P67A1SdZ8McA1MdA3A3MeS0S10SdZ29fc9A1MfS0S10G4S0S10G4S0S10G4S0S10G4S0S10G4S0S10S11P1d6A1S0S10S11P1d7A1S0S10S11P1d8A1S0S10S11P1d9A1S2S10A1M10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S10S11P182A1S0S10S11P183A1S0S10S11P184A1S0S10S11P185A1S0S10S11P186A1S0S10S11P187A1S0S10S11P188A1S0S10S11P189A1S0S10S11P80A1S0S10S11P81A1S0S10S11P18cA1S0S10S11P18dA1S0S10S11P18eA1S0S10S11P18fA1S0S10S11P190A1S0S10S11P191A1S0S10S11P192A1S0S10S11P193A1S0S10S11P8aA1S0S10S11P8bA1S0S10S11P8cA1S0S10S11P8dA1S0S10S11P8eA1S0S10S11P8fA1S0S10S11P90A1S0S10S11P91A1S0S10S11P92A1S0S10S11P93A1S0S10S11P19eA1S0S10S11P19fA1S0S10S11P1a0A1S0S10S11P1a1A1G10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S21SaS10A1S0S15S16S14S37G1SdNd0A1A3SdNfff30A1G4S2SeA1M11S18A5S0S15S16G3SdN50A1M12G4S0SeSfSdN48A1M13GcG4A3S0SeSfSdN40A1M14GcGfA3S0SeSfSdN38A1M15GcGeA3S0SeSfSdN30A1M16GcGaA3S0SeSfSdN28A1M17GcG9A3S0SeSfSdN20A1M18GcG7A3S0SeSfSdN18A1M19GcG6A3S0SeSfSdN10A1M1aGcS14S37G6SdZ2A1M1bA3A3S0SeSfSdN8A1M1cGcSdZ135f8A1A3G11A3A3A3A3A3A3A3A3A3S18A5S0S15S16G6G4S11P65M1dA1M1eG11S18A5S0S15S16G1G2G4S0SeSfSdN78A1GcG4A3S0SeSfSdN70A1GcG4A3S0SeSfSdN68A1GcG4A3S0SeSfSdN60A1GcG4A3S0SeSfSdN58A1GcS14S37G1SdZ20A1M1fA3M20A3S0SeSfG12GcSdZ13484A1A3S0SeSfG13GcG1bA3S0SeSfG14GcS14S37G1GdA3M21A3S0SeSfG15GcSdZ1fc3cA1A3S0SeSfG17GcG4A3S0SeSfG18GcG4A3S0SeSfG19GcG4A3S0SeSfG1aGcG4A3S0SeSfG1cGcG4A3S0SeSfG2GcG4A3S0SeSfG16GcG21A3G11A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S20A5S0S15S16G4SdZ28cb0A1SdZ28d50A1G11S1aA5S0S15S16G4SdZ28d58A1GfS0SeSfSdZ29e80A1Z4M22SdZ5A1A3S0SeSfSdZ29ea8A1GcSdZ5a7a2A1A3S0SeSfSdZ29eb8A1GcSdZ5a7a0A1M23A3S0SeSfSdZ29ea0A1GcSdZ5aba0A1M24A3S0SeSfSdZ29ec8A1GcSdZ22224A1A3S0SeSfSdZ29e90A1GcG4A3S0SeSfSdZ29e88A1GcG4A3S0SeSfSdZ29f10A1G22SdZffffffffffffffffA1M25A3S0SeSfSdZ29f08A1G22G25A3S0SeSfSdZ29f80A1Z1M26SdG26A1M27A3G11A3A3A3A3A3A3A3A3A3A3S1aA5S0S15S16G4GfSdZ39fc9A1M28G11S18A5S0S15S16G4G28SdZ3a02cA1S0SeSfSdZ39fd4A1G26G4A3S0SeSfSdZ39fd0A1G26G27A3S0SeSfSdZ3a020A1GcG4A3S0SeSfSdZ3a018A1GcSdZ3a008A1M29A3S0SeSfSdZ3a010A1GcG29A3S0SeSfSdZ3a028A1G22S11P1aA1M2aA3S0SeSfG29GcG29A3S0SeSfSdZ5a100A1GcGdA3S0SeSfSdZ5a108A1GcG4A3S0SeSfSdZ5a0f8A1GcG4A3S0SeSfSdZ3a000A1GcG20A3G11A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S15S16G4SdZ3a030A1M2bSdZ5a338A1S0SeSfSdZ5a118A1G22G27A3S0SeSfSdZ5a230A1GcSdZ138acA1A3S0SeSfSdZ5a130A1GcSdZ20080A1A3S0SeSfSdZ5a120A1GcSdZ5a128A1A3S0SeSfSdZ3a0c0A1GcS14S3bS19S3GbS19S4Q20M2cS11P9A1M2dA3M2eA3S14S3bS14S3cS19S3Q10S14S39G2eSdZ10M2fA1M30A3A3G30A3S14S3cS19S3G2cS19S4G2cS14S39G2dG1fA3A3A3G1fA3A3A3A3S0SeSfSdZ3a080A1M31GcG31A3S0SeSfSdZ3a0a0A1GcSdZ5a390A1A3S0SeSfG2bG22G1bA3S0SeSfSdZ3a0c8A1GcSdZ3a0e0A1M32A3S0SeSfG32GcG4A3G11A3A3A3A3A3A3A3A3A3A3S1aA5S0
S15S16G4SdZ5a778A1G23G11S1aA5S0S15S16G4G23G24S0SeSfSdZ5a7a1A1G26SdZaA1A3S0SeSfG23G26SdZ30A1A3G11A3A3S18A5S2S15A1A3A3A3A3A3A3A3A3A3A3A3S0S12S13G7SdZ7fffA1A2S0S12S13GaSdZ3fffffaA1A2S0S12S13G8S11P64A1M33A2S0S12S23G33S14S37GaG8A3A2S0S12S13S14S37G8GaA3G1eA2S0S12S13G33G1eA2S0S12S13SdZ10000A1G1eA2S0S12S13G1eSdZ4000000A1A2S0S12S1bG1dG2fA2S0S12S1bG5G22A2S0S12S1dS17S3aG6G4A3A1S0S12S13SdZ1000A1M34G6A2S0S12S13S14S37G6G1eA3SdZ7fffff800000A1M35A2S0S12S13S11P1eA1M36S14S37G1SdN800000A1A3M37A2S0S12S13G37G36A2S0S12S13SdZ7fff7f800000A1M38G36A2S0S12S13G36G35A2S0S12S13G1S11P4M39A1M3aA2S0S12S13G1S11P6M3bA1M3cA2S0S12S13SdZ7fff80000000A1M3dS11P19A1M3eA2S0S12S13G3eSdZ800000400000A1A2S0S12S13G27G2aA2S0S12S24G2aSdZ400000A1A2S0S12S1dS17S3dS19S3GbS22P2S11P15A1M3fG26A3A3M40G4A3A1S0S12S1dS17S3aG40SdZ2fA1A3A1S0S12S13G3fS11P5A1M41A2S0S12S13G3fSdZ1ffffA1M42A2S0S12S1bG0G22A2S0S12S13G3dG1A2S0S12S13G1SdZ7fffffffff20A1A2S0S12S13G27G1bA2S0S12S13G1bSdZ400A1A2S0S12S13S11P3A1SdZ100A1A2S0S12S13G3dG3aA2S0S12S13S14S37G3aG41A3SdZ7fffffffffefA1A2S0S12S13G41G42A2S0S12S1bG39Z3M43A2S0S12S1bG3bG43A2S0S12S13G3dG3cA2S0S12S13G3cSdZ7ffffffffff0A1A2S0S12S13G38S14S37G1SdN100000A1A3A2S0S12S17S38SdN300A1SdNfff80A1M44A3S0S12S17S38G44SdN10000000000A1A3S0S12S13G27S11P9fA1M45A2S0S12S13G45SdG22A1A2S0S12S13G34S11Pf0A1M46A2S0S12S13G46G35A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P1daS3A9").
Definition C_2 : sstate := Eval vm_compute in rc2_regroup C_2_raw.
Definition s_CAa2 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XA2a4 C_2) in exact x).
Definition s_CAb2 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XA2b4 C_2) in exact x).
Definition s_CBa2 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XB2a4 C_2) in exact x).
Definition s_CBb2 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XB2b4 C_2) in exact x).
Lemma ent_C2 : ltac2:(tb__ "0|0|
S44S43S8S99S75S56S7fA3S4A3S44S43S8S99S78S56S80A3S4A3S44S43S8S99S7bS56S81A3S4A3S43S8S99S7cS56S82A3S4A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma ent_C2_props : ltac2:(tb__ "0|1|
S44S43S8S8eS7fP1fM0A2S4A3S44S43S8S8eS80G0A2S4A3S44S43S8S8eS81G0A2S4A3S44S43S8S8eS82G0A2S4A3S44S43S8S9fS7fS96S96A3S4A3S44S43S8S9fS80S96S96A3S4A3S44S43S8S9fS81S96S96A3S4A3S43S8S9fS82S96S96A3S4A3A2A2A2A2A2A2A2").
Proof. repeat (split; [vm_cast_no_check (@eq_refl bool true)|]). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_2_shape : ltac2:(tb__ "0|0|
S44S43S42S29S56A1SaaA3S44S43S8S27S56A1S3A3S43S10S28S56ZaA2S11P66A1A3A2A2"). Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S5S1cA1") := ltac2:(tb__ "0|1|
S4dS56S0S4cS4eU0M0A1S0S4cS4eU1A1S0S4cS4fG0A1S2S4cA1A3A3A3A2").
Definition C_2m : sstate := ltac:(let x := eval vm_compute in (xget C_2 (MEMO_13)) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = Some C_2m. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S43S5S1cA1S4dS56S0S4cS4eU0M0A1S0S4cS4eU1A1S0S4cS4fG0A1S2S4cA1A3A3A3A2S7S1cS70A2A3").
Proof. exact (@eq_trans _ (apply_xforms C_2 [XRebase 0; XRebase 1; XMerge 0]) MEMO_13 (Some C_2m) (@eq_refl _ (apply_xforms C_2 [XRebase 0; XRebase 1; XMerge 0])) MEMO_13_c). Qed.
Lemma xs_C2_ok : ltac2:(tb__ "0|1|
S43S5S1cA1S4dS56S0S4cS4eU0M0A1S0S4cS4eU1A1S0S4cS4fG0A1S2S4cA1A3A3A3A2S7S1cS70A2A3"). Proof. exact MEMO_13_e. Qed.
Local Definition MEMO_14 := unbase_obj_at C_2m 0 (-128).
Definition C_2x : sstate := ltac:(let x := eval vm_compute in (match MEMO_14 with Some s => s | None => C_2m end) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = Some C_2x. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S43S5S1cA1S94S70U0N80A3S7S1cS53A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at C_2m 0 (-128)) MEMO_14 (Some C_2x) (@eq_refl _ (unbase_obj_at C_2m 0 (-128))) MEMO_14_c). Qed.
Lemma unb_C2 : ltac2:(tb__ "0|0|
S43S5S1cA1S94S70U0N80A3S7S1cS53A2A3"). Proof. exact MEMO_14_e. Qed.
Definition s_ff2 : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_2x PreF) in exact x).
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S5S9S15A1A1") := ltac2:(tb__ "0|0|
S98S53S97S5aA3").
Definition R_ff2 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_15 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = Some R_ff2. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S53S97S5aA3S7G0S5fA2A3").
Proof. exact (@eq_trans _ (entails_fr C_2x PreF s_ff2) MEMO_15 (Some R_ff2) (@eq_refl _ (entails_fr C_2x PreF s_ff2)) MEMO_15_c). Qed.
Lemma efr_ff2 : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S53S97S5aA3S7G0S5fA2A3"). Proof. exact MEMO_15_e. Qed.
Lemma chk_ff2 : ltac2:(tb__ "0|1|
S44S43S8Sb0S53S97S5aS5fS0S1cS9bS9aA1S2S1cA1A3A5S4A3S44S43S8Sa0S1fS53A1M0S96S7S6U0A2Sa8S5fA5S4A3S43S8Sb4S12S35S1dS17S3aS11P66A1SdZ0A1A3A1A1G0A3S4A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ true) | split; [vm_cast_no_check (@eq_refl _ true) | vm_cast_no_check (@eq_refl _ true)]]. Qed.
Lemma s_ff2_vals : ltac2:(tb__ "0|0|
S44S43S10S8dS5aPcA2S11P66A1A3S44S43S10S8dS5aPdA2S11P65A1A3S44S43S10S8dS5aPaA2S14S37S11P1A1SdN80A1A3A3S43S10S8dS5aPfA2SdNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_2x_shape : ltac2:(tb__ "0|0|
S44S43S42S29S53A1SaaA3S44S43S41S1eS53A1S1eS56A1A3S44S43S9S12A1S1fS53A1S1fS56A1A3S43S8S27S53A1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
S9eS53S5aS5fS9bS9aA1A4").
Definition T_2f : sstate := ltac:(let x := eval vm_compute in (MEMO_16) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = T_2f. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S43S1cS9eS53S5aS5fS9bS9aA1A4S58A3").
Proof. exact (@eq_trans _ (T_after C_2x s_ff2 R_ff2 (L_free EC_U)) MEMO_16 (T_2f) (@eq_refl _ (T_after C_2x s_ff2 R_ff2 (L_free EC_U))) MEMO_16_c). Qed.
Lemma T_2f_eq : ltac2:(tb__ "0|0|
S43S1cS9eS53S5aS5fS9bS9aA1A4S58A3"). Proof. exact MEMO_16_e. Qed.
Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|1|
S91S58S90S8bS1eS58A1M0A2S9cG0A1A3").
Definition T_2fS : sstate := ltac:(let x := eval vm_compute in (MEMO_17) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = T_2fS. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|1|
S43S1cS91S58S90S8bS1eS58A1M0A2S9cG0A1A3S5dA3").
Proof. exact (@eq_trans _ (app_objs T_2f (statics_objs C_U (ss_next T_2f)) (Pos.succ (ss_next T_2f))) MEMO_17 (T_2fS) (@eq_refl _ (app_objs T_2f (statics_objs C_U (ss_next T_2f)) (Pos.succ (ss_next T_2f)))) MEMO_17_c). Qed.
Lemma T_2fS_eq : ltac2:(tb__ "0|1|
S43S1cS91S58S90S8bS1eS58A1M0A2S9cG0A1A3S5dA3"). Proof. exact MEMO_17_e. Qed.
Lemma swf_T_2fS : swf T_2fS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_T2f : ltac2:(tb__ "0|0|
S43S8SbaS8bS1fS58A1S2ScS10S10A2A1S26S58A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_2fS_shape : ltac2:(tb__ "0|0|
S44S43S41S1eS5dA1S9cS1eS58A1A1A3S43S8S27S5dA1S3A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S5S9S45A1A1") := ltac2:(tb__ "0|0|
S48S8cS8fS2S42A1S5dS4A5").
Definition LVF2 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_18 with Some l => l | None => [] end) in exact x).

Definition E_fl2 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVF2 (mkLeaf T_2fS RsFuel))) in exact x).
Local Lemma MEMO_18_c : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S88S7G0S0S45S46S52S4aA2S2S45A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_18). Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS2S42A1S5dS4A5S7G0S0S45S46S52S4aA2S2S45A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_2fS true) MEMO_18 (Some [mkLeaf E_fl2 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_2fS true)) MEMO_18_c). Qed.
Lemma run_T2f : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS2S42A1S5dS4A5S7G0S0S45S46S52S4aA2S2S45A1A3A2A3").
Proof. exact MEMO_18_e. Qed.
Lemma E_fl2_shape : ltac2:(tb__ "0|1|
S44S43S42S29S52A1SadA3S44S43S10S28S52ZdA2SdZ2A1M0A3S44S43S10S28S52ZcA2G0A3S43S8S27S52A1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_fl2 : list xform := ltac2:(tb__ "0|2|
S0S4cS50U0M0SdN18A1A2S0S4cS50G0SdN38A1A2S0S4cS50U5M1SdSb5Sa6Z4A2A1A2S0S4cS50G1SdSa6A1A2S0S4cS50UcSdSb5Sa5Z2A2A1A2S2S4cA1A3A3A3A3A3").
Local Definition MEMO_19 := apply_xforms E_fl2 xs_fl2.
Definition E_fl21 : sstate := ltac:(let x := eval vm_compute in (xget E_fl2 (MEMO_19)) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = Some E_fl21. Proof. vm_cast_no_check (@eq_refl _ MEMO_19). Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS52S84A2S7S1cS71A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_fl2 xs_fl2) MEMO_19 (Some E_fl21) (@eq_refl _ (apply_xforms E_fl2 xs_fl2)) MEMO_19_c). Qed.
Lemma xs_fl2_ok : ltac2:(tb__ "0|0|
S43S5S1cA1S4dS52S84A2S7S1cS71A2A3"). Proof. exact MEMO_19_e. Qed.
Local Definition MEMO_20 := unbase_obj_at E_fl21 1 (-64).
Definition E_fl22 : sstate := ltac:(let x := eval vm_compute in (match MEMO_20 with Some s => s | None => E_fl21 end) in exact x).
Local Lemma MEMO_20_c : MEMO_20 = Some E_fl22. Proof. vm_cast_no_check (@eq_refl _ MEMO_20). Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|0|
S43S5S1cA1S94S71U1N40A3S7S1cS6cA2A3").
Proof. exact (@eq_trans _ (unbase_obj_at E_fl21 1 (-64)) MEMO_20 (Some E_fl22) (@eq_refl _ (unbase_obj_at E_fl21 1 (-64))) MEMO_20_c). Qed.
Lemma unb_fl2 : ltac2:(tb__ "0|0|
S43S5S1cA1S94S71U1N40A3S7S1cS6cA2A3"). Proof. exact MEMO_20_e. Qed.

Definition O10_fl2 : sobj := ltac:(let x := eval vm_compute in (nth 12 (ss_objs E_fl22) dummy_obj) in exact x).
Local Definition MEMO_21 := obj_to_list E_fl22 12 5.
Definition E_fl23 : sstate := ltac:(let x := eval vm_compute in (MEMO_21) in exact x).
Local Lemma MEMO_21_c : MEMO_21 = E_fl23. Proof. vm_cast_no_check (@eq_refl _ MEMO_21). Qed.
Local Lemma MEMO_21_e : obj_to_list E_fl22 12 5 = E_fl23.
Proof. exact (@eq_trans _ (obj_to_list E_fl22 12 5) MEMO_21 (E_fl23) (@eq_refl _ (obj_to_list E_fl22 12 5)) MEMO_21_c). Qed.
Lemma E_fl23_eq : obj_to_list E_fl22 12 5 = E_fl23. Proof. exact MEMO_21_e. Qed.
Definition BL_fl2 : list bexp := ltac2:(tb__ "0|0|
S0Sa1Sa2Z30A1S0Sa1Sa2ZaA1S2Sa1A1A3A3").
Lemma obj10_fl2 : ltac2:(tb__ "0|5|
S44S43S5S15A1Sb2S15S26S6cA1UcA3S7S15S6eA2A3S44S43S10S33S6eA1SdSa5A1M0A3S44S43S10S32S6eA1SdSb5Sa5Z2M1A2A1A3S44S43S8S2eS31S6eA1M2A1S4A3S44S43S8S2fG2A1S3A3S44S43S5S9Sa1A1M3A1Sa4S30S6eA1G0Z0Sb6G1A1A4S7G3S83A2A3S36S43S9SbdQ8A1M4A1Sb8Sa1G4Sa3R1A1S83A4SbcZ1A1A3Frho;A2A2A2A2A2A2").
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [vm_cast_no_check (@eq_refl _ (Some BL_fl2)) | intros rho; reflexivity]]]]]]. Qed.
Lemma norl_fl2 : ltac2:(tb__ "0|0|
S44S43S8Sb9P5S6cA2S3A3S43S8Sb9P6S6dA2S3A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Definition O_b2z : sobj := ltac2:(tb__ "0|1|
S16SdZ0A1M0G0G0S2SeA1S2bP6A1A5").
Definition E_fl2c : sstate := ltac:(let x := eval vm_compute in (app_objs E_fl23 [O_b2z] (ss_next E_fl23)) in exact x).
Lemma E_fl2c_eq : ltac2:(tb__ "0|0|
S43S1cS91S6dS0S15S8aS2S15A1A3S1eS6dA1A3S57A3"). Proof. reflexivity. Qed.
Lemma swf_E_fl2c : swf E_fl2c = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_fl2_facts : ltac2:(tb__ "0|3|
S44S43S9S12A1M0S1fS57A1S1fS52A1M1A3S44S43G0S1fS6dA1G1A3S44S43S41S1eS57A1S1eS52A1M2A3S44S43S41S1eS6dA1G2A3S44S43S41S1eS6cA1G2A3S43S41G2S1eS5dA1A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition s_fl2 : wsub := ltac2:(tb__ "0|7|
S0ScS41S10A2M0S1S41S10PcSdZ5a7a0A1A4M1S0G0S1S41S10PdSdZ2A1M2A4M3S0G0S1S41S10PeSdZ0A1M4A4M5S0G0S1S41S10PfG4A4M6S0G0G5S0G0G3S0G0G1S0G0S1S41S10P5bS11P1a1A1A4S0G0S1S41S10P5aS11P1a0A1A4S0G0S1S41S10P59S11P19fA1A4S0G0S1S41S10P58S11P19eA1A4S0G0S1S41S10P57S11P93A1A4S0G0S1S41S10P56S11P92A1A4S0G0S1S41S10P55S11P91A1A4S0G0S1S41S10P54S11P90A1A4S0G0S1S41S10P53S11P8fA1A4S0G0S1S41S10P52S11P8eA1A4S0G0S1S41S10P51S11P8dA1A4S0G0S1S41S10P50S11P8cA1A4S0G0S1S41S10P4fS11P8bA1A4S0G0S1S41S10P4eS11P8aA1A4S0G0S1S41S10P4dS11P193A1A4S0G0S1S41S10P4cS11P192A1A4S0G0S1S41S10P4bS11P191A1A4S0G0S1S41S10P4aS11P190A1A4S0G0S1S41S10P49S11P18fA1A4S0G0S1S41S10P48S11P18eA1A4S0G0S1S41S10P47S11P18dA1A4S0G0S1S41S10P46S11P18cA1A4S0G0S1S41S10P45S11P81A1A4S0G0S1S41S10P44S11P80A1A4S0G0S1S41S10P43S11P189A1A4S0G0S1S41S10P42S11P188A1A4S0G0S1S41S10P41S11P187A1A4S0G0S1S41S10P40S11P186A1A4S0G0S1S41S10P3fS11P185A1A4S0G0S1S41S10P3eS11P184A1A4S0G0S1S41S10P3dS11P183A1A4S0G0S1S41S10P3cS11P182A1A4S0G0S1S41S10P33S11P1f9A1A4S0G0S1S41S10P32S11P1f8A1A4S0G0S1S41S10P31S11P1f7A1A4S0G0S1S41S10P30S11P1f6A1A4S0G0S1S41S10P2fG4A4S0G0S1S41S10P2eG4A4S0G0S1S41S10P2dG4A4S0G0S1S41S10P2cG4A4S0G0S1S41S10P2bG4A4S0G0S1S41S10P29SdZ5a338A1A4S0G0S1S41S10P28G4A4S0G0S1S41S10P24S11P1eaA1A4S0G0S1S41S10P23G4A4S0G0S1S41S10P22G4A4S0G0S1S41S10P21G2A4S0G0G6S0G0S1S41S10P1bS11P1e1A1A4S0G0S1S41S10P1aS11P1e0A1A4S0G0S1S41S10P19S11P1dfA1A4S0G0S1S41S10P18SdZ3a0d0A1A4S0G0S1S41S10PaS14S37S11P1A1SdNc0A1A3A4S0G0S1S41S10P15SdZ22500A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_22 : ltac2:(tb__ "0|0|
S5S9S15A1A1") := ltac2:(tb__ "0|0|
S98S57SacS5bA3").
Definition R_fl2 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_22 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = Some R_fl2. Proof. vm_cast_no_check (@eq_refl _ MEMO_22). Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S57SacS5bA3S7G0S64A2A3").
Proof. exact (@eq_trans _ (entails_fr E_fl2c WLoutS.Pre_wl2 s_fl2) MEMO_22 (Some R_fl2) (@eq_refl _ (entails_fr E_fl2c WLoutS.Pre_wl2 s_fl2)) MEMO_22_c). Qed.
Lemma efr_fl2 : ltac2:(tb__ "0|1|
S43S5S9S15A1M0A1S98S57SacS5bA3S7G0S64A2A3"). Proof. exact MEMO_22_e. Qed.
Lemma chk_fl2 : ltac2:(tb__ "0|0|
S43S8Sb1S57SacS5bS64S0S45S46SabS47A2S2S45A1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_fl2 : ltac2:(tb__ "0|0|
S43S8Sb3S12S2cS1eS57A1A1S1fS52A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_fl2_vals : ltac2:(tb__ "0|1|
S44S43S10S8dS5bPcA2SdSa5A1A3S44S43S10S8dS5bPdA2SdZ2A1A3S44S43S10S8dS5bPeA2SdZ0A1M0A3S43S10S8dS5bPfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_23 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
SafS5bP5cSabS1eS57A1S64A5").
Definition T_fl2D : sstate := ltac:(let x := eval vm_compute in (MEMO_23) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = T_fl2D. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : ltac2:(tb__ "0|0|
S43S1cSafS5bP5cSabS1eS57A1S64A5S65A3").
Proof. exact (@eq_trans _ (import_post s_fl2 92 WLoutS.D (ss_next E_fl2c) R_fl2) MEMO_23 (T_fl2D) (@eq_refl _ (import_post s_fl2 92 WLoutS.D (ss_next E_fl2c) R_fl2)) MEMO_23_c). Qed.
Lemma T_fl2D_eq : ltac2:(tb__ "0|0|
S43S1cSafS5bP5cSabS1eS57A1S64A5S65A3"). Proof. exact MEMO_23_e. Qed.
Local Definition MEMO_24 : ltac2:(tb__ "0|0|
S1c") := ltac2:(tb__ "0|0|
SaeS1fS52A1S65A2").
Definition T_fl2E : sstate := ltac:(let x := eval vm_compute in (MEMO_24) in exact x).
Local Lemma MEMO_24_c : MEMO_24 = T_fl2E. Proof. vm_cast_no_check (@eq_refl _ MEMO_24). Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|0|
S43S1cSaeS1fS52A1S65A2S61A3").
Proof. exact (@eq_trans _ (add_facts (ss_facts E_fl2) T_fl2D) MEMO_24 (T_fl2E) (@eq_refl _ (add_facts (ss_facts E_fl2) T_fl2D)) MEMO_24_c). Qed.
Lemma T_fl2E_eq : ltac2:(tb__ "0|1|
S44S43S1cSaeS1fS52A1M0S65A2S61A3S44S43S8Sb3S12S2cS1eS65A1A1G0A3S4A3S44S43S8S27S61A1S3A3S43S8S9dS1eS57A1S1eS61A1A2S4A3A2A2A2").
Proof. split; [exact MEMO_24_e | split; [vm_cast_no_check (@eq_refl _ true) | split; reflexivity]]. Qed.

Local Definition MEMO_25 : ltac2:(tb__ "0|0|
S5S9S45A1A1") := ltac2:(tb__ "0|0|
S48S8cS8fS2S42A1S61S4A5").
Definition E_x2 : sstate := ltac:(let x := eval vm_compute in (lf0 T_fl2E (MEMO_25) 0) in exact x).

Local Lemma MEMO_25_c : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S89S7G0S0S45S46S63S4aA2S2S45A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_25). Qed.
Local Lemma MEMO_25_e : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS2S42A1S61S4A5S7G0S0S45S46S63S4aA2S2S45A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_fl2E true) MEMO_25 (Some [mkLeaf E_x2 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_fl2E true)) MEMO_25_c). Qed.
Lemma run_fl2 : ltac2:(tb__ "0|1|
S43S5S9S45A1M0A1S48S8cS8fS2S42A1S61S4A5S7G0S0S45S46S63S4aA2S2S45A1A3A2A3").
Proof. exact MEMO_25_e. Qed.
Lemma cert_x2 : ltac2:(tb__ "0|0|
S44S43S5S3fA1S4bS8cS29S63A1A2S7S3fS40A2A3S44S43S10S28S63Z11A2SdZ5eA1A3S43S10S28S63ZaA2SdZ0A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.

