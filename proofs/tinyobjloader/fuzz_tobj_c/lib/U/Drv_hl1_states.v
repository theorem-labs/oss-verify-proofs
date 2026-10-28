(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "false"; "nil"; "bool"; "option"; "Some"; "list"; "None"; "app"; "prod"; "fst"; "andb"; "nat"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "SVar"; "sprop"; "SPUle"; "SAlu"; "sobj"; "mkObj"; "DUnknown"; "SPBranch"; "SExt"; "sstate"; "DImage"; "SPAlign"; "ss_next"; "SPNot"; "ss_objs"; "ss_facts"; "ss_lenient"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPEq"; "SPUlt"; "mkSS"; "reg_sv"; "ss_pc"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SRL"; "ALU_OR"; "ALU_SLL"; "BC_EQ"; "BC_NE"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "mkLeaf"; "sym_run"; "set_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface"; "FZ_U"; "L_fuzz"; "fz_rets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl1_states"; "S_1"; "S_2"; "S_3"; "s_fz1"; "s_fz2"; "s_fz3"; "P_1"; "P_2"; "P_3"; "N_2"; "N_3"; "P_1S"; "P_2S"; "P_3S"; "R_fz1"; "R_fz2"; "R_fz3"; "X_2"; "X_3"; "X_4"; "N_4"; "NX1"; "NX2"; "NX3"; "MEMO_12"; "MEMO_4"; "MEMO_8"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "app_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "PreFZ"; "LCUTS"; "O_payL"; "tvL"; "PDfz"; "N_1"; "robj_inwi"; "NX0"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "call_checkT"; "new_objs_tv"; "robjs_check"; "tvL_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.TAddr"; "fz_entry_"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"].
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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code Drv_wins.
Require Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Drv_hl0_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr TAddr LAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S_1 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc N_1) (ss_regs N_1) (ss_fregs N_1) (ss_fcsr N_1) (ss_resv N_1) (firstn 13 (ss_objs N_1)) L_facts (ss_next N_1) false) in exact x).
Lemma ent_S1 : ltac2:(tb__ "0|0|
S37S5S7aS3eS67S22S43A1A2S43S4SbS2eS13A2A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma N_1_objs : ltac2:(tb__ "0|0|
S38S37S8S18A1S22S67A1SaS18S22S43A1S60S42S69A2A3A3S37S2eS20S67A1S20S43A1A3A2").
Proof. split; reflexivity. Qed.
Lemma S_1_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS43A1S7cA3S38S37S5S24S43A1S3A3S38S37S6S18A1S6aS18S22S43A1U2A3S7S18S64A2A3S38S37S13S2bS43ZaA2S14Pf0A1A3S38S37S13S2bS43ZbA2S14P9eA1A3S37S5S2dS43A1S2A3A2A2A2A2A2").
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | vm_cast_no_check (@eq_refl bool true)]]]]]. Qed.

Definition s_fz1 : wsub := ltac:(let x := eval vm_compute in ((15%positive, SLit (-1048000)) :: infer_sub 1 S_1 PreFZ) in exact x).
Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S6S8S18A1A1") := ltac2:(tb__ "0|0|
S79S43S62S46A3").
Definition R_fz1 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_1 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = Some R_fz1. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S43S62S46A3S7G0S51A2A3").
Proof. exact (@eq_trans _ (entails_fr S_1 PreFZ s_fz1) MEMO_1 (Some R_fz1) (@eq_refl _ (entails_fr S_1 PreFZ s_fz1)) MEMO_1_c). Qed.
Lemma efr_fz1 : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S43S62S46A3S7G0S51A2A3"). Proof. exact MEMO_1_e. Qed.

Lemma chk_fz1 : ltac2:(tb__ "0|4|
S38S37S5S6fS42P1fS43S62S46S51S78SbS1dS8SbS13S13A2A1M0A2M1S1dScS1dG0A2S66A4A7S2A3S38S37S5S7dS46S5eA2S2A3S38S37S5S6cG1G1SdS72S5eS46S20S43A1ScS1dG0R1A3M2SfS1dG0R1A3M3A5S70S62G2G3A3A2Ld;S66A3S2A3S37S5S71S23S43A1S65S9SeA1S68S51A5S2A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma s_fz1_vals : ltac2:(tb__ "0|0|
S38S37S13S6dS46PcA2S14Pf0A1A3S38S37S13S6dS46PdA2S14P9eA1A3S38S37S13S6dS46PaA2S17S30S14P1A1S10Nd0A1A3A3S37S13S6dS46PfA2S10Nffdc0A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma S_1_call_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS43A1S7cA3S38S37S5S24S43A1S3A3S37S6S18A1S6aS18S22S43A1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_2 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S6eS5eS43S46S51S40S3fS75S2fU0S41S3fA1Z0A4A2A5").
Definition P_1 : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = P_1. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S37S1dS6eS5eS43S46S51S40S3fS75S2fU0S41S3fA1Z0A4A2A5S49A3").
Proof. exact (@eq_trans _ (T_afterN NF S_1 s_fz1 R_fz1 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0))) MEMO_2 (P_1) (@eq_refl _ (T_afterN NF S_1 s_fz1 R_fz1 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0)))) MEMO_2_c). Qed.
Lemma P_1_eq : ltac2:(tb__ "0|0|
S37S1dS6eS5eS43S46S51S40S3fS75S2fU0S41S3fA1Z0A4A2A5S49A3"). Proof. exact MEMO_2_e. Qed.

Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|1|
S61S49S60S42S20S49A1M0A2S5fG0A1A3").
Definition P_1S : sstate := ltac:(let x := eval vm_compute in (MEMO_3) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = P_1S. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|1|
S37S1dS61S49S60S42S20S49A1M0A2S5fG0A1A3S4eA3").
Proof. exact (@eq_trans _ (app_objs P_1 (statics_objs C_U (ss_next P_1)) (Pos.succ (ss_next P_1))) MEMO_3 (P_1S) (@eq_refl _ (app_objs P_1 (statics_objs C_U (ss_next P_1)) (Pos.succ (ss_next P_1)))) MEMO_3_c). Qed.
Lemma P_1S_eq : ltac2:(tb__ "0|1|
S37S1dS61S49S60S42S20S49A1M0A2S5fG0A1A3S4eA3"). Proof. exact MEMO_3_e. Qed.
Lemma swf_P_1S : swf P_1S = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_1 : ltac2:(tb__ "0|1|
S37S5S7bS42S23S49A1S65SaS18S76S18U2S22S49A1M0A3S77S18U3G0A3A3A4S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma P_1S_shape : ltac2:(tb__ "0|0|
S38S37S2eS20S4eA1S5fS20S49A1A1A3S38S37S5S24S4eA1S3A3S37S6S18A1S6aS18S22S49A1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Definition NX1 : positive := ltac:(let x := eval vm_compute in (ss_next P_1) in exact x).
Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S6S8S3aA1A1") := ltac2:(tb__ "0|0|
S3dS73S74S63S4eS2A5").
Definition LVS_1 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_4 with Some l => l | None => [] end) in exact x).
Definition N_2 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVS_1 (mkLeaf P_1S RsFuel))) in exact x).
Definition X_2 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVS_1 (mkLeaf P_1S RsFuel))) in exact x).
Local Lemma MEMO_4_c : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S5cS7G0S0S3aS3cS4cS3bA2S0S3aS3cS54S3bA2S4S3aA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S4eS2A5S7G0S0S3aS3cS4cS3bA2S0S3aS3cS54S3bA2S4S3aA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS P_1S true) MEMO_4 (Some [mkLeaf N_2 RsCut; mkLeaf X_2 RsCut]) (@eq_refl _ (sym_run segs FUEL LCUTS P_1S true)) MEMO_4_c). Qed.
Lemma run_P1 : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S4eS2A5S7G0S0S3aS3cS4cS3bA2S0S3aS3cS54S3bA2S4S3aA1A3A3A2A3").
Proof. exact MEMO_4_e. Qed.
Definition P_1b : sstate := ltac:(let x := eval vm_compute in (T_afterN NF S_1 s_fz1 R_fz1 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0))) in exact x).
Lemma P_1b_eq : T_afterN NF S_1 s_fz1 R_fz1 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0)) = P_1b.
Proof. vm_cast_no_check (@eq_refl _ P_1b). Qed.
Definition P_1bS : sstate := ltac:(let x := eval vm_compute in (app_objs P_1b (statics_objs C_U (ss_next P_1b)) (Pos.succ (ss_next P_1b))) in exact x).
Lemma P_1bS_eq : app_objs P_1b (statics_objs C_U (ss_next P_1b)) (Pos.succ (ss_next P_1b)) = P_1bS.
Proof. vm_cast_no_check (@eq_refl _ P_1bS). Qed.
Lemma swf_P_1bS : swf P_1bS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_1b : robjs_missT_statics C_U (ss_facts P_1b) tvL (firstn 2 (ss_objs P_1b) ++ skipn 3 (ss_objs P_1b)) = true.
Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma run_P1b : sym_run Code.segs FUEL LCUTS P_1bS true = sym_run Code.segs FUEL LCUTS P_1S true.
Proof. vm_cast_no_check (@eq_refl _ (sym_run Code.segs FUEL LCUTS P_1S true)). Qed.
Lemma posts_1 : ltac2:(tb__ "0|5|
S2fS6bS2fR1S41S3fA1A3S39S1dS1dS39S1dS1dS38S37S1dS6eS5eS43S46S51S40S3fR4A2A5R2A3S38S37S1dS61R2S60S42S20R2A1M0A2S5fG0A1A3R1A3S38S37S5S2dR1A1S2A3S38S37S5S7bS42S23R2A1S65SaS18S76S18U2S22R2A1M1A3M2S77S18U3G1A3M3A3A4S2A3S38S37S8S18A1G1SaS18G2S0S18S64G3A3A3A3S38S37S2eG0S58A3S38S37S2eS20R1A1S5fS58A1A3S38S37S5S24R1A1S3A3S37S6S8S3aA1M4A1S3dS73S74S63R1S2A5S7G4S0S3aS3cS4cS3bA2S0S3aS3cS54S3bA2S4S3aA1A3A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;").
Proof.
  intros r Hr. cbn [fz_rets FZ_U] in Hr.
  destruct Hr as [<-|[<-|[]]]; [exists P_1, P_1S; split; [exact P_1_eq | split; [exact P_1S_eq | split; [exact swf_P_1S | split; [exact missT_P_1 | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact run_P1]]]]]]]] | exists P_1b, P_1bS; split; [exact P_1b_eq | split; [exact P_1bS_eq | split; [exact swf_P_1bS | split; [exact missT_P_1b | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | rewrite run_P1b; exact run_P1]]]]]]]]].
Qed.
Lemma fork_2 : ltac2:(tb__ "0|4|
S38S37S6S15A1M0S6aS15S23S4cA1U0M1A3S7S15S1bS36S17S30S14P9fA1S10N2A1A3S10Z0A1A3M2A2A3S38S37G0S6aS15S23S54A1G1A3S7S15S21G2A1A2A3S38S37S2fS2cS54A1S7eA3S38S37S13S2bS54ZaA2S14Pf1A1A3S38S37S2eS20S54A1S20S4eA1M3A3S37S2eS20S4cA1G3A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition S_2 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc N_2) (ss_regs N_2) (ss_fregs N_2) (ss_fcsr N_2) (ss_resv N_2) (firstn 13 (ss_objs N_2)) L_facts (ss_next N_2) false) in exact x).
Lemma ent_S2 : ltac2:(tb__ "0|0|
S37S5S7aS3eS4cS22S44A1A2S44S4SbS2eS13A2A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma N_2_objs : ltac2:(tb__ "0|0|
S38S37S8S18A1S22S4cA1SaS18S22S44A1S60S42S58A2A3A3S37S2eS20S4cA1S20S44A1A3A2").
Proof. split; reflexivity. Qed.
Lemma S_2_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS44A1S7cA3S38S37S5S24S44A1S3A3S38S37S6S18A1S6aS18S22S44A1U2A3S7S18S64A2A3S38S37S13S2bS44ZaA2S14Pf0A1A3S38S37S13S2bS44ZbA2S14P9eA1A3S37S5S2dS44A1S2A3A2A2A2A2A2").
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | vm_cast_no_check (@eq_refl bool true)]]]]]. Qed.

Definition s_fz2 : wsub := ltac:(let x := eval vm_compute in ((15%positive, SLit (-1048000)) :: infer_sub 1 S_2 PreFZ) in exact x).
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S6S8S18A1A1") := ltac2:(tb__ "0|0|
S79S44S62S47A3").
Definition R_fz2 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_5 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some R_fz2. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S44S62S47A3S7G0S52A2A3").
Proof. exact (@eq_trans _ (entails_fr S_2 PreFZ s_fz2) MEMO_5 (Some R_fz2) (@eq_refl _ (entails_fr S_2 PreFZ s_fz2)) MEMO_5_c). Qed.
Lemma efr_fz2 : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S44S62S47A3S7G0S52A2A3"). Proof. exact MEMO_5_e. Qed.

Lemma chk_fz2 : ltac2:(tb__ "0|4|
S38S37S5S6fS42P1fS44S62S47S52S78SbS1dS8SbS13S13A2A1M0A2M1S1dScS1dG0A2S66A4A7S2A3S38S37S5S7dS47S5eA2S2A3S38S37S5S6cG1G1SdS72S5eS47S20S44A1ScS1dG0R1A3M2SfS1dG0R1A3M3A5S70S62G2G3A3A2Ld;S66A3S2A3S37S5S71S23S44A1S65S9SeA1S68S52A5S2A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma s_fz2_vals : ltac2:(tb__ "0|0|
S38S37S13S6dS47PcA2S14Pf0A1A3S38S37S13S6dS47PdA2S14P9eA1A3S38S37S13S6dS47PaA2S17S30S14P1A1S10Nd0A1A3A3S37S13S6dS47PfA2S10Nffdc0A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma S_2_call_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS44A1S7cA3S38S37S5S24S44A1S3A3S37S6S18A1S6aS18S22S44A1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S6eS5eS44S47S52S40S3fS75S2fU0S41S3fA1Z0A4A2A5").
Definition P_2 : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = P_2. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S37S1dS6eS5eS44S47S52S40S3fS75S2fU0S41S3fA1Z0A4A2A5S4aA3").
Proof. exact (@eq_trans _ (T_afterN NF S_2 s_fz2 R_fz2 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0))) MEMO_6 (P_2) (@eq_refl _ (T_afterN NF S_2 s_fz2 R_fz2 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0)))) MEMO_6_c). Qed.
Lemma P_2_eq : ltac2:(tb__ "0|0|
S37S1dS6eS5eS44S47S52S40S3fS75S2fU0S41S3fA1Z0A4A2A5S4aA3"). Proof. exact MEMO_6_e. Qed.

Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|1|
S61S4aS60S42S20S4aA1M0A2S5fG0A1A3").
Definition P_2S : sstate := ltac:(let x := eval vm_compute in (MEMO_7) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = P_2S. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|1|
S37S1dS61S4aS60S42S20S4aA1M0A2S5fG0A1A3S4fA3").
Proof. exact (@eq_trans _ (app_objs P_2 (statics_objs C_U (ss_next P_2)) (Pos.succ (ss_next P_2))) MEMO_7 (P_2S) (@eq_refl _ (app_objs P_2 (statics_objs C_U (ss_next P_2)) (Pos.succ (ss_next P_2)))) MEMO_7_c). Qed.
Lemma P_2S_eq : ltac2:(tb__ "0|1|
S37S1dS61S4aS60S42S20S4aA1M0A2S5fG0A1A3S4fA3"). Proof. exact MEMO_7_e. Qed.
Lemma swf_P_2S : swf P_2S = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_2 : ltac2:(tb__ "0|1|
S37S5S7bS42S23S4aA1S65SaS18S76S18U2S22S4aA1M0A3S77S18U3G0A3A3A4S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma P_2S_shape : ltac2:(tb__ "0|0|
S38S37S2eS20S4fA1S5fS20S4aA1A1A3S38S37S5S24S4fA1S3A3S37S6S18A1S6aS18S22S4aA1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Definition NX2 : positive := ltac:(let x := eval vm_compute in (ss_next P_2) in exact x).
Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S6S8S3aA1A1") := ltac2:(tb__ "0|0|
S3dS73S74S63S4fS2A5").
Definition LVS_2 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_8 with Some l => l | None => [] end) in exact x).
Definition N_3 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVS_2 (mkLeaf P_2S RsFuel))) in exact x).
Definition X_3 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVS_2 (mkLeaf P_2S RsFuel))) in exact x).
Local Lemma MEMO_8_c : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S5dS7G0S0S3aS3cS4dS3bA2S0S3aS3cS55S3bA2S4S3aA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S4fS2A5S7G0S0S3aS3cS4dS3bA2S0S3aS3cS55S3bA2S4S3aA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS P_2S true) MEMO_8 (Some [mkLeaf N_3 RsCut; mkLeaf X_3 RsCut]) (@eq_refl _ (sym_run segs FUEL LCUTS P_2S true)) MEMO_8_c). Qed.
Lemma run_P2 : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S4fS2A5S7G0S0S3aS3cS4dS3bA2S0S3aS3cS55S3bA2S4S3aA1A3A3A2A3").
Proof. exact MEMO_8_e. Qed.
Definition P_2b : sstate := ltac:(let x := eval vm_compute in (T_afterN NF S_2 s_fz2 R_fz2 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0))) in exact x).
Lemma P_2b_eq : T_afterN NF S_2 s_fz2 R_fz2 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0)) = P_2b.
Proof. vm_cast_no_check (@eq_refl _ P_2b). Qed.
Definition P_2bS : sstate := ltac:(let x := eval vm_compute in (app_objs P_2b (statics_objs C_U (ss_next P_2b)) (Pos.succ (ss_next P_2b))) in exact x).
Lemma P_2bS_eq : app_objs P_2b (statics_objs C_U (ss_next P_2b)) (Pos.succ (ss_next P_2b)) = P_2bS.
Proof. vm_cast_no_check (@eq_refl _ P_2bS). Qed.
Lemma swf_P_2bS : swf P_2bS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_2b : robjs_missT_statics C_U (ss_facts P_2b) tvL (firstn 2 (ss_objs P_2b) ++ skipn 3 (ss_objs P_2b)) = true.
Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma run_P2b : sym_run Code.segs FUEL LCUTS P_2bS true = sym_run Code.segs FUEL LCUTS P_2S true.
Proof. vm_cast_no_check (@eq_refl _ (sym_run Code.segs FUEL LCUTS P_2S true)). Qed.
Lemma posts_2 : ltac2:(tb__ "0|5|
S2fS6bS2fR1S41S3fA1A3S39S1dS1dS39S1dS1dS38S37S1dS6eS5eS44S47S52S40S3fR4A2A5R2A3S38S37S1dS61R2S60S42S20R2A1M0A2S5fG0A1A3R1A3S38S37S5S2dR1A1S2A3S38S37S5S7bS42S23R2A1S65SaS18S76S18U2S22R2A1M1A3M2S77S18U3G1A3M3A3A4S2A3S38S37S8S18A1G1SaS18G2S0S18S64G3A3A3A3S38S37S2eG0S59A3S38S37S2eS20R1A1S5fS59A1A3S38S37S5S24R1A1S3A3S37S6S8S3aA1M4A1S3dS73S74S63R1S2A5S7G4S0S3aS3cS4dS3bA2S0S3aS3cS55S3bA2S4S3aA1A3A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;").
Proof.
  intros r Hr. cbn [fz_rets FZ_U] in Hr.
  destruct Hr as [<-|[<-|[]]]; [exists P_2, P_2S; split; [exact P_2_eq | split; [exact P_2S_eq | split; [exact swf_P_2S | split; [exact missT_P_2 | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact run_P2]]]]]]]] | exists P_2b, P_2bS; split; [exact P_2b_eq | split; [exact P_2bS_eq | split; [exact swf_P_2bS | split; [exact missT_P_2b | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | rewrite run_P2b; exact run_P2]]]]]]]]].
Qed.
Lemma fork_3 : ltac2:(tb__ "0|4|
S38S37S6S15A1M0S6aS15S23S4dA1U0M1A3S7S15S1bS36S17S30S14P9fA1S10N3A1A3S10Z0A1A3M2A2A3S38S37G0S6aS15S23S55A1G1A3S7S15S21G2A1A2A3S38S37S2fS2cS55A1S7eA3S38S37S13S2bS55ZaA2S14Pf1A1A3S38S37S2eS20S55A1S20S4fA1M3A3S37S2eS20S4dA1G3A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition S_3 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc N_3) (ss_regs N_3) (ss_fregs N_3) (ss_fcsr N_3) (ss_resv N_3) (firstn 13 (ss_objs N_3)) L_facts (ss_next N_3) false) in exact x).
Lemma ent_S3 : ltac2:(tb__ "0|0|
S37S5S7aS3eS4dS22S45A1A2S45S4SbS2eS13A2A1A3S2A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma N_3_objs : ltac2:(tb__ "0|0|
S38S37S8S18A1S22S4dA1SaS18S22S45A1S60S42S59A2A3A3S37S2eS20S4dA1S20S45A1A3A2").
Proof. split; reflexivity. Qed.
Lemma S_3_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS45A1S7cA3S38S37S5S24S45A1S3A3S38S37S6S18A1S6aS18S22S45A1U2A3S7S18S64A2A3S38S37S13S2bS45ZaA2S14Pf0A1A3S38S37S13S2bS45ZbA2S14P9eA1A3S37S5S2dS45A1S2A3A2A2A2A2A2").
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | vm_cast_no_check (@eq_refl bool true)]]]]]. Qed.

Definition s_fz3 : wsub := ltac:(let x := eval vm_compute in ((15%positive, SLit (-1048000)) :: infer_sub 1 S_3 PreFZ) in exact x).
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S6S8S18A1A1") := ltac2:(tb__ "0|0|
S79S45S62S48A3").
Definition R_fz3 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_9 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some R_fz3. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S45S62S48A3S7G0S53A2A3").
Proof. exact (@eq_trans _ (entails_fr S_3 PreFZ s_fz3) MEMO_9 (Some R_fz3) (@eq_refl _ (entails_fr S_3 PreFZ s_fz3)) MEMO_9_c). Qed.
Lemma efr_fz3 : ltac2:(tb__ "0|1|
S37S6S8S18A1M0A1S79S45S62S48A3S7G0S53A2A3"). Proof. exact MEMO_9_e. Qed.

Lemma chk_fz3 : ltac2:(tb__ "0|4|
S38S37S5S6fS42P1fS45S62S48S53S78SbS1dS8SbS13S13A2A1M0A2M1S1dScS1dG0A2S66A4A7S2A3S38S37S5S7dS48S5eA2S2A3S38S37S5S6cG1G1SdS72S5eS48S20S45A1ScS1dG0R1A3M2SfS1dG0R1A3M3A5S70S62G2G3A3A2Ld;S66A3S2A3S37S5S71S23S45A1S65S9SeA1S68S53A5S2A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma s_fz3_vals : ltac2:(tb__ "0|0|
S38S37S13S6dS48PcA2S14Pf0A1A3S38S37S13S6dS48PdA2S14P9eA1A3S38S37S13S6dS48PaA2S17S30S14P1A1S10Nd0A1A3A3S37S13S6dS48PfA2S10Nffdc0A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma S_3_call_shape : ltac2:(tb__ "0|0|
S38S37S2fS2cS45A1S7cA3S38S37S5S24S45A1S3A3S37S6S18A1S6aS18S22S45A1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S6eS5eS45S48S53S40S3fS75S2fU0S41S3fA1Z0A4A2A5").
Definition P_3 : sstate := ltac:(let x := eval vm_compute in (MEMO_10) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = P_3. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S37S1dS6eS5eS45S48S53S40S3fS75S2fU0S41S3fA1Z0A4A2A5S4bA3").
Proof. exact (@eq_trans _ (T_afterN NF S_3 s_fz3 R_fz3 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0))) MEMO_10 (P_3) (@eq_refl _ (T_afterN NF S_3 s_fz3 R_fz3 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0)))) MEMO_10_c). Qed.
Lemma P_3_eq : ltac2:(tb__ "0|0|
S37S1dS6eS5eS45S48S53S40S3fS75S2fU0S41S3fA1Z0A4A2A5S4bA3"). Proof. exact MEMO_10_e. Qed.

Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|1|
S61S4bS60S42S20S4bA1M0A2S5fG0A1A3").
Definition P_3S : sstate := ltac:(let x := eval vm_compute in (MEMO_11) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = P_3S. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|1|
S37S1dS61S4bS60S42S20S4bA1M0A2S5fG0A1A3S50A3").
Proof. exact (@eq_trans _ (app_objs P_3 (statics_objs C_U (ss_next P_3)) (Pos.succ (ss_next P_3))) MEMO_11 (P_3S) (@eq_refl _ (app_objs P_3 (statics_objs C_U (ss_next P_3)) (Pos.succ (ss_next P_3)))) MEMO_11_c). Qed.
Lemma P_3S_eq : ltac2:(tb__ "0|1|
S37S1dS61S4bS60S42S20S4bA1M0A2S5fG0A1A3S50A3"). Proof. exact MEMO_11_e. Qed.
Lemma swf_P_3S : swf P_3S = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_3 : ltac2:(tb__ "0|1|
S37S5S7bS42S23S4bA1S65SaS18S76S18U2S22S4bA1M0A3S77S18U3G0A3A3A4S2A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma P_3S_shape : ltac2:(tb__ "0|0|
S38S37S2eS20S50A1S5fS20S4bA1A1A3S38S37S5S24S50A1S3A3S37S6S18A1S6aS18S22S4bA1U2A3S7S18S64A2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Definition NX3 : positive := ltac:(let x := eval vm_compute in (ss_next P_3) in exact x).
Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S6S8S3aA1A1") := ltac2:(tb__ "0|0|
S3dS73S74S63S50S2A5").
Definition LVS_3 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_12 with Some l => l | None => [] end) in exact x).
Definition N_4 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVS_3 (mkLeaf P_3S RsFuel))) in exact x).
Definition X_4 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVS_3 (mkLeaf P_3S RsFuel))) in exact x).
Local Lemma MEMO_12_c : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S5bS7G0S0S3aS3cS57S3bA2S0S3aS3cS56S3bA2S4S3aA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S50S2A5S7G0S0S3aS3cS57S3bA2S0S3aS3cS56S3bA2S4S3aA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS P_3S true) MEMO_12 (Some [mkLeaf N_4 RsCut; mkLeaf X_4 RsCut]) (@eq_refl _ (sym_run segs FUEL LCUTS P_3S true)) MEMO_12_c). Qed.
Lemma run_P3 : ltac2:(tb__ "0|1|
S37S6S8S3aA1M0A1S3dS73S74S63S50S2A5S7G0S0S3aS3cS57S3bA2S0S3aS3cS56S3bA2S4S3aA1A3A3A2A3").
Proof. exact MEMO_12_e. Qed.
Definition P_3b : sstate := ltac:(let x := eval vm_compute in (T_afterN NF S_3 s_fz3 R_fz3 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0))) in exact x).
Lemma P_3b_eq : T_afterN NF S_3 s_fz3 R_fz3 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0)) = P_3b.
Proof. vm_cast_no_check (@eq_refl _ P_3b). Qed.
Definition P_3bS : sstate := ltac:(let x := eval vm_compute in (app_objs P_3b (statics_objs C_U (ss_next P_3b)) (Pos.succ (ss_next P_3b))) in exact x).
Lemma P_3bS_eq : app_objs P_3b (statics_objs C_U (ss_next P_3b)) (Pos.succ (ss_next P_3b)) = P_3bS.
Proof. vm_cast_no_check (@eq_refl _ P_3bS). Qed.
Lemma swf_P_3bS : swf P_3bS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_3b : robjs_missT_statics C_U (ss_facts P_3b) tvL (firstn 2 (ss_objs P_3b) ++ skipn 3 (ss_objs P_3b)) = true.
Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma run_P3b : sym_run Code.segs FUEL LCUTS P_3bS true = sym_run Code.segs FUEL LCUTS P_3S true.
Proof. vm_cast_no_check (@eq_refl _ (sym_run Code.segs FUEL LCUTS P_3S true)). Qed.
Lemma posts_3 : ltac2:(tb__ "0|5|
S2fS6bS2fR1S41S3fA1A3S39S1dS1dS39S1dS1dS38S37S1dS6eS5eS45S48S53S40S3fR4A2A5R2A3S38S37S1dS61R2S60S42S20R2A1M0A2S5fG0A1A3R1A3S38S37S5S2dR1A1S2A3S38S37S5S7bS42S23R2A1S65SaS18S76S18U2S22R2A1M1A3M2S77S18U3G1A3M3A3A4S2A3S38S37S8S18A1G1SaS18G2S0S18S64G3A3A3A3S38S37S2eG0S5aA3S38S37S2eS20R1A1S5fS5aA1A3S38S37S5S24R1A1S3A3S37S6S8S3aA1M4A1S3dS73S74S63R1S2A5S7G4S0S3aS3cS57S3bA2S0S3aS3cS56S3bA2S4S3aA1A3A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;").
Proof.
  intros r Hr. cbn [fz_rets FZ_U] in Hr.
  destruct Hr as [<-|[<-|[]]]; [exists P_3, P_3S; split; [exact P_3_eq | split; [exact P_3S_eq | split; [exact swf_P_3S | split; [exact missT_P_3 | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact run_P3]]]]]]]] | exists P_3b, P_3bS; split; [exact P_3b_eq | split; [exact P_3bS_eq | split; [exact swf_P_3bS | split; [exact missT_P_3b | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | rewrite run_P3b; exact run_P3]]]]]]]]].
Qed.
Lemma fork_4 : ltac2:(tb__ "0|4|
S38S37S6S15A1M0S6aS15S23S57A1U0M1A3S7S15S1bS36S17S30S14P9fA1S10N4A1A3S10Z0A1A3M2A2A3S38S37G0S6aS15S23S56A1G1A3S7S15S21G2A1A2A3S38S37S2fS2cS56A1S7eA3S38S37S13S2bS56ZaA2S14Pf1A1A3S38S37S2eS20S56A1S20S50A1M3A3S37S2eS20S57A1G3A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

