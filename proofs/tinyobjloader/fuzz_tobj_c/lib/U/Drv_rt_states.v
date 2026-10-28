(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "option"; "nat"; "true"; "list"; "Some"; "false"; "bool"; "prod"; "None"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "cell"; "mkCell"; "sprop"; "SPUle"; "sobj"; "SAlu"; "mkObj"; "sstate"; "DUnknown"; "ss_facts"; "ss_next"; "DImage"; "SExt"; "SPBranch"; "SPAlign"; "SPNot"; "ss_objs"; "DList"; "reg_sv"; "sprop_below"; "ss_pc"; "DRom"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPUlt"; "mkSS"; "ob_cells"; "swf"; "dflt_writable"; "is_arr"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "valuation"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsEcall"; "sym_run"; "RsCut"; "instr_at"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "ALU_OR"; "BC_EQ"; "BC_GE"; "BC_NE"; "instr"; "ALU_XOR"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XSplit"; "apply_xforms"; "XRebase"; "XMerge"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "T_gnull"; "X_ref"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_rt_states"; "E_goom"; "E_ref"; "E_goomc"; "E_refc"; "E_refx"; "s_f"; "s_gw"; "E_goomx"; "T_fDi"; "T_gDi"; "E_fex"; "E_gex"; "E_goomb"; "E_refl"; "E_refr"; "R_f"; "R_gw"; "T_fD"; "T_gD"; "T_gnullS"; "X_refS"; "B544"; "xs_fd"; "xs_gd"; "BL_ref"; "xs_goom"; "xs_ref"; "MEMO_17"; "MEMO_2"; "MEMO_7"; "MEMO_9"; "O_emp6"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "D"; "Pre_wl1"; "Pre_wl2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "cells_bytes"; "beval"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states.MAddr"; "stderr_file"; "msg_oom_addr"; "wl_ecall"; "stderr_wbase"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states"; "obj"; "O_b1"; "O_b2"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue"; "reframe_obj"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "robjs_missT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@Corelib.Lists.ListDef"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "msg_refused"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue ObjXform ListObj MuslWL MuslMemcpyHdr DrvGlue ObjUnbase TobjJV DataWin DrvStatics DrvPristine DrvLoop SysRead.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.
Import ListNotations.

Import MAddr RAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S16") := ltac2:(tb__ "0|0|
S71S4fS72S73Pc1A2Pc2A3").
Definition T_gnullS : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = T_gnullS. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S35S16S71S4fS72S73Pc1A2Pc2A3S64A3").
Proof. exact (@eq_trans _ (app_objs T_gnull (statics_objs C_U 193%positive) 194%positive) MEMO_1 (T_gnullS) (@eq_refl _ (app_objs T_gnull (statics_objs C_U 193%positive) 194%positive)) MEMO_1_c). Qed.
Lemma T_gnullS_eq : ltac2:(tb__ "0|0|
S35S16S71S4fS72S73Pc1A2Pc2A3S64A3"). Proof. exact MEMO_1_e. Qed.
Lemma swf_T_gnullS : swf T_gnullS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_2 : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S3aS4dS4eS2S34A1S64S5A5").
Local Definition MEMO_2__f : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S81S4dS4eS2S34A1S64S5A5").
Definition E_goom : sstate := ltac:(let x := eval vm_compute in (lf0 T_gnullS (MEMO_2__f) 0) in exact x).
Local Lemma MEMO_2_c : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S6dS7G0S0S37S38S51S39A2S2S37A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_2 MEMO_2__f. Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S64S5A5S7G0S0S37S38S51S39A2S2S37A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_gnullS true) MEMO_2 (Some [mkLeaf E_goom RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_gnullS true)) MEMO_2_c). Qed.
Lemma run_gnullS : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S64S5A5S7G0S0S37S38S51S39A2S2S37A1A3A2A3").
Proof. exact MEMO_2_e. Qed.
Lemma E_goom_pc : ltac2:(tb__ "0|0|
S36S35S34S23S51A1S84A3S35S33S19S51A1Pc2A3A2"). Proof. split; reflexivity. Qed.

Definition xs_goom : list xform := ltac2:(tb__ "0|2|
S0S47S48U0M0ScN88A1A2S0S47S48G0ScNa8A1A2S0S47S48U6M1ScS7cS82Z7cA2A1A2S0S47S48G1ScS7cS82Z78A2A1A2S2S47A1A3A3A3A3").
Local Definition MEMO_3 := apply_xforms E_goom xs_goom.
Local Definition MEMO_3__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_goom xs_goom.
Definition E_goomx : sstate := ltac:(let x := eval vm_compute in (xget E_goom (MEMO_3__f)) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = Some E_goomx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_3 MEMO_3__f. Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S35S3S16A1S49S51S6aA2S7S16S58A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_goom xs_goom) MEMO_3 (Some E_goomx) (@eq_refl _ (apply_xforms E_goom xs_goom)) MEMO_3_c). Qed.
Lemma xs_goom_ok : ltac2:(tb__ "0|0|
S35S3S16A1S49S51S6aA2S7S16S58A2A3"). Proof. exact MEMO_3_e. Qed.
Lemma norl_goom : ltac2:(tb__ "0|0|
S36S35S9S80P5S58A2S8A3S35S9S80P6S58A2S8A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_goomb : sstate := ltac:(let x := eval vm_compute in (app_objs E_goomx [O_b1] (ss_next E_goomx)) in exact x).
Definition E_goomc : sstate := ltac:(let x := eval vm_compute in (app_objs E_goomb [O_b2] (ss_next E_goomx)) in exact x).
Lemma E_goomb_eq : ltac2:(tb__ "0|0|
S35S16S71S58S0S13S87S2S13A1A3S19S58A1A3S5dA3"). Proof. reflexivity. Qed.
Lemma E_goomc_eq : ltac2:(tb__ "0|0|
S35S16S71S5dS0S13S88S2S13A1A3S19S58A1A3S53A3"). Proof. reflexivity. Qed.
Lemma swf_E_goomc : ltac2:(tb__ "0|0|
S36S35S9S2bS5dA1S5A3S35S9S2bS53A1S5A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_goom_facts : ltac2:(tb__ "0|3|
S36S35S6S11A1M0S18S53A1S18S51A1M1A3S36S35G0S18S58A1G1A3S36S35S33S19S53A1S19S51A1M2A3S36S35S33S19S58A1G2A3S36S35G0S18S5dA1G1A3S35S33S19S5dA1G2A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma missT_gb2 : ltac2:(tb__ "0|1|
S35S9S8dS73S18S51A1S0SaSdSdA2M0S1SdSdSeP66A1SeP65A1A4S2G0A1A3S83S7cS83Z13A2S1fS5dA1A6S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_gnull : ltac2:(tb__ "0|1|
S35S9S8cS73S18S4fA1S0SaSdSdA2M0S1SdSdSeP66A1SeP65A1A4S2G0A1A3S1fS4fA1A4S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition s_gw : wsub := ltac2:(tb__ "0|8|
S0SaS33SdA2M0S1S33SdPcM1ScZ5a798A1A4S0G0S1S33SdPdM2ScZ0A1M3A4S0G0S1S33SdPeM4ScZ103b1A1A4S0G0S1S33SdPfScZ13A1A4M5S0G0S1S33SdG4S14S3dSeP1A1M6ScN80A1A3M7A4S0G0S1S33SdG2ScN88A1A4S0G0S1S33SdG1G7A4S0G0S1S33SdP5bSeP97A1A4S0G0S1S33SdP5aSeP96A1A4S0G0S1S33SdP59SeP95A1A4S0G0S1S33SdP58SeP94A1A4S0G0S1S33SdP57SeP93A1A4S0G0S1S33SdP56SeP92A1A4S0G0S1S33SdP55SeP91A1A4S0G0S1S33SdP54SeP90A1A4S0G0S1S33SdP53SeP8fA1A4S0G0S1S33SdP52SeP8eA1A4S0G0S1S33SdP51SeP8dA1A4S0G0S1S33SdP50SeP8cA1A4S0G0S1S33SdP4fSeP8bA1A4S0G0S1S33SdP4eSeP8aA1A4S0G0S1S33SdP4dSeP89A1A4S0G0S1S33SdP4cSeP88A1A4S0G0S1S33SdP4bSeP87A1A4S0G0S1S33SdP4aSeP86A1A4S0G0S1S33SdP49SeP85A1A4S0G0S1S33SdP48SeP84A1A4S0G0S1S33SdP47SeP83A1A4S0G0S1S33SdP46SeP82A1A4S0G0S1S33SdP45SeP81A1A4S0G0S1S33SdP44SeP80A1A4S0G0S1S33SdP43SeP7fA1A4S0G0S1S33SdP42SeP7eA1A4S0G0S1S33SdP41SeP7dA1A4S0G0S1S33SdP40SeP7cA1A4S0G0S1S33SdP3fSeP7bA1A4S0G0S1S33SdP3eSeP7aA1A4S0G0S1S33SdP3dSeP79A1A4S0G0S1S33SdP3cSeP78A1A4S0G0S1S33SdP33SePb8A1A4S0G0S1S33SdP32SePb7A1A4S0G0S1S33SdP31SePb6A1A4S0G0S1S33SdP30SePb5A1A4S0G0S1S33SdP2fG3A4S0G0S1S33SdP2eG3A4S0G0S1S33SdP2dG3A4S0G0S1S33SdP2cG3A4S0G0S1S33SdP2bSeP66A1A4S0G0S1S33SdP29ScZ5a338A1A4S0G0S1S33SdP28ScZ3A1A4S0G0S1S33SdP24SePa9A1A4S0G0S1S33SdP23SePa8A1A4S0G0S1S33SdP22SePa7A1A4S0G0S1S33SdP21G3A4S0G0G5S0G0S1S33SdP1bSePa0A1A4S0G0S1S33SdP1aScZ22224A1A4S0G0S1S33SdP19SeP9eA1A4S0G0S1S33SdP18ScZ3a0d0A1A4S0G0S1S33SdPaS14S3dG6ScN130A1A3A4S0G0S1S33SdP15ScZ227b4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S3S6S13A1A1") := ltac2:(tb__ "0|0|
S79S53S77S57A3").
Definition R_gw : list sobj := ltac:(let x := eval vm_compute in (match MEMO_4 with Some R => R | None => [] end) in exact x).

Local Lemma MEMO_4_c : MEMO_4 = Some R_gw. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|1|
S35S3S6S13A1M0A1S79S53S77S57A3S7G0S61A2A3").
Proof. exact (@eq_trans _ (entails_fr E_goomc WLerrS.Pre_wl1 s_gw) MEMO_4 (Some R_gw) (@eq_refl _ (entails_fr E_goomc WLerrS.Pre_wl1 s_gw)) MEMO_4_c). Qed.
Lemma efr_gw : ltac2:(tb__ "0|1|
S35S3S6S13A1M0A1S79S53S77S57A3S7G0S61A2A3"). Proof. exact MEMO_4_e. Qed.
Lemma chk_gw : ltac2:(tb__ "0|0|
S35S9S7bS53S77S57S61S0S37S38S76S3bA2S2S37A1A3A5S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_gw : ltac2:(tb__ "0|0|
S35S9S89S11S22S19S53A1A1S18S51A1A3S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_gw_vals : ltac2:(tb__ "0|0|
S36S35SdS75S57PcA2ScS85A1A3S36S35SdS75S57PdA2ScZ0A1A3S36S35SdS75S57PeA2ScS83A1A3S35SdS75S57PfA2ScZ13A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S16") := ltac2:(tb__ "0|0|
S7aS57P5cS76S19S53A1S61A5").
Definition T_gDi : sstate := ltac:(let x := eval vm_compute in (MEMO_5) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = T_gDi. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S35S16S7aS57P5cS76S19S53A1S61A5S5aA3").
Proof. exact (@eq_trans _ (import_post s_gw 92 WLerrS.D (ss_next E_goomc) R_gw) MEMO_5 (T_gDi) (@eq_refl _ (import_post s_gw 92 WLerrS.D (ss_next E_goomc) R_gw)) MEMO_5_c). Qed.
Lemma T_gDi_eq : ltac2:(tb__ "0|0|
S35S16S7aS57P5cS76S19S53A1S61A5S5aA3"). Proof. exact MEMO_5_e. Qed.

Definition xs_gd : list xform := ltac2:(tb__ "0|6|
S0S47S4aU0M0A1S0S47S4aU4M1A1S0S47S4aU5M2A1S0S47S4cS0S4G1S0S4G0S0S4G2S0S4U7S0S4U8S0S4U9S0S4U3S0S4UaS0S4UbS0S4UcS0S4UdS0S4UeS0S4UfS0S4U10S0S4U11S0S4U1S0S4U2M3S0S4U6S2S4A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S47S4bG0A1M4S0S47G4S0S47G4S0S47S4bG3A1M5S0S47G5S2S47A1A3A3A3A3A3A3A3A3A3").

Local Definition MEMO_6 : ltac2:(tb__ "0|0|
S3S16A1") := ltac2:(tb__ "0|0|
S49S74S18S51A1S5aA2S68A2").
Local Definition MEMO_6__f : ltac2:(tb__ "0|0|
S3S16A1") := ltac2:(tb__ "0|0|
S8eS74S18S51A1S5aA2S68A2").
Definition T_gD : sstate := ltac:(let x := eval vm_compute in (xget T_gDi (MEMO_6__f)) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = Some T_gD. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_6 MEMO_6__f. Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S35S3S16A1S49S74S18S51A1S5aA2S68A2S7S16S63A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_goom) T_gDi) xs_gd) MEMO_6 (Some T_gD) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_goom) T_gDi) xs_gd)) MEMO_6_c). Qed.
Lemma xs_gd_ok : ltac2:(tb__ "0|0|
S35S3S16A1S49S74S18S51A1S5aA2S68A2S7S16S63A2A3"). Proof. exact MEMO_6_e. Qed.
Lemma fb_gd : ltac2:(tb__ "0|0|
S35S9S89S11S22S19S5aA1A1S18S51A1A3S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S3aS4dS4eS2S34A1S63S5A5").
Local Definition MEMO_7__f : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S81S4dS4eS2S34A1S63S5A5").
Definition E_gex : sstate := ltac:(let x := eval vm_compute in (lf0 T_gD (MEMO_7__f) 0) in exact x).
Local Lemma MEMO_7_c : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S6eS7G0S0S37S38S5cS39A2S2S37A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_7 MEMO_7__f. Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S63S5A5S7G0S0S37S38S5cS39A2S2S37A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_gD true) MEMO_7 (Some [mkLeaf E_gex RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_gD true)) MEMO_7_c). Qed.
Lemma run_gd : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S63S5A5S7G0S0S37S38S5cS39A2S2S37A1A3A2A3").
Proof. exact MEMO_7_e. Qed.
Lemma cert_gexit : ltac2:(tb__ "0|0|
S36S35S3S44A1S3cS4dS23S5cA1A2S7S44S46A2A3S36S35SdS21S5cZ11A2ScZ5eA1A3S35SdS21S5cZaA2ScZ2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.

Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S16") := ltac2:(tb__ "0|0|
S71S50S72S73P99A2P9aA3").
Definition X_refS : sstate := ltac:(let x := eval vm_compute in (MEMO_8) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = X_refS. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S35S16S71S50S72S73P99A2P9aA3S65A3").
Proof. exact (@eq_trans _ (app_objs X_ref (statics_objs C_U 153%positive) 154%positive) MEMO_8 (X_refS) (@eq_refl _ (app_objs X_ref (statics_objs C_U 153%positive) 154%positive)) MEMO_8_c). Qed.
Lemma X_refS_eq : ltac2:(tb__ "0|0|
S35S16S71S50S72S73P99A2P9aA3S65A3"). Proof. exact MEMO_8_e. Qed.
Lemma swf_X_refS : swf X_refS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_xref : ltac2:(tb__ "0|1|
S35S9S8cS73S18S50A1S0SaSdSdA2M0S1SdSdSeP66A1SeP65A1A4S2G0A1A3S1fS50A1A4S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S3aS4dS4eS2S34A1S65S5A5").
Local Definition MEMO_9__f : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S81S4dS4eS2S34A1S65S5A5").
Definition E_ref : sstate := ltac:(let x := eval vm_compute in (lf0 X_refS (MEMO_9__f) 0) in exact x).
Local Lemma MEMO_9_c : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S6fS7G0S0S37S38S52S39A2S2S37A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_9 MEMO_9__f. Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S65S5A5S7G0S0S37S38S52S39A2S2S37A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] X_refS true) MEMO_9 (Some [mkLeaf E_ref RsEcall]) (@eq_refl _ (sym_run segs FUEL [] X_refS true)) MEMO_9_c). Qed.
Lemma run_xrefS : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S65S5A5S7G0S0S37S38S52S39A2S2S37A1A3A2A3").
Proof. exact MEMO_9_e. Qed.
Lemma E_ref_pc : ltac2:(tb__ "0|0|
S36S35S34S23S52A1S84A3S35S33S19S52A1P9aA3A2"). Proof. split; reflexivity. Qed.

Definition xs_ref : list xform := ltac2:(tb__ "0|2|
S0S47S48U0M0ScN18aA1A2S0S47S48G0ScN1b0A1A2S0S47S48G0ScN208A1A2S0S47S48G0ScN228A1A2S0S47S48U8M1ScS7cS82Z7cA2A1A2S0S47S48G1ScS7cS82Z78A2A1A2S2S47A1A3A3A3A3A3A3").
Local Definition MEMO_10 := apply_xforms E_ref xs_ref.
Local Definition MEMO_10__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_ref xs_ref.
Definition E_refx : sstate := ltac:(let x := eval vm_compute in (xget E_ref (MEMO_10__f)) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some E_refx. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_10 MEMO_10__f. Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S35S3S16A1S49S52S6bA2S7S16S55A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_ref xs_ref) MEMO_10 (Some E_refx) (@eq_refl _ (apply_xforms E_ref xs_ref)) MEMO_10_c). Qed.
Lemma xs_ref_ok : ltac2:(tb__ "0|0|
S35S3S16A1S49S52S6bA2S7S16S55A2A3"). Proof. exact MEMO_10_e. Qed.

Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S3S6S7dA1A1") := ltac2:(tb__ "0|0|
S7eS2aS86S55U3A2A1ScN1b0A1Z0U26A4").
Definition BL_ref : list bexp := ltac:(let x := eval vm_compute in (match MEMO_11 with Some bl => bl | None => [] end) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some BL_ref. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|1|
S35S3S6S7dA1M0A1S7eS2aS86S55U3A2A1ScN1b0A1Z0U26A4S7G0S69A2A3").
Proof. exact (@eq_trans _ (cells_bytes (ob_cells (obj E_refx 3)) (SLit (-432)) 0 38) MEMO_11 (Some BL_ref) (@eq_refl _ (cells_bytes (ob_cells (obj E_refx 3)) (SLit (-432)) 0 38)) MEMO_11_c). Qed.
Lemma cb_ref : ltac2:(tb__ "0|1|
S35S3S6S7dA1M0A1S7eS2aS86S55U3A2A1ScN1b0A1Z0U26A4S7G0S69A2A3"). Proof. exact MEMO_11_e. Qed.
Lemma obj3_ref : ltac2:(tb__ "0|3|
S36S35S3S13A1S8aS13S1fS55A1U3M0A3S7S13S86S55G0A2M1A2A3S36S35SdS31G1A1ScN1b0A1A3S36S35SdS30G1A1ScN18aA1A3S36S35S9S2cS2fG1A1M2A1S5A3S36S35S9S2dG2A1S8A3S35SdS2eG1A1S14S3dSeP1A1ScN80A1A3A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma norl_ref : ltac2:(tb__ "0|0|
S36S35S9S80P5S55A2S8A3S35S9S80P6S55A2S8A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Lemma BL_ref_msg : ltac2:(tb__ "0|1|
S32S35S6S91Q8A1M0A1S8fS7dG0S7fR1A1S69A4S90A3Frho;"). Proof. intros rho. reflexivity. Qed.
Local Definition MEMO_12 := obj_to_list E_refx 3 5.
Definition E_refl : sstate := ltac:(let x := eval vm_compute in (MEMO_12) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = E_refl. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : obj_to_list E_refx 3 5 = E_refl.
Proof. exact (@eq_trans _ (obj_to_list E_refx 3 5) MEMO_12 (E_refl) (@eq_refl _ (obj_to_list E_refx 3 5)) MEMO_12_c). Qed.
Lemma E_refl_eq : obj_to_list E_refx 3 5 = E_refl. Proof. exact MEMO_12_e. Qed.

Definition B544 : sv := SAlu ALU_ADD (SVar 1) (SLit (-560)).
Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S16") := ltac2:(tb__ "0|0|
S8bS5eU3S66ScZ0A1ScZ26A1A5").
Definition E_refr : sstate := ltac:(let x := eval vm_compute in (MEMO_13) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = E_refr. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|0|
S35S16S8bS5eU3S66ScZ0A1ScZ26A1A5S5fA3").
Proof. exact (@eq_trans _ (reframe_obj E_refl 3 B544 (SLit 0) (SLit 38)) MEMO_13 (E_refr) (@eq_refl _ (reframe_obj E_refl 3 B544 (SLit 0) (SLit 38))) MEMO_13_c). Qed.
Lemma E_refr_eq : ltac2:(tb__ "0|0|
S35S16S8bS5eU3S66ScZ0A1ScZ26A1A5S5fA3"). Proof. exact MEMO_13_e. Qed.
Lemma swf_E_refr : swf E_refr = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl_refr : state_has_rl 6 E_refr = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Lemma obj3_refl : ltac2:(tb__ "0|0|
S35S3S13A1S8aS13S1fS5eA1U3A3S7S13S15S14S3dSeP1A1ScN80A1A3ScN1b0A1ScN18aA1S2SfA1S20P5A1A5A2A3"). Proof. reflexivity. Qed.
Definition O_emp6 : sobj := ltac2:(tb__ "0|1|
S15ScZ0A1M0G0G0S2SfA1S24P6A1A5").
Definition E_refc : sstate := ltac:(let x := eval vm_compute in (app_objs E_refr [O_emp6] (ss_next E_refr)) in exact x).
Lemma E_refc_eq : ltac2:(tb__ "0|0|
S35S16S71S5fS0S13S70S2S13A1A3S19S5fA1A3S54A3"). Proof. reflexivity. Qed.
Lemma swf_E_refc : swf E_refc = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_ref_facts : ltac2:(tb__ "0|3|
S36S35S6S11A1M0S18S54A1S18S52A1M1A3S36S35G0S18S55A1G1A3S36S35G0S18S5fA1G1A3S36S35G0S18S5eA1G1A3S36S35S33S19S54A1S19S52A1M2A3S36S35S33S19S55A1G2A3S36S35S33S19S5fA1G2A3S35S33S19S5eA1G2A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_f : wsub := ltac2:(tb__ "0|a|
S0SaS33SdA2M0S1S33SdPcM1S14S3dSeP1A1M2ScN230A1A3M3A4S0G0S1S33SdPdM4ScZ26A1A4S0G0S1S33SdPeM5ScZ0A1M6A4S0G0S1S33SdPfG6A4M7S0G0S1S33SdG5S14S3dG2ScN80A1A3M8A4S0G0S1S33SdG4ScN208A1A4S0G0S1S33SdG1G8A4S0G0S1S33SdP5bSeP97A1A4S0G0S1S33SdP5aSeP96A1A4S0G0S1S33SdP59SeP95A1A4S0G0S1S33SdP58SeP94A1A4S0G0S1S33SdP57SeP93A1A4S0G0S1S33SdP56SeP92A1A4S0G0S1S33SdP55SeP91A1A4S0G0S1S33SdP54SeP90A1A4S0G0S1S33SdP53SeP8fA1A4S0G0S1S33SdP52SeP8eA1A4S0G0S1S33SdP51SeP8dA1A4S0G0S1S33SdP50SeP8cA1A4S0G0S1S33SdP4fSeP8bA1A4S0G0S1S33SdP4eSeP8aA1A4S0G0S1S33SdP4dSeP89A1A4S0G0S1S33SdP4cSeP88A1A4S0G0S1S33SdP4bSeP87A1A4S0G0S1S33SdP4aSeP86A1A4S0G0S1S33SdP49SeP85A1A4S0G0S1S33SdP48SeP84A1A4S0G0S1S33SdP47SeP83A1A4S0G0S1S33SdP46SeP82A1A4S0G0S1S33SdP45SeP81A1A4S0G0S1S33SdP44SeP80A1A4S0G0S1S33SdP43SeP7fA1A4S0G0S1S33SdP42SeP7eA1A4S0G0S1S33SdP41SeP7dA1A4S0G0S1S33SdP40SeP7cA1A4S0G0S1S33SdP3fSeP7bA1A4S0G0S1S33SdP3eSeP7aA1A4S0G0S1S33SdP3dSeP79A1A4S0G0S1S33SdP3cSeP78A1A4S0G0S1S33SdP33SeP76A1A4S0G0S1S33SdP32SeP75A1A4S0G0S1S33SdP31SeP74A1A4S0G0S1S33SdP30ScZaA1A4S0G0S1S33SdP2fG6A4S0G0S1S33SdP2eG6A4S0G0S1S33SdP2dG6A4S0G0S1S33SdP2cG6A4S0G0S1S33SdP2bSeP66A1A4S0G0S1S33SdP29ScZ5a338A1A4S0G0S1S33SdP28ScZ5a798A1A4S0G0S1S33SdP24ScZ66A1A4S0G0S1S33SdP23ScZ65A1M9A4S0G0S1S33SdP22G6A4S0G0S1S33SdP21S14S45S14S3dG2ScN20aA1A3G3A3A4S0G0G7S0G0S1S33SdP1bScZ64A1A4S0G0S1S33SdP1aG9A4S0G0S1S33SdP19ScZ73A1A4S0G0S1S33SdP18ScZ3a0d0A1A4S0G0S1S33SdPaS14S3dG2ScN2b0A1A3A4S0G0S1S33SdP15ScZ22a3cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S3S6S13A1A1") := ltac2:(tb__ "0|0|
S79S54S78S56A3").
Definition R_f : list sobj := ltac:(let x := eval vm_compute in (match MEMO_14 with Some R => R | None => [] end) in exact x).

Local Lemma MEMO_14_c : MEMO_14 = Some R_f. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|1|
S35S3S6S13A1M0A1S79S54S78S56A3S7G0S60A2A3").
Proof. exact (@eq_trans _ (entails_fr E_refc WLerrS.Pre_wl2 s_f) MEMO_14 (Some R_f) (@eq_refl _ (entails_fr E_refc WLerrS.Pre_wl2 s_f)) MEMO_14_c). Qed.
Lemma efr_f : ltac2:(tb__ "0|1|
S35S3S6S13A1M0A1S79S54S78S56A3S7G0S60A2A3"). Proof. exact MEMO_14_e. Qed.
Lemma chk_f : ltac2:(tb__ "0|0|
S35S9S7bS54S78S56S60S0S37S38S76S3bA2S2S37A1A3A5S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_f : ltac2:(tb__ "0|0|
S35S9S89S11S22S19S54A1A1S18S52A1A3S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_f_vals : ltac2:(tb__ "0|1|
S36S35SdS75S56PcA2S66A3S36S35SdS75S56PdA2ScZ26A1A3S36S35SdS75S56PeA2ScZ0A1M0A3S35SdS75S56PfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S16") := ltac2:(tb__ "0|0|
S7aS56P5cS76S19S54A1S60A5").
Definition T_fDi : sstate := ltac:(let x := eval vm_compute in (MEMO_15) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = T_fDi. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|0|
S35S16S7aS56P5cS76S19S54A1S60A5S59A3").
Proof. exact (@eq_trans _ (import_post s_f 92 WLerrS.D (ss_next E_refc) R_f) MEMO_15 (T_fDi) (@eq_refl _ (import_post s_f 92 WLerrS.D (ss_next E_refc) R_f)) MEMO_15_c). Qed.
Lemma T_fDi_eq : ltac2:(tb__ "0|0|
S35S16S7aS56P5cS76S19S54A1S60A5S59A3"). Proof. exact MEMO_15_e. Qed.

Definition xs_fd : list xform := ltac2:(tb__ "0|7|
S0S47S4aU0M0A1S0S47S4aU4M1A1S0S47S4aU5M2A1S0S47S4aU6M3A1S0S47S4cS0S4G1S0S4G0S0S4G2S0S4U1S0S4G3S0S4U8S0S4U9S0S4UaS0S4U3S0S4UbS0S4UcS0S4UdS0S4UeS0S4UfS0S4U10S0S4U11S0S4U12S0S4U2M4S0S4U7S2S4A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S47S4bG0A1M5S0S47G5S0S47S4bG4A1S0S47S4bG1A1M6S0S47G6S2S47A1A3A3A3A3A3A3A3A3A3A3").

Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S3S16A1") := ltac2:(tb__ "0|0|
S49S74S18S52A1S59A2S67A2").
Local Definition MEMO_16__f : ltac2:(tb__ "0|0|
S3S16A1") := ltac2:(tb__ "0|0|
S8eS74S18S52A1S59A2S67A2").
Definition T_fD : sstate := ltac:(let x := eval vm_compute in (xget T_fDi (MEMO_16__f)) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = Some T_fD. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_16 MEMO_16__f. Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S35S3S16A1S49S74S18S52A1S59A2S67A2S7S16S62A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_ref) T_fDi) xs_fd) MEMO_16 (Some T_fD) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_ref) T_fDi) xs_fd)) MEMO_16_c). Qed.
Lemma xs_fd_ok : ltac2:(tb__ "0|0|
S35S3S16A1S49S74S18S52A1S59A2S67A2S7S16S62A2A3"). Proof. exact MEMO_16_e. Qed.
Lemma fb_fd : ltac2:(tb__ "0|0|
S35S9S89S11S22S19S59A1A1S18S52A1A3S5A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S3aS4dS4eS2S34A1S62S5A5").
Local Definition MEMO_17__f : ltac2:(tb__ "0|0|
S3S6S37A1A1") := ltac2:(tb__ "0|0|
S81S4dS4eS2S34A1S62S5A5").
Definition E_fex : sstate := ltac:(let x := eval vm_compute in (lf0 T_fD (MEMO_17__f) 0) in exact x).
Local Lemma MEMO_17_c : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S6cS7G0S0S37S38S5bS39A2S2S37A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_17 MEMO_17__f. Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S62S5A5S7G0S0S37S38S5bS39A2S2S37A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_fD true) MEMO_17 (Some [mkLeaf E_fex RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_fD true)) MEMO_17_c). Qed.
Lemma run_fd : ltac2:(tb__ "0|1|
S35S3S6S37A1M0A1S3aS4dS4eS2S34A1S62S5A5S7G0S0S37S38S5bS39A2S2S37A1A3A2A3").
Proof. exact MEMO_17_e. Qed.
Lemma cert_fexit : ltac2:(tb__ "0|0|
S36S35S3S44A1S3cS4dS23S5bA1A2S7S44S46A2A3S36S35SdS21S5bZ11A2ScZ5eA1A3S35SdS21S5bZaA2ScZ2A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.
