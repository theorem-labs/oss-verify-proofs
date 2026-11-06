(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_031.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module Lib_load_obj_epiD2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "pair"; "nil"; "list"; "prod"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "axwf"; "entailsA"; "la_reason"; "la_state"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "ss_facts"; "SPBranch"; "sprop_eqb"; "ss_pc"; "swf"; "SPNot"; "sobj"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "Pre_ms"; "L_ms"; "ms_T0"; "optL"; "optR"; "s_msx"; "vOUT"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "Pre_fr"; "L_fr"; "free_pc"; "pc_fa"; "s_free"; "cps_epi"; "dropX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "C_L"; "K_fa"; "cps_ad"; "E_fd"; "s_fa"; "s_fd"; "E_fa"; "E_ms0"; "X_A1"; "T_fa"; "T_ms"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "pc_L"; "s_ms"; "szB"; "vNx"; "E_fd0"; "L_L1"; "L_L3"; "R_fa"; "R_fd"; "R_ms"; "T_fd"; "T_ms0"; "X_A"; "nB"; "pc_adA"; "pc_adB"; "s_L1"; "s_L3"; "s_fa0"; "s_fa1"; "vCap"; "vG"; "xf_fd"; "E_fd1"; "Ls_fd"; "Ls_j1"; "T_fa0"; "T_fd0"; "gA"; "hnz"; "nobj"; "vNd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@Stdlib.Lists.List"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD"; "pop_stateA"; "lenN_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "memcpy_pc"; "memset_pc"; "ssf8_pc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1.

Definition pc_adA : Z := 0x8e740.  Definition pc_L : Z := 0x8e788.  Definition pc_adB : Z := 0x8e7d8.
Definition cps_ad : list Z := ltac2:(tb__ "0|0|
S4SbS51S4SbS43S4SbS52S31A3A3A3").
Definition Ls_j1 : list leafA := Eval vm_compute in runL 300 cps_ad K_j1.
Definition L_ok : axst := Eval vm_compute in leafL Ls_j1 memcpy_pc 0.
Definition X_fa0 : axst := Eval vm_compute in leafL Ls_j1 pc_fa 0.
Definition X_A : axst := Eval vm_compute in leafL Ls_j1 pc_adA 0.

Definition hnz : sprop := ltac2:(tb__ "0|0|
S20S1cS65S6dS18Z0A1A3A1").
Definition X_A1 : axst := Eval vm_compute in lenN_stateA X_A.
Definition gA : sv := SVar (ss_next (ax_S X_A)).
Definition X_A2 : axst := Eval vm_compute in pop_stateA X_A1 pH gA.
Definition L_L1 : axst := Eval vm_compute in leafL (runL 300 cps_ad X_A2) pc_L 0.

Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition xf_fd (A : axst) : list axform := ltac2:(tb__ "0|1|
S4S6eS71S72S61VA;A1M0U1A2A1S4S6eS70S72G0U2A2A1S6S6eA1A3A3").
Definition szB (cap : sv) : sv := SAlu ALU_ADD cap (SLit 32).
Definition fd_site (E0 : axst) (hd : sv) : axst := ltac2:(tb__ "0|0|
S32Vhd;S27S6fVE0;S59VE0;A1A2A1A2").
Definition fd_after (E : axst) (cap : sv) : axst := ltac2:(tb__ "0|1|
S66S76S2cVE;S30VE;S45Vcap;A1A2M0S28S6bVE;S2cG0A3A1S2dA5A1").
Definition Eb_fd : axst := Eval vm_compute in fd_site (leafL (runL 300 cps_ad L_L1) free_pc 0) pH.
Definition Tb_fd : axst := Eval vm_compute in fd_after Eb_fd (SVar 682).
Definition Xb_B : axst := Eval vm_compute in leafL (runL 300 cps_ad Tb_fd) pc_adB 0.
Definition Xb_B2 : axst := Eval vm_compute in pop_stateA Xb_B (SVar 681) (SVar 684).
Definition L_L2 : axst := Eval vm_compute in leafL (runL 300 cps_ad Xb_B2) pc_L 0.

Definition vNd : sv := SVar 681.  Definition vNx : sv := SVar 726.  Definition vCap : sv := SVar 727.  Definition vG : sv := SVar 729.  Definition vGp : sv := SVar 684.
Definition C_L : axst := Eval vm_compute in dropV [680]%positive (junkR [1; 26]%nat L_L2).
Definition s_L1 : wsub := ltac2:(tb__ "0|2|
S4S8ScS17A2M0S5ScS17P2d9S19P2acM1A1A4S4G0S5ScS17G1S19P2a8A1A4S4G0S5ScS17P2daS19P2adA1A4S68S23SdS48A1SdS33A1A3A3A3A3").

Definition E_fd0 : axst := Eval vm_compute in leafL (runL 300 cps_ad C_L) free_pc 0.
Definition E_fd1 : axst := Eval vm_compute in optL (apply_axforms E_fd0 (xf_fd E_fd0)).
Definition E_fd : axst := Eval vm_compute in dropX vNd E_fd1.
Definition s_fd : wsub := ltac2:(tb__ "0|0|
S30S36S45S57A1A2").
Definition R_fd : list sobj := Eval vm_compute in optR (entails_frA E_fd Pre_fr s_fd).
Definition T_fd0 : axst := Eval vm_compute in T_afterA Pre_fr E_fd s_fd R_fd L_fr.
Definition T_fd : axst := Eval vm_compute in ax_tidy T_fd0.
Definition Ls_fd : list leafA := Eval vm_compute in runL 300 cps_ad T_fd.
Definition X_fa1 : axst := Eval vm_compute in leafL Ls_fd pc_fa 0.
Definition X_B : axst := Eval vm_compute in leafL Ls_fd pc_adB 0.
Definition nB : positive := Eval vm_compute in ss_next (ax_S X_B).
Definition X_B2 : axst := Eval vm_compute in pop_stateA X_B vNx vG.
Definition L_L3 : axst := Eval vm_compute in leafL (runL 300 cps_ad X_B2) pc_L 0.
Definition s_L3 : wsub := ltac2:(tb__ "0|1|
S4S8ScS17A2M0S5ScS17P2d9S19S78S50P3A2A1A4S4G0S5ScS17P2acS58A4S4G0S5ScS17P2daS19S78S50P4A2A1A4S68S23SdS49A1SdS33A1A3A3A3A3").

Lemma epiD2_checks_loop1 : ltac2:(tb__ "0|6|
S1S0S7S8SbS15A2M0A1M1S2bSfG0SfS5SbS15S1eSdS13R1A1A1A1S12R1A1A4LL;M2S5cA4S4G0S5SbS15S7aS16A4S4G0S5SbS15S2fS16A4S4G0S5SbS15S51S16A4S6G0A1M3A3A3A3A3S1S0S2S64S1aS1dS60A1M4S1bSdS4fA1A1A3S3A3S1S0SeS74S4fA1S3bA3S1S0S2S1fSdS3bA1M5A1S3A3S1S0SeS73S3bS6dS5fA3S3eA3S1S0S2S1fSdS3eA1A1S3A3S1S0S17S14S3bA1S18S77A1A3S1S0S2S64S1aG4S1bG5A1A3S3A3S1S0G1S2bSfG0G2S63U12cS35S3eA3A4S4G0S5SbS15S43S16A4G3A3A3S1S0S2S10S33A1S3A3S1S0S2S11S48S33S53A3S3A3S0S2S6aS53S23A2S3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD2_checks_fd : ltac2:(tb__ "0|6|
S1S0S7S8SbS15A2M0A1M1S2bSfG0SfS5SbS15S1eSdS13R1A1A1A1S12R1A1A4LL;M2S63U12cM3S35S33A3A4S4G0S5SbS15S2eS16A4S6G0A1M4A3A3S1S0SaSeA1S6fS47S59S47A1A2S9SeS5aA2A3S1S0S2S10S36A1S3A3S1S0SaS7S21A1M5A1S6bS36S2cS38A3S9G5S4bA2A3S1S0S2S6cS36S2cS38S4bS4SeS2dS6SeA1A3A5S3A3S1S0S2S75S23S38A2S3A3S1S0S2S79S23S22SdS36A1A1A2S3A3S1S0S17S69S38PcA2S62A3S1S0S17S69S38PdA2S45S57A1A3S1S0SeS66S5eA1S4dA3S1S0S2S10S4dA1S3A3S1S0G1S2bSfG0G2S5bA4S4G0S5SbS15S2fS16A4S4G0S5SbS15S52S16A4G4A3A3A3S1S0S2S64S1aS1dS20S1cS65S46S18Z0A1A3A1A1S1bSdS3fA1A1A3S3A3S1S0SeS73S3fS46S58A3S40A3S1S0S2S1fSdS40A1A1S3A3S1S0S17S14S3fA1S18S77A1A3S1S0G1S2bSfG0G2S63G3S35S40A3A4S4G0S5SbS15S43S16A4G4A3A3S1S0S2S11S49S33S54A3S3A3S0S2S6aS54S23A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition K_fa : axst := Eval vm_compute in dropV [465; 680; 681; 682; 683; 684; 685; 726; 727; 728; 729; 730]%positive (junkR [1; 20; 21; 23; 24; 25; 26]%nat X_fa1).
Definition s_fa0 : wsub := ltac2:(tb__ "0|0|
S68S23SdS41A1SdS34A1A3").
Definition s_fa1 : wsub := ltac2:(tb__ "0|0|
S68S23SdS42A1SdS34A1A3").
Definition E_fa0 : axst := Eval vm_compute in leafL (runL 300 cps_ad K_fa) free_pc 0.
Definition E_fa : axst := Eval vm_compute in dropX vARn E_fa0.
Definition s_fa : wsub := s_free E_fa (SLit 64).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_frA E_fa Pre_fr s_fa).
Definition T_fa0 : axst := Eval vm_compute in T_afterA Pre_fr E_fa s_fa R_fa L_fr.
Definition T_fa : axst := Eval vm_compute in ax_tidy T_fa0.
Definition E_ms0 : axst := Eval vm_compute in leafL (runL 300 cps_ad T_fa) memset_pc 0.
Definition s_ms : wsub := ltac2:(tb__ "0|0|
S29S3aS2aS18Zd0A1A3").
Definition R_ms : list sobj := Eval vm_compute in R_of E_ms0 Pre_ms s_ms.
Definition T_ms0 : axst := Eval vm_compute in ms_T0 E_ms0 s_ms.
Definition T_ms : axst := Eval vm_compute in ax_tidy T_ms0.
Definition E_s80 : axst := Eval vm_compute in leafL (runL 300 cps_ad T_ms) ssf8_pc 0.

Lemma epiD2_checks_fa : ltac2:(tb__ "0|9|
S1S0S2S10S34A1S3A3S1S0S2S11S41S34S55A3S3A3S1S0S2S11S42S34S56A3S3A3S1S0S2S6aS55S23A2S3A3S1S0S2S6aS56S23A2S3A3S1S0S2S64S1aS1dS1cS65S6dS18Z0A1M0A3A1S1bSdS41A1A1A3S3A3S1S0S2S64S1aS1dS1cS65S46G0A3A1S1bSdS42A1A1A3S3A3S1S0S7S8SbS15A2M1A1M2S2bSfG1SfS5SbS15S1eSdS13R1A1A1A1S12R1A1A4LL;M3S63U12cM4S35S34A3A4S4G1S5SbS15S2eS16A4S6G1A1M5A3A3S1S0S2S10S39A1S3A3S1S0SaS7S21A1M6A1M7S6bS39S2cS37A3S9G6S4aA2A3S1S0S2S6cS39S2cS37S4aS4SeS2dS6SeA1M8A3A5S3A3S1S0S2S75S23S37A2S3A3S1S0S2S79S23S22SdS39A1A1A2S3A3S1S0S17S69S37PcA2S67A3S1S0S17S69S37PdA2S18Z40A1A3S1S0SeS66S5dA1S3cA3S1S0S2S10S3cA1S3A3S1S0G2S2bSfG1G3S63G4S35S3cA3A4S4G1S5SbS15S7bS16A4G5A3A3S1S0G7S6bS3aS24S44A3S9G6S4cA2A3S1S0S2S6cS3aS24S44S4cS4SeS25G8A3A5S3A3S1S0SeS26S3aS44A2S4eA3S1S0SeS66S4eA1S3dA3S1S0S2S10S3dA1S3A3S0G2S2bSfG1G3S63G4S35S3dA3A4S4G1S5SbS15S7cS16A4G5A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiD2.

(* [comment removed for export] *)
Module Lib_load_obj_avn_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "app"; "prod"; "Some"; "nat"; "nil"; "option"; "fst"; "list"; "length"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SLit"; "SVar"; "sprop_eqb"; "sv"; "ss_facts"; "ss_next"; "SAlu"; "SMd"; "SPUlt"; "sobj"; "valuation"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "s_vn"; "E_vn"; "R_vn"; "kept_vn"; "Xk_vn"; "brest_vn"; "T_vn_f0"; "T_vn_ok0"; "bd_vn"; "h0"; "tv_vn"; "PDk_vn"; "cutsV"; "exitsV"; "hand_vn"; "room_vn"; "PhisV"; "T_vn_f"; "T_vn_ok"; "c_avn"; "cps_arm"; "k_avn"; "nd_vn_f"; "nd_vn_ok"; "passed_vn"; "xf_vn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.HVN"; "Pre_hvn"; "P_fail"; "P_ok"; "nd0"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "A1"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "bud_pay2"; "ejcertAF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_avn_eqs"; "E_vn1"; "xfb"; "B_vn_f"; "B_vn_ok"; "H_ecertV_ok"; "extra_vn"; "keep_ecertV_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "AHead"; "am_eqb"; "nd_below"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "HNEXT"; "xLC"; "pNX"; "pH"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "bd_permb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition keep_ecertV_ok : list sprop := ltac2:(tb__ "0|9|
S4SfS19S12P1ccA1S12P1d3A1M0A2S4SfS10S12P1eaA1S12P1e0A1M1A2S4SfS10S12P197A1M2S18S4eS11Z3A1S17S4dS17S4dG1S12P1e1A1A3S11Z1A1A3A3A2S4SfS10G0S12PeA1M3A2S4SfS10G3S11Z4000000A1A2S4SfS10S12P196A1M4S12P1eA1M5A2S4SfS10S17S4dG4S18S4eS11Z4A1S12P198A1M6A3M7A3G5A2S4SfS10G4S11Z800000000000A1A2S4SfS10G2G6A2S4SfS10G6S11ZffffffffA1M8A2S4SfS10G7G8A2S9SfA1A3A3A3A3A3A3A3A3A3A3A3").
Definition H_ecertV_ok : list sprop := ltac2:(tb__ "0|0|
S8cS55S5S4aS2aS2bA3A2").
Lemma ecertV_ok : ltac2:(tb__ "0|1|
S0S3S4cS85S45S2eUc8S32S45S67S4aS4aS8bS53A1M0S2aA4S67S4aS4aG0S2bA4A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma avn_checks : ltac2:(tb__ "0|a|
S1S0SaScS1aA1M0A1S79S1fS3eS1eA3S7G0S20A2A3S1S0S3S78S1fS3eS1eS20S67S6S6S38S5eA2M1S1bS1bOF_;F_;M2A2M3S38G3SbS38S5eSbG1G2R1A3A3Ld;S29A4A5S2A3S1S0S3S8dS45S1eA2S2A3S1S0S3S89S1eS7aA2S2A3S1S0S3S7cS1eS36S63S75S27S2S41A3M4A1A3S2A3S1S0S3S65S60S1eS61G4A1A2S64S71S2A2M5A2S2A3S1S0S3S3cS6S7eG2A2M6G6S7fS3eS7aS1eS16S39S1fA1M7A1M8SbS7eG2R1A3A5Ld;S29A3S2A3S1S0S3S81S47S28A2S2A3S1S0S3S82S87S48A1S26A2S2A3S1S0S3S80S22S3aS1fA1A2S2A3S1S0ScS5bA1S5cS1eS62G4A1A2S2cA3S1S0S3S4bS15G7A1S11Z0M9A1G9S26S5S5bS2cS23A3A5S2A3S1S0S3S66G8S5fS28S46S26G5A4A2S2A3S0S3S5dG8S23A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition extra_vn (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S49Vo;A1S2S6aVo;A1X3x2").

Definition E_vn1 : axst := Eval vm_compute in optL (apply_axforms E_hvn xf_vn).
Lemma E_vn1_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S88S37A2S7S38S4fA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vn_eq : ltac2:(tb__ "0|0|
S0S38S8aS4fS5SfS4SfS2dS9SfA1A3S15S39S4fA1A1A3A2S1fA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma avn_checks2 : ltac2:(tb__ "0|5|
S1S0S3S6bS15S39S1fA1M0A1M1S21S46S54S20A5S2A3S1S0S3S6dG1S21S46S6cS22A5S2A3S1S0S3S69G1A1S2A3S1S0S3S81S28S47A2S2A3S1S0S3S76S45S16G0A1M2A2S2A3S1S0S84G2S6eA3S1S0S3S3bSfS13S10S6fS44A2A1S15S39S4fA1M3A1M4A3S2A3S1S0S3S3bSfS13S10S44S11Z4000000A1A2A1G4A3S2A3S1S0S3S3bSfS13S19S72S6fA2A1G4A3S2A3S1S0S3S3bSfS13S10S33S11ZffffffffA1A2A1G1A3S2A3S1S0S3S3bSfS13S10S31S18S4eS11Z3A1S70A3A2A1G4A3S2A3S1S0S3S3bSfS13S10S70S17S4dS44S11Z1A1A3A2A1G4A3S2A3S0S3S3cSfS1cS16G3A1A1S5SfS4SfS2dS9SfA1A3G4A3A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept : ltac2:(tb__ "0|0|
S3dS6S14S14A2SeS14S14S73S86Z10S74A2A4S21A3").
Proof. cbn. do 17 right. left. reflexivity. Qed.

Lemma T_vn_ok0_eq : ltac2:(tb__ "0|0|
S0S38S7dS3eS1fS1eS20S40S22A6S25A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_f0_eq : ltac2:(tb__ "0|0|
S0S38S7dS3eS1fS1eS20S3fS22A6S24A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition xfb (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S56S5aU0M0Z80A2S4S56S59S4S8G0S4S8U3S4S8U1S4S8U2S68U4M1S83SdS1aS1dS39VT;A1A1A2G1A2A2A3A3A3A3A1S4S56S58G0A1S9S56A1A3A3A3").
Definition B_vn_ok : axst := Eval vm_compute in optL (apply_axforms T_vn_ok0 (xfb T_vn_ok0)).
Definition B_vn_f : axst := Eval vm_compute in optL (apply_axforms T_vn_f0 (xfb T_vn_f0)).
Lemma B_vn_ok_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S25S50S25A1A2S7S38S52A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma B_vn_f_ok : ltac2:(tb__ "0|0|
S0SaS38A1S57S24S50S24A1A2S7S38S51A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_ok_eq : ax_tidy B_vn_ok = T_vn_ok.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_vn_f_eq : ax_tidy B_vn_f = T_vn_f.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma nd_vn_ok_eq : ltac2:(tb__ "0|2|
S0S5eS5fS5S6S14S14A2S21S7bS77S1eS3eS40S1fA4M0S63S75S27S2S43A3M1A1A2A3S46S5S5bS5cG0S62G1A1A2S23A3S60G0S61G1A1A2A4S35A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nd_vn_f_eq : ltac2:(tb__ "0|2|
S0S5eS5fS5S6S14S14A2S21S7bS77S1eS3eS3fS1fA4M0S63S75S27S2S42A3M1A1A2A3S46S5S5bS5cG0S62G1A1A2S23A3S60G0S61G1A1A2A4S34A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma avn_checks3 : ltac2:(tb__ "0|6|
S1S0S3S69S15S39S30A1M0A1M1A1S2A3S1S0S3S69S15S39S2fA1M2A1M3A1S2A3S1S0S3S3bSfS13S10S6fS44A2A1M4G1A3S2A3S1S0S3S3bSfS13S10S44S11Z4000000A1A2A1M5G1A3S2A3S1S0S3S3bSfG4G3A3S2A3S1S0S3S3bSfG5G3A3S2A3S1S0S3S76S6eS16G0A1A2S2A3S0S3S76S6eS16G2A1A2S2A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_avn_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_avn_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf"; "P0_hvn"; "PD_hvn"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "kept_vn"; "PDk_vn"; "cutsV"; "h0"; "R_vn"; "E_vn"; "Xk_vn"; "passed_vn"; "room_vn"; "s_vn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.HVN"; "Pre_hvn"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "X_latchE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_avn_eqs"; "E_vn1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_avn_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S3dS0S2ScA1M0S11OF_;M1A2M2G2S38S5G0G1R1A3S6G0G1R1A3A2Lp;S4cA3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_lt : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vn : nd_am HVN.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vn : ltac2:(tb__ "0|1|
S3dS0SeS18A2M0G0S2eS1eS22S6SeS18R1A3A1S1bA3Ld;S30A3"). Proof. repeat constructor. Qed.
Lemma P0_hvn_mono : ltac2:(tb__ "0|2|
S2S0SbSbA2M0A1M1G1G1S2S0G0SbA2A1S11G0S31G0R1R5A3S31G0R2R5A3F_;Fbn;S2fR6R5R3R2A4S2fR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS (A & B & C & D & E). split; [|split; [exact B | split; [exact C | split; [exact D | exact E]]]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma room_vn_holds : ltac2:(tb__ "0|0|
S11S3dS14S13R1A1S15SfS75A1A1A3S13R2S55A2F_;Frho;").
Proof.
  intros rho HF. pose proof avn_checks2 as (_ & _ & _ & _ & _ & _ & _ & CL & _ & _ & CC & CN & _).
  pose proof (holds_mem _ _ _ HF CL) as FL. pose proof (holds_mem _ _ _ HF CC) as FC. pose proof (holds_mem _ _ _ HF CN) as FN.
  rewrite h_ule in FL, FC, FN. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_avn) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  rewrite uval_mul_lit in FC by lia.
  assert (E1 : uval rho (SAlu ALU_ADD c_avn (SLit 3)) = uval rho c_avn + 3) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (E2 : uval rho (SMd M_MUL (SLit 4) (SAlu ALU_ADD c_avn (SLit 3))) = 4 * (uval rho c_avn + 3)) by (rewrite uval_mul_lit by (rewrite ?E1; lia); rewrite E1; reflexivity).
  unfold room_vn. rewrite h_ule, E2. rewrite uval_lit by (unfold B_EW, Lib_vec_reserve.B_EW; lia).
  apply (room4_arith (uval rho c_avn) (uval rho pNX) (uval rho vLEN) 3); lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S71S11S2S25Q40A1A1S3fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S70SdVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SbS5cVCST;R1A2S2dS39Z0R2A2S3aR2S6cA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SbS5cVXGL;R1A2S2dS39Z0R2A2S3aR2S6cA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SbS74R1A1S5cVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S0S0SbSbA2SbA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF0 : ltac2:(tb__ "0|1|
S2eS3S7fZ0S3eS0S0SbSbA2M0SbA2G0S5G0SbA2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S34VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1cVAInv;VCST;VXGL;S61VKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S37VAInv;VCST;VXGL;S61VKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma HXpow : ltac2:(tb__ "0|0|
SbS2dS39S69R1A2S3aR1S3bS69Zb8A2A2A2S5cVXGL;R2A2F_;Fa;").
Proof.
  intros a Ha. apply HXlits. apply (in_litsL_In _ 145824 184 a); [|unfold pow10_tab, ScanDoubleAddr.pow10_tab in Ha; cbn in Ha |- *; lia].
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.X_lits. cbn [In]. do 17 right. left. reflexivity.
Qed.

Lemma HIN_vn : ltac2:(tb__ "0|1|
S11S4bS71S11S2S25Q40A1A1S3fS3dS14S13R6A1S15SfS52A1A1A3VP0;Vrho0;A1S6aS61Vrho0;R8A3VAInv;R7R6R5R4A4S1dVrho0;R8A2S77RbS73S72R9A1A1A2S1fVFB;RaA2S20VFF;RbA2S24VFB;RcReS8S0S12S12A2S4dS54A3M0A4S78RfG0A2S79R10G0A2S21VFF;RfR11S33A4S2dS7dVCST;Vrho0;VFB;VFF;R12S4dS33S51A8S2dS7eVCST;VXGL;Vrho0;VFB;VFF;R12S4dS33S53A9S2fVCST;S76VFB;R12S4dA3S7cVFF;R12S33A3S49S48R12S51R11A3S56A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof avn_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_vn) by (apply (tvinA_sublist FB Ai rho (kept_vn ++ passed_vn)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vn) by (exact (tvd_app_l rho kept_vn passed_vn HD)).
  assert (HZk : tvz rho kept_vn) by (apply (tvz_sublist rho (kept_vn ++ passed_vn)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_vn frL extra_vn R_vn rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_vn in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_vn frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_vn frL o a HF CLN HT0 HZk lines_in_kept HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_vn frL xextraLO Xk_vn rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_vn frL r a Hav HP0 HE Ha).
  -
    pose proof avn_checks as (_ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hvn. rewrite !rw_call'.
    change (wsub_get s_vn 15) with vBUF. change (wsub_get s_vn 18) with vLEN. change (wsub_get s_vn 12) with bA. change (wsub_get s_vn 58) with alA.
    change (wsub_get s_vn 56) with k_avn. change (wsub_get s_vn 54) with d_avn.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split; [|split; [|split]]].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_vn rho R_vn ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_vn) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_vn) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + fact HF (SPUle k_avn (SLit 4294967295)) HkB. rewrite h_ule, uval_lit in HkB by lia.
      intros Hk. apply (tvz_in_kd rho (kept_vn ++ passed_vn) d_avn 4 k_avn HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF0. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SbS2S25Q40A1A1S29F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27SeS11S2S25Q40A1A1S29S3dS14S13R3A1S15SfR4A1A1A3VTR;S26SdR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S29S29S29S2cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S29OS29S2cR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27SeSeS4aS2S17A1M0S2S0SeS58A2M1A1S2S0S12S12A2M2A1S29S11S2S25Q40A1A1M3G2S31G2R1R5A3S31G2R2S10RbA1A3F_;Fr;S2eSaG0A1S5bRaR9R8A3S7G0R7A2A3S2eS9S5aRbRaR9R8S3eG1SeS5SeS58A2R7A4A5S4A3S11G3VTR;S26SdRfRdR2R1A5S57SdS16SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S2S40A1M4S4bS3fS28SdR9R8R10S1G4S5dR3S5eR2R1A2A4A5R13RaR9R4R2A4R13S49S48RbRfS3cR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS58G4S4bS3fS11G3G4S4bS3fS31G1S1SeS58RaR9A4R14A3S28SdR12R11R19S1G4S5dR9S5eR8R7A2A4A5R1cR13R12RaR8A4S6aS16SfR1aA1A1S49S48R14R18S3cR9R13RaA3A3R19A2R8A3S28SdR9R8ReS1G4S5dR7S5eR6R5A2A4A5ReS49S48R16R1aS3cRbR15RcA3A3R1bA2R15RaR9R8R6A6S2dS7aR17S3cRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S6bR18S3cRdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S26SdS59R11S49S48R19R1dS3cReR18RfA3A3R1eA2R18RdRcA5S7bR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26SdR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S18SeS11S2S25Q40A1A1S29R6R3A1VTR;S26SdVJAv;R6A1R5R4R3A5R2A2F_;VTR;S26SdVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CHVN : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S66S11S2S25Q40A1A1S65Z5R3A2VTR;S26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S67S50S4S60A3AaS5fR3R2A5S57SdS64R3R2S68VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4eR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4fA3S36S4cR7R5A3S2dS39Z0S35S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2VTR;S26SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_vn : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0VTR;S26SdVJAFv;S32S41A2S47R3R2A5VFAM;S35S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S47S41A4U1A4S1SbS12S42S43Z11S44A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof avn_checks as (Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr).
  pose proof avn_checks2 as (_ & _ & CLN & _ & Cnp & Cnx & ClcL & CL26 & CiC & _ & _ & _ & Cfb).
  set (ndv := NDA tv_vn frL bd_vn (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_vn rho tp)).
  { intros w Hw. rewrite <- E_vn_eq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_vn rho E_hvn E_vn1 tp w E_vn1_ok).
      unfold ndv, tv_vn. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vn _ E_hvn rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hvn rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [exact (room_vn_holds rho HF1) | constructor]. }
  apply TR_facts. intros HF.

  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_vn HF CLN HTK HZ). unfold tv_vn. apply in_or_app. left. exact lines_in_kept. }
  intros Hdnz.

  unfold ndv, tv_vn.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hvn CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HVN.Pre_hvn (ndh h0 true HVN.nd0) PDk_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVN eq_refl
           E_vn s_vn R_vn Xk_vn rho tp kept_vn passed_vn frL bd_vn brest_vn (AHead pH true) (FAM (efmeasA (E_hvn, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_vn rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_vn frL rho' HK lines_in_kept Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    cbn [PDk_vn liftPD PDh PD_hvn map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite T_vn_ok0_eq, nd_vn_ok_eq.
      apply (TR_pre (SPA segs (JAv nd_vn_ok) T_vn_ok rho' tp')).
      { intros w Hw. rewrite <- T_vn_ok_eq. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vn_ok) (xfb T_vn_ok0) rho' T_vn_ok0 B_vn_ok tp' w B_vn_ok_ok Hw). }
      apply (CUTV T_vn_ok nd_vn_ok 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvn T_vn_ok ndA1 nd_vn_ok 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite T_vn_f0_eq, nd_vn_f_eq.
      apply (TR_pre (SPA segs (JAv nd_vn_f) T_vn_f rho' tp')).
      { intros w Hw. rewrite <- T_vn_f_eq. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vn_f) (xfb T_vn_f0) rho' T_vn_f0 B_vn_f tp' w B_vn_f_ok Hw). }
      apply (CUTV T_vn_f nd_vn_f 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvn T_vn_f ndA1 nd_vn_f 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S23SdVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6eSdS6dVAInv;VCST;VXGL;A5").

Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S45A2S62R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S46A2S63R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVN_T : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S66S11S2S25Q40A1A1S65Z5R3A2S2bSdVok;S26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S67S50S4S60A3AaS5fR3R2A5S57SdS64R3R2S68VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4eR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vn.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hvn CST) PTrue HVN.Pre_hvn (ndh h0 true HVN.nd0) (PDh PD_hvn h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hvn CST) PTrue HVN.Pre_hvn HVN.nd0 PD_hvn NF h0 true h0_lt HamC_vn HamPD_vn (P0_hvn_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vn_sum AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4fA3S36S4cR7R5A3S2dS39Z0S35S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2S2bSdVok;S26SdVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertV_ok 200%nat cps_arm NP cutsV exitsV ok (FAMQ tp0') Hok
           ecertV_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsV In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
Qed.

Theorem arm_vn_T : ltac2:(tb__ "0|1|
S11S2S25Q40A1A1M0G0S2bSdVok;S26SdVJAFv;S32S41A2S47R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vn (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHVN_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6fSdS6dVAInv;VCST;VXGL;A5").

Variable FAM : ltac2:(tb__ "0|0|
SbS2S25Q40A1A1S29F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SbSbS2S25Q40A1A1S2cS39R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S45A2S62R3R2A5VFAM;S35S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S62S45A4U1A4S1SbS12S42S43Z1S44A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S46A2S63R3R2A5VFAM;S35S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S63S46A4U1A4S1SbS12S42S43Z1S44A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVN_E : ltac2:(tb__ "0|1|
S2S0SbSbA2M0A1S2S0G0SbA2A1S66S11S2S25Q40A1A1S65Z5R3A2S2aSdS26SdS1aVAInv;VCST;VXGL;VKc;S2fVCST;R6R5A3R6R5R4S19S67S50S4S60A3AaS5fR3R2A5S57SdS64R3R2S68VAInv;VCST;VXGL;VKc;S2fVCST;A1S19S4eR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vn.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hvn CST) PTrue HVN.Pre_hvn (ndh h0 true HVN.nd0) (PDh PD_hvn h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hvn CST) PTrue HVN.Pre_hvn HVN.nd0 PD_hvn NF h0 true h0_lt HamC_vn HamPD_vn (P0_hvn_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vn_sum_ex AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS18S3S0SbS12A2M0S11S2S25Q40A1A1M1SbG1S31S0S0S0SeS18A2M2S3A2M3G0A2S1G3G0S1G2S3S1SeS18R8R7A4R6A4R5A4S4fA3S36S4cR7R5A3S2dS39Z0S35S1G3G0S1G2S3S1SeS18RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2S2aSdS26SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertV_ok 200%nat cps_arm NP cutsV exitsV (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertV_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsV In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vn tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE rho1 tp1 w (proj1 (proj2 (proj2 (proj2 avn_checks2))))). exact Hw.
Qed.

Theorem arm_vn_E : ltac2:(tb__ "0|2|
S11S2S25Q40A1A1M0G0S2aSdS26SdVJAFv;S32S41A2S47R3R2A5VFAM;S35S1S0S0SeS18A2M1S3A2S0SbS12A2S1G1S3S1SeS18S47S41A4U1A4S1SbS12S42S43Z11S44A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vn (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHVN_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_avn_pf.

(* [comment removed for export] *)
Module Lib_load_obj_pro_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "Some"; "option"; "prod"; "list"; "app"; "pair"; "andb"; "false"; "S"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "ss_objs"; "sprop"; "swf"; "cell"; "dflt_writable"; "ob_cells"; "ob_dflt"; "sprop_eqb"; "sv_eqb"; "DUnknown"; "SVar"; "obj_wf"; "sstate"; "DZero"; "SPAlign"; "SPBranch"; "SPEq"; "SPNot"; "SPUle"; "mkCell"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_next"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "fr_lo"; "NP"; "vF"; "g5"; "Pre_ms"; "E_ma"; "E_mo0"; "E_mz0"; "T_f8a1"; "T_sm1"; "E_f8a"; "E_f8a0"; "E_f8a1"; "E_mo1"; "E_mz"; "E_sm0"; "T_f8a2"; "T_mo1"; "s_ma"; "L_ms"; "objs_butlast"; "s_sm"; "C_pro0"; "E_mz2"; "Pre_ma"; "R_ma"; "X_lo"; "idxB"; "Pre_00"; "Pre_f8"; "Pre_sm"; "R_f8a"; "R_mo"; "R_mz"; "R_sm"; "s_f8a"; "s_mo"; "s_mz"; "E_f8a2"; "E_mz1"; "L_sm"; "T_f8a0"; "T_mo0"; "T_sm"; "E_ma0"; "L_00"; "L_f8"; "T_mz0"; "W2"; "sel_last"; "vFL"; "xf_shback"; "xf_shcall"; "C_pro"; "C_pro2"; "C_pro3"; "Pre_lo"; "T_mz1"; "bslot"; "fpiece"; "fslot"; "idxF"; "idxFlo"; "ilast"; "sel2last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs"; "Fx"; "nx"; "nd_r1"; "bd_pro"; "nd_r2"; "zmid"; "Tn8"; "XN"; "cv_1"; "cv_i"; "cv_xf"; "showR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXSelect"; "AXRebase"; "AXMerge"; "AXUnbase"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "tv_factsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk"; "frameFb"; "pure_shape"; "lastO"; "fUle"; "wr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "T_s00_1"; "T_ma_null"; "E_mb"; "E_mc"; "E_s00"; "E_s00_0"; "Pre_mc48"; "E_mc3"; "E_mb0"; "E_mc1"; "E_mc2"; "R_mb"; "R_mc"; "R_s00"; "blkAR"; "s_mb"; "s_mc"; "s_s00"; "E_mc4"; "E_mc5"; "E_s00_1"; "T_ma_ok0"; "T_s00_0"; "vARn"; "E_mc0"; "L_mc48"; "T_mb0"; "T_mb"; "T_mc"; "T_s00"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_pro_chk.K2"; "xextraLO"; "robjs_chkC"; "xrs_chkC"; "xr_inlits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bd_wpos"; "KU"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.LI"; "bd_lo0"; "nd_lo0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "frame_open_stateA"; "local_ok"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "last"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "V_RES"; "L_malloc_null"; "L_malloc_ok"; "V_FLAG"; "flagbyte_obj"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "sm5_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_pro_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module K2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2. End K2. Module HK. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit. End HK.

Definition extraXlo (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2S2L_;Sb3Vr;A1S3Sb6Vr;A1X2x2").
Definition pure_shape (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
SccS10S10ScScS9S17A1M0S2Lx;SdeS11VPre;A1S11R1A1A2S3S17G0SdLl;Ls;X9x2SbcVPre;R1A2A2S22S13R1A1S13VPre;A1A2A2LL;VLs;A3").
Definition frameFb (A : axst) : bool := ltac2:(tb__ "0|0|
S16S4S1bS2aS15S37A1S36A2S4S1bS2cS24S37A1S19Se4Se3Z2Z3dA2Z1A2A1A2S5S1bA1A3A3S75VA;A1A2").
Definition fUle : sprop := SPUle vF (SLit (140737479966720 - 2048)).

Lemma pro_chk_sm : ltac2:(tb__ "0|f|
S1S0S9S8S89Sd0A2M0A1S80S6cA1S4G0SbS89Sd0SddSd1A4S5G0A1A3A3S1S0S7S9S17A1M1A1SbaS43S52S49A3S6G1S56A2A3S1S0S2Sb9S43S52S49S56S4S10S5cS5S10A1A3A5S3A3S1S0S2Sb8S35S49A2S3A3S1S0S2S8dS35S76S43A1M2A2S3A3S1S0S2S8bG2Sc4A2S3A3S1S0S2SbeSc3A1S3A3S1S0S18Sc5SbbS49S52S5cS43A4M3Sd6A2S36A3S1S0S2S8dG2P6eM4A2S3A3S1S0S18Sc5G3Sd9A2S66A3S1S0S2S8dG2P78A2S3A3S1S0S2Sb4S75S43A1M5S5S8S18S18A2M6A1M7S5S8S8S18S89A2S18A2A1M8S81S56A5S3A3S1S0S2Sb5G5G7G8Sb3S12S43A1A5S3A3S1S0S18Sc5S49PcA2S19Z7c0A1A3S1S0S10Sb7S52S43S49S56S5cA5S5fA3S1S0S7S10A1S83S5fS4S82S85S65S5fU3A2A1S5S82A1A3A2S6S10S3dA2A3S1S0S18S13S3dA1S19Sc1A1A3S1S0G1S1aS11S3dA1A1SaS17S48S3dA1M9S4S17SdaS66S4S1dS2dS19Z0A1MaZ1MbS19GbA1A3S5S1dA1A3A2S5S17A1A3A3A3S1S0S9G6A1S12S3dA1SaG6S4eS4G6SbS18S18S36S19Sc2Z5McA1MdA1A4G7A3A3A3S1S0S2S1cS11Sc9S3dG9SaG6S4eG7A3G4GdA5A1A1S3A3S1S0S2S8dS35S76S3dA1MeA2S3A3S1S0S2S8bGeS77A2S3A3S1S0S10Sc9S3dG9S4eG4GdA5S4aA3S1S0S10Se0S4aS4G6SbS18S18S36GaA4S12S4aA1A3A2S69A3S1S0S2ScbS1bS21S28G4GcA2A1S75S4aA1A3S3A3S0S2S8eG4S76S4aA1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_f8 : ltac2:(tb__ "0|14|
S1S0S18S13S3fA1S19Sc1A1M0A3S1S0S9S17A1M1S1aS11S3fA1A1M2SaS17S48S3fA1M3S4S17Sc8S37Z0Z100S1fScdS17G2S7aA3A1S27A5S5S17A1M4A3A3A3S1S0S2S90S3fA1S3A3S1S0S2S8bS76S3fA1S77A2S3A3S1S0S2S8fS75S3fA1S5S8S18S18A2A1M5S34S81G3A5S3A3S1S0S10Sc6S3fG3P6eM6S5S8S89S89A2A1M7A4S40A3S1S0S18S13S40A1G0A3S1S0S2S90S40A1S3A3S1S0S2Sd3S4eS12S40A1A2S3A3S1S0S2S1cS11Sc7S40S4eS37Z44M8Ze7M9A5MaA1A1S3A3S1S0S10GaS5aA3S1S0S2S8fS75S40A1G5S34S81S1aS11S40A1A1A5S3A3S1S0S7S10A1MbS83S5aS68S5aG8A2A2S6S10S3eA2A3S1S0S7G1A1SbaS3eS51S57A3S6G1S53A2A3S1S0S2Sb9S3eS51S57S53S4S10S62S5S10A1A3McA5S3A3S1S0S2Sb8S35S57A2S3A3S1S0S2S8dS35S76S3eA1MdA2S3A3S1S0S2S8bGdS77A2S3A3S1S0S2SbdGdSc3A2S3A3S1S0S2S91S51GcA2S3A3S1S0S2Sb4S75S3eA1MeG5S34S81S53A5S3A3S1S0S2Sb5GeG5S34Sb3S12S3eA1A5S3A3S1S0S10Sb7S51S3eS57S53S62A5S5dA3S1S0GbS83S5dS67S5dA1A2S6S10S3cA2A3S1S0S18S13S3cA1G0A3S1S0G1S1aS11S3cA1A1MfSaS17S48S3cA1M10S4S17Sc8S37G8G9S1fScdS17GfS7aA3M11A1S20G11A1M12A5G4A3A3A3S1S0S2S1eG12A1S3A3S1S0S2S90S3cA1S3A3S1S0S2S8bS76S3cA1S77A2S3A3S1S0S2S8fS75S3cA1G5S34S81G10A5S3A3S1S0S10Sc6S3cG10G6G7A4S44A3S1S0S18S13S44A1G0A3S1S0S2S90S44A1S3A3S1S0S2S1cS11Sc7S44S12S44A1S37G9Zf8A5M13A1A1S3A3S1S0S10G13S6aA3S0S2S8fS75S44A1G5S34S81S1aS11S44A1A1A5S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition lastO (A : axst) : sobj := ltac2:(tb__ "0|0|
ScdS17S1aS11VA;A1A1S7aA3").
Definition wr_at (A : axst) (i : nat) : bool := ltac2:(tb__ "0|0|
S7S17A1S2Lx;SceS17S1aS11VA;A1A1Vi;A3S17S1eS20R1A1A1Lo;SdX7x2").

Lemma pro_chk_mo : ltac2:(tb__ "0|a|
S1S0S18S13S3aA1S19Sc1A1M0A3S1S0S9S17A1M1S1aS11S3aA1A1SaS17S48S3aA1M2S4S17Sc8S37Ze7Zf8S1fS92S3aA1M3A1S20G3A1M4A5S5S17A1A3A3A3S1S0S2S1eG4A1S3A3S1S0S2S90S3aA1S3A3S1S0S2S8bS76S3aA1S77A2S3A3S1S0S2S8fS75S3aA1S5S8S18S18A2A1M5S34S81G2A5S3A3S1S0S10Sc6S3aG2P6eS5S8S89S89A2A1A4S41A3S1S0S7G1A1SbaS41S38S58A3S6G1S54A2A3S1S0S2Sb9S41S38S58S54S4S10S47S5S10A1A3M6A5S3A3S1S0S2Sb8S35S58A2S3A3S1S0S2S8dS35S76S41A1M7A2S3A3S1S0S2S8bG7S77A2S3A3S1S0S2SbdG7Sc3A2S3A3S1S0S2S91S38G6A2S3A3S1S0S2Sb4S75S41A1M8G5S34S81S54A5S3A3S1S0S2Sb5G8G5S34Sb3S12S41A1A5S3A3S1S0S10Sb7S38S41S58S54S47A5S5eA3S1S0S7S10A1S83S5eS4S82S85S65S5eU1A2A1S5S82A1A3A2S6S10S45A2A3S1S0S18S13S45A1G0A3S1S0S2S90S45A1S3A3S1S0S2S1cS11Sc7S45S12S45A1S37Z20Z40A5M9A1A1S3A3S1S0S10G9S6bA3S0S2S8fS75S45A1G5S34S81S1aS11S45A1A1A5S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_mz : ltac2:(tb__ "0|15|
S1S0S18S13S3bA1S19Sc1A1A3S1S0S9S17A1M0S1aS11S3bA1A1SaS17S48S3bA1M1S4S17Sc8S37Z20M2Z40M3S1fS92S3bA1M4A1M5S20G4A1M6A5S5S17A1A3A3A3S1S0S2S1eG6A1S3A3S1S0S2S90S3bA1S3A3S1S0S2S8bS76S3bA1S77A2S3A3S1S0S2SccS8S89S89A2M7ScaG5G6G2G3A4S4G7SbS89S89Z1d0Z30A4S5G7A1A3M8A3S3A3S1S0S2S8fS75S3bA1S5S8S18S18A2A1M9S34S81G1A5S3A3S1S0S10Sc6S3bG1P6eG8A4S5bA3S1S0S7S10A1MaS83S5bS4S82S84S71S5bA1MbS19Z1f0McA1A2S4S82S84SeGbA1MdS19Z200MeA1A2S5S82A1MfA3A3A2S6S10S4bA2A3S1S0S7S17A1SceS17S1aS11S4bA1M10A1GdA3S6S17S6fGcGeS5S1dA1M11S23A4A2A3S1S0S2S25S76S4bA1S70GcZ10G11S23A4M12A2S3A3S1S0S2ScbS1bS21S93A1S75S4bA1A3S3A3S1S0S10S14S4bSd2G10GdG12A3A2S42A3S1S0S7G0A1SbaS42S38S59A3S6G0S55A2A3S1S0S2Sb9S42S38S59S55S4S10S47S5S10A1A3A5S3A3S1S0S2Sb8S35S59A2S3A3S1S0S2S8dS35S76S42A1M13A2S3A3S1S0S2S8bG13S77A2S3A3S1S0S2SbdG13Sc3A2S3A3S1S0S2Sb4S75S42A1M14G9S34S81S55A5S3A3S1S0S2Sb5G14G9S34Sb3S12S42A1A5S3A3S1S0S10Sb7S38S42S59S55S47A5S63A3S0GaS83S63S4S82S86U1A1GfA3A2S6S10S6dA2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_ma : ltac2:(tb__ "0|c|
S1S0S7S10A1S83S60S4S82S84S72S60A1S19N10A1A2S5S82A1A3A2S6S10S39A2A3S1S0S7S9S17A1M0A1SbaS39S4cS46A3S6G0S4dA2A3S1S0S2Sb9S39S4cS46S4dS4S10Sd7Sd4S64Sd5A3M1S4S10Sd8Sd4S64Sd5A3M2S5S10A1A3A3A5S3A3S1S0S2Sb8S35S46A2S3A3S1S0S2S8dS35S76S39A1M3A2S3A3S1S0S2S8bG3S77A2S3A3S1S0S2SbdG3S78A2S3A3S1S0S2S33G3Sc5S46PcA2M4A2S3A3S1S0S18Sc5SbbS46S4cG2S39A4Sd6A2S24SdfG3UaA2A1M5A3S1S0S2Sc0S75S39A1M6G4SbfSc3S78A5S3A3S1S0S2Sb4G6S5S8S18S18A2A1M7S34S81S4dA5S3A3S1S0S2Sb5G6G7S34Sb3S12S39A1A5S3A3S1S0S18G4S19Z40M8A1A3S1S0S18G5SacA3S1S0S10Sb7S4cS39S46S4dG1A5S96A3S1S0S18S13S96A1S19Sc1A1A3S1S0S2S90S96A1S3A3S1S0S2Sd3S7cS96A1M9S12S96A1A2S3A3S1S0S2S1cS11Sc7S96G9S37Z20G8A5MaA1A1S3A3S1S0S10GaS7bA3S1S0S2S8fS75S96A1G7S34S81S1aS11S96A1A1A5S3A3S1S0S10Sb7S4cS39S46S4dG2A5SaaA3S1S0S2SccS1bS31S76SaaA1A1SaS1bS8cSa3A1S75SaaA1MbA3A3S3A3S0S2ScbS1bS21S2bS29SdcSacS19Z0A1A3A1A1GbA3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_mc : ltac2:(tb__ "0|d|
S1S0S7S10A1M0S83SadS4S82S84S4fSadSacZ0M1A3S19Z30A1A2S5S82A1M2A3A2S6S10S9eA2A3S1S0S7S26A1Se2S11S9eA1S4fS9eS36Z1f0M3A3S4S1dScfG3S19G1A1M4A2S4S1dScfZ1f8G4A2S5S1dA1A3A3A3S6S26S11S9fA1M5A2A3S1S0S2S1cG5A1S3A3S1S0S10S14S9eG5A2S9fA3S1S0G0S83S9fS4S82S84S4fS9fS36G1A3S19Z1d0M6A1A2G2A3A2S6S10S9cA2A3S1S0G0S83S9cS4S82S85S74S9cS4fS9cS36G6A3S4fS9cS36G3A3A3A1G2A3A2S6S10Sa7A2A3S1S0G0S83Sa7S4S82S87SdbSfS17S1aS11Sa7A1A1A2U2A2A1G2A3A2S6S10Sa8A2A3S1S0G0S83Sa8S4S82S88S73Sa8A1G6A2G2A3A2S6S10S98A2A3S1S0S7S9S17A1M7A1SbaS98S9bSa5A3S6G7Sa1A2A3S1S0S2Sb9S98S9bSa5Sa1S4S10SaeS5S10A1A3M8A5S3A3S1S0S2Sb8S35Sa5A2S3A3S1S0S2S8dS35S76S98A1M9A2S3A3S1S0S2S8bG9S79A2S3A3S1S0S2SbdG9S78A2S3A3S1S0S2SbeS78A1S3A3S1S0S2S91S9bG8A2S3A3S1S0S8aS32S11S9bA1A1Se1A3S1S0S18S13S9bA1S19Sc1A1A3S1S0S2Sb4S75S98A1MaS4S8S18S18A2MbSa3S5GbA1A3McS34S81Sa1A5S3A3S1S0S2Sb5GaGcS34Sb3S12S98A1A5S3A3S0S10Sb7S9bS98Sa5Sa1SaeA5Sb1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_s00 : ltac2:(tb__ "0|11|
S1S0S18S13S9aA1S19Sc1A1M0A3S1S0S2S90S9aA1S3A3S1S0S2S1cS11Sc7S9aS12S9aA1S37Z44M1Ze7M2A5M3A1A1S3A3S1S0S10G3Sa9A3S1S0S2S8fS75S9aA1S4S8S18S18A2M4Sa3S5G4A1A3M5S34S81S1aS11S9aA1A1A5S3A3S1S0S7S10A1M6S83Sa9S68Sa9G1A2A2S6S10S99A2A3S1S0S7S9S17A1M7A1SbaS99S50Sa6A3S6G7Sa2A2A3S1S0S2Sb9S99S50Sa6Sa2S4S10S61S5S10A1A3M8A5S3A3S1S0S2Sb8S35Sa6A2S3A3S1S0S2S8dS35S76S99A1M9A2S3A3S1S0S2S8bG9S79A2S3A3S1S0S2SbdG9S78A2S3A3S1S0S2S91S50G8A2S3A3S1S0S2Sb4S75S99A1MaG5S34S81Sa2A5S3A3S1S0S2Sb5GaG5S34Sb3S12S99A1A5S3A3S1S0S10Sb7S50S99Sa6Sa2S61A5SabA3S1S0G6S83SabS67SabA1A2S6S10S95A2A3S1S0S18S13S95A1G0A3S1S0G7S1aS11S95A1A1SaS17S48S95A1MbS4S17Sc8S37G1G2S1fS92S95A1McA1MdS20GcA1MeA5S5S17A1A3A3A3S1S0S2S1eGeA1S3A3S1S0S2S90S95A1S3A3S1S0S2S8bS76S95A1S79A2S3A3S1S0S2SccS8S89S89A2MfScaGdGeG1G2A4S4GfSbS89S89Z220Z518A4S5GfA1A3M10A3S3A3S1S0S2S8fS75S95A1G5S34S81GbA5S3A3S0S10Sc6S95GbP6eG10A4Sb2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma pro_chk_mb : ltac2:(tb__ "0|c|
S1S0S7S10A1M0S83S9dS7fS9dS36Z280M1Z4b8M2A4A2S6S10S7dS9dS36G1G2A4M3A2A3S1S0S2S94G3SeS7eS9dS36G1A3A1M4A2S3A3S1S0S2S25S76G3A1S6eS36G1G2A3M5A2S3A3S1S0S2ScbS1bS21S93A1S75G3A1A3S3A3S1S0S2S7S17A1S2Lx;SceS17S1aS11G3A1M6A1G4A3S17ScScS22S2eR1A1S36A2S22S30R1A1S19G1A1A2A2S22S2fR1A1S19Z738A1A2A2Lo;SdX7x2S3A3S1S0S10S14G3Sd2G6G4G5A3A2S97A3S1S0S7S9S17A1M7A1SbaS97S38Sa4A3S6G7Sa0A2A3S1S0S2Sb9S97S38Sa4Sa0S4S10S47S5S10A1A3A5S3A3S1S0S2Sb8S35Sa4A2S3A3S1S0S2S8dS35S76S97A1M8A2S3A3S1S0S2S8bG8S79A2S3A3S1S0S2SbdG8S78A2S3A3S1S0S2Sb4S75S97A1M9S4S8S18S18A2MaSa3S5GaA1A3MbS34S81Sa0A5S3A3S1S0S2Sb5G9GbS34Sb3S12S97A1A5S3A3S1S0S10Sb7S38S97Sa4Sa0S47A5SafA3S0G0S83SafS4S82S86U1A1S5S82A1A3A2S6S10Sb0A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_pro_chk.

(* [comment removed for export] *)
Module Lib_load_obj_land_chk2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "Some"; "nil"; "S"; "option"; "nat"; "prod"; "list"; "app"; "fst"; "pair"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sstate"; "ss_next"; "swf"; "sprop"; "SVar"; "sobj"; "ss_facts"; "sv_eqb"; "SPUle"; "sprop_eqb"; "sprop_below"; "ss_objs"; "valuation"; "ob_base"; "ob_hi"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land"; "s_blr"; "E_blr"; "s_landAE"; "s_landBE"; "iK"; "R_blr"; "T_blr0"; "T_blr0a"; "T_blr1"; "T_blr1a"; "cps_land"; "E_blr1"; "E_blr2"; "K0a"; "K0b"; "M_afterE"; "M_bodyE"; "XR_after0"; "XR_body0"; "XkB"; "iD"; "E_blr0"; "XR_after1"; "XR_body1"; "iC"; "tv_pass"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "FUEL_lo"; "find_idxb"; "idxB"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2.BLR"; "Pre_blr"; "P_ret0"; "P_ret1"; "nd_pre"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "ndLE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tv_sub_eqb"; "import_tv"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "fr_below"; "AHead"; "am_eqb"; "am_subst"; "nd_bd"; "fr_sub_eqb"; "ndesc"; "ANone"; "nd_am"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk"; "tv1"; "V_P"; "add_objs"; "add_objs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2"; "Ab0"; "Ab1"; "Za1_a0"; "Za1_b0"; "Za2_a0"; "Za2_b0"; "Za3_a0"; "Za3_b0"; "Za4_a0"; "Za4_b0"; "Zs1_a0"; "Zs1_b0"; "Zs2_a0"; "Zs2_b0"; "Zs3_a0"; "Zs3_b0"; "Zs4_a0"; "Zs4_b0"; "i1256_a0"; "i1256_b0"; "i480_a0"; "i480_b0"; "i880_a0"; "i880_b0"; "i96_a0"; "i96_b0"; "tvLand_a0"; "tvLand_b0"; "C10_a0"; "C10_b0"; "C11_a0"; "C11_b0"; "C12_a0"; "C12_b0"; "C13_a0"; "C13_b0"; "C9_a0"; "C9_b0"; "D1_a0"; "D1_b0"; "D2_a0"; "D2_b0"; "nulls_a0"; "nulls_b0"; "xfb"; "XF_a0"; "XF_b0"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "T_afterA3"; "pdescA"; "pd_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.BLRAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2.BLRP"; "PDk_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "datasA"; "pH"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "fnodup"; "xnodup"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "B32"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVAy TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition tvLand_b0 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landBE) tvL.
Definition nulls_b0 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_b0.
Definition bdLand_b0 : list bitem := Eval vm_compute in bd_subst s_landBE (nd_bd ndLE).
Definition XF_b0 : list axform := Eval vm_compute in canon_xf XR_body0.
Definition C9_b0 : axst := Eval vm_compute in optL (apply_axforms XR_body0 XF_b0).
Definition i96_b0 : nat := Eval vm_compute in idxB C9_b0 bA 96.
Definition D1_b0 : axst := Eval vm_compute in optL (apply_axforms C9_b0 [AXSplit i96_b0 (SLit 104)]).
Definition Za1_b0 : axst := Eval vm_compute in zs1 D1_b0 (S i96_b0) 112.
Definition Zs1_b0 : sstate := Eval vm_compute in zs2 Za1_b0 (S i96_b0) [c8 104 (SLit 0)].
Definition D2_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_b0 Zs1_b0) [AXMerge (S i96_b0)]).
Definition C10_b0 : axst := Eval vm_compute in optL (apply_axforms D2_b0 [AXMerge i96_b0]).
Definition i480_b0 : nat := Eval vm_compute in idxB C10_b0 bA 480.
Definition Za2_b0 : axst := Eval vm_compute in zs1 C10_b0 i480_b0 488.
Definition Zs2_b0 : sstate := Eval vm_compute in zs2 Za2_b0 (S i480_b0) [c1 488 (SLit 0)].
Definition C11_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_b0 Zs2_b0) [AXMerge i480_b0]).
Definition i1256_b0 : nat := Eval vm_compute in idxB C11_b0 bA 1256.
Definition Za3_b0 : axst := Eval vm_compute in zs1 C11_b0 i1256_b0 1260.
Definition Zs3_b0 : sstate := Eval vm_compute in zs2 Za3_b0 (S i1256_b0) [c4 1260 (SLit 0); c1 1264 (SLit 0)].
Definition C12_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_b0 Zs3_b0) [AXMerge i1256_b0]).
Definition i880_b0 : nat := Eval vm_compute in idxB C12_b0 bA 880.
Definition Za4_b0 : axst := Eval vm_compute in zs1 C12_b0 i880_b0 904.
Definition Zs4_b0 : sstate := Eval vm_compute in zs2 Za4_b0 i880_b0 [c1 885 (SLit 0)].
Definition C13_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_b0 Zs4_b0) [AXMerge i880_b0]).

Lemma pipe_b0 : ltac2:(tb__ "0|9|
S1S0S8S11A1M0S17S41Sa7A2S5S11S9eA2A3S1S0G0S17S9eS4S16S18S92S1cZ68M1A1A2S6S16A1M2A3A2S5S11Sa0A2A3S1S0G0S17Sa0S4S16S18S7S92A1M3S1cZ70A1A2G2A3A2S5S11S7cA2A3S1S0S8S1fA1M4S53S12S7cA1G3S4S1eSbfG1S1cZ0A1M5A2S6S1eA1M6A3A3S5S1fS84A2A3S1S0S3S21S84A1S2A3S1S0G0S17S13S7cS84A2S4S16S19G3A1G2A3A2S5S11Sa2A2A3S1S0G0S17Sa2S4S16S19S92A1G2A3A2S5S11S96A2A3S1S0G0S17S96S4S16S18S8eS1cZ1e8M7A1A2G2A3A2S5S11S7eA2A3S1S0G4S53S12S7eA1S7S8eA1S4S1eS5fG7G5A2G6A3A3S5S1fS86A2A3S1S0S3S21S86A1S2A3S1S0G0S17S13S7eS86A2S4S16S19S8eA1G2A3A2S5S11S98A2A3S1S0G0S17S98S4S16S18S8cS1cZ4ecM8A1A2G2A3A2S5S11S80A2A3S1S0G4S53S12S80A1S7S8cA1S4S1eS60G8G5A2S4S1eS5fZ4f0G5A2G6A3A3A3S5S1fS88A2A3S1S0S3S21S88A1S2A3S1S0G0S17S13S80S88A2S4S16S19S8cA1G2A3A2S5S11S9aA2A3S1S0G0S17S9aS4S16S18S90S1cZ388A1A2G2A3A2S5S11S82A2A3S1S0G4S53S12S82A1S90S4S1eS5fZ375G5A2G6A3A3S5S1fS8aA2A3S1S0S3S21S8aA1S2A3S1S0G0S17S13S82S8aA2S4S16S19S90A1G2A3A2S5S11S9cA2A3S0S11S9cS3dA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_b0 : ltac2:(tb__ "0|1|
S1S0S11S77S3fSb9SbbA1M0A2SceA3S0S3S78S3fG0A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_b0 : ltac2:(tb__ "0|3|
S1S0S3S15S3dS3fS32A3S2A3S1S0S3S65S32S4eA2S2A3S1S0S3S5dS4eS20S12S3dA1A1M0A2S2A3S1S0S3S67S32S94S4bA3S2A3S1S0S3S6fS32S4aS4aA3S2A3S1S0S3S6cS6dS32S6bSbaS2A2A2S6bS1cZ0A1M1S2A2A2S2A3S1S0S3Sc9ScSaS1dS1dA2M2S75Sa4A3S94A2S2A3S1S0S3S4cG2Sc7Sa4A3S2A3S1S0S3S66G0S94A2S2A3S1S0S3S6aG0S4aA2S2A3S1S0SbSb1A1Sb0S32S6eS62A1A2Sa9A3S0S3S4cS2eS2eS26S64S32R1A2G1A2Lx;SacS9S2eS5eSadU190U36A2A4A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition tvLand_a0 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landAE) tvL.
Definition nulls_a0 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_a0.
Definition bdLand_a0 : list bitem := Eval vm_compute in bd_subst s_landAE (nd_bd ndLE).
Definition XF_a0 : list axform := Eval vm_compute in canon_xf XR_after0.
Definition C9_a0 : axst := Eval vm_compute in optL (apply_axforms XR_after0 XF_a0).
Definition i96_a0 : nat := Eval vm_compute in idxB C9_a0 bA 96.
Definition D1_a0 : axst := Eval vm_compute in optL (apply_axforms C9_a0 [AXSplit i96_a0 (SLit 104)]).
Definition Za1_a0 : axst := Eval vm_compute in zs1 D1_a0 (S i96_a0) 112.
Definition Zs1_a0 : sstate := Eval vm_compute in zs2 Za1_a0 (S i96_a0) [c8 104 (SLit 0)].
Definition D2_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_a0 Zs1_a0) [AXMerge (S i96_a0)]).
Definition C10_a0 : axst := Eval vm_compute in optL (apply_axforms D2_a0 [AXMerge i96_a0]).
Definition i480_a0 : nat := Eval vm_compute in idxB C10_a0 bA 480.
Definition Za2_a0 : axst := Eval vm_compute in zs1 C10_a0 i480_a0 488.
Definition Zs2_a0 : sstate := Eval vm_compute in zs2 Za2_a0 (S i480_a0) [c1 488 (SLit 0)].
Definition C11_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_a0 Zs2_a0) [AXMerge i480_a0]).
Definition i1256_a0 : nat := Eval vm_compute in idxB C11_a0 bA 1256.
Definition Za3_a0 : axst := Eval vm_compute in zs1 C11_a0 i1256_a0 1260.
Definition Zs3_a0 : sstate := Eval vm_compute in zs2 Za3_a0 (S i1256_a0) [c4 1260 (SLit 0); c1 1264 (SLit 0)].
Definition C12_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_a0 Zs3_a0) [AXMerge i1256_a0]).
Definition i880_a0 : nat := Eval vm_compute in idxB C12_a0 bA 880.
Definition Za4_a0 : axst := Eval vm_compute in zs1 C12_a0 i880_a0 904.
Definition Zs4_a0 : sstate := Eval vm_compute in zs2 Za4_a0 i880_a0 [c1 885 (SLit 0)].
Definition C13_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_a0 Zs4_a0) [AXMerge i880_a0]).

Lemma pipe_a0 : ltac2:(tb__ "0|9|
S1S0S8S11A1M0S17S40Sa6A2S5S11S9dA2A3S1S0G0S17S9dS4S16S18S91S1cZ68M1A1A2S6S16A1M2A3A2S5S11S9fA2A3S1S0G0S17S9fS4S16S18S7S91A1M3S1cZ70A1A2G2A3A2S5S11S7bA2A3S1S0S8S1fA1M4S53S12S7bA1G3S4S1eSbfG1S1cZ0A1M5A2S6S1eA1M6A3A3S5S1fS83A2A3S1S0S3S21S83A1S2A3S1S0G0S17S13S7bS83A2S4S16S19G3A1G2A3A2S5S11Sa1A2A3S1S0G0S17Sa1S4S16S19S91A1G2A3A2S5S11S95A2A3S1S0G0S17S95S4S16S18S8dS1cZ1e8M7A1A2G2A3A2S5S11S7dA2A3S1S0G4S53S12S7dA1S7S8dA1S4S1eS5fG7G5A2G6A3A3S5S1fS85A2A3S1S0S3S21S85A1S2A3S1S0G0S17S13S7dS85A2S4S16S19S8dA1G2A3A2S5S11S97A2A3S1S0G0S17S97S4S16S18S8bS1cZ4ecM8A1A2G2A3A2S5S11S7fA2A3S1S0G4S53S12S7fA1S7S8bA1S4S1eS60G8G5A2S4S1eS5fZ4f0G5A2G6A3A3A3S5S1fS87A2A3S1S0S3S21S87A1S2A3S1S0G0S17S13S7fS87A2S4S16S19S8bA1G2A3A2S5S11S99A2A3S1S0G0S17S99S4S16S18S8fS1cZ388A1A2G2A3A2S5S11S81A2A3S1S0G4S53S12S81A1S8fS4S1eS5fZ375G5A2G6A3A3S5S1fS89A2A3S1S0S3S21S89A1S2A3S1S0G0S17S13S81S89A2S4S16S19S8fA1G2A3A2S5S11S9bA2A3S0S11S9bS3cA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_a0 : ltac2:(tb__ "0|1|
S1S0S11S77S3eSb9SbbA1M0A2ScdA3S0S3S78S3eG0A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_a0 : ltac2:(tb__ "0|3|
S1S0S3S15S3cS3eS31A3S2A3S1S0S3S65S31S4eA2S2A3S1S0S3S5dS4eS20S12S3cA1A1M0A2S2A3S1S0S3S67S31S93S4bA3S2A3S1S0S3S6fS31S4aS4aA3S2A3S1S0S3S6cS6dS31S6bSbaS2A2A2S6bS1cZ0A1M1S2A2A2S2A3S1S0S3Sc9ScSaS1dS1dA2M2S75Sa3A3S93A2S2A3S1S0S3S4cG2Sc7Sa3A3S2A3S1S0S3S66G0S93A2S2A3S1S0S3S6aG0S4aA2S2A3S1S0SbSb1A1Sb0S31S6eS62A1A2Sa8A3S0S3S4cS2eS2eS26S64S31R1A2G1A2Lx;SacS9S2eS5eSadU190U36A2A4A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xfb (T : axst) : list axform := ltac2:(tb__ "0|3|
S4S16S1aU1M0Sb6A2S4S16S1bS4S9G0S4S9U0M1SadU2M2ScbS10S24S2aS12VT;A1A1A2G2A2A2A3A3A1S4S16S19G1A1S6S16A1A3A3A3").
Definition Ab1 : axst := Eval vm_compute in optL (apply_axforms T_blr1a (xfb T_blr1a)).
Definition Ab0 : axst := Eval vm_compute in optL (apply_axforms T_blr0a (xfb T_blr0a)).
Lemma back_checks : ltac2:(tb__ "0|9|
S1S0S8S11A1M0S17S38Sa5S38A1A2S5S11S7aA2A3S1S0S3Sb2SbdS14S7aA1M1A1M2G1A2S2A3S1S0S3S4cS22S29S20S12S7aA1M3A1A1SbcS25G3A1A1M4A3S2A3S1S0S11SafSaeS7aG2A2G4A2S37A3S1S0G0S17S36Sa5S36A1A2S5S11S79A2A3S1S0S3Sb2SbdS14S79A1M5A1M6G5A2S2A3S1S0S3S4cS22S29S20S12S79A1M7A1A1SbcS25G7A1A1M8A3S2A3S0S11SafSaeS79G6A2G8A2S35A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition bd_bli : list bitem := Eval vm_compute in bd_subst s_blr (nd_bd BLR.nd_pre).
Lemma site_checks : ltac2:(tb__ "0|1c|
S1S0S3Sb2S42S14S30A1A2S2A3S1S0S8SbS24A1M0A1Sc6S30S54S2fA3S5G0S34A2A3S1S0S3Sc5S30S54S2fS34SacSaSaS11S70A2M1S2bS2bOF_;F_;M2A2M3S11G3SdS11S70SdG1G2R1A3A3Ld;Sb8A4A5S2A3S1S0S3ScfS4eS2fA2S2A3S1S0S3Sc3S2fSabA2S2A3S1S0S3S5dS4eS20S12S30A1A1M4A2S2A3S1S0S3S67S2fS48S73S57A1A3S2A3S1S0S3S6cS6dS2fS72S57A1A2S71A2S2A3S1S0S3S4cSaSb4G2A2M5G5Sb5S54SabS2fG4SdSb4G2R1A3A5Ld;Sb8A3S2A3S1S0SbSb1A1Sb0S2fS6eS57A1A2SaaA3S1S0S8S11A1M6S17S44S51S44S23PaA1ScaSb7A1A3S9S4S16S18R1S1cNd8M7A1A2S4S16S18S7R1A1M8S1cNb8A1A2S4S16S1aG8G7A2S6S16A1M9A3A3A3Ti;A2S5S11S3aA2A3S1S0G6S17S3aS50S24S24SfS26S2cR1A1Sc1Sb7A1A2S26S2dR1A1S1cZ0A1MaA2A2Lo;S2aS12S3aA1A1U0A4S9S4S16S18R1S1cScaSb6A1MbA1A2S4S16S1aR1GbA2G9A3A3Ti;A2S5S11S3bA2A3S1S0S11SaeS3bS4SaS1dS1dA2McSeS1dS1dGaGaA4S14S3bA1A3A2S30A3S1S0S3S66G4ScGcS49S48A3A2S2A3S1S0S3S6aG4S4aA2S2A3S1S0SbGcA1MdS68Sc4S2fS54S56S30A4MeS58A2S4GcSeS1dS1dS43SccZ10S33A2A4S6GcA1A3MfA3S1S0GdS68Sc4S2fS54S55S30A4M10S58A2GfA3S1S0S1dS63GeS23P8cM11A1M12A2S43A3S1S0S1dS63GeS23P8dM13A1A2S47A3S1S0S1dS63GeS23P8eM14A1M15A2S33A3S1S0S1dS63G10G12A2S43A3S1S0S1dS63G10G15A2S33A3S1S0S3S4cS2eS2eSc2S69SabS2fG4S12S56A1A4S23R1A1M16A2Lv;S4S2eG11S4S2eG13S4S2eG14S6S2eA1A3M17A3A3A3S2A3S1S0S3S4cS2eS2eSc2S69SabS2fG4S12S55A1A4G16A2Lv;S4S2eG11G17A3A3S2A3S1S0S1dS63S2fS23PdA1A2S52A3S1S0S11Sb3S54S30S2fS34S56S42A6S38A3S1S0S11Sb3S54S30S2fS34S55S42A6S36A3S1S0S3S4dS22S28S27S33S1cSc0A1A2A1M18S25S12S38A1A1M19A3S2A3S1S0S3S4dS22S28S27S47S33A2A1G19A3S2A3S1S0S3S4dS22S28S27S1cSd0A1SbeA2A1M1aG19A3S2A3S1S0S3S4dS22G18S25S12S36A1A1M1bA3S2A3S0S3S4dS22G1aG1bA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma run_checks : ltac2:(tb__ "0|7|
S1S0S3S5bS74S4fS39S20S12S37A1A1M0S4S11S37S6S11A1M1A3S4S11S46S4S11S45G1A3A3A6S2A3S1S0S3S5bS74S4fS39S20S12S35A1A1M2S4S11S35G1A3S4S11S41S4S11S40G1A3A3A6S2A3S1S0S3S5cS74S4fS39G0S4S59S5aS37Z259M3S61A3S6S59A1M4A3S4S59S5aS46Z258M5S61A3S4S59S5aS45G5S61A3G4A3A3A6S2A3S1S0S3S5cS74S4fS39G2S4S59S5aS35G3S61A3G4A3S4S59S5aS41G5S61A3S4S59S5aS40G5S61A3G4A3A3A6S2A3S1S0S3S5dS4eG0A2S2A3S1S0S3S5dS4eG2A2S2A3S1S0S3Sc8G0S76A2S2A3S1S0S3Sc8G2S76A2S2A3S1S0S3S66G0S75A2S2A3S1S0S3S6aG0S4aA2S2A3S1S0S3S66G2S75A2S2A3S1S0S3S6aG2S4aA2S2A3S1S0S3S5dS20S12S30A1A1M6G0A2S2A3S0S3S5dG6G2A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

End Lib_load_obj_land_chk2.

(* [comment removed for export] *)
Module Lib_load_obj_hv3m.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "nat"; "list"; "pair"; "Some"; "option"; "andb"; "app"; "false"; "prod"; "S"; "fst"; "length"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_setS"; "ax_X"; "leafA"; "axwf"; "entailsA"; "g8"; "has_facts"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "sobj"; "SAlu"; "SPUle"; "ss_facts"; "ss_objs"; "sprop_eqb"; "ss_next"; "SVar"; "ss_pc"; "DUnknown"; "cell"; "mkObj"; "obj_wf"; "sv_eqb"; "swf"; "SPEq"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "cb_av"; "d_av"; "vDg"; "vKg"; "bd_grown"; "bd_keep"; "k_av"; "tv_grown"; "tv_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "robjs_chkR"; "sel_front"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "nth_error"; "filter"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "NP"; "g5"; "optR"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "Pre_mc"; "L_mc1"; "E_o1"; "s_mc"; "R_mc"; "T_mcg"; "T_mck"; "dst_obj"; "i_dst"; "mc_chk"; "mid_dst"; "E_mc"; "E_mg"; "E_mg0"; "E_mg1"; "E_mk"; "E_mk0"; "E_mk1"; "Lg0"; "Lg1"; "Lk0"; "Lk1"; "T_mc0"; "T_mcr"; "T_mg0"; "T_mgb"; "T_mgr"; "T_mk0"; "T_mkb"; "T_mkr"; "X_g"; "mc_ok"; "pure_posts_ok"; "s_o1"; "xf_mc"; "xfb_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "c_op"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "optL'"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS";
"shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition E_mk0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_keepS) memcpy_pc 0.
Definition E_mg0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_grownS) memcpy_pc 0.
Definition dst_obj (d : sv) : sobj := ltac2:(tb__ "0|0|
S2cS22S51Vd;S3eA3S1eZ0A1S1eZcA1S3S2bA1S2aA5").
Definition mid_dst (d : sv) : sobj := ltac2:(tb__ "0|0|
S2cVd;S3eS22S51S3eS1eZcA1A3S3S2bA1S2aA5").
Definition xf_mc (d : sv) (T : axst) : list axform := ltac2:(tb__ "0|3|
S47Vd;S1eZ0A1VT;A3S4S0S38S39R1S3eA2S0S38S39SdR1A1M0S22S51S3eS1eZcA1A3A2S3S38A1M1A3A3S5S38A1S85S3aVT;R1A2A1S13S47S52S1eZ20A1R1A3S4SaS38R3S0S38S39R1S1eZ80M2A1A2S0S38S39G0S1eZ8cA1A2S0S38S3dG0G2A2G1A3A3A3A3Tj1;TT1;Tpre;Ti;").
Definition i_dst (d : sv) (E1 : axst) : nat := ltac2:(tb__ "0|0|
S47Vd;S3eVE1;A3").
Definition E_mc (d : sv) (E1 : axst) : axst := ltac2:(tb__ "0|0|
S16VE1;S8bS14VE1;A1S5fVd;VE1;A2S5eVd;A1A3A2").
Definition E_mk1 : axst := Eval vm_compute in optL' (apply_axforms E_mk0 (xf_mc d_av E_mk0)).
Definition E_mg1 : axst := Eval vm_compute in optL' (apply_axforms E_mg0 (xf_mc vDg E_mg0)).
Definition E_mk : axst := Eval vm_compute in E_mc d_av E_mk1.
Definition E_mg : axst := Eval vm_compute in E_mc vDg E_mg1.
Definition Pre_mc : axst := Pre_memcpy memcpy_pc.
Definition L_mc1 : axst := L_memcpy (ae_ret_asan_memcpy AE_A).
Definition s_mc (E : axst) (d k : sv) : wsub := ltac2:(tb__ "0|1|
S0ScS4fS1fA2M0S6S4fS1fP35Vd;A4S0G0S6S4fS1fP36S7dZ4Vk;A2A4S0G0S6S4fS1fP37S22S51S52S1eZ80A1A3A4S0G0S6S4fS1fP38S1eZcA1A4S0G0S6S4fS1fS9bS56A4S87PaS14VE;A1S14S57A1A3A3A3A3A3A3").
Definition R_mc (E : axst) (d k : sv) : list sobj := ltac2:(tb__ "0|0|
S55S88VE;S57S5aVE;Vd;Vk;A3A3A1").
Definition mc_ok (E : axst) (d k : sv) : bool := ltac2:(tb__ "0|2|
S8S5S21A1M0A1S1Lx;S88VE;S57S5aVE;Vd;Vk;A3M1A3G0S89VE;S57G1R1S0S13S58S0S13S58S3S13A1A3A3A5LR;SbX8x2").
Definition T_mc0 (E : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
S97S57VE;S5aVE;Vd;Vk;A3S5bVE;Vd;Vk;A3S58A5").

Definition T_mcr (d : sv) (T : axst) : axst := ltac2:(tb__ "0|0|
S16VT;S8bS14VT;A1U1S61Vd;A1A3A2").
Definition xfb_mc (d : sv) (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S38S3cU2A1S3S38A1M0A3S5S38A1S85S3aVT;R1A2A1S13SfS21S25S14R1A1A1A2S4SaS38R3S0S38S4aS0S4S47Vd;S1eZ0A1R2A3S0S4S47Vd;S3eR2A3S0S4S47Vd;S22S51S3eS1eZcA1A3R2A3S0S4S47S52S1eZ20A1R2A3S0S4S47S52S1eZ80A1R2A3S0S4S47S52S1eZ8cA1R2A3S3S4A1A3A3A3A3A3A3R1A2S0S38S3bU0A1M1S0S38G1S0S38S3bU1A1M2S0S38G2G0A3A3A3A3A3A3Tm;TT1;Tpre;").
Definition X_g : list (sv * sv) := ltac2:(tb__ "0|1|
S0ScS1fS1fA2M0S6S1fS1fS40S7dZ4S41A2A4S4eG0G0S10S2eSeS1fS1fR1A3S3fA2A1Lr;S84A3A3").
Definition T_mk0 : axst := Eval vm_compute in T_mc0 E_mk d_av k_av.
Definition T_mg0 : axst := Eval vm_compute in T_mc0 E_mg vDg vKg.
Definition T_mkr : axst := Eval vm_compute in T_mcr d_av T_mk0.
Definition T_mgr : axst := Eval vm_compute in T_mcr vDg T_mg0.
Definition T_mkb : axst := Eval vm_compute in optL' (apply_axforms T_mkr (xfb_mc d_av T_mkr)).
Definition T_mgb : axst := Eval vm_compute in optL' (apply_axforms T_mgr (xfb_mc vDg T_mgr)).
Definition T_mck : axst := Eval vm_compute in shadow_reopen_stateA T_mkb X_hv g5 4 30.
Definition T_mcg : axst := Eval vm_compute in shadow_reopen_stateA T_mgb X_g g5 4 30.

Definition pure_posts_ok (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
S4cS13S13S9S9S5S21A1M0S1Lx;S8fS14VPre;A1S14R1A1A2S2S21G0SbLl;Ls;X5x2S8aVPre;R1A2A2S2eS15R1A1S15VPre;A1A2A2LL;VLs;A3").

Definition mc_chk (d k : sv) (tv : list (sv * sv)) (bd : list bitem) (X : list (sv * sv)) (E0 E1 E T0 Tr Tb T : axst) : Prop := ltac2:(tb__ "0|14|
S12S11S8S13A1M0S3aVE0;S79Vd;VE0;A2A2S7S13VE1;A2A3S12S11S8S21A1M1S4dS21S25S14VE1;A1M2A1S5fVd;VE1;A2A3S7S21S61Vd;A1M3A2A3S12S11S1S2dS27G2A1S5eVd;A1M4A2S2A3S12S11S13S62Vd;VE1;A2VE;A3S12S11S1S76VE;Vd;Vk;A3S2A3S12S11S1S98S53S5aVE;Vd;Vk;A3A2S2A3S12S11S1S9dS53S27S14VE;A1M5A1M6A2S2A3S12S11S1S94G6S93Vtv;S7bVbd;S92S8dS2A2A4A2S2A3S12S11S1S90G6Vbd;A2S2A3S12S11S1S91Vbd;A1S2A3S12S11S1S77S57S0S13S58S0S13S58S3S13A1A3A3A2S2A3S12S11S1S81S24G5A1M7Vtv;S7bS48S5bVE;Vd;Vk;A3A5S2A3S12S11S1S83G7Vtv;S7bS82S17VE;A1A5S2A3S12S11S1S80G7A1S2A3S12S11S1S96G6S7cA2S2A3S12S11S13S6dVE;Vd;Vk;A3VT0;A3S12S11G1S4dS21S25S14VT0;A1M8A1U1A3S7S21G4A2A3S12S11S1S2dS27G8A1G3A2S2A3S12S11S13S6eVd;VT0;A2VTr;A3S12S11G0S3aVTr;S7aVd;VTr;A2A2S7S13VTb;A2A3S12S11S1fS15VTb;A1S1eS9aA1A3S12S11S1S1cS0S20S30S1bS54A1S52A2S0S20S23S28S54A1S1eS9fS9eZ2Z3dA2Z1A2A1A2S3S20A1A3A3S24S14VTb;A1M9A1MaA2S2A3S12S11S1S95VX;S17VTb;A1A2S2A3S12S11S13S99VTb;VX;S54Z4MbZ1eA5VT;A3S12S11S1S2fS14VT;A1A1S2A3S12S11S1S49GaVtv;S7bS48S25G9A1A5S2A3S12S11S1S80GaA1S2A3S12S11S1S4bS20S26S23S22S51S3eS1eZcA1A3S7dGbVk;A2McA2A1MdS24G2A1MeA3S2A3S12S11S1S4bS20S26S23S22S51Vd;GcA3S28P1eA1MfA2A1M10GeA3S2A3S12S11S1S4bS20S26S23GfS1eZ7fffff800000A1A2A1M11GeA3S2A3S12S11S1S4bS20S26S23GcS1eZffffffffA1A2A1M12GeA3S2A3S12S11S1S4bS20GdS24G8A1M13A3S2A3S12S11S1S4bS20G10G13A3S2A3S12S11S1S4bS20G11G13A3S2A3S11S1S4bS20G12G13A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv3_checks_mk : ltac2:(tb__ "0|0|
S60S3fS44S46S43S84S67S68S66S72S74S73S5dAc"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv3_checks_mg : ltac2:(tb__ "0|0|
S60S40S41S45S42S75S64S65S63S6fS71S70S5cAc"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Lk0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mck) c_op 0.
Definition Lk1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mck) c_op 1.
Definition Lg0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mcg) c_op 0.
Definition Lg1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mcg) c_op 1.
Definition gen_o1 (L C : axst) : axst := ltac2:(tb__ "0|0|
S14VL;A1S37S27R1A1S4fS28R1A1S1fS16VL;S31S29R3A1S8eS1fS35R3A1UfR1A4S33R3A1S32R3A1S36R3A1S25R3A1S0S20S23R1S1eZ1A1A2S24S14VC;A1A1A3S9cR2P1A2S34R3A1A9A2Tpw;Tn;TS;").
Definition E_o1 : axst := Eval vm_compute in gen_o1 Lk1 T_mck.
Definition s_o1 (L : axst) : wsub := ltac2:(tb__ "0|0|
S87S53S14VL;A1S14S59A1A3").
Lemma hv3_checks_o1 : ltac2:(tb__ "0|4|
S12S11S1S19S59A1S2A3S12S11S1S2fS14S59A1M0A1S2A3S12S11S50S29G0A1S7eA3S12S11S5S5S50A1M1A1S7fS13G1S13S7fS18S50S18S29S14S1dR1A1A1A1LL;S8cU258S86R1A3A4LT;S0S13S5dS0S13S5cS3S13A1M2A3A3A4S0G1S0S50S7eS0S50S7eS3S50A1A3A3M3S0G1G3S3G1A1A3A3A3S11S1S4cS13S13S1aR1S59S78R1A1A3LL;S0S13S6bS0S13S6cS0S13S69S0S13S6aG2A3A3A3A3A3S2A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv3m.

