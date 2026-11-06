(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "pair"; "nil"; "Some"; "list"; "option"; "nat"; "prod"; "app"; "S"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "axwf"; "entailsA"; "la_reason"; "la_state"; "ax_base"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "SVar"; "cell"; "sprop"; "ss_facts"; "SPBranch"; "sprop_eqb"; "ss_pc"; "swf"; "ss_objs"; "SPNot"; "mkObj"; "ss_next"; "sstate"; "DUnknown"; "c_off"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "Pre_ms"; "z24"; "L_ms"; "ms_T0"; "optL"; "optR"; "s_msx"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "Pre_fr"; "L_fr"; "free_pc"; "pc_fa"; "s_free"; "cps_epi"; "dropX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "C_L"; "K_fa"; "E_fd"; "E_ml"; "cps_ad"; "s_fa"; "s_fd"; "E_fa"; "T_ml1"; "X_A1"; "T_fa"; "T_ml"; "T_ml0"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "iL24"; "pc_L"; "s_ml"; "szB"; "vNx"; "E_fd0"; "L_L1"; "L_L3"; "R_fa"; "R_fd"; "R_ml"; "T_fd"; "T_ml2"; "X_A"; "nB"; "pc_adA"; "pc_adB"; "s_L1"; "s_L3"; "s_fa0"; "s_fa1"; "vCap"; "vG"; "xf_fd"; "E_fd1"; "E_ml0"; "FUEL_oz"; "Ls_fd"; "Ls_j1"; "Ls_ml"; "T_fa0"; "T_fd0"; "drop_cell_obj"; "gA"; "hnz"; "iLN"; "nobj"; "vNd"; "xf_ml"; "xfb_ml"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@Stdlib.Lists.List"; "existsb"; "filter"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "lnA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD"; "pop_stateA"; "lenN_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "memcpy_pc"; "memset_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1.

Definition pc_adA : Z := 0x8e880.  Definition pc_L : Z := 0x8e89c.  Definition pc_adB : Z := 0x8e880.
Definition cps_ad : list Z := ltac2:(tb__ "0|0|
S2S19S70S2S19S62S2S19S71S4dA3A3A3").
Definition Ls_j1 : list leafA := Eval vm_compute in runL 300 cps_ad K_j1.

Definition E_ml0 : axst := Eval vm_compute in leafL Ls_j1 memset_pc 0.
Definition iLN : nat := Eval vm_compute in idxB E_ml0 lnA 0.
Definition xf_ml : list axform := ltac2:(tb__ "0|0|
S2S42S47S84S20Z18A1A2S6S42A1A3").
Definition E_ml : axst := Eval vm_compute in optL (apply_axforms E_ml0 xf_ml).
Definition s_ml : wsub := ltac2:(tb__ "0|0|
S3dS52S97S20Z18A1A3").
Definition R_ml : list sobj := Eval vm_compute in R_of E_ml Pre_ms s_ml.
Definition T_ml0 : axst := Eval vm_compute in ms_T0 E_ml s_ml.
Definition T_ml1 : axst := Eval vm_compute in optS T_ml0 (zero_cells_at (ax_S T_ml0) 1 z24).
Definition iL24 : nat := Eval vm_compute in idxB T_ml1 lnA 24.
Definition xfb_ml : list axform := ltac2:(tb__ "0|3|
S2S42S46ScSaS2SaU0S2SaU1M0S2SaS61S6SaA1A3A3A3ScSaS40U2M1S8dS61G1A2A2S40SdS61A1M2S8dSeS1eS29S10S57A1A1A2G2A2A2A3A3A1S2S42S44G0A1S6S42A1A3A3").
Definition T_ml2 : axst := Eval vm_compute in optL (apply_axforms T_ml1 xfb_ml).
Definition T_ml : axst := Eval vm_compute in ax_tidy T_ml2.
Definition Ls_ml : list leafA := Eval vm_compute in runL 300 cps_ad T_ml.
Definition L_ok : axst := Eval vm_compute in leafL Ls_ml memcpy_pc 0.
Definition X_fa0 : axst := Eval vm_compute in leafL Ls_ml pc_fa 0.
Definition X_A : axst := Eval vm_compute in leafL Ls_ml pc_adA 0.

Definition hnz : sprop := ltac2:(tb__ "0|0|
S2aS25S8eS96S20Z0A1A3A1").
Definition X_A1 : axst := Eval vm_compute in lenN_stateA X_A.
Definition gA : sv := SVar (ss_next (ax_S X_A)).
Definition X_A2 : axst := Eval vm_compute in pop_stateA X_A1 pH gA.
Definition L_L1 : axst := Eval vm_compute in leafL (runL 300 cps_ad X_A2) pc_L 0.

Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).
Definition xf_fd (A : axst) : list axform := ltac2:(tb__ "0|1|
S2S42S45S8dS85VA;A1M0U1A2A1S2S42S44S8dG0U2A2A1S6S42A1A3A3").
Definition szB (cap : sv) : sv := SAlu ALU_ADD cap (SLit 32).
Definition fd_site (E0 : axst) (hd : sv) : axst := ltac2:(tb__ "0|0|
S4eVhd;S3bS43VE0;S78VE0;A1A2A1A2").
Definition fd_after (E : axst) (cap : sv) : axst := ltac2:(tb__ "0|1|
S8fS9bS48VE;S4cVE;S64Vcap;A1A2M0S3cS94VE;S48G0A3A1S49A5A1").
Definition Eb_fd : axst := Eval vm_compute in fd_site (leafL (runL 300 cps_ad L_L1) free_pc 0) pH.
Definition Tb_fd : axst := Eval vm_compute in fd_after Eb_fd (SVar 722).
Definition Xb_B : axst := Eval vm_compute in leafL (runL 300 cps_ad Tb_fd) pc_adB 0.
Definition Xb_B2 : axst := Eval vm_compute in pop_stateA Xb_B (SVar 721) (SVar 724).
Definition L_L2 : axst := Eval vm_compute in leafL (runL 300 cps_ad Xb_B2) pc_L 0.

Definition vNd : sv := SVar 721.  Definition vNx : sv := SVar 766.  Definition vCap : sv := SVar 767.  Definition vG : sv := SVar 769.  Definition vGp : sv := SVar 724.
Definition C_L : axst := Eval vm_compute in dropV [720]%positive (junkR [1]%nat L_L2).
Definition s_L1 : wsub := ltac2:(tb__ "0|2|
S2SbS1aS1fA2M0S5S1aS1fP301S21P2d4M1A1A4S2G0S5S1aS1fG1S21P2d0A1A4S2G0S5S1aS1fP302S21P2d5A1A4S91S36S10S67A1S10S4fA1A3A3A3A3").

Definition E_fd0 : axst := Eval vm_compute in leafL (runL 300 cps_ad C_L) free_pc 0.
Definition E_fd1 : axst := Eval vm_compute in optL (apply_axforms E_fd0 (xf_fd E_fd0)).
Definition E_fd : axst := Eval vm_compute in dropX vNd E_fd1.
Definition s_fd : wsub := ltac2:(tb__ "0|0|
S4cS51S64S76A1A2").
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
S2SbS1aS1fA2M0S5S1aS1fP301S21S9dS6fP3A2A1A4S2G0S5S1aS1fP2d4S77A4S2G0S5S1aS1fP302S21S9dS6fP4A2A1A4S91S36S10S68A1S10S4fA1A3A3A3A3").

Lemma epiD2_checks_ml : ltac2:(tb__ "0|5|
S1S0S8SbS19S1bA2M0A1S3eS12G0S12S5S19S1bS27S10S16R1A1A1A1S15R1A1A4LL;S7dA4S2G0S5S19S1bSa0S1cA4S6G0A1A3A3S1S0S9S11A1M1S43S7aS87A2S7S11S52A2A3S1S0S9S8S1eA1M2A1S94S52S37S63A3S7G2S6bA2A3S1S0S3S95S52S37S63S6bS2S11S39S6S11A1A3A5S4A3S1S0S11S3aS52S63A2S5bA3S1S0S9S2dA1Sa3S10S5bA1U1M3S38A3S7S2dS10S57A1M4A2A3S1S0S11S18S5bG4A2S57A3S1S0S3S28G4A1S4A3S1S0G1S43S57S88A2S7S11S6dA2A3S1S0S11S8fS6dA1S5aA3S1S0S3S13S5aA1S4A3S0S9S1eA1S8cS1eS29S10S5aA1A1G3A3S7S1eS2bS97S20Z0A1S20Z20A1ScS22S38S2S22Sa2Z18S20Z10A1A2S6S22A1A3A3S2eA5A2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD2_checks_loop1 : ltac2:(tb__ "0|6|
S1S0S8SbS19S1bA2M0A1M1S3eS12G0S12S5S19S1bS27S10S16R1A1A1A1S15R1A1A4LL;M2S7eA4S2G0S5S19S1bS9fS1cA4S2G0S5S19S1bS4bS1cA4S2G0S5S19S1bS70S1cA4S6G0A1M3A3A3A3A3S1S0S3S8aS23S26S83A1M4S24S10S6eA1A1A3S4A3S1S0S11S99S6eA1S58A3S1S0S3S28S10S58A1M5A1S4A3S1S0S11S98S58S96S82A3S5cA3S1S0S3S28S10S5cA1A1S4A3S1S0S1fS17S58A1S20S9cA1A3S1S0S3S8aS23G4S24G5A1A3S4A3S1S0G1S3eS12G0G2S89U12cS53S5cA3A4S2G0S5S19S1bS62S1cA4G3A3A3S1S0S3S13S4fA1S4A3S1S0S3S14S67S4fS72A3S4A3S0S3S93S72S36A2S4A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD2_checks_fd : ltac2:(tb__ "0|6|
S1S0S8SbS19S1bA2M0A1M1S3eS12G0S12S5S19S1bS27S10S16R1A1A1A1S15R1A1A4LL;M2S89U12cM3S53S4fA3A4S2G0S5S19S1bS4aS1cA4S6G0A1M4A3A3S1S0S9S11A1S43S66S78S66A1A2S7S11S79A2A3S1S0S3S13S51A1S4A3S1S0S9S8S1eA1M5A1S94S51S48S55A3S7G5S6aA2A3S1S0S3S95S51S48S55S6aS2S11S49S6S11A1A3A5S4A3S1S0S3S9aS36S55A2S4A3S1S0S3S9eS36S2cS10S51A1A1A2S4A3S1S0S1fS92S55PcA2S86A3S1S0S1fS92S55PdA2S64S76A1A3S1S0S11S8fS80A1S6cA3S1S0S3S13S6cA1S4A3S1S0G1S3eS12G0G2S7cA4S2G0S5S19S1bS4bS1cA4S2G0S5S19S1bS71S1cA4G4A3A3A3S1S0S3S8aS23S26S2aS25S8eS65S20Z0A1A3A1A1S24S10S5dA1A1A3S4A3S1S0S11S98S5dS65S77A3S5eA3S1S0S3S28S10S5eA1A1S4A3S1S0S1fS17S5dA1S20S9cA1A3S1S0G1S3eS12G0G2S89G3S53S5eA3A4S2G0S5S19S1bS62S1cA4G4A3A3S1S0S3S14S68S4fS73A3S4A3S0S3S93S73S36A2S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition drop_cell_obj (off : Z) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S2bS30Vo;A1S34Vo;A1S33Vo;A1S8bS22S22SfS35S2fR1A1S20Voff;A1A2A1Lc;S31Vo;A1A3S32Vo;A1A5").
Definition drop_cell_at (A : axst) (i : nat) (off : Z) : axst := ltac2:(tb__ "0|1|
S29S10VA;A1M0A1S8S1eA1S18VA;S1dG0ScS1eS3fS1eVi;R1A3ScS1eS3eS1eS1eS81Voff;A1S3fS1eU1S41S1eVi;R1A3A3A4S41S1eSdVi;A1R1A3A3A3A2A2Tobjs;").
Definition K_fa : axst := Eval vm_compute in
  drop_cell_at (dropV [465; 720; 721; 722; 723; 724; 725; 766; 767; 768; 769; 770]%positive (junkR [1; 18; 23; 24; 27]%nat X_fa1)) (idxB X_fa1 (SVar 10) (-640)) (-368).
Definition s_fa0 : wsub := ltac2:(tb__ "0|0|
S91S36S10S5fA1S10S50A1A3").
Definition s_fa1 : wsub := ltac2:(tb__ "0|0|
S91S36S10S60A1S10S50A1A3").
Definition E_fa0 : axst := Eval vm_compute in leafL (runL 300 cps_ad K_fa) free_pc 0.
Definition E_fa : axst := Eval vm_compute in dropX vARn E_fa0.
Definition s_fa : wsub := s_free E_fa (SLit 64).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_frA E_fa Pre_fr s_fa).
Definition T_fa0 : axst := Eval vm_compute in T_afterA Pre_fr E_fa s_fa R_fa L_fr.
Definition T_fa : axst := Eval vm_compute in ax_tidy T_fa0.

Definition FUEL_oz : nat := 3000%nat.
Definition E_s80 : axst := Eval vm_compute in leafL (runL FUEL_oz cps_ad T_fa) ssf8_pc 0.

Lemma epiD2_checks_fa : ltac2:(tb__ "0|6|
S1S0S3S13S50A1S4A3S1S0S3S14S5fS50S74A3S4A3S1S0S3S14S60S50S75A3S4A3S1S0S3S93S74S36A2S4A3S1S0S3S93S75S36A2S4A3S1S0S3S8aS23S26S25S8eS96S20Z0A1M0A3A1S24S10S5fA1A1A3S4A3S1S0S3S8aS23S26S25S8eS65G0A3A1S24S10S60A1A1A3S4A3S1S0S8SbS19S1bA2M1A1M2S3eS12G1S12S5S19S1bS27S10S16R1A1A1A1S15R1A1A4LL;M3S89U12cS53S50A3A4S2G1S5S19S1bS4aS1cA4S6G1A1M4A3A3S1S0S3S13S56A1S4A3S1S0S9S8S1eA1M5A1S94S56S48S54A3S7G5S69A2A3S1S0S3S95S56S48S54S69S2S11S49S6S11A1A3A5S4A3S1S0S3S9aS36S54A2S4A3S1S0S3S9eS36S2cS10S56A1A1A2S4A3S1S0S1fS92S54PcA2S90A3S1S0S1fS92S54PdA2S20Z40A1A3S1S0S11S8fS7fA1S59A3S1S0S3S13S59A1S4A3S0G2S3eS12G1G3S89S7bS53S59A3A4S2G1S5S19S1bSa1S1cA4G4A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
