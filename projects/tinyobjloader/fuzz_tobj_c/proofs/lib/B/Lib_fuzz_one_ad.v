(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nat"; "pair"; "nil"; "prod"; "Some"; "list"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SPBranch"; "sprop_eqb"; "swf"; "SPNot"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "entailsA"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "AXSelect"; "AXSplit"; "AXUnbase"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "Pre_fr"; "E_fd"; "C_L"; "E_fa"; "K_fa"; "s_fa"; "s_fd"; "L_fr"; "X_A1"; "T_fa"; "R_fa"; "R_fd"; "SFR"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vNx"; "E_fa1"; "E_fd0"; "E_fd1"; "L_L1"; "L_L3"; "T_fa0"; "T_fd"; "T_fd0"; "X_A"; "nB"; "s_L1"; "s_L3"; "s_fa0"; "s_fa1"; "s_free"; "szB"; "vCap"; "vG"; "vNd"; "xf_fd"; "xfb_fd"; "E_fa0"; "Ls_fd"; "Ls_ok"; "fd_after0"; "gA"; "hnz"; "xf_fa"; "xfb_fa"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one"; "showL"; "runF"; "Fx"; "optL"; "ax_tidy"; "dropX"; "pH"; "free_pc"; "nx"; "pAR"; "pc_L"; "pc_fa"; "pc_sx"; "T_err"; "body_shape"; "glob_shape"; "nobj"; "optR"; "pc_adA"; "pc_adB"; "shapes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD"; "pop_stateA"; "lenN_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "WIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.

Definition L_sxE : axst := Eval vm_compute in leafF (runF T_err) pc_sx 0.

Definition Ls_ok : list leafA := Eval vm_compute in runF T_suc.
Definition X_fa0 : axst := Eval vm_compute in leafF Ls_ok pc_fa 0.
Definition X_A : axst := Eval vm_compute in leafF Ls_ok pc_adA 0.
Definition hnz : sprop := ltac2:(tb__ "0|0|
S14S11S6eS5dSeZ0A1A3A1").
Definition X_A1 : axst := Eval vm_compute in lenN_stateA X_A.
Definition gA : sv := Eval vm_compute in SVar (nx X_A).
Definition X_A2 : axst := Eval vm_compute in pop_stateA X_A1 pH gA.
Definition L_L1 : axst := Eval vm_compute in leafF (runF X_A2) pc_L 0.

Definition Pre_fr : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.Pre_free_tol AE_A.
Definition L_fr : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.L_free_tol AE_A.
Definition SFR : Z := 128.
Definition s_free (E : axst) (sz : sv) : wsub := ltac2:(tb__ "0|1|
S2S8S23SdA2M0S6S23SdS7eSeS75S76S7dS33A2A1A1A4S2G0S6S23SdPdVsz;A4S6cPaS17VE;A1S17S27A1A3A3A3").
Definition szB (cap : sv) : sv := SAlu ALU_ADD cap (SLit 32).

Definition xf_fd (A : axst) : list axform := ltac2:(tb__ "0|3|
S2S1bS1eS77S67VA;A1M0U1A2A1S2S1bS1dS77G0U2A2A1S2S1bS20U0M1SeS75S33A1M2A1A2S2S1bS21G1G2A2S7S1bA1A3A3A3A3").
Definition fd_site (E0 : axst) (hd : sv) : axst := ltac2:(tb__ "0|0|
S5cVhd;S5aS1cVE0;S4dVE0;A1A2A1A2").
Definition fd_after0 (E : axst) (sz : sv) : axst := ltac2:(tb__ "0|1|
S73S27VE;S48VE;Vsz;A2M0S68S71VE;S27G0A3A1S2eA5").
Definition xfb_fd : list axform := ltac2:(tb__ "0|1|
S2S1bS1eU0M0A1S2S1bS1fS2S5G0S2S5U3S2S5U4S2S5U5S2S5U6S2S5U7S2S5U8S2S5U9S2S5UaS2S5UbS2S5UcS2S5U1S2S5U2S7S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S2S1bS1dG0A1S7S1bA1A3A3A3").
Definition fd_after (E : axst) (sz : sv) : axst := ltac2:(tb__ "0|0|
S5bS5aS1cS52VE;Vsz;A2S4eA2A1A1").

Definition Eb_fd : axst := Eval vm_compute in fd_site (leafF (runF L_L1) free_pc 0) pH.
Definition Tb_fd : axst := Eval vm_compute in fd_after Eb_fd (szB (SVar 248)).
Definition Xb_B : axst := Eval vm_compute in leafF (runF Tb_fd) pc_adB 0.
Definition Xb_B2 : axst := Eval vm_compute in pop_stateA Xb_B (SVar 247) (SVar 250).
Definition L_L2 : axst := Eval vm_compute in leafF (runF Xb_B2) pc_L 0.

Definition vNd : sv := SVar 247.  Definition vNx : sv := SVar 292.  Definition vCap : sv := SVar 293.  Definition vG : sv := SVar 295.  Definition vGp : sv := SVar 250.
Definition C_L : axst := Eval vm_compute in dropV [246]%positive (junkRN [1]%nat L_L2).
Definition s_L1 : wsub := ltac2:(tb__ "0|2|
S2S8S23SdA2M0S6S23SdP127SfPfaM1A1A4S2G0S6S23SdG1SfPf6A1A4S2G0S6S23SdP128SfPfbA1A4S6cS26S17S3dA1S17S29A1A3A3A3A3").

Definition E_fd0 : axst := Eval vm_compute in leafF (runF C_L) free_pc 0.
Definition E_fd1 : axst := Eval vm_compute in optL (apply_axforms E_fd0 (xf_fd E_fd0)).
Definition E_fd : axst := Eval vm_compute in dropX vNd E_fd1.
Definition s_fd : wsub := ltac2:(tb__ "0|0|
S48S28S49S4aA1A2").
Definition R_fd : list sobj := Eval vm_compute in optR (entails_frA E_fd Pre_fr s_fd).
Definition T_fd0 : axst := Eval vm_compute in T_afterA Pre_fr E_fd s_fd R_fd L_fr.
Definition T_fd : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_fd0 xfb_fd)).
Definition Ls_fd : list leafA := Eval vm_compute in runF T_fd.
Definition X_fa1 : axst := Eval vm_compute in leafF Ls_fd pc_fa 0.
Definition X_B : axst := Eval vm_compute in leafF Ls_fd pc_adB 0.
Definition nB : positive := Eval vm_compute in nx X_B.
Definition X_B2 : axst := Eval vm_compute in pop_stateA X_B vNx vG.
Definition L_L3 : axst := Eval vm_compute in leafF (runF X_B2) pc_L 0.
Definition s_L3 : wsub := ltac2:(tb__ "0|1|
S2S8S23SdA2M0S6S23SdP127SfS7bS43P3A2A1A4S2G0S6S23SdPfaS4bA4S2G0S6S23SdP128SfS7bS43P4A2A1A4S6cS26S17S3eA1S17S29A1A3A3A3A3").

Lemma fz_checks_loop1 : ltac2:(tb__ "0|4|
S1S0SaS8S22S24A2M0A1M1S57S58S64A1A1S2G0S6S22S24S63S25A4S7G0A1M2A3A3S1S0G1S57S51A1S2G0S6S22S24S62S25A4S2G0S6S22S24S69S25A4G2A3A3A3S1S0S3S6dS10S12S54A1M3S59S42A1A3S4A3S1S0S16S79S42A1S2fA3S1S0S3S13S17S2fA1A1S4A3S1S0S16S78S2fS5dS53A3S34A3S1S0S3S13S17S34A1A1S4A3S1S0SdS1aS2fA1SeS7aA1A3S1S0S3S6dS10G3S59S2fA1A3S4A3S1S0G1S57S58S34A1A1S2G0S6S22S24S61S25A4G2A3A3S1S0S3S18S29A1S4A3S1S0S3S19S3dS29S44A3S4A3S0S3S70S44S26A2S4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_checks_fd : ltac2:(tb__ "0|7|
S1S0SaS8S22S24A2M0A1M1S57S58S29A1A1S2G0S6S22S24S5eS25A4S7G0A1M2A3A3S1S0SbS16A1M3S1cS3bS4dS3bA1A2S9S16S3cA2A3S1S0S16S5cS4cS3cA2S28A3S1S0S3S18S28A1S4A3S1S0SbSaS15A1M4A1S71S28S27S2dA3S9G4S32A2A3S1S0S3S72S28S27S2dS32S2S16S2eS7S16A1A3A5S4A3S1S0S3S74S26S2dA2S4A3S1S0S3S7cS26S5fS28A1A2S4A3S1S0SdS6fS2dPcA2S4cA3S1S0SdS6fS2dPdA2S49S4aA1A3S1S0S16S73S27S28S2dS32S2eA5S41A3S1S0G3S1cS41S4eA2M5S9S16S5aG5A1M6A2A3S1S0S16S5bG6A1S40A3S1S0S3S18S40A1S4A3S1S0G1S57S50A1S2G0S6S22S24S62S25A4S2G0S6S22S24S6aS25A4G2A3A3A3S1S0S3S6dS10S12S14S11S6eS39SeZ0A1A3A1A1S59S35A1A3S4A3S1S0S16S78S35S39S4bA3S36A3S1S0S3S13S17S36A1A1S4A3S1S0SdS1aS35A1SeS7aA1A3S1S0G1S57S58S36A1A1S2G0S6S22S24S61S25A4G2A3A3S1S0S3S19S3eS29S45A3S4A3S0S3S70S45S26A2S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition K_fa : axst := Eval vm_compute in
  dropV [226; 246; 247; 248; 249; 250; 251; 292; 293; 294; 295; 296]%positive (junkRN [1; 19; 20; 21; 26; 27]%nat X_fa1).
Definition s_fa0 : wsub := ltac2:(tb__ "0|0|
S6cS26S17S37A1S17S2bA1A3").
Definition s_fa1 : wsub := ltac2:(tb__ "0|0|
S6cS26S17S38A1S17S2bA1A3").
Definition E_fa0 : axst := Eval vm_compute in leafF (runF K_fa) free_pc 0.
Definition xf_fa : list axform := ltac2:(tb__ "0|2|
S2S1bS20U0M0SeS75S33A1M1A1A2S2S1bS21G0G1A2S7S1bA1A3A3").
Definition E_fa1 : axst := Eval vm_compute in optL (apply_axforms E_fa0 xf_fa).
Definition E_fa : axst := Eval vm_compute in dropX pAR E_fa1.
Definition s_fa : wsub := s_free E_fa (SLit 64).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_frA E_fa Pre_fr s_fa).
Definition T_fa0 : axst := Eval vm_compute in T_afterA Pre_fr E_fa s_fa R_fa L_fr.
Definition xfb_fa : list axform := ltac2:(tb__ "0|1|
S2S1bS1eU0M0A1S2S1bS1fS2S5G0S2S5U3S2S5U4S2S5U5S2S5U6S2S5U7S2S5U8S2S5U9S2S5UaS2S5UbS2S5U1S2S5U2S7S5A1A3A3A3A3A3A3A3A3A3A3A3A3A1S2S1bS1dG0A1S7S1bA1A3A3A3").
Definition T_fa : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_fa0 xfb_fa)).
Definition L_sxK : axst := Eval vm_compute in leafF (runF T_fa) pc_sx 0.

Lemma fz_checks_fa : ltac2:(tb__ "0|9|
S1S0S3S18S2bA1S4A3S1S0S3S19S37S2bS46A3S4A3S1S0S3S19S38S2bS47A3S4A3S1S0S3S70S46S26A2S4A3S1S0S3S70S47S26A2S4A3S1S0S3S6dS10S12S11S6eS5dSeZ0A1M0A3A1S59S37A1A3S4A3S1S0S3S6dS10S12S11S6eS39G0A3A1S59S38A1A3S4A3S1S0SaS8S22S24A2M1A1M2S57S58S2bA1A1S2G1S6S22S24S5eS25A4S7G1A1M3A3A3S1S0SbS16A1M4S1cS4fS55A2S9S16S3aA2A3S1S0S16S5cS60S3aA2S2aA3S1S0S3S18S2aA1S4A3S1S0SbSaS15A1M5A1S71S2aS27S2cA3S9G5S31A2A3S1S0S3S72S2aS27S2cS31S2S16S2eS7S16A1A3A5S4A3S1S0S3S74S26S2cA2S4A3S1S0S3S7cS26S5fS2aA1A2S4A3S1S0SdS6fS2cPcA2S60A3S1S0SdS6fS2cPdA2SeZ40A1A3S1S0S16S73S27S2aS2cS31S2eA5S3fA3S1S0G4S1cS3fS56A2M6S9S16S5aG6A1M7A2A3S1S0S16S5bG7A1S30A3S1S0S3S18S30A1S4A3S1S0SaS8S8SdSdA2SdA2M8A1S6bS30A1ScG8S65S66A3A3S0G2S57S58S30A1A1S2G1S6S22S24S63S25A4G3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
