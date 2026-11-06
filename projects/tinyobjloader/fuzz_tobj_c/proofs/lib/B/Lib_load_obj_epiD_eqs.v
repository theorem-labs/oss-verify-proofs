(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "true"; "list"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SLit"; "SPUle"; "valuation"; "SAlu"; "SPEq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "ANone"; "AHeadN"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "ejcertAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "nd_d2"; "gp"; "PhisD"; "nd_d1"; "nd_e"; "KU1"; "ndN"; "tvA"; "cutsD1"; "cutsD2"; "cutsD3"; "exitsD1"; "exitsD2"; "exitsD3"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_d0"; "nd_fa"; "nd_z"; "H_ecertD1_ok"; "H_ecertD2_ok"; "H_ecertD3_ok"; "V_ld"; "keep_ecertD1_ok"; "keep_ecertD2_ok"; "keep_ecertD3_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "vG"; "nB"; "vNx"; "cps_ad"; "C_L"; "E_fa0"; "E_fd0"; "E_ml0"; "E_s80"; "FUEL_oz"; "K_fa"; "L_L1"; "L_L3"; "L_ok"; "T_fa"; "T_fd"; "T_ml"; "X_A"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vCap"; "vNd"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "ldef"; "tblL"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Corelib.Init.Logic"; "eq"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "E_bd0"; "K_disp"; "K_j1"; "L_fl0"; "L_fl1"; "L_j1s"; "Lb_j1"; "T_bd"; "T_fl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "Ee_sf0"; "P_errL"; "Te_s8"; "Te_sf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3.

Definition V_ld : list positive := [466; 468]%positive.
Definition PhisD : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|4|
S1S3S8S19A1M0S10OFrho;M1A2S0G0G1S36S5aA4S1S3G0S10OF_;M2A2M3S0G0G2S4S19A1S10S5eL_;A4S4G3A1A3A3").

Definition tvA : list (sv * sv) := ltac2:(tb__ "0|1|
S1S3SbSbA2M0S0SbSbS72SeZ40A1A4S4G0A1A3").
Definition KU1 : list bitem := [BIc 0 KU 1].
Definition nd_d0 : ndesc := ndEp tvL bd_disp.
Definition nd_d1 : ndesc := ndEp kept_bd brest_bd.
Definition nd_d2 : ndesc := ndEp tvA KU1.
Definition ndN (nd cap nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S15S1S3SbSbA2S0SbSbVnd;S73Vcap;A1A4S25A3S59S5S56S23S1S56S57Z0Z1S58A3S4S56A1A3A3S17Vnx;Vg;A2A4").
Definition ndT (nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S15S25S59S23S17Vnx;Vg;A2A4").
Definition nd_A2 : ndesc := ltac2:(tb__ "0|0|
S24S71ScP2d2A1ScP2d1A1ScP2d4A1A4").
Definition nd_CL : ndesc := ltac2:(tb__ "0|0|
S24S52S51S3cS3aA4").
Definition nd_B2 : ndesc := ltac2:(tb__ "0|0|
S24S3cScS5cS3bP1A2A1ScS3bA1ScS5cS3bP3A2A1A4").
Definition nd_fa : ndesc := ltac2:(tb__ "0|0|
S15S25S59S23S16A4").
Definition nd_e : ndesc := ltac2:(tb__ "0|0|
S15S4S3SbSbA2A1S59S4S56A1S16A4").
Definition nd_z : ndesc := ltac2:(tb__ "0|0|
S15S4S3SbSbA2A1S4S3S3SbS18A2SbA2A1S4S56A1S16A4").
Definition gp (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S11S63Vg;SeVk;A1A3").

Definition cutsD1 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S65S30A4U0M4A4S0S18SbZ186S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6bS21A4G4A4S0S18SbZ17cS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6cS1eA4U1A4S0S18SbZ172S1aA4A4S4G3A1A3A3A3").
Definition exitsD1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S64S30A4U0M4A4S0S18SbZ185S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S69S21A4G4A4S0S18SbZ17bS1aA4M5A4S1G3S0G1G2S0G0S2S0S13S14S67S21A4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S68S21A4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S6aS1eA4U1A4S0S18SbZ171S1aA4A4S4G3A1A3A3A3A3A3").
Definition cutsD2 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S66S1eA4U1M4A4S0S18SbZ168S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S4cS2dA4G4A4S0S18SbZ15eS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S3eS2fA4G4A4S0S18SbZ12cM5S1fS3aZ8A2A4A4S1G3S0G1G2S0G0S2S0S13S14S49S2cS3cS3aA2A4G4A4S0S18SbG5S1fS3aZ6A2A4A4S1G3S0G1G2S0G0S2S0S13S14S4eS2eA4G4A4S0S18SbG5S1fScS5cS3bP3A2A1ZcA2A4A4S1G3S0G1G2S0G0S2S0S13S14S4aS1eA4G4A4S0S18SbZ167SeZ1A1A4A4S4G3A1A3A3A3A3A3A3").
Definition exitsD2 : list efnode := ltac2:(tb__ "0|9|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S47S1eA4U1M4A4S0S18SbZ167M5S1aA4M6A4S1G3S0G1G2S0G0S2S0S13S14S4fS1eA4G4A4G6A4S1G3S0G1G2S0G0S2S0S13S14S4bS1eA4G4A4G6A4S1G3S0G1G2S0G0S2S0S13S14S45S2dA4G4A4S0S18SbZ15dS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S40S2fA4G4A4S0S18SbZ12cM7S1fS3aZ7A2A4A4S1G3S0G1G2S0G0S2S0S13S14S50S2cS3cS3aA2M8A4G4A4S0S18SbZ12bS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S4dG8A4G4A4S0S18SbG7S1fS3aZ5A2A4A4S1G3S0G1G2S0G0S2S0S13S14S46S2eA4G4A4S0S18SbG7S1fScS5cS3bP3A2A1ZbA2A4A4S1G3S0G1G2S0G0S2S0S13S14S41S1eA4G4A4S0S18SbG5SeZ2A1A4A4S4G3A1A3A3A3A3A3A3A3A3A3").
Definition cutsD3 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S44S31A4U1M4A4S0S18SbZfaS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S48S22A4G4A4S0S18SbZf0S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6fS22A4G4A4S0S18SbZdcS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S70S32A4G4A4S0S18SbZd2S1aA4A4S4G3A1A3A3A3A3").
Definition exitsD3 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S3fS31A4U1M4A4S0S18SbZf9S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S42S22A4G4A4S0S18SbZe5S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6dS22A4G4A4S0S18SbZdbS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6eS32A4G4A4S0S18SbZd1S1aA4A4S4G3A1A3A3A3A3").

Definition keep_ecertD1_ok : list sprop := ltac2:(tb__ "0|0|
S1SdSfScP1d4A1SeZffffffffA1A2S4SdA1A3").
Definition H_ecertD1_ok : list sprop := ltac2:(tb__ "0|0|
S61S37S5S1bS26S29A3A2").
Lemma ecertD1_ok : ltac2:(tb__ "0|1|
S5dS6S1cS5fS55S20U12cS3dS55S53S1bS1bS60S33A1M0S26A4S53S1bS1bG0S29A4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertD2_ok : list sprop := ltac2:(tb__ "0|3|
S1SdSfScPe9A1M0SeZ800000000000A1A2S1SdSfScP1d1A1ScP1eA1M1A2S1SdS12S11S62ScP12fA1M2SeZ3A1A3G0A2S1SdSfG2SeZ1fffffffffffffffA1A2S1SdSfG1SeZ7fffff800000A1A2S4SdA1A3A3A3A3A3").
Definition H_ecertD2_ok : list sprop := ltac2:(tb__ "0|0|
S61S38S5S1bS27S2aA3A2").
Lemma ecertD2_ok : ltac2:(tb__ "0|1|
S5dS6S1cS5fS55S20U12cS3dS55S53S1bS1bS60S34A1M0S27A4S53S1bS1bG0S2aA4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertD3_ok : list sprop := ltac2:(tb__ "0|4|
S1SdSfScPe9A1M0SeZ800000000000A1M1A2S1SdSfScP12fA1M2SeZ1fffffffffffffffA1A2S1SdSfS11S62G2SeZ3A1A3M3G0A2S1SdSfG0G3A2S1SdSfScPcA1G1A2S4SdA1A3A3A3A3A3").
Definition H_ecertD3_ok : list sprop := ltac2:(tb__ "0|0|
S61S39S5S1bS28S2bA3A2").
Lemma ecertD3_ok : ltac2:(tb__ "0|1|
S5dS6S1cS5fS55S20S43S3dS55S53S1bS1bS60S35A1M0S28A4S53S1bS1bG0S2bA4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ldef_reads : phi_reads V_ld ldef.
Proof.
  intros rho rho' HV _ HM HD z Hz. rewrite <- HM. apply HD.
  rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhisD_reads : ltac2:(tb__ "0|3|
S54S3S8S19A1M0S10OF_;M1A2M2G2S1dS9G0G1R1A3SaG0G1R1A3A2Lp;S20A3").
Proof. constructor; [exact ldef_reads | constructor; [intros rho rho' _ _ _ _; exact I | constructor]]. Qed.

Lemma tblL_ldef : ltac2:(tb__ "0|0|
S10S5bR1A1S5aR2A1F_;Frho;").
Proof. intros rho [_ H]. exact H. Qed.
