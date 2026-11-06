(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_022.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s6 eq.

(* [comment removed for export] *)
Module Lib_build_line_index_rom_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "list"; "cons"; "Some"; "option"; "nil"; "prod"; "app"; "bool"; "fst"; "nat"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom"; "E_vrx"; "s_v"; "pC"; "pK"; "pD"; "vKg"; "R_v"; "T_grown"; "T_keep"; "X_stS"; "Xk_v"; "tvB"; "xf_vback"; "T_fail0"; "T_grown0"; "T_grownF"; "T_keep0"; "T_keepF"; "X_stA"; "kb16"; "vDg"; "E_ms0"; "E_vr"; "FUEL_blr"; "L_ms"; "PhisV"; "Pre_ms"; "R_m"; "T_fail"; "T_grownC"; "T_keepC"; "T_ms0"; "X_st"; "cutpcs_blr"; "cutsE"; "exitsE"; "ok_facts"; "s_m"; "sel_st"; "slot_facts"; "xf_vcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom"; "Pre_vr"; "P_grown"; "P_keep"; "KLG"; "PHI"; "P_fail"; "bdP"; "tv0"; "vW"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "SLit"; "sobj"; "sprop"; "ss_facts"; "ss_objs"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"; "efnode"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "drop_lastA"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.RV"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_eqs"; "o_slotX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr BLRAddr.

Goal True. idtac "checking ejcertAF (vm_compute)". Abort.
Lemma ejcertAF_ok0 : ltac2:(tb__ "0|0|
S0SbS56S5dS60S28S26S30P64S31S32A8SeA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ejcertAF_V : ltac2:(tb__ "0|6|
S4S5cA1S52S4S9S4S52A1M0S4cOF_;M1A2M2A1M3G3SdS4S53A1S52S4S57A1M4G4S0S4G0A1S58G2G0ScG0G1A2M5R7A4S58G2G0G5R6A4A3S0SbS56RaR9R8R6R5R4R3R2A8S56RaR9R7R6R5R4R3R2A8A3F_;Fexits;Fcuts;Fg;Fcps;Ffuel;FPhis';FPhis;Fnp;Fsg;").
Proof.
  intros sg np Phis Phis' fuel cps g cuts exits H. unfold ejcertAF, eecheckJAF_pf, echeckJAF_pf, VK. rewrite H. reflexivity.
Qed.

Lemma E_vrx_eq : ltac2:(tb__ "0|0|
S0S7S2A1S4eS25S37A2S6S2SfA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S2S55S38SfS10S15S3aS19A6S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S2S55S38SfS10S15S3dS19A6S1cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S2S55S38SfS10S15S39S19A6S1dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S7S2A1S4eS1fS1bA2S6S2S17A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail_eq : ltac2:(tb__ "0|0|
S0S7S2A1S4eS1cS1bA2S6S2S2bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S7S2A1S4eS1dS1bA2S6S2S16A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepF_eq : ltac2:(tb__ "0|0|
S0S2S59S17SaS49S33S13S11S12A3S4aS3S17A1A1A3A2S20A3"). Proof. reflexivity. Qed.
Lemma T_grownF_eq : ltac2:(tb__ "0|0|
S0S2S59S16SaS49S36S11S14A2S4aS3S16A1A1A3A2S1eA3"). Proof. reflexivity. Qed.
Lemma T_keepC_eq : ltac2:(tb__ "0|0|
S0S2S5aS20S46S51S13S22S11A1A3S47Z10A1A3S2dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownC_eq : ltac2:(tb__ "0|0|
S0S2S5aS1eS46S51S23S22S11A1A3S47Z10A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S0S4S9S45S45A2A1S54S4dS10S38S3aSfA4S3fA2S1aS13S12A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S0S4S9S45S45A2A1S54S4dS10S38S3dSfA4S3fA2S1aS13S12A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|0|
S0S4S9S45S45A2A1S54S4dS10S38S39SfA4S5eA2S1aS23S14A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0S4S43A1S44S4dS10S38S3aSfA4S3eS40S41A2A2S5S43S3cS46S51S11S47Z1A1A3S12A2S5S43S3bS12A1S8S43A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0S4S43A1S44S4dS10S38S39SfA4S3eS40S42A2A2S5S43S3cS46S51S11S47Z1A1A3S14A2S5S43S3bS14A1S8S43A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_ms0_eq : ltac2:(tb__ "0|0|
S0S2S61S29S24S34S2aS27A5S2eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o_slotX : sobj := Eval vm_compute in last (ss_objs (ax_S X_stS)) O_D.
Lemma X_stS_eq : ltac2:(tb__ "0|0|
S0S7S2A1S4eS2fS5S4fS50S35A1S8S4fA1A3A2S6S2S18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_stA_eq : ltac2:(tb__ "0|1|
S1S0S4S48A1S4bS3S18A1A1SaS48S4bS3S21A1A1M0S5S48S5fS8S48A1A3A3A3S0S2S5bS18G0A2S21A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_build_line_index_rom_eqs.

(* [comment removed for export] *)
Module Lib_build_line_index_rom_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "True"; "@Corelib.Init.Datatypes"; "bool"; "true"; "prod"; "list"; "pair"; "cons"; "nil"; "nat"; "app"; "option"; "None"; "Some"; "fst"; "false"; "length"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "sprop_eqb"; "SPUle"; "SLit"; "ss_facts"; "SAlu"; "ss_next"; "SVar"; "holds"; "rm"; "sobj"; "sv_eqb"; "cell"; "ob_base"; "rw"; "sprop_below"; "swf"; "ob_cells"; "ob_hi"; "ob_lo"; "soff"; "DUnknown"; "SPBranch"; "SPNot"; "mkObj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_subst"; "bud_le"; "BXok_d"; "bd_wpos"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_base"; "ax_X"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "of_nat"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "nth_error"; "hd"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom"; "pC"; "pK"; "pD"; "vLEN"; "kb16"; "tvB"; "pI"; "s_grown"; "vKg"; "ndB"; "vBUF"; "s_L0"; "s_keep"; "s_retE"; "bdL"; "pJ"; "vDg"; "R_v"; "VL"; "E_ms0"; "E_vrx"; "K_ok"; "ndPL"; "nd_pre"; "s_st"; "s_v"; "PROGL"; "ndP"; "vALC"; "vOUT"; "E_vr"; "PD_vrr"; "P_ret1"; "Pre_blr"; "T_grown"; "T_grownC"; "T_grownF"; "T_keepC"; "T_keepF"; "X_st"; "X_stA"; "cutsE"; "exitsE"; "ndPE"; "pNX"; "slot_facts"; "tvP"; "C_LI"; "FUEL_blr"; "K_st"; "L_ms"; "O_D"; "O_txt"; "P_ret0"; "P_retL0"; "P_retL1"; "Pre_ms"; "R_m"; "T_keep"; "X_stS"; "Xk_v"; "bdS"; "cutpcs_blr"; "ok_facts"; "s_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "nd_below"; "ND"; "JA_pre"; "nd_tv"; "JA"; "TPA"; "fbinA"; "ffinA"; "ok_frameKA"; "tvinA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub_id_below"; "rho_absorb"; "wsub"; "sv_subst"; "in_ranges"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "import_subA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom"; "B32"; "vC"; "vK"; "KLG"; "PHI"; "Pre_vr"; "spm"; "vDt"; "P_grown"; "c8"; "tv0"; "vDn"; "vKn"; "nd0"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "sv_vars_all"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "FBx"; "ivar_ok"; "tvz"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf.Sum"; "baseBF";
"PhiL"; "Posts_blr"; "Phis"; "bdK"; "extraB"; "baseBz"; "d0"; "K0"; "L0"; "Phi0"; "extraAL"; "extraTX"; "tableL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "JAF"; "carve_site_chk"; "JLAP"; "phiK"; "phi_reads"; "ejcertAF"; "wsub_id_on"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "pdescA"; "pd_okA"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf"; "P0_blr"; "Psi_def"; "P0_bli0"; "PDk_blr"; "Psi_bli"; "Psi_ret1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "decodes"; "lines_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.BLRAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_pf"; "P0_vrr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_eqs"; "o_slotX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_memset_pre"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Arith.PeanoNat.Nat"; "pred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "is_shadowZ"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase CellTile ArrMat TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr BLRAddr.

Definition P0_bli0 (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S16S1S40S34Vr;S5fA2M0R1A2S42R1S41G0S34Vr;S58A2A2A2A2SeaVCST;Vr;VFB;VFF;R2A5F_;Fa;S101VFF;S34Vr;S71A2Z30A3A2").
Definition P0_blr (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1Sf2VCST;VFB;VFF;Vr;A4S16S1S40S34Vr;Sc1A2M0R1A2S42R1S41G0S43Z10S34Vr;SbcA2A2A2A2A2S2S0SfS4eQ8A1M1A1S23Vr;S4fQ40R2A2A2S10G1A1A3A1F_;Fz;A2").

Definition Psi_def (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S16S1S40S34Vrho;S21P8cA1A2M0R1A2S42R1S41G0S43Z10S34Vrho;S21P8eA1A2A2A2A2A2S2S0SfS4eQ8A1M1A1S23Vrho;S4fQ40R2A2A2S10G1A1A3A1F_;Fz;").
Definition Psi_bli (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S9S8S16S16A2M0A1M1G1S1S0S16S45S14G0R1A2A1S34Vrho;S21P8dA1A2A3S1Sf6S23Vrho;A1S34Vrho;S21P8cA1A2R1A3Sf7R1S34Vr0;S58A2A2A2A2LT;A2").
Definition Psi_ret1 (r0 rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1Sf4Vr0;Vrho;A2Sf1Vr0;Vrho;A2A2").
Definition PDk_blr : list pdescK := ltac2:(tb__ "0|3|
SbS8S8S3bS96A2M0S1aS1aOFrho;Fr0;M1A2M2SaG0G1SaS3bS96S8aS70A4Sf1A4SbG2SaG0G1SaS3bS96S75S70A4Sf5A4ScG2A1A3A3").

Lemma U_Z_to_bv : ltac2:(tb__ "0|1|
S16S1S40Z0R1A2S42R1S44Z2Z40A2A2A2S0S16S50Q40M0S4fG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. exact Hz. Qed.
Lemma rd64_shift : ltac2:(tb__ "0|4|
S4eQ40M0A1SfS4eQ8A1A1M1F_;M2G2S16S16S16S0SfS16A1M3S100R5R3A2S11S16R1A2A3S16S1S40Z0R1A2S42R1Z8A2A2S0G1R7S4fG0S41R5R2A2A2A1R8S4fG0S41R6R2A2A2A1A3F_;Fj;S0G3S100R6R4A2S11S16R3A2A3F_;F_;Fv;Fa';Fa;Fm';Fm;").
Proof.
  intros m m' a a' v H HE. pose proof (rd64_range m a v H) as R.
  rewrite <- (U_Z_to_bv v R). apply rd64_of_bytes. intros j Hj. rewrite (HE (Z.of_nat j)) by lia. apply (rd64_enc_bytes m a v H j Hj).
Qed.
Lemma decodes_shift : ltac2:(tb__ "0|4|
S4eQ40M0A1SfS4eQ8A1A1M1Fx;M2G2S9S8S16S16A2M3A1S16S16S16S1S40Z0R1A2S42R1S43Z10S45S14G3R4A2A1A2A2A2S0G1R6S4fG0S41R3R2A2A2A1R7S4fG0S41R4R2A2A2A1A3F_;Fj;Sf6R6R3R4A3Sf6R6R3R5A3F_;F_;Fd';Fd;FT;Fm';Fm;").
Proof.
  intros m m' T. induction T as [|p r IH]; intros d d' HE HD; [exact I|]. cbn [length] in HE. destruct HD as [[H1 H2] HR]. split.
  - split.
    + apply (rd64_shift m m' d d'); [exact H1|]. intros j Hj. apply HE. lia.
    + apply (rd64_shift m m' (d + 8) (d' + 8)); [exact H2|]. intros j Hj. rewrite <- !Z.add_assoc. apply HE. lia.
  - apply (IH (d + 16) (d' + 16)); [|exact HR]. intros j Hj. rewrite <- !Z.add_assoc. apply HE. lia.
Qed.
Lemma nth_error_lastZ {A} : ltac2:(tb__ "0|1|
S9VA;A1VA;VA;S0SfVA;A1S4cVA;SeVA;R3SbVA;R2ScVA;A1A3A3M0S10bS14VA;G0A2A1A3S11VA;R1A2A3S0VA;R2R3A3F_;Fq;Fx;Fl;").
Proof. intros l x q H. rewrite length_app in H. cbn [length] in H. replace (Nat.pred (length l + 1)) with (length l) in H by lia. rewrite nth_error_last in H. injection H as <-. reflexivity. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sf8S1aS9S4eQ40A1A1Sb8OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S109S48VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S16S10aVCST;R1A2S1S40Z0R2A2S42R2SfdA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S16S10aVXGL;R1A2S1S40Z0R2A2S42R2SfdA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S9S8S8S16S16A2S16A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Variable rho0 : valuation.

Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S1aOFr;") := ltac2:(tb__ "0|0|
Sf0VCST;VFB;VFF;A3").
Definition Posts_blr : list (axst * jpostA) := ltac2:(tb__ "0|0|
S102VAInv;VCST;VXGL;VKc;Sf0VCST;A1S97Sf3VFB;VFF;VBX;Aa").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S9cVAInv;VCST;VXGL;S51VKc;Vrho0;VP0;VFB;VFF;VBX;S97Vnd;Ac").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb3S48S51Vrho0;Vtp0;Sd4A5").

Definition d0 : Z := uval rho0 vDt.
Definition K0 : Z := uval rho0 vK.
Definition L0 : Z := uval rho0 vLEN.

Definition Phi0 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S16S1S40Sd9R1A2S42R1S41Sd9S43Z10SdaA2A2A2A2S2S0SfS4eQ8A1M0A1S23Vrho;S4fQ40R2A2A2S10G0A1A3A1F_;Fz;").

Definition tableL (rho : valuation) (T : list (Z * Z)) : Prop := ltac2:(tb__ "0|2|
S1S0S16S45S14S8S16S16A2M0VT;A2M1A1S34Vrho;S55A2A3S1Sf6S23Vrho;A1S34Vrho;S57A2VT;A3S1Sf7VT;SdbA2G0S0SfG0A1S4cG0VT;S10bG1A1A3S11G0R1A2A3S40S41S41S12S16S16R2A3S15S16S16R2A3A2Z1A2S34Vrho;S81A2A2F_;Fq;A2A2A2").
Definition PhiL (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S1S3S9S8S16S16A2A1M0G0SdfVrho;R1A2LT;A2S16S1S40S34Vrho;S57A2M1R1A2S42R1S41G1S43Z10S34Vrho;S56A2A2A2A2A2S2S0SfS4eQ8A1M2A1S23Vrho;S4fQ40R2A2A2S10G2A1A3A1F_;Fz;A2").
Definition Phis : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|4|
SbS8S9S17A1M0S1aOFrho;M1A2M2SaG0G1ScS17A1M3SdcA4SbG2SaG0G1SbS17P119SbS17P118SbS17P122SbS17P11aG3A3A3A3A3Sd3A4ScG2A1A3A3").
Let JAFv (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Se2VAInv;VCST;VXGL;S51VKc;Vrho0;VP0;VFB;VFF;VBX;S97Se5Sd5Vk;A2Vnd;Ad").

Lemma Phis_reads : ltac2:(tb__ "0|3|
SacS8S9S17A1M0S1aOF_;M1A2M2G2Se6S12G0G1R1A3S15G0G1R1A3A2Lp;Sd5A3").
Proof.
  unfold Phis. constructor; [|constructor; [|constructor]]; cbn [fst snd]; unfold Phi0, PhiL, tableL.
  - intros rho rho' _ _ HM H z Hz. rewrite <- HM. exact (H z Hz).
  - intros rho rho' HV _ HM [(T & H1 & H2 & H3 & H4) HD].
    assert (E : forall v, In v [281; 280; 290; 282]%positive -> uval rho' (SVar v) = uval rho (SVar v)) by (intros v Hv; unfold uval; cbn [eval]; rewrite <- (HV v Hv); reflexivity).
    unfold pC, pD, pK, pNX in *.
    rewrite (E 281%positive) by (cbn; tauto). rewrite (E 280%positive) by (cbn; tauto). rewrite (E 290%positive) by (cbn; tauto). rewrite (E 282%positive) by (cbn; tauto).
    split; [exists T|].
    + split; [exact H1|]. split; [|split; [exact H3 | exact H4]]. apply (decodes_ext (rm rho)); [intros z Hz; symmetry; apply HM | exact H2].
    + intros z Hz. rewrite <- HM. exact (HD z Hz).
Qed.
Lemma ejcertAF_ok : ltac2:(tb__ "0|0|
S0S6Se7S48S51Sd5S85S93P64S7eS7fA8S7A3").
Proof. rewrite (ejcertAF_V segs NF Phis PhisV FUEL_blr cutpcs_blr 100 cutsE exitsE eq_refl). exact ejcertAF_ok0. Qed.

Lemma JA_P0 : ltac2:(tb__ "0|0|
S96S3bS1aS9S4eQ40A1A1SafS52S48VJAv;R5A1R4R3R2R1A6S1VP0;Vrho0;A1Sc9S51Vrho0;R4A3A2F_;Fw;Ftp;Frho;FS;Fnd;").
Proof. intros nd S rho tp [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.
Lemma vals_uval : ltac2:(tb__ "0|1|
S1aS17Sc9S51Vrho0;R2A3Sd1R2S51A2S0S16S34R4S21R3A1M0A2S34Vrho0;G0A2A3F_;F_;Fv;Frho;").
Proof. intros rho v Hav Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Definition baseBF (F : list sprop) : Prop := ltac2:(tb__ "0|4|
S1S0S6S49S19S1bS1cS21P1eA1M0Sc0SfbA1A2A1VF;A3S7A3S1S0S6S49S19S1bS1cG0S21PaA1M1A2A1VF;A3S7A3S1S0S6S49S19S1bS1cG1S1dSc8A1M2A2A1VF;A3S7A3S1S0S6S49S19S1bS1cG1S72A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS1fSa2S72S1dZ20A1A3G2A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS72G2A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS55S56A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS56S1dSbaA1A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS1fSa2S57S59S56A1A3G0A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS57G0A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS1fSa2S5fS58A3S1dZ7fffff800000A1M3A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS1dZ1000A1S5fA2A1VF;A3S7A3S1S0S6S49S19S1bS1cS58S1dS44Z2Z1aA2A1A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS5fG3A2A1VF;A3S7A3S1S0S6S49S19S1bS1cS1dZ7fff7f800000A1G0A2A1VF;A3S7A3S0S6S49S19S1bS1cG0G3A2A1VF;A3S7A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Record baseBz (rho : valuation) : Prop := BBZ {
  bz_sp : aceil + 144 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_v : uval rho (SVar 10) <= uval rho vOUT /\ uval rho vOUT + 32 <= 2 ^ 47;
  bz_ck : uval rho pC <= uval rho pK <= B32;
  bz_ek : uval rho (kb16 pK) = 16 * uval rho pK;
  bz_dk : uval rho pD + uval rho (kb16 pK) <= bv_unsigned (rw rho V_TOP);
  bz_txt : 4096 <= uval rho vBUF /\ uval rho vBUF + uval rho vLEN <= 140737479966720 /\ uval rho vLEN <= 2 ^ 26;
  bz_top : bv_unsigned (rw rho V_TOP) + 144 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S1aS16S1S40Z0R1A2S40R1S34R2S21PaA1M0A2A2A2S0S16S34R3Sc0R2A1A2S46S34R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RR.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma baseBz_of : ltac2:(tb__ "0|0|
S1aS9S19A1SacS19S22R2A1R1A3Sd2R2A1Sd8R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B14) as H17. zf H17. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H17.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2. zf HT1. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8. pose proof (holds_mem _ _ _ HF B9) as H9.
  pose proof (holds_mem _ _ _ HF B10) as H10. pose proof (holds_mem _ _ _ HF B11) as H11. pose proof (holds_mem _ _ _ HF B12) as H12.
  pose proof (holds_mem _ _ _ HF B13) as H13.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf H11. zf H12. zf H13. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold two47, RR.two47, B32, FR in *.
  rewrite !uval_lit in H3, H5, H6, H8, H12, H13, HT1, HT2, H17 by lia.
  rewrite uval_spm in H1 by lia. pose proof (uval_range rho pC). pose proof (uval_range rho pD). pose proof (uval_range rho vOUT).
  pose proof (uval_range rho vBUF). pose proof (uval_range rho vLEN).
  assert (EK : uval rho (kb16 pK) = 16 * uval rho pK) by (unfold kb16; apply uval_mul_lit; lia).
  rewrite uval_add_small in H5 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H5 by lia.
  rewrite uval_add_small in H9 by lia. rewrite uval_lit in H11 by lia. rewrite uval_add_small in H11 by lia.
  constructor; unfold aceil, B32, FR; lia.
Qed.

Lemma P0b_now : ltac2:(tb__ "0|1|
S1aSc9S51Vrho0;R1A3VP0;Vrho0;A1S1S16S1S40S34R4S5fA2M0R1A2S42R1S41G0S34R4S58A2A2A2A2SeaVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S101VFF;S34R3S71A2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav ((A & B) & _). unfold uval, vBUF, vLEN, vALC. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 13%positive eq_refl), <- (proj1 Hav 33%positive eq_refl).
  auto.
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|0|
S1aS9S8S18S18A2A1S9S8S8S18S16A2S18A2A1S16SeaVCST;Vrho0;VFB;VFF;R1A5SeaVCST;Vrho0;ScdVFB;R5R4A3SebVFF;R5R3A3R2A5F_;Fa;Ffr;Ftv;Frho;").
Proof.
  intros rho tv fr a [H|[H|[(b & n & Hin & Hr)|(f & sz & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [unfold FBx; apply in_or_app; left; exact Hin | exact Hr].
  - right; right; right. exists f, sz, fl. split; [unfold FFx; apply in_or_app; left; exact Hin | exact Hr].
Qed.

Lemma d_nz_of_J : ltac2:(tb__ "0|1|
S96S1aS9S4eQ40A1A1S9Sb9A1Sb8S18S18VJAv;R7R6R5R4R3A5S4aS8S18S18A2SaS18S18R3S59R2A1A4S9bR8A1A3S40S34R8R3A2SbaA2S2S0S16S34R9R4A2Z0M0A3A1S2S0S16S34RaR6A2G0A3A1F_;F_;F_;F_;Fk;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d k HJ Hin Hk Hk0 Hd.
  pose proof (JA_null_size0 AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue nd rho tp tr md (d, kb16 k) HJ Hin Hd) as Z0.
  cbn [snd] in Z0. change (bv_unsigned (eval rho (kb16 k))) with (uval rho (kb16 k)) in Z0.
  unfold kb16, B32 in *. rewrite uval_mul_lit in Z0 by lia. lia.
Qed.

Lemma JA_blk_txt : ltac2:(tb__ "0|2|
S96S3bS1aS9S4eQ40A1A1SafS18S18S52S48VJAv;R7A1R6R5R4R3A6S4aS8S18S18A2SaS18S18R3R2A4S9bR8A1A3S2S0S16S34R7R4A2Z0A3A1S16S1S40S34Vrho0;S5fA2M0R1A2S42R1S41G0S34Vrho0;S58A2A2A2A2S2S1S40S34RaR7A2M1R2A2S42R2S41G1S34RaR6A2A2A2A2A1F_;Fa;F_;F_;F_;Fn;Fd;Fw;Ftp;Frho;FS;Fnd;").
Proof.
  intros nd S rho tp [tr [ms md]] d n [_ (Ai & kc & HJ)] Hin Hnz a Ha Hr.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _).
  destruct (proj1 (Forall_forall _ _) HN (d, n) Hin Hnz) as (_ & Hlive & Hnfb). unfold tvv in Hlive, Hnfb. cbn [fst snd] in Hlive, Hnfb.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho tp md FB FF _ _ a HM HB HFF HT Hlive Hnfb).
  - unfold uval in Hr. exact Hr.
  - exact (proj1 (proj1 HP0) a Ha).
Qed.

Lemma JA_blk_txtK : ltac2:(tb__ "0|2|
S96S3bS1aS9S4eQ40A1A1SafS18S18S52S48VJAv;R7A1R6R5R4R3A6S4aS8S18S18A2SaS18S18R3S59R2A1A4S9bR8A1A3S40S34R7R3A2SbaA2S16S1S40S34Vrho0;S5fA2M0R1A2S42R1S41G0S34Vrho0;S58A2A2A2A2S2S1S40S34RaR7A2M1R2A2S42R2S41G1S43Z10S34RaR6A2A2A2A2A2A1F_;Fa;F_;F_;F_;Fk;Fd;Fw;Ftp;Frho;FS;Fnd;").
Proof.
  intros nd S rho tp w d k Hw Hin Hk a Ha. pose proof (uval_range rho k) as Rk.
  assert (EK : uval rho (kb16 k) = 16 * uval rho k) by (unfold kb16; apply uval_mul_lit; unfold B32 in Hk; lia).
  destruct (Z.eq_dec (uval rho k) 0) as [K0z|Kn0]; [lia|].
  assert (Hd : uval rho d <> 0).
  { destruct w as [tr [ms md]]. destruct Hw as [_ HJ]. exact (d_nz_of_J nd rho tp tr md d k HJ Hin Hk Kn0). }
  rewrite <- EK. exact (JA_blk_txt nd S rho tp w d (kb16 k) Hw Hin Hd a Ha).
Qed.

Lemma baseBF_E_vrx : ltac2:(tb__ "0|0|
Sd2S1eS3cS69A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseBF_E_ms0 : ltac2:(tb__ "0|0|
Sd2S1eS3cS68A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma R_v_shape : ltac2:(tb__ "0|0|
S0S9S24A1S66SbS24S32S21PaA1S1dS47SfbA1A1S1dZ0A1S2bS4dS24S88S66A3A1S2fA5SbS24S89ScS24A1A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma not_in_R_blk : ltac2:(tb__ "0|3|
S1aS16S16S16Sd8R4A1Sc9S51Vrho0;R5A3S40Z0R5A2S40S41R6S43Z10M0R5A2A2S50Q40M1S28R7S106A2A2A2S16S1S40S34Vrho0;S5fA2M2R1A2S42R1S41G2S34Vrho0;S58A2A2A2A2S2S1S40R9R2A2S42R2S41R9S43G0R8A2A2A2A2A1F_;Fa;S1S40R8R6A2S42R6S41R8S43G0R7A2A2A2A2S2SabRaS66S4fG1R7A2A3A1F_;F_;F_;F_;F_;F_;Fz;Fkz;Fdz;Frho;").
Proof.
  intros rho dz kz z BZ Hav Hd Hk HTX Hz (o & Ho & Hr). destruct BZ as [Bsp Bv Bck EK Bdk Btx [BT1 BT2]].
  rewrite U_Z_to_bv in Hr by lia.
  rewrite R_v_shape in Ho. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - apply range_lit' in Hr; [|unfold FR; lia|unfold FR; lia]. unfold FR in Hr. lia.
  - unfold obj_range, obj_lo_of, obj_hi_of, O_txt in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
    rewrite soff_lit_small in Hr by lia. change (soff rho (SVar 13)) with (soff rho vLEN) in Hr. rewrite (soff_smallu rho vLEN) in Hr by lia.
    change (bv_unsigned (eval rho vBUF)) with (uval rho (SVar 12)) in Hr. change (uval rho vLEN) with (uval rho (SVar 13)) in Hr.
    rewrite (vals_uval rho 12 Hav ltac:(reflexivity)), (vals_uval rho 13 Hav ltac:(reflexivity)) in Hr.
    apply (HTX z); [change vBUF with (SVar 12); change vLEN with (SVar 13); lia | exact Hz].
Qed.

Lemma HIN_vr : ltac2:(tb__ "0|4|
S1aSf8Se9SacS19S22R3A1S1eS3cS69A1A1A3VP0;Vrho0;A1Sc9S51Vrho0;R5A3S9eVFB;R5A2S9fVFF;R6A2Sa1VFB;R7R8S5aS57S56A2M0A4ScfR9G0A2S3S1aS1aS3S9S4eQ40A1A1M1G1S3Sb8Sb8VAInv;RcR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S9dVrho0;RaA2Sd3RcA1S1SeeVCST;Vrho0;VFB;VFF;RdScS8S18S18A2A1M2ScS8S8S18S16A2S18A2A1M3S66A8S1SefVCST;VXGL;Vrho0;VFB;VFF;RdG2G3S91A9SfcVFB;SebVFF;RdG3A3Sa6Sa8RdS66RbA3S6eA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;Frho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HZ (rho1 & tp1 & md1 & HM) HT [_ HDEF]. destruct (P0b_now rho Hav HP0) as (HTt & HA).
  pose proof (baseBz_of rho _ HF baseBF_E_vrx) as BZ. pose proof BZ as [Bsp Bv Bck EK Bdk Btx Btop]. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. rewrite R_v_shape in Ho. cbn in Ho. destruct Ho as [<-|[<-|[]]].
    + left. apply range_lit' in Hr; [|unfold FR; lia|unfold FR; lia]. unfold FR in *. lia.
    + apply pclMA_x. apply HTt. unfold obj_range, obj_lo_of, obj_hi_of, O_txt in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      rewrite soff_lit_small in Hr by lia. change (soff rho (SVar 13)) with (soff rho vLEN) in Hr. rewrite (soff_smallu rho vLEN) in Hr by lia. unfold uval, vBUF in *. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
    + rewrite uval_lit in Ha by lia. left. lia.
    + rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
    + apply pclMA_x. apply HTt. exact Ha.
  - unfold P0_vrr, P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with pK. change (wsub_get s_v 15) with pD. change (wsub_get s_v 14) with vALC.
    split; [split|].
    + intros HK0 HD0. unfold tvz in HZ. pose proof (proj1 (Forall_forall _ _) HZ (pD, kb16 pK) ltac:(left; reflexivity)) as X.
      cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X. specialize (X ltac:(intros Y; exact (Y HD0))).
      change (bv_unsigned (eval rho (kb16 pK))) with (uval rho (kb16 pK)) in X. rewrite EK in X. unfold uval in X. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    +
      assert (EvD : uval (rho_sub (rho_absorb rho R_v ms) s_v) vDt = uval rho pD) by (unfold uval; rewrite <- eval_subst, eval_absorb; reflexivity).
      assert (EvK : uval (rho_sub (rho_absorb rho R_v ms) s_v) vK = uval rho pK) by (unfold uval; rewrite <- eval_subst, eval_absorb; reflexivity).
      rewrite EvD, EvK. intros z Hz. cbn [rho_sub rm].
      assert (HTX : forall a, uval rho0 vBUF <= a < uval rho0 vBUF + uval rho0 vLEN -> ~ (uval rho pD <= a < uval rho pD + uval rho (kb16 pK))).
      { intros a Ha Hra. pose proof (uval_range rho pK) as RK.
        assert (Hnz : tnz rho (pD, kb16 pK)).
        { unfold tnz. cbn [fst]. intros HD0. unfold tvz in HZ.
          pose proof (proj1 (Forall_forall _ _) HZ (pD, kb16 pK) ltac:(left; reflexivity)) as X. cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X.
          specialize (X ltac:(intros Y; exact (Y HD0))). change (bv_unsigned (eval rho (kb16 pK))) with (uval rho (kb16 pK)) in X. lia. }
        destruct (proj1 (Forall_forall _ _) HN (pD, kb16 pK) ltac:(left; reflexivity) Hnz) as (_ & Hlive & Hnfb). unfold tvv in Hlive, Hnfb. cbn [fst snd] in Hlive, Hnfb.
        apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho1 tp1 md1 FB FF _ _ a HM HB HFF HT Hlive Hnfb); [unfold uval in Hra; exact Hra|].
        apply (proj1 (proj1 HP0) a Ha). }
      unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho R_v (Z_to_bv 64 z)) as [Hin|Hout]; [exfalso|exact (HDEF z Hz)].
      pose proof (uval_range rho pD). apply (not_in_R_blk rho (uval rho pD) (uval rho pK) z BZ Hav ltac:(lia) ltac:(rewrite <- EK; exact Bdk) ltac:(rewrite <- EK; exact HTX) Hz Hin).
Qed.

Lemma site_ms : ltac2:(tb__ "0|0|
S1aS111VAInv;VCST;VXGL;S51Vrho0;VP0;VFB;VFF;S68S95S8eR1S5eS10S16A1Sf8Se9S5Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR HM HTP HTK. destruct (P0b_now rho Hav HP0) as (HT & HA).
  pose proof (baseBz_of rho _ HF baseBF_E_ms0) as [Bsp Bv Bck EK Bdk Btx Btop]. apply T_ok_rw in HTK as [HTK HTR].
  factz HF (SPNot (SPBranch BC_EQ pD (SLit 0))) HD0. rewrite uval_lit in HD0 by lia.
  factz HF (SPUle (SAlu ALU_ADD (kb16 pC) (SLit 16)) (kb16 pK)) HSL.
  pose proof (uval_range rho pC) as RC. pose proof (uval_range rho pD) as Rd.
  assert (EC : uval rho (kb16 pC) = 16 * uval rho pC) by (unfold kb16; apply uval_mul_lit; unfold B32 in *; lia).
  rewrite uval_add_small in HSL by (rewrite EC, uval_lit by lia; unfold B32 in *; lia). rewrite EC, EK, uval_lit in HSL by lia.

  cbn [nd_tv ndB tvB] in HN. assert (Hnz : tnz rho (pD, kb16 pK)) by (unfold tnz; cbn [fst]; unfold uval in HD0; exact HD0).
  destruct (proj1 (Forall_forall _ _) HN (pD, kb16 pK) ltac:(left; reflexivity) Hnz) as (_ & HinL & _). unfold tvv in HinL. cbn [fst snd] in HinL.
  change (bv_unsigned (eval rho pD)) with (uval rho pD) in HinL. change (bv_unsigned (eval rho (kb16 pK))) with (uval rho (kb16 pK)) in HinL.
  assert (INBLK : forall a, uval rho pD <= a < uval rho pD + uval rho (kb16 pK) -> cmaddrA CST Ai None a).
  { intros a Ha. right; right; left. exists (uval rho pD), (uval rho (kb16 pK)). split; [exact HinL|]. split; [discriminate | lia]. }
  split; [|split; [|exact I]].
  - intros o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
    + left. apply range_lit' in Hr; [|lia|lia]. unfold FR in *. lia.
    + unfold O_vec16 in Hr. apply range_lit' in Hr; [|lia|lia]. left. unfold vOUT in *. lia.
    + unfold O_al in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | unfold vALC in *; lia].
    + eapply (pclMA_cmaddrA CST rho0 FB FF); [exact HBf | exact HFF | exact HTP |]. apply HT.
      unfold obj_range, obj_lo_of, obj_hi_of, O_txt in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
      rewrite soff_lit_small in Hr by lia. change (soff rho (SVar 13)) with (soff rho vLEN) in Hr. rewrite (soff_smallu rho vLEN) in Hr by lia. unfold uval, vBUF in *. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; left.
    + rewrite uval_lit in Ha by lia. left. unfold vOUT in *. lia.
    + rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | unfold vALC in *; lia].
    + eapply (pclMA_cmaddrA CST rho0 FB FF); [exact HBf | exact HFF | exact HTP |]. apply HT. unfold vBUF, vLEN in *. exact Ha.
    + apply INBLK. fold pD pK in Ha. fold (kb16 pK) in Ha. exact Ha.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|0|
S1aS9S19A1S18SacS19S22R3A1R2A3Sd2R3A1S0S6S49S19S1bS1cS1fSa2S55S1dZ1A1A3R3A2A1R4A3S7A3S0S6S49S19S1bS1cR4S1dSbaA1A2A1R5A3S7A3SacS19S22R7A1S82S55R5A2A3F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF HB H1 H2. pose proof (baseBz_of rho _ HF HB) as [Bsp Bv Bck EK Bdk Btx].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite ?uval_lit in F2 by lia.
  pose proof (uval_range rho pC) as RC.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (EC : uval rho (kb16 pC) = 16 * uval rho pC) by (unfold kb16; apply uval_mul_lit; lia).
  assert (EKk : uval rho (kb16 k) = 16 * uval rho k) by (unfold kb16; apply uval_mul_lit; lia).
  unfold slot_facts. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia). rewrite EC, EKk, uval_lit by lia. lia.
  - rewrite EC, EKk. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S1aOF_;S9S19A1S9S35A1S0S6S39R1A1S7A3S110S51Vrho0;R4R3S1dZ0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma VL_val : ltac2:(tb__ "0|1|
S1aS18S16S40S34R3R2A2S44Z2Z1aA2M0A2S40S34R4S58A2G0A2S1S40Z0R3A2S42R3Z40A2A2S0S16S34R6S67R5R4A2A2S41S43Z8S46S41S41G0Z10A2S34R6S58A2A2S34R6R5A2A2A2R4A2A3F_;F_;F_;Fph;Fj;Fr;").
Proof.
  intros r j ph Hj Hl Hph. unfold VL. pose proof (uval_range r j) as Rj. pose proof (uval_range r vLEN) as Rl.
  assert (EA : uval r (SAlu ALU_ADD (SLit (2 ^ 26 + 16)) vLEN) = 2 ^ 26 + 16 + uval r vLEN) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (ES : uval r (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 26 + 16)) vLEN) j) = 2 ^ 26 + 16 + uval r vLEN - uval r j).
  { unfold uval in *. rewrite U_sub. rewrite EA. unfold M64v. apply Z.mod_small. lia. }
  assert (EM : uval r (SMd M_MUL (SLit 8) (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 26 + 16)) vLEN) j)) = 8 * (2 ^ 26 + 16 + uval r vLEN - uval r j)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  rewrite uval_add_small by (rewrite EM, uval_lit by lia; lia). rewrite EM, uval_lit by lia. reflexivity.
Qed.
Lemma meas_VL : ltac2:(tb__ "0|4|
S3bS96SdS16S18S16S1aS40S34R1R3A2S44Z2M0Z1aA2M1A2S40S34R2S58A2G1A2S1S40Z0R4A2S42R4Z40M2A2A2S0S16Se1SaS8S8S3bS96A2M3SdA2S8S16S18A2SaG3SdSaS3bS96RaR9A4R8A4SaS16S18R7S67R6R5A2A4A4R4A2S41S43R7S44G0G2A2A2S41S43Z8S46S41S41G1Z10A2S34R4S58A2A2S34R4R6A2A2A2R5A2A2A3F_;F_;F_;Fr;Fph;Fj;Frk;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA. cbn [ef_rank ef_var fst snd]. change (bv_unsigned (eval r (VL j ph))) with (uval r (VL j ph)). rewrite VL_val by assumption. reflexivity. Qed.

Lemma slot_rng : ltac2:(tb__ "0|5|
S1aS9S19A1SacS19S22R2A1R1A3Sd2R2A1S0S6S49S19S1bS1cS1fSa2S59S55A1M0S1dZ10M1A1A3M2S59S56A1A2A1R3A3S7A3S1S0S16S34R5S1fSa2S57G0A3A2S41S34R5S57A2S34R5G0A2M3A2A3S1S0S16S2eR5G0A2G3A3S1S0S16S2eR5G2A2S41G3G1A2A3S1S0S16G3S43G1S34R5S55A2A2M4A3S40S41G4G1A2S43G1S34R5S56A2A2A2A2A2A2A2F_;F_;F_;FF;Fr;").
Proof.
  intros r F HF HB HS. pose proof (baseBz_of r _ HF HB) as [Bsp Bv Bck EK Bdk Btx Btop].
  pose proof (holds_mem _ _ _ HF HS) as F1. zf F1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *.
  pose proof (uval_range r pC) as RC. pose proof (uval_range r pD) as Rd. unfold B32 in *.
  assert (EC : uval r (kb16 pC) = 16 * uval r pC) by (unfold kb16; apply uval_mul_lit; lia).
  rewrite uval_add_small in F1 by (rewrite EC, uval_lit by lia; lia). rewrite EC, EK, uval_lit in F1 by lia.
  split; [rewrite uval_add_small by (rewrite EC; lia); reflexivity|]. split; [apply soff_smallu; rewrite EC; lia|].
  split; [|split; [exact EC | exact F1]].
  rewrite (soff_smallu r) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
  rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia). rewrite EC, uval_lit by lia. lia.
Qed.

Definition extraAL (o : sobj) : bool := ltac2:(tb__ "0|1|
S6S6L_;M0S25S27Vo;A1S71A2G0S25S2dVo;A1S1dZ0A1A2S25S2cVo;A1S1dZ30A1A2S13X6x2S13X6x2").
Definition extraTX (o : sobj) : bool := ltac2:(tb__ "0|1|
S6S6L_;M0S25S27Vo;A1S5fA2G0S25S2dVo;A1S1dZ0A1A2S25S2cVo;A1S58A2S13X6x2S13X6x2").
Definition extraB (o : sobj) : bool := ltac2:(tb__ "0|0|
S6S6L_;SddVo;A1S7SdeVo;A1X6x2").
Lemma extraB_sound : ltac2:(tb__ "0|1|
S1aS9S24A1S9S8S18S18A2A1S9S8S8S18S16A2S18A2A1S24S16Sc9S51Vrho0;R6A3VP0;Vrho0;A1S40S34R8S58A2S44Z2Z1aA2A2S4aS24R5R8A3S0S6Sd7R6A1S7A3S1S40S12S16S16S33RbR7A2M0A3R6A2S42R6S15S16S16G0A3A2A2S4SeaVCST;Vrho0;ScdVFB;RcRaA3SebVFF;RcR9A3R7A5S4S1S40Z0R7A2S42R7SfdA2A2S10fR7A1A2A2F_;F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Fobjs;Frho;").
Proof.
  intros rho objs tv' fr o a Hav HP0 HL _ HE Hr. left. destruct (P0b_now rho Hav HP0) as (HT & (f & s & fl & Hin & H1 & H2)).
  unfold extraB, extraAL, extraTX in HE. apply lazy_orb_prop in HE as [HE|HE];
    apply lazy_andb_prop in HE as [Hb HE]; apply lazy_andb_prop in HE as [Hl Hh];
    apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hl; apply sv_eqb_sound in Hh; unfold obj_range, obj_lo_of, obj_hi_of in Hr; rewrite Hb, Hl, Hh in Hr; cbn [fst snd] in Hr.
  - rewrite !soff_lit_small in Hr by lia. change (bv_unsigned (eval rho vALC)) with (uval rho vALC) in Hr.
    right; right; right. exists f, s, fl. split; [apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.In_FFx; left; exact Hin | lia].
  - rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vLEN) in Hr by lia. change (bv_unsigned (eval rho vBUF)) with (uval rho vBUF) in Hr.
    apply pclMA_x. apply HT. lia.
Qed.
Lemma Csite_keep : ltac2:(tb__ "0|0|
S0S6Se3S7bS5aS57S56A2ScS8S8S18S16A2S18A2A1U0Sd7A5S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Csite_grown : ltac2:(tb__ "0|0|
S0S6Se3S79S5aS65S5dA2ScS8S8S18S16A2S18A2A1U0Sd7A5S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma PhiL_transport : ltac2:(tb__ "0|4|
S1aS1aS17S4aS17R1SbS17P119SbS17P118SbS17P122SbS17P11aScS17A1A3A3A3A3A3S0S4eQ40M0A1S28R4R2A2S28R3R2A2A3F_;Fv;S40S34R3S55A2S34R3S56A2A2S16S1S40S34R5S57A2M1R1A2S42R1S41G1S43Z10S34R5S56A2A2A2A2A2S0SfS4eQ8A1A1S23R5S4fG0R2A2M2A2S23R6G2A2A3F_;Fz;Sd3R5A1M3G3F_;F_;F_;F_;Fr';Fr;").
Proof.
  intros r r' HV HCK HM [(T & H1 & H2 & H3 & H4) HD].
  assert (E : forall v, In v [281; 280; 290; 282]%positive -> uval r' (SVar v) = uval r (SVar v)) by (intros v Hv; unfold uval; cbn [eval]; rewrite <- (HV v Hv); reflexivity).
  unfold PhiL, tableL. unfold pC, pD, pK, pNX in *.
  rewrite (E 281%positive) by (cbn; tauto). rewrite (E 280%positive) by (cbn; tauto). rewrite (E 290%positive) by (cbn; tauto). rewrite (E 282%positive) by (cbn; tauto).
  split; [exists T|].
  - split; [exact H1|]. split; [|split; [exact H3 | exact H4]]. apply (decodes_ext (rm r)); [|exact H2]. intros z Hz. apply HM. lia.
  - intros z Hz. rewrite HM by exact Hz. exact (HD z Hz).
Qed.
Lemma PhiL_reads : ltac2:(tb__ "0|0|
Se6SbS17P119SbS17P118SbS17P122SbS17P11aScS17A1A3A3A3A3Sd3A2").
Proof. exact (Forall_inv (Forall_inv_tail Phis_reads)). Qed.

Lemma chk_st : ltac2:(tb__ "0|5|
S1S0S6S3dS7dS86S6dA3S7A3S1S0S6Sa7S6dS51A2S7A3S1S0S6Sd0S51S20S3cS7dA1M0A1M1A2S7A3S1S0S6S98G1S5eA2S7A3S1S0S6SccS6dS5aS57S56A2M2G2A3S7A3S1S0S6S37S1eG0A1S36S6dS92S5bS55S56A3A2S63S5bS55S56A3A3S7A3S1Sd2S1eS3cS90A1A1M3A1S1S0S6S49S19S1bS1cS1fSa2S59S55A1M4S1dZ10A1A3S59S56A1A2A1G3A3S7A3S1S0S18S27SffA1S1fSa2S57G4A3A3S0S9S26A1S2bSffA1SbS26Sc3Z8S1fSa3S64S5bA3A2SbS26Sc3Z0S5bA2ScS26A1A3A3A3A2A2A2A2A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_keep : ltac2:(tb__ "0|5|
S1S0S6S3dS7aS6aS61A3S7A3S1S0S6Sa7S61S51A2S7A3S1S0S6Sd0S51S20S3cS7aA1M0A1M1A2S7A3S1S0S6S98G1S99S5aS57S56A2M2ScS8S8S18S16A2S18A2A1SbS35SbeS1fSa2S55S1dZ1A1A3S56A2SbS35SbdS56A1SbS35S6fS5bA1ScS35A1A3A3A3M3A3A2S7A3S1S0S6SccS61G2G2A3S7A3S1S0S6S37S1eG0A1S36S61S63S5bS55S56A3A2G3A3S7A3S1S0S6Se8SbS17P119SbS17P118SbS17P122SbS17P11aScS17A1A3A3A3A3S61A2S7A3S1S0S18Sa5S61P11cA2S64A3S1S0S18Sa5S61PdA2S58A3S1S0S6S2aG0A1S7A3S1S0S18S3eS7bA1S1dSfeA1A3S0S6S4bS19S29S20S3cS8fA1M4A1A1SeS19S94S57S55S56A3S1eG4A1A3A3S7A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_grown : ltac2:(tb__ "0|5|
S1S0S6S3dS78S6aS5cA3S7A3S1S0S6Sa7S5cS51A2S7A3S1S0S6Sd0S51S20S3cS78A1M0A1M1A2S7A3S1S0S6S98G1S99S5aS65S5dA2M2ScS8S8S18S16A2S18A2A1SbS35SbeS1fSa2S55S1dZ1A1A3S5dA2SbS35SbdS5dA1SbS35S6fS5bA1ScS35A1A3A3A3M3A3A2S7A3S1S0S6SccS5cG2S5aS57S56A2A3S7A3S1S0S6S37S1eG0A1S36S5cS63S5bS55S56A3A2G3A3S7A3S1S0S18Sa5S5cP119A2S55A3S1S0S18Sa5S5cP118A2S65A3S1S0S18Sa5S5cP122A2S81A3S1S0S18Sa5S5cP11aA2S5dA3S1S0S18Sa5S5cP11cA2S64A3S1S0S18Sa5S5cPdA2S58A3S1S0S6S2aG0A1S7A3S1S0S18S3eS79A1S1dSfeA1A3S0S6S4bS19S29S20S3cS77A1M4A1A1SeS19S82S55S5dA2S1eG4A1A3A3S7A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_vr : ltac2:(tb__ "0|7|
S1S0S6S4bS8SecS1aS1aOF_;F_;M0A2M1G1SedSbfS51S6eS20S3cS69A1A1M2S12SecG0R1A3A5Ld;S74A3S7A3S1S0S18SaaSb7S6eSbfSc2S69A4M3Sc5A2S65A3S1S0S18SaaG3Sc6A2S5dA3S1S0S6ScaSceS51S6eG2S3cSc2A1A4M4Sc5A2S7A3S1S0S6ScaG4Sc6A2S7A3S1S0S6S49S19S1bS31S30Sa4S65S1dZ0A1A3A1A1S1eS3cS77A1A1M5A3S7A3S1S0S6S49S19S1bS1cS1fSa2S65S59S5dA1A3S21P1eA1M6A2A1G5A3S7A3S1S0S6S49S19S1bS1cS5dS1dSbaA1A2A1G5A3S7A3S1S0S6S49S19S1bS1cG6Sc0SfbA1A2A1G5A3S7A3S0S6S49S19S1bS1cS1fSa2S55S1dZ1A1A3S5dA2A1G5A3S7A3A2A2A2A2A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma slot_in_blk : ltac2:(tb__ "0|7|
S1aS9S19A1S18S18SacS19S22R4A1R3A3S0S6S49S19S1bS1cS1fSa2S59S55A1M0S1dZ10M1A1A3S59R2A1A2A1R4A3S7A3S0S6S49S19S1bS1cR3S1dSbaA1A2A1R5A3S7A3S0S6S49S19S1bS1cS55R4A2A1R6A3S7A3S0S6S49S19S1bS1cS1fSa2R6S59R5A1A3S21P1eA1M2A2A1R7A3S7A3S0S6S49S19S1bS1cG2S1dZ7fffff800000M3A1A2A1R8A3S7A3S0S6S49S19S1bS1cR8G2A2A1R9A3S7A3S1S0S16S34RbS1fSa2R9G0A3A2S41S34RbR9A2M4S43G1S34RbS55A2A2M5A2A3S1S40S41G5G1A2S43G1S34RbR8A2A2M6A2S1S0S16S34RbS59R8A1A2G6A3S40S41G4G6A2G3A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fk;Fd;FF;Fr;").
Proof.
  intros r F d k HF H1 H2 H3 H4 H5 H6.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6. zf F1. zf F2. zf F3. zf F4. zf F5. zf F6.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *. unfold B32 in *. rewrite ?uval_lit in F2, F5 by lia.
  pose proof (uval_range r pC) as RC. pose proof (uval_range r d) as Rd. pose proof (uval_range r k) as Rk.
  assert (EC : uval r (kb16 pC) = 16 * uval r pC) by (unfold kb16; apply uval_mul_lit; lia).
  assert (EK : uval r (kb16 k) = 16 * uval r k) by (unfold kb16; apply uval_mul_lit; lia).
  rewrite uval_add_small in F1 by (rewrite EC, uval_lit by lia; lia). rewrite EC, EK, uval_lit in F1 by lia.
  rewrite uval_add_small in F4 by (rewrite EK; lia). rewrite EK in F4.
  rewrite uval_add_small by (rewrite EC; lia). rewrite EC. lia.
Qed.

Definition bdK (k : sv) : list bitem := ltac2:(tb__ "0|0|
SbS35SbeS1fSa2S55S1dZ1A1A3Vk;A2SbS35SbdVk;A1SbS35S6fS5bA1ScS35A1A3A3A3").
Lemma glue_carve : ltac2:(tb__ "0|9|
S3bS3bS3bS9S19A1Sa9S18S18S1aS9S4eQ40M0A1A1SafS0S3bS10cRaSeS19R7S1eS3cRaA1A1A3A2R9A3S0S6S4bS19S29S20S3cRbA1M1A1A1SeS19R8S1eG1A1A3A3S7A3S9Sb9A1Sb8VJAv;S99S5aR9R8A2ScS8S8S18S16A2S18A2A1M2Sd6R8A1A3R7R6R2R1A5SacS19S22R8A1S1eS3cRfA1A1A3SacS19S22R9A1RdA3F_;F_;Fmd;Ftr;S0S3bS112RcS1fSa2R8S59S55A1M3A3S1dZ10M4A1M5A3RbA3S0S18S3eRdA1S1dSfeA1A3S0S6S2aS3cRdA1A1S7A3S0S6Se3RfS5aRbRaA2G2U0Sd7A5S7A3S0S6S49S19S1bS1cS1fSa2G3G5A3S59RbA1A2A1SeS19ReS1eS3cR11A1A1A3A3S7A3S0S6S49S19S1bS1cRcS1dSbaA1A2A1SeS19RfS1eS3cR12A1A1A3A3S7A3S0S6S49S19S1bS1cS55RdA2A1SeS19R10S1eS3cR13A1A1A3A3S7A3S0S6S49S19S1bS1cS1fSa2RfS59ReA1A3S21P1eA1M6A2A1SeS19R11S1eS3cR14A1A1A3A3S7A3S0S6S49S19S1bS1cG6S1dZ7fffff800000A1A2A1SeS19R12S1eS3cR15A1A1A3A3S7A3S0S6S49S19S1bS1cR11G6A2A1SeS19R13S1eS3cR16A1A1A3A3S7A3S0S6S49S19S1bS1cS58S1dS44Z2Z1aA2A1A2A1SeS19R14S1eS3cR17A1A1A3A3S7A3S0S6S3dR16S6aR14A3S7A3S0S6Sa7R15S51A2S7A3S0S6Sd0S51S20S3cR18A1A1A2S7A3S0S6S98S20S3cR19A1A1S99S5aR16R15A2G2Sd6R15A1A3A2S7A3S0S6SccR18S5aR17R16A2S5aS57S56A2A3S7A3S0S6S37S1eS3cR1bA1A1S36R19S63S5bS55S56A3A2Sd6R17A1A3S7A3S16S1S40S41S34R18R1aA2S43G4S34R18S55A2A2A2M7R1A2S42R1S41G7G4A2A2A2S2S0SfS4eQ8A1M8A1S23R19S4fG0R2A2A2S10G8A1A3A1F_;Fz;S52S48VJAv;S99S5aR1aR19A2G2Sd6R19A1A3A1R1fR18R17R16A6S52S48VJAv;S5eA1S6aSa6R19R1cA2R18R17A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp';Frho';Fk;Fd;Fs;Ffl;FTC;FTF;FTB;").
Proof.
  intros TB TF TC fl s d k rho' tp' w HTF Hbelow Hfl HTC Hbase Hwf Hsite HS1 HS2 HS3 HS4 HS5 HS6 HL26 Hent Hid Hnf Hnb Htv Hbud Hdef Hw.
  assert (Hw1 : SPA segs (JAv (ND (tvB d k) [] (bdK k))) TF rho' tp' w).
  { rewrite <- HTF. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |]. intros tr md HJ HF. apply Forall_app. split; [exact (Hfl tr md HJ HF) | exact HF]. }
  assert (HFT : forall r, Forall (holds r) (ss_facts (ax_S TF)) -> Forall (holds r) (fl ++ ss_facts (ax_S TB))) by (intros r H; rewrite <- HTF in H; exact H).
  destruct w as [tr [ms md]].
  destruct (JA_carve_tr segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HNP (tvB d k) [] (bdK k) ANone 0 d (kb16 k) (SAlu ALU_ADD d (kb16 pC)) (SLit 16) TF rho' tp' tr ms md
              eq_refl Hbase ltac:(rewrite HTC; exact Hwf)) as (Hw2 & _ & _).
  - intros r HF. apply HFT in HF. destruct (slot_in_blk r _ d k HF HS1 HS2 HS3 HS4 HS5 HS6) as (A1 & A2 & A3 & A4). pose proof (uval_range r pC). rewrite A1, A3, uval_lit by lia. lia.
  - apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF TF (tvB d k) [] 0%nat extraB rho' Hsite).
    intros Ai tp1 md1 HF HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. apply HFT in HF.
    pose proof (holds_mem _ _ _ HF HL26) as F26. zf F26. rewrite uval_lit in F26 by lia.
    exact (extraB_sound rho' _ _ _ o a Hav' HP0' F26 Ho HE Hr).
  - intros z Hz. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw1)) as HF. apply HFT in HF.
    destruct (slot_in_blk rho' _ d k HF HS1 HS2 HS3 HS4 HS5 HS6) as (A1 & A2 & A3 & A4). rewrite A1, uval_lit in Hz by lia. apply Hdef. lia.
  - exact Hw1.
  - rewrite HTC in Hw2.
    exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc TC K_ok s (ND (tvB d k) [] (bdK k)) ndB (rho') tp' _ Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw2).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S16S9S4eQ40A1A1SaeF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S53S3bS1aS9S4eQ40A1A1SaeSacS19S22R3A1S1eS3cR4A1A1A3VTR;S52S48R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SaeSaeSaeSafR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SaeOSaeSafR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Qa : assn), (forall a, TR (P a) Qa) -> TR (fun w => exists a, P a w) Qa.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S53S53S3bS3bSa9S9S24A1M0S9S8S3bSb2A2M1A1S9S8S18S18A2M2A1SaeS1aS9S4eQ40A1A1M3G2S4aG2R1R5A3S4aG2R2S3fRbA1A3F_;Fr;S0SfG0A1Sb6RaR9R8A3S11G0R7A2A3S0S6Sb5RbRaR9R8SadG1S3bS12S3bSb2A2R7A4A5S7A3S1aG3VTR;S52S48RfRdR2R1A5Sb3S48S20S3cRdA1A1R2R1RaA5A2Ftp1;Frho1;S9Sb9A1M4Se9Sb8S54S48R9R8R10SaG4Sf9R3SfaR2R1A2A4A5R13RaR9R4R2A4R13Sa6Sa8RbRfSe0R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S3bSb2G4Se9Sb8S1aG3G4Se9Sb8S4aG1SaS3bSb2RaR9A4R14A3S54S48R12R11R19SaG4Sf9R9SfaR8R7A2A4A5R1cR13R12RaR8A4Sc9S20S3cR1aA1A1Sa6Sa8R14R18Se0R9R13RaA3A3R19A2R8A3S54S48R9R8ReSaG4Sf9R7SfaR6R5A2A4A5ReSa6Sa8R16R1aSe0RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S10dR17Se0RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1aScbR18Se0RdR17ReA3R1cR1dS3cR1eA1S3cR1fA1S3cR11A1R1RcA9VTR;S52S48Sb4R11Sa6Sa8R19R1dSe0ReR18RfA3A3R1eA2R18RdRcA5S10eR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S52S48R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_phi : ltac2:(tb__ "0|0|
S1aOF_;S96S3bS1aS9S4eQ40A1A1SaeR6R3A1VTR;S52S48VJAv;R6A1R5R4R3A5R2A2F_;VTR;S52S48Se2VAInv;VCST;VXGL;S51VKc;Vrho0;VP0;VFB;VFF;VBX;S97R7R6AdR5R4R3A5R2A2F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Hypothesis CMEMSET : ltac2:(tb__ "0|1|
Sf8S1aS9S4eQ40A1A1VTR;S52S48S105VAInv;R3VKc;A3S8dR2R1A5Sb3S48S51R2R1SbS8S3bSb2A2M0SaS3bSb2S87S104VAInv;VCST;VXGL;R3VKc;A5A4ScG0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
S9S8S16S16A2M0A1S9S8G0S16A2A1S3aS1aS9S4eQ40A1A1S38Z3R3A2VTR;S52S48S9aVAInv;VCST;VXGL;VKc;SfcR6R5A2R6R5R4S97Sc7AaSbfR3R2A5Sb3S48S51R3R2S102VAInv;VCST;VXGL;VKc;SfcS97S74R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|5|
S3bS96SdS8S16S18A2M0S1aS9S4eQ40A1A1M1S16G1S4aS8S8S8S3bS96A2M2SdA2M3G0A2SaG3G0SaG2SdSaS3bS96R8R7A4R6A4R5A4S7eA3Se5Sd5R7R5A3S1S40Z0Se1SaG3G0SaG2SdSaS3bS96RaR9A4R8A4R7A4R6A2M4A2S42G4R4A2A2VTR;S52S48VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|2|
S3bS96S1aOF_;M0S1aG0F_;S1aS9S4eQ40A1A1M1S16G1S4aS8S3bSb2A2SaS3bSb2R8Se4VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S97R7R5AbA4Sd4A3S1aR8R1A1R8Vrho0;R2A2F_;Fr;VTR;S52S48Se2VAInv;VCST;VXGL;S51VKc;Vrho0;VP0;VFB;VFF;VBX;S97R8R9AdRaR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;FPhi;Fnd;FP;").

Ltac meas := unfold efmeasA; cbn [ef_rank ef_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_blr PDk_blr PostsCk map fst snd]; do n right; left; reflexivity.

Ltac loopz HF :=
  let F1 := fresh in let F2 := fresh in
  fact HF (SPUle pJ (SLit (2 ^ 26))) F1; fact HF (SPUle vLEN (SLit (2 ^ 26))) F2; zf F1; zf F2; rewrite uval_lit in F1, F2 by lia;
  lazymatch type of F1 with uval ?r _ <= _ => pose proof (uval_range r pJ); pose proof (uval_range r vLEN) end.

Lemma TR_phi_in : ltac2:(tb__ "0|0|
S1aOF_;S96S3bS1aS9S4eQ40A1A1SaeR6R3A1VTR;S52S48Se2VAInv;VCST;VXGL;S51VKc;Vrho0;VP0;VFB;VFF;VBX;S97R7R6AdR5R4R3A5R2A2VTR;S52S48VJAv;R7A1R6R5R4A5R3A2F_;F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Proof. intros Phi nd S rho tp Qa HP H. eapply TR_pre; [|exact H]. intros w Hw. apply SPA_JAF_intro; [exact Hw | exact HP]. Qed.

Lemma X_L0 : ltac2:(tb__ "0|2|
S3bS1aS9S4eQ40A1A1M0S16G0S0S6S3dR5S84S60R5A1A3S7A3S0S6Sa7S60R6A1S51A2S7A3S0S6Sd0S51S20S3cR7A1A1A2S7A3S0S6S98S20S3cR8A1A1S6cA2S7A3S0S6SccS60R9A1Sc4S5aS57S56A2A3S7A3S0S6S37S1eS3cRaA1A1S36S60RaA1S63S5bS55S56A3A2S63S1dZ0A1M1SbbSbcA3A3S7A3S0S18Sa5S60RbA1P119A2SbbA3S0S18Sa5S60RcA1P118A2Sc1A3S0S18Sa5S60RdA1P11aA2SbcA3S0S18Sa5S60ReA1P122A2G1A3S0S6S49S19S1bS1cSbbG1A2A1S1eS3cRfA1A1A3S7A3S40S43Z5aS44Z2Z40A2A2RdA2VTR;S52S48VJAFv;U0S6cA2R11R10RfA5VFAM;ReRdA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FX;").
Proof.
  intros X rho tp b tp0 Hent Hid Hnf Hnb Htv Hbud Hs281 Hs280 Hs282 Hs290 HC0 Hb.
  apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof (holds_mem _ _ _ HF HC0) as FC0. zf FC0. rewrite uval_lit in FC0 by lia. pose proof (uval_range rho vC) as RC.
  eapply TR_pre; [|apply (REENTER C_LI ndB 1%nat (50, VL pJ 6) (rho_sub rho (s_L0 X))); [innth 1 | |]].
  - intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X C_LI (s_L0 X) nd_pre ndB rho tp w Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw).
  - cbn [phiK Phis nth map snd]. unfold PhiL, tableL.
    assert (E281 : uval (rho_sub rho (s_L0 X)) pC = uval rho vC) by (unfold uval, pC; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs281; reflexivity).
    assert (E280 : uval (rho_sub rho (s_L0 X)) pD = d0) by (unfold d0, vDt; rewrite <- (vals_uval rho 15 Hav ltac:(reflexivity)); unfold uval, pD; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs280; reflexivity).
    assert (E282 : uval (rho_sub rho (s_L0 X)) pK = K0) by (unfold K0, vK; rewrite <- (vals_uval rho 17 Hav ltac:(reflexivity)); unfold uval, pK; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs282; reflexivity).
    assert (EM : rm (rho_sub rho (s_L0 X)) = rm rho) by reflexivity.
    rewrite E281, E280, E282, EM. split; [exists []|].
    + cbn [length Z.of_nat]. split; [lia|]. split; [exact I|]. split; [apply lines_ok_nil|]. intros q Hq. cbn in Hq. discriminate.
    + exact HPhi.
  - unfold efmeasA. cbn [ef_rank ef_var fst snd]. pose proof (urange (eval (rho_sub rho (s_L0 X)) (VL pJ 6))). lia.
Qed.

Lemma X_R0 : ltac2:(tb__ "0|2|
S3bS1aS9S4eQ40A1A1M0S16G0S0S6S3dR5S75S62R5A1A3S7A3S0S6Sa7S62R6A1S51A2S7A3S0S6Sd0S51S20S3cR7A1A1A2S7A3S0S6S98S20S3cR8A1A1S80A2S7A3S0S6SccS62R9A1Sc4S83A3S7A3S0S6S37S1eS3cRaA1A1S36S62RaA1ScS35A1M1A2G1A3S7A3S0S18Sa5S62RbA1P8cA2Sc1A3S0S18Sa5S62RcA1P8dA2SbbA3S0S18Sa5S62RdA1P8eA2SbcA3S0S6S49S19S1bS1cSbbS1dZ0A1A2A1S1eS3cReA1A1A3S7A3VTR;S52S48VJAFv;U0S80A2RfReRdA5VFAM;RcRbA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FX;").
Proof.
  intros X rho tp b tp0 Hent Hid Hnf Hnb Htv Hbud Hs140 Hs141 Hs142 HC0.
  apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof (holds_mem _ _ _ HF HC0) as FC0. zf FC0. rewrite uval_lit in FC0 by lia. pose proof (uval_range rho vC) as RC.
  apply (TR_pre (SPA segs (JAv ndP) P_ret1 (rho_sub rho (s_retE X)) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X P_ret1 (s_retE X) ndPE ndP rho tp w Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw). }
  apply (TR_phi_in (fun r => Psi_ret1 rho0 r) ndP P_ret1 (rho_sub rho (s_retE X)) tp).
  - unfold Psi_ret1, Psi_bli, Psi_def.
    assert (E141 : uval (rho_sub rho (s_retE X)) (SVar 141) = uval rho vC) by (unfold uval; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs141; reflexivity).
    assert (E140 : uval (rho_sub rho (s_retE X)) (SVar 140) = d0) by (unfold d0, vDt; rewrite <- (vals_uval rho 15 Hav ltac:(reflexivity)); unfold uval; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs140; reflexivity).
    assert (E142 : uval (rho_sub rho (s_retE X)) (SVar 142) = K0) by (unfold K0, vK; rewrite <- (vals_uval rho 17 Hav ltac:(reflexivity)); unfold uval; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs142; reflexivity).
    assert (EM : rm (rho_sub rho (s_retE X)) = rm rho) by reflexivity.
    rewrite E141, E140, E142, EM. split; [exists []|exact HPhi].
    cbn [length Z.of_nat]. split; [lia|]. split; [exact I | apply lines_ok_nil].
  - apply (POST P_ret1 ndP (fun r => Psi_ret1 rho0 r) Psi_ret1); [innth 1 | intros r Hr; exact Hr].
Qed.

Lemma X_RL : ltac2:(tb__ "0|2|
S3bS3bSa9S1aS1aOF_;F_;S1aS9S4eQ40A1A1M0S16G0S0S6S3dR8R7R6A3S7A3S0S6Sa7R7S51A2S7A3S0S6Sd0S51S20S3cRaA1A1A2S7A3S0S6S98S20S3cRbA1A1S6bA2S7A3S0S6SccRaS5aS57S56A2S83A3S7A3S0S6S37S1eS3cRdA1A1S36RbScS35A1M1A2G1A3S7A3S4aS8S3bSb2A2SaS3bSb2RdSe4VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S97S70RbAbA4Sd4A3S1aSd3R1A1ReVrho0;Sa6R2RfA2A2F_;Fr;VTR;S52S48VJAFv;U1S6bA2R10RcRbA5VFAM;RaR9A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;Fs;FP;FX;").
Proof.
  intros X P s Psi rho tp b tp0 Hent Hid Hnf Hnb Htv Hbud HinP HPSI.
  apply TR_phi. intros HPhi.
  apply (TR_pre (SPA segs (JAv ndP) P (rho_sub rho s) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X P s ndPL ndP rho tp w Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw). }
  apply (TR_phi_in (fun r => Psi rho0 r) ndP P (rho_sub rho s) tp); [exact (HPSI rho HPhi)|].
  apply (POST P ndP (fun r => Psi rho0 r) Psi); [exact HinP | intros r Hr; exact Hr].
Qed.
Lemma X_RL1 : ltac2:(tb__ "0|1|
S1aS9S4eQ40A1A1M0S16G0VTR;S52S48VJAFv;U1S6bA2S8cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_RL P_retL1 P_ret1 (s_retL 1) Psi_ret1 rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 1 |].
  intros r [(T & H1 & H2 & H3 & H4) HD]. unfold Psi_ret1, Psi_bli, Psi_def.
  assert (E141 : uval (rho_sub r (s_retL 1)) (SVar 141) = uval r pC) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (E140 : uval (rho_sub r (s_retL 1)) (SVar 140) = uval r pD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (E142 : uval (rho_sub r (s_retL 1)) (SVar 142) = uval r pK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EM : rm (rho_sub r (s_retL 1)) = rm r) by reflexivity.
  rewrite E141, E140, E142, EM. split; [exists T; split; [exact H1 | split; [exact H2 | exact H3]] | exact HD].
Qed.
Lemma X_RL0 : ltac2:(tb__ "0|1|
S1aS9S4eQ40A1A1M0S16G0VTR;S52S48VJAFv;U1S6bA2S8bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_RL P_retL0 P_ret0 (s_retL 0) Psi_def rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 0 |].
  intros r [_ HD]. unfold Psi_def.
  assert (E140 : uval (rho_sub r (s_retL 0)) (SVar 140) = uval r pD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (E142 : uval (rho_sub r (s_retL 0)) (SVar 142) = uval r pK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EM : rm (rho_sub r (s_retL 0)) = rm r) by reflexivity.
  rewrite E140, E142, EM. exact HD.
Qed.

Lemma X_E_ms : ltac2:(tb__ "0|3|
S1aS9S4eQ40A1A1M0S16G0S40Se1SaS8S8S3bS96A2M1SdA2S8S16S18A2SaG1SdSaS3bS96S68S5eA4U1M2A4SaS16S18Z32S67S64Z3A2A4A4R4A2R2A2VTR;S52S48VJAFv;G2S5eA2S68R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi. apply TR_facts. intros HF. loopz HF.
  rewrite (meas_VL E_ms0 ndB 1%nat 50 pJ 3 rho) in Hb by lia.
  pose proof (baseBz_of rho _ HF baseBF_E_ms0) as [Bsp Bv Bck EK Bdk Btx Btop].
  factz HF (SPNot (SPBranch BC_EQ pD (SLit 0))) HD0. rewrite uval_lit in HD0 by lia.
  apply (purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ms0 s_m R_m rho tp ndB (bdL pI pC pK) (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [nd_bd ndB]. apply payA_same. reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact (site_ms rho).
  - intros Ai tr ms md Hsm HM HX. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms0 memset_pc s_m R_m rho tp tr ms md Hsm HM HX ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
  - intros L rho' tp' [<-|[]] Hag HKR. cbn [nd_tv nd_fr nd_am ndB ND]. rewrite T_ms0_eq.
    assert (EJ : uval rho' pJ = uval rho pJ) by (unfold uval, pJ; cbn [eval]; rewrite <- (proj1 Hag 284%positive eq_refl); reflexivity).
    assert (EL : uval rho' vLEN = uval rho vLEN) by (unfold uval, vLEN; cbn [eval]; rewrite <- (proj1 Hag 13%positive eq_refl); reflexivity).
    assert (HP' : PhiL rho').
    { apply (PhiL_transport rho rho'); [| lia | | exact HPhi].
      - intros v Hv. apply (proj1 Hag). cbn in Hv. destruct Hv as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
      - intros z Hz. apply (HKR (pD, kb16 pK) z); [left; reflexivity | unfold tnz; cbn [fst]; unfold uval in HD0; exact HD0 |].
        unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho pD)) with (uval rho pD). change (bv_unsigned (eval rho (kb16 pK))) with (uval rho (kb16 pK)). rewrite EK. exact Hz. }
    eapply TR_pre; [|apply (REENTER K_ms ndB 1%nat (50, VL pJ 2) rho'); [innth 4 | exact HP' | rewrite (meas_VL K_ms ndB 1%nat 50 pJ 2 rho') by lia; lia]].
    intros w Hw. exact Hw.
Qed.

Lemma X_X_st : ltac2:(tb__ "0|3|
S1aS9S4eQ40A1A1M0S16G0S40Se1SaS8S8S3bS96A2M1SdA2S8S16S18A2SaG1SdSaS3bS96S7cS5eA4U1M2A4SaS16S18Z32S67S64Z1A2A4A4R4A2R2A2VTR;S52S48VJAFv;G2S5eA2S7cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi. apply TR_facts. intros HF. loopz HF.
  rewrite (meas_VL X_st ndB 1%nat 50 pJ 1 rho) in Hb by lia.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof chk_st as (Cent & Cid & Cnf & Cnb & Ctv & Cbud & CbaseS & CslotS & Cbase & Ccells).

  factz HF (SPUle pI pJ) FIJ. factz HF (SPUle pJ vLEN) FJL. factz HF (SPUle pNX pI) FNI. factz HF (SPUle pC pI) FCI.
  pose proof (uval_range rho pI) as RI. pose proof (uval_range rho pC) as RC. pose proof (uval_range rho pD) as RD. pose proof (uval_range rho pNX) as RN.
  assert (EL0 : uval rho vLEN = L0) by (unfold L0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (ESUB : uval rho (SAlu ALU_SUB pJ pI) = uval rho pJ - uval rho pI) by (unfold uval in *; rewrite U_sub; unfold M64v; apply Z.mod_small; lia).
  assert (EC1 : uval rho (SAlu ALU_ADD pC (SLit 1)) = uval rho pC + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (EJ1 : uval rho (SAlu ALU_ADD pJ (SLit 1)) = uval rho pJ + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  apply (TR_pre (fun w => exists r2, (PhiL (rho_sub r2 s_st) /\ (forall e, eval r2 e = eval rho e)) /\ SPA segs (JAv ndS) K_st (rho_sub r2 s_st) tp w)).
  { intros w Hw0. pose proof (SPA_axforms segs _ [AXSelect sel_st] rho X_st X_stS tp w X_stS_eq Hw0) as Hw. clear Hw0.
    pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HFS.
    destruct w as [tr [ms md]].
    change (JAv ndB) with (JAv (NDA (tvB pD pK) [] (bdL pI pC pK) ANone)) in Hw.
    destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue (tvB pD pK) [] (bdL pI pC pK) ANone 0 pD (kb16 pK)
                X_stS (ss_objs (ax_S X_stA)) o_slotX (SLit 16) rho tp tr ms md (proj1 X_stA_eq) eq_refl ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as (Hw2 & OUT & DEF & CELLS).
    { intros r HFr. rewrite Cbase. destruct (slot_rng r _ HFr CbaseS CslotS) as (A1 & A2 & A3 & A4 & A5).
      pose proof (baseBz_of r _ HFr CbaseS) as [_ _ _ EKr _ _ _]. pose proof (uval_range r pC). rewrite A1, A4, EKr, uval_lit by lia. lia. }
    { exact Hw. }
    rewrite (proj2 X_stA_eq) in Hw2. rewrite Cbase in OUT, DEF, CELLS. rewrite Ccells in CELLS.
    destruct (slot_rng rho _ HFS CbaseS CslotS) as (A1 & A2 & A3 & A4 & A5). pose proof (baseBz_of rho _ HFS CbaseS) as [Bsp Bv Bck EK Bdk Btx Btop].
    rewrite A1, A4 in OUT, DEF, CELLS. rewrite (uval_lit rho 16) in OUT, DEF, CELLS by lia.
    set (r2 := rho_absorb rho [o_slotX] (vms md tp ms)) in *. exists r2.
    assert (EV : forall e, eval r2 e = eval rho e) by (intros e; unfold r2; apply eval_absorb).
    assert (US : forall e, uval (rho_sub r2 s_st) e = uval rho (sv_subst s_st e)) by (intros e; unfold uval; rewrite <- eval_subst, EV; reflexivity).
    split; [split; [|exact EV]|].
    -
      destruct HPhi as [(T & HT1 & HT2 & HT3 & HT4) HDEF].
      assert (E1 : uval (rho_sub r2 s_st) pC = uval rho pC + 1) by (rewrite US; exact EC1).
      assert (E2 : uval (rho_sub r2 s_st) pD = uval rho pD) by (rewrite US; reflexivity).
      assert (E3 : uval (rho_sub r2 s_st) pK = uval rho pK) by (rewrite US; reflexivity).
      assert (E4 : uval (rho_sub r2 s_st) pNX = uval rho pJ + 1) by (rewrite US; exact EJ1).
      assert (EM : rm (rho_sub r2 s_st) = rm r2) by reflexivity.
      unfold PhiL, tableL. rewrite E1, E2, E3, E4, EM.
      split; [exists (T ++ [(uval rho pI, uval rho pJ - uval rho pI)])|].
      + rewrite length_app. cbn [length]. split; [lia|]. split; [|split].
        * apply decodes_app.
          -- apply (decodes_ext (rm rho)); [|exact HT2]. intros z Hz. apply OUT. rewrite U_Z_to_bv by lia. lia.
          -- split; cbn [fst snd].
             ++ replace (uval rho pD + 16 * Z.of_nat (length T)) with (uval rho pD + 16 * uval rho pC + 0) by lia.
                rewrite (CELLS 0 pI); [reflexivity | right; left; reflexivity | lia | lia].
             ++ replace (uval rho pD + 16 * Z.of_nat (length T) + 8) with (uval rho pD + 16 * uval rho pC + 8) by lia.
                rewrite (CELLS 8 (SAlu ALU_SUB pJ pI)); [rewrite ESUB; reflexivity | left; reflexivity | lia | lia].
        * apply lines_ok_app; cbn [fst snd]; [exact HT3 | lia | lia | lia |]. intros q Hq _. pose proof (HT4 q Hq). lia.
        * intros q Hq. replace (Nat.pred (length T + 1)) with (length T) in Hq by lia. rewrite nth_error_last in Hq. injection Hq as <-. cbn [fst snd]. lia.
      + intros z Hz. destruct (Z_lt_dec z (uval rho pD + 16 * uval rho pC)) as [L1|L1]; [|destruct (Z_lt_dec z (uval rho pD + 16 * uval rho pC + 16)) as [L2|L2]].
        * rewrite OUT by (rewrite U_Z_to_bv by lia; lia). exact (HDEF z Hz).
        * apply DEF. lia.
        * rewrite OUT by (rewrite U_Z_to_bv by lia; lia). exact (HDEF z Hz).
    - exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_stA K_st s_st ndB ndS r2 tp _ Cent Cid Cnf Cnb Ctv eq_refl Cbud eq_refl Hw2). }
  apply TR_exw; intros r2. eapply TR_pureP; [intros w [Hx _]; exact Hx|]. intros [HP2 EV].
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  assert (EJ : uval (rho_sub r2 s_st) pJ = uval rho pJ) by (unfold uval; rewrite <- eval_subst, EV; reflexivity).
  assert (EL : uval (rho_sub r2 s_st) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst, EV; reflexivity).
  apply (REENTER K_st ndS 1%nat (50, VL pJ 0)); [innth 5 | exact HP2 | rewrite (meas_VL K_st ndS 1%nat 50 pJ 0 (rho_sub r2 s_st)) by lia; lia].
Qed.

Lemma X_E_vr : ltac2:(tb__ "0|3|
S1aS9S4eQ40A1A1M0S16G0S40Se1SaS8S8S3bS96A2M1SdA2S8S16S18A2SaG1SdSaS3bS96S73S5eA4U1M2A4SaS16S18Z32S67S64Z5A2A4A4R4A2R2A2VTR;S52S48VJAFv;G2S5eA2S73R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  eapply TR_pre with (P := SPA segs (JAv ndB) E_vrx rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vr E_vrx tp w E_vrx_eq Hw). }
  apply TR_facts. intros HF. loopz HF.
  rewrite (meas_VL E_vr ndB 1%nat 50 pJ 5 rho) in Hb by lia.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof (baseBz_of rho _ HF baseBF_E_vrx) as BZ. pose proof BZ as [Bsp Bv Bck EK Bdk Btx Btop].
  pose proof (uval_range rho pD) as RD. pose proof (uval_range rho pC) as RC.

  apply (TR_pureP _ (forall a, uval rho0 vBUF <= a < uval rho0 vBUF + uval rho0 vLEN -> ~ (uval rho pD <= a < uval rho pD + 16 * uval rho pK))).
  { intros w Hw. apply (JA_blk_txtK ndB E_vrx rho tp w pD pK Hw); [left; reflexivity | lia]. }
  intros HTX.
  assert (NR : forall z, uval rho pD <= z < uval rho pD + 16 * uval rho pK -> ~ in_ranges rho R_v (Z_to_bv 64 z)).
  { intros z Hz. apply (not_in_R_blk rho (uval rho pD) (uval rho pK) z BZ Hav); [lia | lia | exact HTX | exact Hz]. }
  pose proof chk_vr as (Cpd & HimpD & HimpK & HivD & HivK & CgD0 & CgD30 & CgKB & Cg30sp & CgC1).
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX P0_vrr PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_vr nd0 PD_vrr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vrx s_v R_v Xk_v rho tp [] (tvB pD pK) [] (bdL pI pC pK) [PROGL pI] ANone (FAM b tp0)).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact Cpd.
  - intros Ai ms HF' HP0' Hav' HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_vr rho Ai ms HF' HP0' Hav' HBf HFF HN HZ HM HT HPhi).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK HPSI. cbn [PD_vrr RVP.PDk_vrr In] in Hd.
    assert (EJ : uval rho' pJ = uval rho pJ) by (unfold uval, pJ; cbn [eval]; rewrite <- (proj1 Hag 284%positive eq_refl); reflexivity).
    assert (EL : uval rho' vLEN = uval rho vLEN) by (unfold uval, vLEN; cbn [eval]; rewrite <- (proj1 Hag 13%positive eq_refl); reflexivity).
    assert (HV : forall v, In v [281; 280; 290; 282]%positive -> rw rho v = rw rho' v).
    { intros v Hv. apply (proj1 Hag). cbn in Hv. destruct Hv as [<-|[<-|[<-|[<-|[]]]]]; reflexivity. }
    assert (ED' : uval rho' pD = uval rho pD) by (unfold uval, pD; cbn [eval]; rewrite <- (proj1 Hag 280%positive eq_refl); reflexivity).
    assert (EC' : uval rho' pC = uval rho pC) by (unfold uval, pC; cbn [eval]; rewrite <- (proj1 Hag 281%positive eq_refl); reflexivity).
    assert (EK' : uval rho' pK = uval rho pK) by (unfold uval, pK; cbn [eval]; rewrite <- (proj1 Hag 282%positive eq_refl); reflexivity).
    assert (ET' : rw rho' V_TOP = rw rho V_TOP) by (symmetry; exact (proj1 Hag 30%positive eq_refl)).
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <- <-; cbn [fst snd nd_tv nd_bd nd_am nd0 ND am_subst app];
      destruct HPSI as (r0c & rhoL & HPsi & Hd1 & Hd2 & Hd3); cbn [fst snd] in HPsi, Hd1, Hd2, Hd3;
      assert (ER0D : uval r0c vDt = uval rho pD) by (unfold uval; rewrite Hd1; reflexivity);
      assert (ER0K : uval r0c vK = uval rho pK) by (unfold uval; rewrite Hd1; reflexivity);
      assert (ER0C : uval r0c vC = uval rho pC) by (unfold uval; rewrite Hd1; reflexivity).
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. cbn [app].
      assert (HP' : PhiL rho').
      { apply (PhiL_transport rho rho' HV ltac:(lia)); [|exact HPhi].
        intros z Hz. destruct (Hd2 _ (NR z Hz)) as [E1 E2]. rewrite E2, (HPsi z) by (rewrite ER0D, ER0K; lia). exact E1. }
      pose proof chk_keep as (Cent & Cid & Cnf & Cnb & Ctv & Cbud & Cidon & Cs284 & Cs13 & Cwf & Cbase & Cbelow).
      eapply TR_pre with (P := SPA segs (JAv (ND (tvB pD pK) [] (bdK pK))) T_keep rho' tp').
      { intros w Hw. exact (SPA_axforms segs _ xf_vback rho' T_keep0 T_keep tp' w T_keep_eq Hw). }
      apply TR_facts. intros HF2.
      factz HF2 (SPUle (SAlu ALU_ADD pC (SLit 1)) pK) F1. rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
      eapply TR_pre; [|apply (REENTER K_ok ndB 1%nat (50, VL pJ 4) (rho_sub rho' s_keep)); [innth 2 | exact (phi_sub _ PhiL PhiL_reads s_keep rho' Cidon HP') |]].
      * intros w Hw.
        refine (glue_carve T_keep T_keepF T_keepC (ok_facts pD pC pK) s_keep pD pK rho' tp' w T_keepF_eq Cbelow _ T_keepC_eq Cbase Cwf Csite_keep _ _ _ _ _ _ _
                  Cent Cid Cnf Cnb Ctv Cbud _ Hw); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
                                                  | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
        -- intros tr md HJ HF3.

           assert (TNZ : tnz rho' (pD, kb16 pK)).
           { unfold tnz. cbn [fst]. apply (d_nz_of_J _ _ _ _ _ pD pK HJ); [left; reflexivity | lia | lia]. }
           pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA _ _ _ _ _ (pD, kb16 pK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
           unfold ok_facts. constructor; [exact (holds_mem _ _ (SPUle (SAlu ALU_ADD pC (SLit 1)) pK) HF3 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc))|].
           constructor; [apply (proj1 (Forall_forall _ _) TF); unfold tv_factsA; cbn [fst snd]; do 5 right; left; reflexivity|].
           constructor; [apply (proj2 (holds_nbeq _ _ _)); rewrite U_lit; change (0 mod M64v) with 0; unfold tnz in TNZ; cbn [fst] in TNZ; exact TNZ|].
           apply (slot_holds rho' _ pK HF3); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
        -- intros z Hz. apply (proj2 HP'). lia.
      * assert (EJ' : uval (rho_sub rho' s_keep) pJ = uval rho pJ) by (unfold uval; rewrite <- eval_subst; exact EJ).
        assert (EL' : uval (rho_sub rho' s_keep) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; exact EL).
        rewrite (meas_VL K_ok ndB 1%nat 50 pJ 4 (rho_sub rho' s_keep)) by lia. lia.
    +
      rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ []) with (@nil bitem). cbn [app].
      assert (HP' : PhiL rho').
      { apply (PhiL_transport rho rho' HV ltac:(lia)); [|exact HPhi].
        intros z Hz. destruct (Hd2 _ (NR z Hz)) as [E1 E2]. rewrite E2, (HPsi z) by (rewrite ER0D, ER0K; lia). exact E1. }
      eapply TR_pre; [|apply (REENTER T_fail ndF 1%nat (45, z0) rho'); [innth 3 | exact HP' | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_vback rho' T_fail0 T_fail tp' w T_fail_eq Hw).
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. cbn [app].
      eapply TR_pre with (P := SPA segs (JAv (ND (tvB vDg vKg) [] (bdK vKg))) T_grown rho' tp').
      { intros w Hw. exact (SPA_axforms segs _ xf_vback rho' T_grown0 T_grown tp' w T_grown_eq Hw). }
      apply TR_facts. intros HF2.
      pose proof (baseBz_of rho' _ HF2 ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ _ _ _ _ [BT1g BT2g]].
      factz HF2 (SPUle vKg (SLit B32)) FKB. factz HF2 (SPUle (SAlu ALU_ADD vDg (kb16 vKg)) (SVar 30)) FD30. factz HF2 (SPUle (SAlu ALU_ADD pC (SLit 1)) vKg) FC1.
      factz HF2 (SPUle vDg (SVar 30)) FDg30.
      unfold B32 in FKB. rewrite uval_lit in FKB by lia. change (uval rho' (SVar 30)) with (bv_unsigned (rw rho' V_TOP)) in FD30, FDg30.
      pose proof (uval_range rho' vDg) as RDg. pose proof (uval_range rho' vKg) as RKg.
      assert (EKg : uval rho' (kb16 vKg) = 16 * uval rho' vKg) by (unfold kb16; apply uval_mul_lit; lia).
      rewrite uval_add_small in FD30 by (rewrite EKg; lia). rewrite EKg, ET' in FD30.
      rewrite uval_add_small in FC1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in FC1 by lia.

      apply (TR_pureP _ (forall a, uval rho0 vBUF <= a < uval rho0 vBUF + uval rho0 vLEN -> ~ (uval rho' vDg <= a < uval rho' vDg + 16 * uval rho' vKg))).
      { intros w Hw. apply (JA_blk_txtK (ND (tvB vDg vKg) [] (bdK vKg)) T_grown rho' tp' w vDg vKg Hw); [left; reflexivity | unfold B32; lia]. }
      intros HTXg.
      assert (NRg : forall z, uval rho' vDg <= z < uval rho' vDg + 16 * uval rho' vKg -> ~ in_ranges rho R_v (Z_to_bv 64 z)).
      { intros z Hz. apply (not_in_R_blk rho (uval rho' vDg) (uval rho' vKg) z BZ Hav); [lia | exact FD30 | exact HTXg | exact Hz]. }
      assert (E_D : uval rho' vDg = uval rhoL vDn) by (unfold uval; rewrite <- (Hd3 vDn HivD), HimpD; reflexivity).
      assert (E_K : uval rho' vKg = uval rhoL vKn) by (unfold uval; rewrite <- (Hd3 vKn HivK), HimpK; reflexivity).
      destruct HPsi as [HC HG]. rewrite ER0C, ER0D in HC. unfold Psi_gdef in HG. rewrite <- E_D, <- E_K in HG.
      pose proof chk_grown as (Cent & Cid & Cnf & Cnb & Ctv & Cbud & Cs281 & Cs280 & Cs290 & Cs282 & Cs284 & Cs13 & Cwf & Cbase & Cbelow).
      assert (HPg : PhiL (rho_sub rho' s_grown)).
      { assert (US : forall e, uval (rho_sub rho' s_grown) e = uval rho' (sv_subst s_grown e)) by (intros e; unfold uval; rewrite <- eval_subst; reflexivity).
        assert (E1 : uval (rho_sub rho' s_grown) pC = uval rho pC) by (rewrite US; exact EC').
        assert (E2 : uval (rho_sub rho' s_grown) pD = uval rho' vDg) by (rewrite US; reflexivity).
        assert (E3 : uval (rho_sub rho' s_grown) pK = uval rho' vKg) by (rewrite US; reflexivity).
        assert (E4 : uval (rho_sub rho' s_grown) pNX = uval rho pNX) by (rewrite US; change (uval rho' (sv_subst s_grown pNX)) with (uval rho' pNX); unfold uval, pNX; cbn [eval]; rewrite <- (proj1 Hag 290%positive eq_refl); reflexivity).
        assert (EM : rm (rho_sub rho' s_grown) = rm rho') by reflexivity.
        destruct HPhi as [(T & HT1 & HT2 & HT3 & HT4) HDEF].
        unfold PhiL, tableL. rewrite E1, E2, E3, E4, EM. split; [exists T|].
        - split; [exact HT1|]. split; [|split; [exact HT3 | exact HT4]].
          apply (decodes_shift (rm rho) (rm rho') T (uval rho pD) (uval rho' vDg)); [|exact HT2]. intros j Hj.
          destruct (Hd2 _ (NRg (uval rho' vDg + j) ltac:(lia))) as [_ E2']. rewrite E2'.
          destruct (Hd2 _ (NR (uval rho pD + j) ltac:(lia))) as [E1' _]. rewrite <- E1'.
          rewrite E_D. apply (proj1 (HC j ltac:(lia))).
        - intros z Hz. destruct (Hd2 _ (NRg z Hz)) as [_ E2']. rewrite E2'. exact (HG z Hz). }
      eapply TR_pre; [|apply (REENTER K_ok ndB 1%nat (50, VL pJ 4) (rho_sub rho' s_grown)); [innth 2 | exact HPg |]].
      * intros w Hw.
        refine (glue_carve T_grown T_grownF T_grownC (slot_facts pC vKg) s_grown vDg vKg rho' tp' w T_grownF_eq Cbelow _ T_grownC_eq Cbase Cwf Csite_grown _ _ _ _ _ _ _
                  Cent Cid Cnf Cnb Ctv Cbud _ Hw); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
                                                  | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
        -- intros tr md _ HF3. apply (slot_holds rho' _ vKg HF3); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
        -- intros z Hz. destruct (Hd2 _ (NRg z ltac:(lia))) as [_ E2']. rewrite E2'. apply HG. lia.
      * assert (EJ' : uval (rho_sub rho' s_grown) pJ = uval rho pJ) by (unfold uval; rewrite <- eval_subst; exact EJ).
        assert (EL' : uval (rho_sub rho' s_grown) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; exact EL).
        rewrite (meas_VL K_ok ndB 1%nat 50 pJ 4 (rho_sub rho' s_grown)) by lia. lia.
Qed.

Ltac xl0 X := apply (X_L0 X);
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | meas].
Ltac xr0 X := apply (X_R0 X);
  [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].

Lemma exits_okT : ltac2:(tb__ "0|4|
S3bS96SdS8S16S18A2M0S1aS9S4eQ40A1A1M1G1S4aS8S8S8S3bS96A2M2SdA2M3G0A2SaG3G0SaG2SdSaS3bS96R7R6A4R5A4R4A4S7fA3VTR;S52S48VJAFv;R6R7A2R8R4R3A5VFAM;Se1SaG3G0SaG2SdSaS3bS96R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FkX;FndX;FX;").
Proof.
  intros X ndX kX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <- <-.
  - xl0 (XL0n 0).
  - xl0 (XL0n 1).
  - xl0 (XL0n 2).
  - xl0 (XL0n 3).
  - xl0 (XL0n 4).
  - xr0 XR0a.
  - xr0 XR0b.
  - apply X_E_vr. lia.
  - apply X_E_ms. lia.
  - apply X_X_st. lia.
  - apply X_RL1.
  - apply X_RL0.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
Sa0S48VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S107S48S103VAInv;VCST;VXGL;A5").

Theorem build_line_index_rom_sum : ltac2:(tb__ "0|0|
S9S4eQ40A1A1Sb1S48Vok;S52S48S9aVAInv;VCST;VXGL;VKc;Sf0VCST;VFB;VFF;A3VFB;VFF;VBX;S97S6cAaS76Vrho0;R1A5Sb3S48S51Vrho0;R1Sd4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_blr cutpcs_blr 100
                (map efdrop cutsE) (map efdrop exitsE) ok (Q tp0) Hok (ejcertAF_jcertAF segs NF Phis _ _ _ _ _ ejcertAF_ok))
         with (ndT := nd_pre) (kT := 0%nat); [|left; reflexivity].
       intros X ndX kX rho tp Hin. apply in_map_iff in Hin as ([[[X' nd'] k'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map (nodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) (map efdrop cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_rom_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP _. apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis ok (map efdrop cutsE) T nd k); [|exact HP].
         apply in_map_iff. exists (T, nd, k, rv'). auto.
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (exit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 Phi Psi nd Posts_blr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. assert (Hw1 : SPA segs (JAv nd_pre) Pre_blr rho0 tp0 w) by (apply JA_pre_intro; exact Hw).
  apply SPA_JAF_intro; [exact Hw1|]. destruct (JA_P0 _ _ _ _ w Hw1) as [HP00 _]. intros z Hz. exact (proj2 HP00 z Hz).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S108S48S103VAInv;VCST;VXGL;A5").

Theorem build_line_index_rom_sum_ex : ltac2:(tb__ "0|0|
S9S4eQ40A1A1Sb0S48S52S48S9aVAInv;VCST;VXGL;VKc;Sf0VCST;VFB;VFF;A3VFB;VFF;VBX;S97S6cAaS76Vrho0;R1A5Sb3S48S51Vrho0;R1Sd4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_blr cutpcs_blr 100 cutsE exitsE (Q tp0) ejcertAF_ok)
         with (ndT := nd_pre) (kT := 0%nat) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX kX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_rom_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP Hm. apply (ereenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis cutsE T nd k rv'); [exact HinT | exact HP | exact Hm].
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (eexit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 Phi Psi nd Posts_blr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. assert (Hw1 : SPA segs (JAv nd_pre) Pre_blr rho0 tp0 w) by (apply JA_pre_intro; exact Hw).
  apply SPA_JAF_intro; [exact Hw1|]. destruct (JA_P0 _ _ _ _ w Hw1) as [HP00 _]. intros z Hz. exact (proj2 HP00 z Hz).
Qed.
End Existence.

End Sum.

Print Assumptions build_line_index_rom_sum.
Print Assumptions build_line_index_rom_sum_ex.
End Lib_build_line_index_rom_pf.

(* [comment removed for export] *)
Module Lib_handle_f_s7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXUnbase"; "apply_axforms"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "DUnknown"; "sprop"; "cell"; "mkObj"; "sobj"; "SVar"; "SLit"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDts"; "XRT"; "pDrp"; "pKrp"; "pKts"; "datasR"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "FCUT2"; "cT"; "trK"; "tr_facts"; "triF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "qDrp'"; "qDts'"; "qKrp'"; "qKts'"; "pNT"; "XT"; "E_wdg"; "JC"; "J_facts"; "O_nxt0"; "O_prv0"; "O_rfx0"; "XT6"; "arr_mergeA"; "pg_back1"; "regsJ"; "sel_pg"; "xf_pgb1"; "xf_pgb2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "reshapeA"; "optAp"; "shB"; "vec_facts0"; "V752e"; "V784"; "V816"; "am2"; "pDco"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "shobj"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "FR"; "hf_J"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "coP"; "fvP"; "miP"; "mmP"; "pX"; "sgP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6.AR"; "o16A"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "optS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA"; "arr_merge_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition O_nxt0 : sobj := ltac2:(tb__ "0|0|
SfS14S4fS50S2SeA1ScA5").
Definition O_prv0 : sobj := ltac2:(tb__ "0|0|
SfS14S51S52S2SeA1ScA5").
Definition O_rfx0 : sobj := ltac2:(tb__ "0|0|
SfS14S53S54S2SeA1ScA5").
Definition sel_pg : list nat := ltac2:(tb__ "0|2|
S4S1S0S1U1S0S1U0S0S1UdS0S1U2S0S1UeS0S1U3S0S1U4S0S1UfS0S1U10S0S1UbS0S1UcS0S1U11M0S2S1A1M1A3A3A3A3A3A3A3A3A3A3A3A3S4S1S41U12G0A2S0S1U23S0S1U24S0S1U25S0S1U26S0S1U27S0S1U28S0S1U29S0S1U2aS0S1U2bS0S1U2cS0S1U5S0S1U2dS0S1U6S0S1U2eS0S1U7S0S1U8S0S1U2fS0S1U9S0S1U30S0S1UaS0S1U31G1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_pgb1 : list axform := ltac2:(tb__ "0|3|
S0S6S8U1M0Z140A2S0S6S8U2N30A2S0S6S8U3Na0M1A2S0S6S8U4G1A2S0S6SaS33A1S0S6S7U0A1S0S6S7G0A1M2S0S6G2S0S6G2S0S6G2S0S6G2S0S6S7U21A1S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xf_pgb2 : list axform := ltac2:(tb__ "0|1|
S0S6S7U23A1M0S0S6G0S0S6G0S0S6G0S0S6G0S0S6G0S2S6A1A3A3A3A3A3A3").
Definition arr_mergeA (A : axst) (i : nat) : axst := ltac2:(tb__ "0|0|
S40VA;S55S59S3fVA;A1Vi;A2A1A2").
Definition XT6 : list (sv * sv) := ltac2:(tb__ "0|2|
S0S5SbSbA2M0S44Pa0M1S3S1aS1aZ30Z48A4A2S0G0S44G1S3S1aS1aZa0Z18A4A2S15S16S17S14S18A4A3A3").
Definition pg_back0 (T : axst) : axst := ltac2:(tb__ "0|0|
S36S36S36VT;U8S2cA3U9S2dA3UaS2eA3").
Definition pg_back1 (T : axst) : axst := ltac2:(tb__ "0|0|
S30S37S9VT;S34A2A1U22A2").
Definition pg_back (T : axst) : axst := ltac2:(tb__ "0|0|
S58S37S9S31VT;A1S35A2A1S2fA2").
Definition T_pgo1 : axst := Eval vm_compute in pg_back0 T_pgo0.
Definition T_pgo : axst := Eval vm_compute in pg_back T_pgo1.
Definition T_pgi1 : axst := Eval vm_compute in ax_setS (pg_back0 T_pgi0) (optS (zcells_at (ax_S (pg_back0 T_pgi0)) 3 [(8, 4)])).
Definition T_pgi : axst := Eval vm_compute in pg_back T_pgi1.
Goal zcells_at (ax_S (pg_back0 T_pgi0)) 3 [(8, 4)] = Some (ax_S T_pgi1)
  /\ map (fun T => match apply_axforms T xf_pgb1 with Some T1 => match arr_merge_at (ax_S T1) 34 with Some _ => true | None => false end | None => false end) [T_pgo1; T_pgi1] = [true; true]
  /\ shape T_pgo = shape JF_ts /\ shape T_pgi = shape JF_ts.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition XT : list (sv * sv) := ltac2:(tb__ "0|0|
S15S16S17S14S18A4").
Definition reopen2 (A : axst) : axst := ltac2:(tb__ "0|0|
S42S42VA;S28S1bZ6ZfA5S28S1bZ14Z17A5").
Definition T_pgoR : axst := Eval vm_compute in reopen2 T_pgo.
Definition T_pgiR : axst := Eval vm_compute in reopen2 T_pgi.
Goal lvs T_pgoR = [(hf_J, RsCut); (da_entry, RsCut)] /\ lvs T_pgiR = [(hf_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_wdg0 : axst := Eval vm_compute in leaf_at T_pgoR da_entry 0.
Definition E_wdg : axst := Eval vm_compute in optAp (apply_axforms E_wdg0 [AXSplit 0 (SLit (-96))]).
Definition s_wdg : wsub := ltac2:(tb__ "0|0|
S57PaS3fS29A1S3fS46A1A3").
Definition R_wdg : list sobj := Eval vm_compute in optR (entails_frA E_wdg Pre_da s_wdg).
Goal entails_frA E_wdg Pre_da s_wdg = Some R_wdg /\ call_checkA E_wdg Pre_da s_wdg R_wdg (map la_state Posts_da) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_wdg0 : axst := Eval vm_compute in T_pure Pre_da E_wdg s_wdg R_wdg P_da.

Definition sel_wdg : list nat := ltac2:(tb__ "0|0|
S4S1S0S1U3S0S1U0S0S1U4S0S1U5S0S1U1S0S1U2S2S1A1A3A3A3A3A3A3S41U6U21A2A3").
Definition T_wdg : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_wdg0 [AXSelect sel_wdg; AXMerge 0])) XT.
Goal shape T_wdg = shape T_pgoR /\ lvs T_wdg = [(hf_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pNT : sv := SVar 349.
Definition qDrp' : sv := SVar 352. Definition qKrp' : sv := SVar 353. Definition qDts' : sv := SVar 354. Definition qKts' : sv := SVar 355.

Definition regsJ : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1SbA2M0S3S1SbU2S56S47A1M1A4S0G0S3S1SbU8S11PaA1A4S0G0S3S1SbU9G1A4S0G0S3S1SbU12S11P164A1A4S0G0S3S1SbU13S38Z0A1A4S0G0S3S1SbU16S3eA4S0G0S3S1SbU18S1cA4S0G0S3S1SbU19S27A4S0G0S3S1SbU1aS38Z43A1A4S0G0S3S1SbU1bS45A4S2G0A1A3A3A3A3A3A3A3A3A3A3").
Definition J_facts : list sprop := ltac2:(tb__ "0|0|
S4SdS0SdS13S27S3dA2S2SdA1A3S4SdS21S1cS1dP157A3S4SdS39S23S25Z4P160A4S4SdS39S24S26Z1P162A4S22A3A3A3A3").
Definition JC (tail : list sobj) : axst := ltac2:(tb__ "0|0|
S1eS48S32S4dS49S3aS23S25A2S3bS1cS12Z0A1S1dA3S4bS4aS4cS4eS3cS24S26A2S1fS2SeA1S19ScS23S25S1cS1dS20S27A1S24S26A8Vtail;S2bS15S23S25S24S26A4A11").
Definition J : axst := JC [].
Definition XJ : axst := ltac2:(tb__ "0|1|
S2aS0S10S43S1bZ6ZfS2SeA1M0ScA5S0S10S43S1bZ14Z17G0ScA5S2S10A1A3A3A1").
Goal map (fun L => leaf_matches1A NPH L J) (leavesA_at FUEL_hf cutpcs_hf K2 hf_J) = [true]
  /\ map (fun L => leaf_matches1A NPH L XJ) (leavesA_at FUEL_hf cutpcs_hf T_pgoR hf_J ++ leavesA_at FUEL_hf cutpcs_hf T_wdg hf_J ++ leavesA_at FUEL_hf cutpcs_hf T_pgiR hf_J) = [true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs J = [(hf_EPI, RsCut); (hf_L14, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_f_s7.

(* [comment removed for export] *)
Module Lib_load_obj_bud.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "app"; "nil"; "prod"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "bitem"; "ASv"; "BI"; "AMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "VPv"; "AK1"; "Cb1"; "LAK"; "LAX"; "LAXK"; "bd_rest"; "ndL"; "Cb3"; "DUP"; "FIN"; "Mline"; "VP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "t_k"; "t_c"; "pLNL"; "pPOS"; "v_av"; "v_avn"; "v_avt"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_sg"; "v_sh"; "gCO"; "gFV"; "gLC"; "gLI"; "gMI"; "gMM"; "gPI"; "gRP"; "gSG"; "gTR"; "gTS"; "pH"; "pI"; "pNX"; "v_acol"; "v_avtw"; "v_avw"; "v_co"; "v_rp"; "v_tr"; "v_ts"; "xLC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "SMd"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SLL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "A1"; "LA"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "PHIe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "NDA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Definition Cb1 (x : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S40S42S3eZ1A1Vx;A3S3eZ0A1A3").
Definition Cb3 (x : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S40S42S3eZ3A1Vx;A3S3eZ2A1A3").
Definition VPv (e : Z) (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8S4dVe;Vc;Vk;A3S0S8S4eVk;A1S3S8A1A3A3").

Definition VP (v : vecs) : list bitem := ltac2:(tb__ "0|9|
S2S8ScZ4M0S40S42S1aS1dVv;A1M1A1M2S3eZ3A1A3S19G1A1A3S2S8ScG0SeG2A1S19S38Vv;A1A1A3S2S8ScG0S1aS1eVv;A1M3A1S19G3A1A3S2S8ScG0S3fS43S1aS1fVv;A1M4A1M5S3eZ1M6A1A3S19G4A1A3S2S8ScG0SeG5A1S19S37Vv;A1A1A3S2S8ScG0S14G2A1S19S36Vv;A1A1A3S2S8ScZ80S1aS27Vv;A1M7A1S19G7A1A3S2S8ScZcM8S2cS19S23Vv;A1A1A3S2S8ScG0S29S19S20Vv;A1A1A3S2S8ScG0S2dS19S24Vv;A1A1A3S2S8ScG0S30S19S26Vv;A1A1A3S2S8ScG8S2bS19S22Vv;A1A1A3S2S8ScG0S2aS19S21Vv;A1A1A3S2S8ScG8S2eS19S25Vv;A1A1A3S2S8ScG8S28S19S39Vv;A1A1A3S2S8ScG0S2fS19S3aVv;A1A1A3S2S8ScG0S31S19S3bVv;A1A1A3ScG6S32S19S3cVv;A1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition FIN (v : vecs) : list bitem := ltac2:(tb__ "0|14|
S0S8SaZ1M0Z0M1S0S4S6S7A2M2S1S6S7Z18S9S1aS23Vv;A1A1M3A1M4A4S0G2S1S6S7Z60M5SbG3G0G1G0A4A4S0G2S1S6S7Z8M6S9S1aS20Vv;A1A1M7A1M8A4S0G2S1S6S7G5SbG7G0G1G0A4A4S0G2S1S6S7G6S9S1aS24Vv;A1A1M9A1MaA4S0G2S1S6S7G5SbG9G0G1G0A4A4S0G2S1S6S7G6S9S1aS26Vv;A1A1MbA1McA4S0G2S1S6S7G5SbGbG0G1G0A4A4S0G2S1S6S7Z78MdS9S1aS22Vv;A1A1A1MeA4S0G2S1S6S7Z68S9S1aS21Vv;A1A1A1MfA4S0G2S1S6S7GdS9S1aS25Vv;A1A1A1M10A4S3G2A1M11A3A3A3A3A3A3A3A3A3A3A3G1A4S0S8SaG1G0S0G2S1S6S7Z70M12G4A4S0G2S1S6S7Z50M13G8A4S0G2S1S6S7G13GaA4S0G2S1S6S7G13GcA4S0G2S1S6S7G12GeA4S0G2S1S6S7G13GfA4S0G2S1S6S7G12G10A4G11A3A3A3A3A3A3A3G1A4S3S8A1A3A3").

Definition DUP (v : vecs) : list bitem := ltac2:(tb__ "0|8|
S0S8SaZ1M0Z0M1S0S4S6S7A2M2S1S6S7Z38S9S1aS1dVv;A1A1A1M3A4S0G2S1S6S7Z8S9S1aS1eVv;A1A1A1M4A4S0G2S1S6S7Z18S9S1aS1fVv;A1A1A1M5A4S0G2S1S6S7Z100S9S1aS27Vv;A1A1A1M6A4S3G2A1M7A3A3A3A3Z310A4S0S8SaG1G0S0G2S1S6S7Z70G3A4S0G2S1S6S7Z10G4A4S0G2S1S6S7Z30G5A4S0G2S1S6S7Z200G6A4G7A3A3A3A3Z220A4S3S8A1A3A3").
Definition bd_rest0 (v : vecs) : list bitem := ltac2:(tb__ "0|0|
S2S8S18Vv;A1S2S8S16Vv;A1S15Vv;A1A3A3").

Definition bd_rest : list bitem := Eval vm_compute in bd_subst [] (bd_rest0 vsP).

Definition LAX (c : Z) : bitem := ltac2:(tb__ "0|2|
SaZ1Z0S0S4S6S7A2M0S1S6S7S49S9S45A1A4S0G0S1S6S7S46S49A1M1S9S1cA1A4S0G0S1S6S7G1S9S1bA1A4S3G0A1A3A3A3Vc;A4").

Definition AK1 : Z := 2048.
Definition LAK (c : Z) : bitem := ltac2:(tb__ "0|1|
SaZ0Z1S0S4S6S7A2M0S1S6S7SdS9S45A1A4S0G0S1S6S7S46SdA1S9S35A1A4S3G0A1A3A3Vc;A4").
Definition LAXK (c : Z) : bitem := ltac2:(tb__ "0|2|
SaZ0Z1S0S4S6S7A2M0S1S6S7SdS9S45A1A4S0G0S1S6S7S46SdA1M1S9S1cA1A4S0G0S1S6S7G1S9S1bA1A4S3G0A1A3A3A3Vc;A4").

Definition bdA (c : Z) : list bitem := ltac2:(tb__ "0|0|
S0S8S4aVc;A1S0S8SfSdA1S12A3A3").
Definition bdX (c : Z) : list bitem := ltac2:(tb__ "0|0|
S0S8S10Vc;A1S0S8S11Z0A1S12A3A3").

Definition ndL (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S50S4cS4bVbd;S4fS33S5A2A4").
Definition ndA1 : ndesc := ndL (bdA A1).
Definition ndX0 : ndesc := ndL (bdX 0).

Definition ndXE : ndesc := ltac2:(tb__ "0|1|
S13S0S8S10Z0M0A1S0S8S11G0A1S3S8A1A3A3A1").
Definition ndLE : ndesc := ltac2:(tb__ "0|1|
S13S0S8S4aZ0M0A1S0S8SfG0A1S3S8A1A3A3A1").

Goal length (bdA A1) = 42%nat /\ bd_below 600 (bdA A1) = true /\ bd_wpos (bdA A1) = true /\ nd_below 600 ndA1 = true /\ nd_below 600 ndX0 = true
     /\ bd_subst [] (bdA A1) = bdA A1 /\ bd_subst [] (bdX 0) = bdX 0.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal bud_le2 (ss_facts (ax_S K_ws)) (bd_subst [] (bdA A1)) (bdA A1) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal bud_le2 (ss_facts (ax_S X_latch7)) (bd_subst [] (bdX 0)) (bdA A1) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Goal bud_le2 (ss_facts (ax_S X_latchA)) (bd_subst s_loop (bdA A1)) (bdX 0) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Mline : Z := 2 ^ 37.
Definition VLA (ph : Z) (inner : sv) : sv := ltac2:(tb__ "0|0|
S3fS41S3fS41S40S42S3eS17A1S3fS44S3dS34A3A3S3eS47S48Z2Z1bA2Vph;A2A1A3Vinner;A3").
Definition z0 : sv := SLit 0.
Definition RL : Z := 500.
End Lib_load_obj_bud.

(* [comment removed for export] *)
Module Lib_load_obj_hv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "la_state"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "option"; "Some"; "andb"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_pc"; "SLit"; "cell"; "sprop"; "sv_eqb"; "SAlu"; "SPUle"; "SVar"; "c_val"; "ob_base"; "ob_cells"; "ob_lo"; "ss_facts"; "ss_objs"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "Pre_sd"; "P_none"; "P_num"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "s_sd"; "E_sd1"; "E_sd1r"; "K_hv0c"; "E_da1"; "E_da2"; "E_da3"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "L_vr3"; "L_vr4"; "L_vr5"; "L_vr6"; "L_vr7"; "L_vr8"; "R_sd"; "T_sd0"; "X_hv"; "cur0"; "cur_of"; "i_nums"; "nums_mat"; "sd_ok"; "xf_sd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "cps_hv"; "runL"; "E_hv0"; "K_hv0"; "leafL"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "c_da"; "c_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0.HVAddr"; "hv_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA"; "add_cells8_ok"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition i_nums : nat := 9%nat.
Definition nums_mat : list Z := ltac2:(tb__ "0|0|
S5SeZ38S5SeZ40S5SeZ48S7SeA1A3A3A3").
Definition K_hv0c : axst := Eval vm_compute in ax_setS K_hv0 (add_cells8 (ax_S K_hv0) i_nums nums_mat).

Definition E_sd1r : axst := Eval vm_compute in leafL (runL 400 cps_hv K_hv0c) sd_entry 0.

Definition xf_sd1 : list axform := ltac2:(tb__ "0|1|
S5S2bS2cU7S14N30A1A2S5S2bS2cU5M0S14N88A1A2S5S2bS2dG0N90A2S7S2bA1A3A3A3").
Definition optL' (x : option axst) : axst := match x with Some a => a | None => Pre_lo end.
Definition E_sd1 : axst := Eval vm_compute in optL' (apply_axforms E_sd1r xf_sd1).

Definition s_sd (E : axst) : wsub := ltac2:(tb__ "0|0|
S5dPaS1VE;A1S1S24A1A3").
Definition R_sd (E : axst) : list sobj := ltac2:(tb__ "0|0|
S5bS57VE;S24S31VE;A1A3A1").
Definition T_sd0 (E L : axst) : axst := ltac2:(tb__ "0|0|
S56S1fS1VE;A1A1S59S31VE;A1S24VL;VE;S45VE;A1A5A2").

Definition cur_of (A : axst) : sv := ltac2:(tb__ "0|5|
S9S12A1M0S11Lx;S30S12S12ScS17S1cR1A1S18S28S1aPaA1S14Na0A1A3A2S17S1eR1A1S14Z0A1M1A2A2Lo;S20S1VA;A1A1A3G1S12G0S9S15A1M2S11Lx;S1dR2A1G1S15G2S11S11Lx;S1bR2A1SeG1Lz;SfG1Li;S27S11S11S27S11Lop;R3R1G1G1G1G1G1G1G1G1G1X27xaLv;La;Lop;S27S11S11G1Lb;La;M3Lop;S29G3Lop;M4G4S6S10S11G1La;Lw;Lsgn;SfS11SeG1Lk;Li;Ll;X11x8Ll;Lc;X9x2Ll;Lo;X9x2").
Definition cur0 : sv := SAlu ALU_ADD (SVar 473) (SLit 1).

Definition T_sd (E L : axst) : axst := ltac2:(tb__ "0|0|
S46VE;VL;A2S0S56S5S16S19S48S49R1A1A2S7S16A1A3R1A2TT0;").
Definition sd_ok (E : axst) : bool := ltac2:(tb__ "0|2|
SaS9S12A1M0A1S6Lx;S57VE;S24S31VE;A1M1A3G0S58VE;S24G1R1S5S0S25S5S0S26S7S0A1A3A3A5LR;SdXax2").

Definition X_hv : list (sv * sv) := ax_X K_body.
Definition E_next (Ty : axst) : axst := ltac2:(tb__ "0|0|
S5eS52S4fU190S4eVTy;A3S2aU0A3S47A2").

Definition T_sd1n : axst := Eval vm_compute in T_sd E_sd1 P_none.   Definition T_sd1y : axst := Eval vm_compute in T_sd E_sd1 P_num.
Definition E_sd2 : axst := Eval vm_compute in E_next T_sd1y.
Definition T_sd2n : axst := Eval vm_compute in T_sd E_sd2 P_none.   Definition T_sd2y : axst := Eval vm_compute in T_sd E_sd2 P_num.
Definition E_sd3 : axst := Eval vm_compute in E_next T_sd2y.
Definition T_sd3n : axst := Eval vm_compute in T_sd E_sd3 P_none.   Definition T_sd3y : axst := Eval vm_compute in T_sd E_sd3 P_num.
Definition E_sd4 : axst := Eval vm_compute in E_next T_sd3y.
Definition T_sd4n : axst := Eval vm_compute in T_sd E_sd4 P_none.   Definition T_sd4y : axst := Eval vm_compute in T_sd E_sd4 P_num.
Definition E_sd5 : axst := Eval vm_compute in E_next T_sd4y.
Definition T_sd5n : axst := Eval vm_compute in T_sd E_sd5 P_none.   Definition T_sd5y : axst := Eval vm_compute in T_sd E_sd5 P_num.
Definition E_sd6 : axst := Eval vm_compute in E_next T_sd5y.
Definition T_sd6n : axst := Eval vm_compute in T_sd E_sd6 P_none.   Definition T_sd6y : axst := Eval vm_compute in T_sd E_sd6 P_num.
Definition E_sd7 : axst := Eval vm_compute in E_next T_sd6y.
Definition T_sd7n : axst := Eval vm_compute in T_sd E_sd7 P_none.   Definition T_sd7y : axst := Eval vm_compute in T_sd E_sd7 P_num.
Definition E_sd8 : axst := Eval vm_compute in E_next T_sd7y.
Definition T_sd8n : axst := Eval vm_compute in T_sd E_sd8 P_none.   Definition T_sd8y : axst := Eval vm_compute in T_sd E_sd8 P_num.

Lemma hv_checks_sd : ltac2:(tb__ "0|2|
S23S22SeS13S1S50A1A1S5cA3S23S22S6S21S1S51A1M0A1S8A3S23S22S6S5fG0S4aS4bA3S8A3S23S22S6S3S34A1S8A3S23S22SeS13S1S33A1A1S2aA3S23S22S9SeA1S5aS2SeS2S13S1S4R1A1A1A1LL;S4fU190S4eS34A3A4S5SeS2aS7SeA1A3A3S23S22SaS0A1S2eS33S4dA2SbS0S32A2A3S23S22S6S2fS0S4cS5S0S32S5S0S38S5S0S39S5S0S3aS5S0S3bS5S0S3cS5S0S3dS5S0S3eS7S0A1A3A3A3A3A3A3A3M1A3A3S8A3S22S6S2fS0S0S53S13S1R1A1A1S2aA2LE;G1A3S8A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cps_v : list Z := ltac2:(tb__ "0|0|
S5SeS55S5SeS54S4eA3A3").
Definition E_da1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd1n) c_da 0.
Definition E_da2 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd2n) c_da 0.
Definition E_da3 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd3n) c_da 0.
Definition L_vr3 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd4n) c_vr 0.
Definition L_vr4 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd5n) c_vr 0.
Definition L_vr5 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd6n) c_vr 0.
Definition L_vr6 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd7n) c_vr 0.
Definition L_vr7 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd8n) c_vr 0.
Definition L_vr8 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd8y) c_vr 0.
Lemma hv_checks_ends : ltac2:(tb__ "0|2|
S23S22S6S2fS0S0S53S13S1R1A1A1M0S54A2LE;S5S0S35S5S0S36S5S0S37S7S0A1M1A3A3A3A3S8A3S22S6S2fS0S0S53G0S55A2LE;S5S0S3fS5S0S40S5S0S41S5S0S42S5S0S43S5S0S44G1A3A3A3A3A3A3A3S8A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv.

