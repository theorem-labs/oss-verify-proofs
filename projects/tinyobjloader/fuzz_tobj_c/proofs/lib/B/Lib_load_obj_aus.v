(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nat"; "pair"; "prod"; "cons"; "Some"; "option"; "nil"; "length"; "list"; "andb"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "la_state"; "leafA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "SPUle"; "sprop_below"; "ss_objs"; "sv_eqb"; "SAlu"; "SPUlt"; "ob_base"; "ob_hi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_aus"; "s_u0"; "E_u1"; "E_u2"; "R_u1"; "R_u2"; "T_u10"; "T_u20"; "s_u1"; "s_u2"; "B_u1"; "B_u2"; "E_u20"; "T_u1"; "T_u2"; "xfb_leaf"; "cutsU"; "exitsU"; "is_winpiece"; "win_idx"; "xf_u1"; "xf_u2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "bdA"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "AHead"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find"; "Pre_mf"; "P_mf"; "Posts_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_mf"; "E_mf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "frL"; "tvL"; "A1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "filter"; "find"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "X_latch"; "pE"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "bud_le2"; "ejcertAF"; "wsub_id_on"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H"; "P_bwH"; "Posts_bwH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr MatFindAddr BWarnAddr LOAddr LOLAddr HVAddr.

Definition is_winpiece (hi : Z) (o : sobj) : bool := ltac2:(tb__ "0|0|
SdS20S23Vo;A1S21S72S19PaA1S18N280A1A3A2S20S24Vo;A1S18Vhi;A1A2A2").
Definition win_idx (hi : Z) (T : axst) : nat := ltac2:(tb__ "0|3|
S9S6S4S16A2M0A1S4Lx;S5dG0G0S36Vhi;SfS4S16R1A3A2Lp;S5bS4S16S60U0M1SbS16S1fS11VT;A1A1M2A2A2G2A4A3G0G0S4Lp;R1S4S16R2Ls;Li;X6x1Lp;G1X9x2").
Definition xfb_leaf (hi : Z) (T : axst) : list axform := ltac2:(tb__ "0|2|
SbS16S1fS11VT;A1A1A2S4S37Vhi;VT;A2S4S7S4fS51S7S4R1S7S4U0M0S5cS4S4SeS7aR1R2A2A1Li;S60U1M1S71R2G1A2A2A3A3A3A1S7S4fS50G0A1SaS4fA1A3A3Tw;Tn;").

Definition xf_u1 : list axform := [AXSplit 7 (SLit (-32))].
Definition E_u1 : axst := Eval vm_compute in optL (apply_axforms E_mf xf_u1).
Definition s_u1 : wsub := ltac2:(tb__ "0|0|
S58PaS11S26A1S11S4bA1A3").
Definition R_u1 : list sobj := Eval vm_compute in optR (entails_frA E_u1 Pre_mf s_u1).

Definition T_u10 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_u1)) (import_postA s_u1 Pre_mf P_mf E_u1 R_u1).
Definition B_u1 : axst := Eval vm_compute in optL (apply_axforms T_u10 (xfb_leaf (-32) T_u10)).
Definition T_u1 : axst := Eval vm_compute in ax_tidy B_u1.

Lemma aus_checks1 : ltac2:(tb__ "0|5|
S1S0S9S10A1M0S4eS52S38A2S8S10S26A2A3S1S0S9ScS16A1M1A1S6bS26S4bS2cA3S8G1S28A2A3S1S0S3S6aS26S4bS2cS28S5fS13S10S12S4dA4A5S2A3S1S0S3S5eS3aS1cS11S26A1M2A1M3A2S2A3S1S0S3S45G3S3eA2S2A3S1S0S3S5aS17S1eG3A1S1bG2A1M4A3S2A3S1S0S10S69G4S6cS2cS4bS4cS26S28A5A2S2aA3S1S0G0S4eS2aS33N20S2aA2A2S8S10S2eA2A3S1S0S10S66S2eA1S31A3S0S3S6dG3S54A2S2A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_u20 : axst := Eval vm_compute in leafL_at (c_bw :: cps_arm) T_u1 c_bw 0.
Definition xf_u2 : list axform := [AXSplit 0 (SLit (-96))].
Definition E_u2 : axst := Eval vm_compute in optL (apply_axforms E_u20 xf_u2).
Definition s_u2 : wsub := ltac2:(tb__ "0|0|
S58PaS11S27A1S11S4aA1A3").
Definition R_u2 : list sobj := Eval vm_compute in optR (entails_frA E_u2 Pre_bw s_u2).
Definition T_u20 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_u2)) (import_postA s_u2 Pre_bw P_bwH E_u2 R_u2).
Definition B_u2 : axst := Eval vm_compute in optL (apply_axforms T_u20 (xfb_leaf (-96) T_u20)).
Definition T_u2 : axst := Eval vm_compute in ax_tidy B_u2.

Lemma aus_checks2 : ltac2:(tb__ "0|5|
S1S0S9S10A1M0S4eS30S39A2S8S10S27A2A3S1S0S9ScS16A1M1A1S6bS27S4aS2dA3S8G1S29A2A3S1S0S3S6aS27S4aS2dS29S5fS13S10S12S75A4A5S2A3S1S0S3S5eS3aS1cS11S27A1M2A1M3A2S2A3S1S0S3S45G3S3eA2S2A3S1S0S3S5aS17S1eG3A1S1bG2A1M4A3S2A3S1S0S10S69G4S6cS2dS4aS74S27S29A5A2S2bA3S1S0G0S4eS2bS33N60S2bA2A2S8S10S2fA2A3S1S0S10S66S2fA1S32A3S1S0S3S6dG3S54A2S2A3S1S0S3S59S17S1aS22S65S61A2A1G4A3S2A3S1S0S3S59S17S1aS1dS61S3bA2A1G4A3S2A3S0S3S59S17S1aS1dS3bS18Z4000000A1A2A1G4A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_u0 : wsub := ltac2:(tb__ "0|0|
S7S6S3dS15A2S5S3dS15P1e3S63A4S58S3aS11S53A1S11S52A1A3A3").
Lemma aus_checks0 : ltac2:(tb__ "0|6|
S1S0S3S14S53S52S25A3S2A3S1S0S3S68S25S3aA2S2A3S1S0S3S5eS3aS1cS11S53A1M0A1M1A2S2A3S1S0S3S45G1S3eA2S2A3S1S0S3S78S25S56S56A3S2A3S1S0S3S49S25S55S55A3S2A3S1S0S3S6eS1bG0A1S79S25S42S57A1M2A2G2A3S2A3S1S0S3S47S48S25S46S64S2A2M3A2G3A2S2A3S1S0S3S70S54S25A2S2A3S1S0S15S67S25P1ccM4A2S19G4A1A3S0S15S67S25P1d3M5A2S19G5A1A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsU : list efnode := ltac2:(tb__ "0|5|
S7S6S6S6S10S44A2M0S4A2M1S6S3cS15A2M2A2M3S5G1G2S5G0S4S5S10S44S31S3eA4U1M4A4S5S3cS15S3fS40ZaS41A2A4A4S7G3S5G1G2S5G0S4S5S10S44S32S3eA4G4A4S5S3cS15S3fS40Z5S41A2A4A4SaG3A1A3A3").
Definition exitsU : list efnode := ltac2:(tb__ "0|5|
S7S6S6S6S10S44A2M0S4A2M1S6S3cS15A2M2A2M3S5G1G2S5G0S4S5S10S44S30S3eA4U1M4A4S5S3cS15S3fS40Z7S41A2A4A4S7G3S5G1G2S5G0S4S5S10S44S62S43A4G4A4S5S3cS15S3fS40Z1S41A2A4A4SaG3A1A3A3").
Lemma ecertU_ok : ltac2:(tb__ "0|0|
S0S3S6fS73S3aS76Uc8S77S3aS34S35A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
