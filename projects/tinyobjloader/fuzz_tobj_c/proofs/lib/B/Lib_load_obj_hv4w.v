(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "pair"; "list"; "nat"; "option"; "prod"; "Some"; "app"; "orb"; "S"; "false"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "g8"; "has_facts"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "sprop"; "SPUle"; "sv_eqb"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_next"; "ss_objs"; "ss_pc"; "DUnknown"; "SAlu"; "cell"; "ob_cells"; "SPEq"; "SPUlt"; "c_off"; "mkObj"; "mkSS"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vF"; "NP"; "g5"; "vLEN"; "optR"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4w"; "PreR"; "E_o3"; "s_w"; "LR"; "T_w0"; "T_w1"; "R_w"; "w_chk"; "Ew0"; "Ew0r"; "Ew1"; "Ew1r"; "Lp0"; "Lp1"; "Lw0"; "Lw1"; "T_w0_0"; "T_w0b"; "T_w1_0"; "T_w1b"; "T_wc"; "drop_rgb"; "relw"; "s_o3j"; "w_ok"; "xf_w"; "xfb_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "filter"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "objs_nl"; "sh_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "bd_op1"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "AHead"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "cps_v"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "pure_posts_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition Lw0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_op1) memcpy_pc 0.
Definition Lw1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_op1) memcpy_pc 1.
Definition PreR : axst := Pre_memcpyR AE_A white_hv 12.
Definition LR : axst := L_memcpyR AE_A white_hv 12.
Definition relw (A : axst) : axst := ltac2:(tb__ "0|2|
S91VA;S75VA;A1P6eS2SaS1dS1dA2M0S6S1dS1dZ60ZcM1A4S2G0S6S1dS1dZ80G1A4S5G0A1A3A3A4").
Definition xf_w (T : axst) : list axform := ltac2:(tb__ "0|2|
S66S45S1fZ20A1VT;A3S8S2S3fS41R1S1fZ80M0A1A2S2S3fS41SeR1A1M1S1fZ8cA1A2S2S3fS44G1G0A2S5S3fA1A3A3A3Tj;").
Definition s_w (E : axst) : wsub := ltac2:(tb__ "0|1|
S2SaS1eS21A2M0S6S1eS21P35S2cS70S45S1fZ80A1A3A4S2G0S6S1eS21P36S1fZcA1A4S2G0S6S1eS21S94S4aA4S7dPaS13VE;A1S13S4bA1A3A3A3A3").
Definition R_w (E : axst) : list sobj := ltac2:(tb__ "0|0|
S49S7fVE;S4bS4dVE;A1A3A1").
Definition w_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S9S7S20A1M0A1S3Lx;S7fVE;S4bS4dVE;A1M1A3G0S80VE;S4bG1R1S2S12S4eS5S12A1A3A5LR;SfX9x2").
Definition T_wc (E : axst) : axst := ltac2:(tb__ "0|0|
S8eS4bVE;S4dVE;A1S51VE;A1S4eA5").
Definition xfb_w (T : axst) : list axform := ltac2:(tb__ "0|3|
S2S3fS43S66S2cS70S45S1fZ80A1M0A3S1fZ0A1VT;A3A1S5S3fA1M1A3S7S3fA1S88S40VT;R1A2A1S12ScS3fR2S2S3fS69S2S8S66S45S1fZ20A1R1A3S2S8S66S45G0R1A3S2S8S66S45S1fZ8cA1R1A3S5S8A1A3A3A3S10S20S29S13R1A1A1A2A2S2S3fS42U0A1M2S2S3fG2G1A3A3A3A3TT1;Tpre;").
Definition Ew0r : axst := Eval vm_compute in relw Lw0.       Definition Ew1r : axst := Eval vm_compute in relw Lw1.
Definition Ew0 : axst := Eval vm_compute in optL' (apply_axforms Ew0r (xf_w Ew0r)).
Definition Ew1 : axst := Eval vm_compute in optL' (apply_axforms Ew1r (xf_w Ew1r)).
Definition T_w0_0 : axst := Eval vm_compute in T_wc Ew0.    Definition T_w1_0 : axst := Eval vm_compute in T_wc Ew1.
Definition T_w0b : axst := Eval vm_compute in optL' (apply_axforms T_w0_0 (xfb_w T_w0_0)).
Definition T_w1b : axst := Eval vm_compute in optL' (apply_axforms T_w1_0 (xfb_w T_w1_0)).
Definition T_w0 : axst := Eval vm_compute in ax_tidy T_w0b.  Definition T_w1 : axst := Eval vm_compute in ax_tidy T_w1b.

Definition w_chk (tv : list (sv * sv)) (bd : list bitem) (L Er E T0 Tb T : axst) : Prop := ltac2:(tb__ "0|e|
S1S0S7S20A1S29S13VL;A1M0A1ScS20S75VL;A1M1S2S20S92S47Z4M2Z12M3S2eS76VL;A1A1M4S2bA5S5S20A1A3A3A3S1S0S21S17VL;A1S1fS93A1A3S1S0S3S1bS2S22S2fS1aS47A1S45A2S2S22S23S25S47A1S1fS96S95Z2Z3dA2Z1A2A1A2S5S22A1A3A3S27G0A1M5A2S4A3S1S0S3S6eSaS1dS1dA2M6S90G4S2bG2G3A4S2G6S6S1dS1dZ60ZcM7A4S2G6S6S1dS1dZ80G7A4S5G6A1A3A3A3S4A3S1S0S3S81S28G0A1M8S83Vtv;S6aVbd;S82S7bS4A2A4M9A2S4A3S1S0S3S68G5Vtv;S6aS67G1A5S4A3S1S0S3S71G5A1S4A3S1S0S12S61VL;A1VEr;A3S1S0S9S12A1MaS40VEr;S64VEr;A1A2SbS12VE;A2A3S1S0S3S63VE;A1S4A3S1S0S3S8fS46S4dVE;A1A2S4A3S1S0S3S86S46S28S13VE;A1MbA1McA2S4A3S1S0S3S81GcG9A2S4A3S1S0S3S8cGcVbd;A2S4A3S1S0S3S8dVbd;A1S4A3S1S0S3S8aS4bS2S12S4eS5S12A1A3A2S4A3S1S0S3S72S27GbA1MdVtv;S6aS67S51VE;A1A5S4A3S1S0S3S74GdVtv;S6aS73S16VE;A1A5S4A3S1S0S3S71GdA1S4A3S1S0S3S84GcS6bA2S4A3S1S0S12S5fVE;A1VT0;A3S1S0GaS40VT0;S65VT0;A1A2SbS12VTb;A2A3S1S0S12S8bVTb;A1VT;A3S1S0S3S84G8S6bA2S4A3S1S0S3S6dS22S26S30S7cS7aA2A1G5A3S4A3S1S0S3S6dS22S26S23S7aS48A2A1G5A3S4A3S0S3S6dS22S26S23S48S1fZ4000000A1A2A1G5A3S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma hv4_checks_w0 : ltac2:(tb__ "0|0|
S52S78S77S59S54S53S5bS5cS4fA8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma hv4_checks_w1 : ltac2:(tb__ "0|0|
S52S78S77S5aS56S55S5dS5eS50A8"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Lp0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_w0) c_op 0.
Definition Lp1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_w1) c_op 0.
Definition drop_rgb (o : sobj) : sobj := ltac2:(tb__ "0|2|
S3S20L_;S24S34Vo;A1M0S45A2S32G0S37Vo;A1S36Vo;A1S6fS2dS2dS11SdSdS24S31R1A1M1S1fZ60A1A2S24G1S1fZ64A1A2A2S24G1S1fZ68A1A2A2A1Lc;S2eVo;A1A3S35Vo;A1A5Vo;X3x2").
Definition gen_o3 (L C : axst) : axst := ltac2:(tb__ "0|0|
S13VL;A1S3dS28R1A1S1eS25R1A1S21S18VL;S33S2aR3A1S7eS21S7eS21S3bR3A1UfR1A4U1bS25S85R2P1A2A1A4S39R3A1S38R3A1S3cR3A1S6cS20S20S60S29R3A1A4S2S22S23R1S1fZ1A1A2S27S13VC;A1A1A3S85R2P2A2S3aR3A1A9A2Tpw;Tn;TS;").
Definition E_o3 : axst := Eval vm_compute in gen_o3 Lp0 T_op1.
Definition s_o3j (L : axst) : wsub := ltac2:(tb__ "0|0|
S7dS46S13VL;A1S13S4cA1A3").
Lemma hv4_checks_o3j : ltac2:(tb__ "0|4|
S1S0S3S14S4cA1S4A3S1S0S3S3eS13S4cA1M0A1S4A3S1S0S1dS2aG0A1S79A3S1S0S7S7S1dA1M1A1S6cS12G1S12S6cS15S1dS15S2aS13S1cR1A1A1A1LL;S89U258S87R1A3A4LT;S2S12S4fS2S12S50S5S12A1M2A3A3A4S2G1S2S1dS79S5S1dA1A3M3S2G1G3S5G1A1A3A3A3S1S0S3S6eS12S12S19R1S4cS62R1A1A3LL;S2S12S57S2S12S58G2A3A3A3S4A3S1S0S3S14S4fA1S4A3S0S3S14S50A1S4A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
