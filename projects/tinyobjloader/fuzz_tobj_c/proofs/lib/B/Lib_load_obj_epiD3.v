(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Datatypes"; "false"; "bool"; "nat"; "true"; "Some"; "cons"; "list"; "nil"; "option"; "prod"; "pair"; "app"; "negb"; "None"; "fst"; "length"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_objs"; "swf"; "ob_base"; "SVar"; "ss_pc"; "sstate"; "sv_eqb"; "DUnknown"; "DZero"; "cell"; "ob_lo"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "axwf"; "la_reason"; "la_state"; "ax_setS"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "Pre_f8"; "L_f8"; "ax_tidy"; "xf_shback"; "xf_shcall"; "vBo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "g5"; "objs_butlast"; "optR"; "O_out"; "sel_last"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "Ee_s8"; "Pre_sf"; "Ee_s8a"; "Ee_sf"; "Te_s81"; "Ee_sfB"; "Ee_sfC"; "Ee_zf"; "Re_s8"; "Te_s8"; "Te_s80"; "Te_s82"; "Te_s8r"; "dflt_obj"; "Ee_sf0"; "L_sf"; "Re_sf"; "Te_sf"; "iOUTe"; "s_s8"; "s_sf"; "sx_s8a"; "xf_merge"; "xf_rebase"; "xf_sh"; "Ee_sfA"; "Ee_sfD"; "X_sx"; "fr_off"; "frame_idx"; "insert_by"; "is_sh"; "needs_rebase"; "sh_idx"; "sx_T82"; "sx_T8r"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "nobj"; "E_s80"; "cps_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@Stdlib.Lists.List"; "filter"; "existsb"; "fold_right"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "lo_ret"; "sf5_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "alA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB"; "zero_fill_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjZeroFillB.

Definition X_sx (E : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S6fScS15S15A2M0G0SfS13S1dS11S15S15R1A3M1S38A2S1dG1S7cA2A2A1Lr;S27VE;A1A3").
Definition sx_s8a (E : axst) : axst := ltac2:(tb__ "0|0|
S77VE;S5dVE;A1S3cZ38ZdbA5").
Definition sx_s8 (E : axst) : axst := ltac2:(tb__ "0|1|
S3bS2eS57VE;A1M0S37G0Z38A2A2A1").
Definition s_s8 (E8 : axst) : wsub := ltac2:(tb__ "0|0|
S8ScS0S15A2SdS0S15S7fS41A4S74PaS25VE8;A1S25S33A1A3A3").
Definition sx_T80 (E8 : axst) : axst := ltac2:(tb__ "0|1|
S75S33VE8;S55VE8;A1M0S3eS6dVE8;S33G0A3A1S34A5").
Definition sx_T81 (T0 : axst) : axst := ltac2:(tb__ "0|0|
S3bS2eVT0;S36VT0;A1A2A1").
Definition sx_T82 (T1 : axst) : axst := ltac2:(tb__ "0|0|
S76VT1;S3dVT1;A1P6eSaScS1S1A2A1A4").
Definition sx_T8r (T2 : axst) : axst := ltac2:(tb__ "0|0|
S77VT2;S27VT2;A1S3cZ14Z34A5").
Definition sx_T8 (T2 : axst) : axst := ax_tidy (sx_T8r T2).

Definition is_sh (o : sobj) : bool := match ob_base o with SVar 140 => true | SAlu ALU_ADD (SVar 140) (SLit _) => true | _ => false end.
Definition dflt_obj : sobj := plain_obj (SLit 0) (SLit 0).
Definition sh_idx (A : axst) : list nat := ltac2:(tb__ "0|0|
S6fS5S5S61S68S16R1S17S25VA;A1A1S4fA4A1Li;S67U0S6aVA;A1A2A3").
Definition xf_sh (A : axst) : list axform := ltac2:(tb__ "0|3|
S9S5A1M0S9S2fA1M1Lx;S63VA;A1SaS2fA1M2S5G0G0G1Ll;R1S8S2fS30S40VA;R2A2A1G2A3S5G0G2Ll0;Ln;X9x2Ll;Li;X9x2").
Definition sx_sfA (E0 : axst) : axst := ltac2:(tb__ "0|0|
S3bS2eVE0;S5aVE0;A1A2A1").
Definition sx_sfB (EA : axst) : axst := ltac2:(tb__ "0|0|
S76VEA;S3dVEA;A1P6eSaScS1S1A2A1A4").

Definition fr_off (o : sobj) : option Z := ltac2:(tb__ "0|1f|
S15SbS1A1M0Lx;M1S19Vo;A1S1S10S1A1M2Lz;M3S0S0G0Li;M4R1S0G2Lp;M5S0S0G0Lp;M6R1S0S0G0Lp0;M7R1S0S0G0Lp1;M8R1S0S0G0Lp2;M9R1S0G2Lp3;MaS0S0G0Lp3;MbR1S0S0G0Lp4;McR1S0G2Lp5;MdGdG1S21Vo;A1MeS1S7S1R1A2Llo;S0G2Li0;MfS2cS15S15G2Lb;La;M10Lop;M11G11S2dG10Lop;M12G12S4S2S15G2La;Lw;Lsgn;M13S0S15S1G2Lk;M14Li0;Ll;M15X15x8X0x3Lp4;S0G2Lp4;M16G2X0x3Lp3;G2X0x3Lp2;S0G2Lp2;M17G2X0x3Lp1;S0G2Lp1;M18G2X0x3Lp0;S0G2Lp0;M19G2X0x3Lp;G2X0x3Li;S2cS15S15S2cG0Lop;R3S15G0La;R2G3S0G4R1G5S0G6R1S0G7R1S0G8R1S0G9R1GaS0GbR1S0GcR1GdGdS15G0Lb;R8S1G1GeS1S7S1S81R2R1A2A2Llo;GfS2cS15S15G2Lb0;La0;M1aLop0;M1bG1bS2dG1aLop0;M1cG1cS4S2S15G2La0;Lw;Lsgn;M1dG15X15x8Lc;GfG1bG1bG1cG1cG1dG15X15x8X0x3Lp4;G16G2X0x3Lp3;G2X0x3Lp2;G17G2X0x3Lp1;G18G2X0x3Lp0;G19G2X0x3Lp;G2X0x3Li;G1bG1bG1cG1cG1dS0S15G14Li;Ll;M1eX15x8G2G2G2G2G2G2G2G2G2X2cxaLb;La;Lop;G11G12G12G13G1eX15x8").
Definition needs_rebase (o : sobj) : bool := match ob_base o with SAlu ALU_ADD (SVar 110) (SLit _) => true | _ => false end.
Definition xf_rebase (A : axst) : list axform := ltac2:(tb__ "0|0|
S66S5S2fS5S32R1A1Li;S6fS5S5S62S68S16R1S17S25VA;A1A1S4fA4A1Li;S67U0S6aVA;A1A2A3A4").
Fixpoint insert_by (k : Z) (i : nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with [] => [(k, i)] | (k', j) :: r => if k <=? k' then (k, i) :: l else (k', j) :: insert_by k i r end.
Definition frame_idx (A : axst) : list nat := ltac2:(tb__ "0|2|
S66ScS1S5A2M0S5S14S1S5A2S71S9G0A1M1S5S5G1SbS1A1G1Lx;S5eS68S16R2S17S25VA;A1A1S4fA4A1S1S60R1R3R2A3Lk;R1Xbx2Lacc;Li;SaG0A1S67U0S6aVA;A1A2A5A4").
Definition xf_merge (A : axst) : list axform := ltac2:(tb__ "0|1|
S5fVA;A1S9S5A1S8S2fS30SeS5R1S6fS5S5SfS70S5S80R1A1R2A3A1Li;S67U0M0S6aVA;A1A2A3A3A1S69S2fS31G0A1S79S12S5R1A2U2A2A3A3Tfi;").
Definition sx_sfC (EB : axst) : axst := ltac2:(tb__ "0|0|
S3bS2eVEB;S59VEB;A1A2A1").
Definition sx_sfD (EC : axst) : axst := ltac2:(tb__ "0|0|
S3bS2eVEC;S58VEC;A1A2A1").
Definition sx_sf (ED : axst) : axst := flag_carve_stateA ED 120.
Definition Pre_sf : axst := Pre_stack_free AE_A 5.
Definition L_sf : axst := L_stack_free AE_A 5.
Definition s_sf (E : axst) : wsub := ltac2:(tb__ "0|1|
S8ScS0S15A2M0SdS0S15P10S1aP78A1A4S8G0SdS0S15PfS1aP13A1A4S74PaS25VE;A1S25S43A1A3A3A3").
Definition sx_Tsf (E : axst) : axst := ltac2:(tb__ "0|1|
S35S7eS43VE;S56VE;A1M0S3eS6dVE;S43G0A3A1S51S27VE;A1A6A1").

Definition iOUTe : nat := Eval vm_compute in idxB E_s80 vOUT 0.
Definition Ee_zf : axst := Eval vm_compute in optS E_s80 (zero_fill_at (ax_S E_s80) iOUTe).
Definition Ee_s8a : axst := Eval vm_compute in sx_s8a Ee_zf.
Definition Ee_s8 : axst := Eval vm_compute in sx_s8 Ee_zf.
Definition Re_s8 : list sobj := Eval vm_compute in optR (entails_frA Ee_s8 Pre_f8 (s_s8 Ee_s8)).
Definition Te_s80 : axst := Eval vm_compute in sx_T80 Ee_s8.
Definition Te_s81 : axst := Eval vm_compute in sx_T81 Te_s80.
Definition Te_s82 : axst := Eval vm_compute in sx_T82 Te_s81.
Definition Te_s8r : axst := Eval vm_compute in sx_T8r Te_s82.
Definition Te_s8 : axst := Eval vm_compute in ax_tidy Te_s8r.
Definition Ee_sf0 : axst := Eval vm_compute in leafL (runL 300 cps_ad Te_s8) sf5_pc 0.
Definition Ee_sfA : axst := Eval vm_compute in sx_sfA Ee_sf0.
Definition Ee_sfB : axst := Eval vm_compute in sx_sfB Ee_sfA.
Definition Ee_sfC : axst := Eval vm_compute in sx_sfC Ee_sfB.
Definition Ee_sfD : axst := Eval vm_compute in sx_sfD Ee_sfC.
Definition Ee_sf : axst := Eval vm_compute in sx_sf Ee_sfD.
Definition Re_sf : list sobj := Eval vm_compute in optR (entails_frA Ee_sf Pre_sf (s_sf Ee_sf)).
Definition Te_sf : axst := Eval vm_compute in sx_Tsf Ee_sf.
Definition P_errL : axst := Eval vm_compute in leafL (runL 300 cps_ad Te_sf) lo_ret 0.

Lemma epiD3_checks_s8 : ltac2:(tb__ "0|7|
S23S22S4S18S25S44A1A1S6A3S23S22S24S57S49A1S44A3S23S22SbS24A1M0S2eS44S37S44Z38M1A2A2S7S24S42A2A3S23S22SbS9S16A1M2A1S6dS42S33S55S42A1M3A3S7G2S4aA2A3S23S22S4S6eS42S33G3S4aS8S24S34SaS24A1A3A5S6A3S23S22S24S75S33S42G3S4aS34A5S4cA3S23S22G0S2eS4cS36S4cA1A2S7S24S46A2A3S23S22G2S17S25S46A1A1SeS16S3dS46A1S8S16S78S3cG1ZdbSaS20A1M4S1eA5SaS16A1A3A3A3S23S22S24S64S46A1S4dA3S23S22S4S18S25S4dA1A1S6A3S23S22S24S65S4dA1S4eA3S23S22S4S18S25S4eA1A1S6A3S23S22S24S35S4eA1S4bA3S23S22S4S28S4bA1S6A3S23S22S9ScS1S39A2M5A1S66S26G5S26SdS1S39S1bS25S2aR1A1A1A1S29R1A1A4LL;S73U12cS6cS4bA3A4S8G5SdS1S39S7bS3aA4SaG5A1A3A3S23S22SbS1cA1S7dS25S6bA1S54A2S7S1cS25S49A1M6A2A3S23S22S24S2bS6bG6A2S49A3S23S22S4S18G6A1S6A3S22SbS16A1S72S16S17G6A1S54A3S7S16S3fG4S1fA2A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD3_checks_sf : ltac2:(tb__ "0|4|
S23S22SbS24A1M0S2eS50S5aS50A1A2S7S24S5bA2A3S23S22S4S18S25S47A1A1S6A3S23S22G0S2eS47S59S47A1A2S7S24S48A2A3S23S22G0S2eS48S58S48A1A2S7S24S5cA2A3S23S22S4S28S45A1S6A3S23S22SbS9S16A1M1A1S6dS45S43S56S45A1M2A3S7G1S52A2A3S23S22S4S6eS45S43G2S52S8S24S51SaS24A1A3A5S6A3S23S22S4S28S53A1S6A3S22S9ScS1S39A2M3A1S66S26G3S26SdS1S39S1bS25S2aR1A1A1A1S29R1A1A4LL;S73U12cS6cS53A3A4S8G3SdS1S39S7aS3aA4SaG3A1A3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
