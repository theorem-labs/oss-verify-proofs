(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "app"; "nil"; "prod"; "pair"; "Some"; "fst"; "list"; "option"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "entailsA"; "la_reason"; "la_state"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "s_fs2"; "E_fs2"; "R_fs2"; "EK"; "EV"; "K_succ"; "Xk_fs2"; "brest_fs2"; "cE"; "kE"; "s_kn"; "s_nn"; "bdrest_fs2"; "E_fs21"; "L_sk"; "L_sn"; "T_fz2"; "T_fz20"; "T_nop2"; "T_nop20"; "T_ok2"; "T_ok20"; "bd_s0"; "bd_succ"; "cps_s"; "kept_fs2"; "tv_fs2"; "xfb_fs2"; "B_fz2"; "B_nop2"; "B_ok2"; "PDk_fs2"; "T_f20"; "bd_nop2"; "bd_ok2"; "hand_fs2"; "payX_fs2"; "payY_fs2"; "qHk2"; "qHn2"; "tvL_k"; "tv_nop2"; "tv_ok2"; "Es_fs0"; "FINi2"; "VPsh2"; "bd_fz2"; "f_absurd"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "nnPhi"; "passed_fs2"; "pc_succ"; "qHz2"; "tv_fz2"; "xf_fs2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1.FS"; "Pre_fs"; "nd_fail_f"; "nd_nop"; "nd_ok"; "NP"; "P_failz"; "P_nop"; "P_ok"; "nd0"; "P_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "NDA"; "am_subst"; "ndesc"; "nd_am"; "nd_tv"; "am_eqb"; "nd_bd"; "nd_below"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "ss_facts"; "sv"; "SAlu"; "SMd"; "ss_next"; "ss_pc"; "valuation"; "SPBranch"; "SPNot"; "SPUle"; "sobj"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "t_c"; "t_k"; "v_sh"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "bd_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "bud_pay2"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Corelib.Init.Nat"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "cps_epi"; "pc_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1.FS.FSAddr"; "fs_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf. End FSP.

Definition EV (c : Z) : bitem := BIc 1 0 c.
Definition EK (k : Z) : bitem := BIc 0 1 k.
Definition cE : Z := 600000.
Definition kE : Z := 64 * KU.
Definition bd_s0 : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS23A1S4SfS1eS24A1S9eA3A3").
Definition nd_s0 : ndesc := ltac2:(tb__ "0|0|
S61S5fS5eS31S60S88S2A2A4").
Definition pc_succ : Z := 0x8e4d0.
Definition cps_s : list Z := pc_succ :: cps_epi.

Definition Es_fs0 : axst := Eval vm_compute in leafL (runL 300 cps_epi K_after0) FS.FSAddr.fs_entry 0.
Definition xf_fs2 : list axform := ltac2:(tb__ "0|2|
S4S7dS82U7M0S6cN100M1A1A2S4S7dS7fG0G1A2S6S7dA1A3A3").
Definition E_fs21 : axst := Eval vm_compute in optL (apply_axforms Es_fs0 xf_fs2).
Definition nnPhi : sprop := ltac2:(tb__ "0|2|
S77S71S9bS6cZ4A1S9dZ80M0S8aS8bS8cA1M1A1A2A3S70S9aS71S9bS6cZ6A1S9dG0S89G1A1A2A3S6cZ1000A1A3A2").
Definition E_fs2 : axst := Eval vm_compute in ax_add_facts [nnPhi] E_fs21.
Definition s_fs2 : wsub := ltac2:(tb__ "0|0|
S4S7S6bS6fA2S8S6bS6fP13S70S9aS84S6cZ100A1A3A4S94PaS14S1cA1S14S54A1A3A3").
Definition R_fs2 : list sobj := Eval vm_compute in optR (entails_frA E_fs2 FS.Pre_fs s_fs2).
Definition PDk_fs2 : list pdescK := liftPD FSP.PD_fs.
Definition passed_fs2 : list (sv * sv) := Eval vm_compute in import_tv s_fs2 (nd_tv FS.nd0).
Definition kept_fs2 : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (existsb (fun p => sv_eqb (fst p) (fst t)) passed_fs2)) tvL.
Definition tv_fs2 : list (sv * sv) := kept_fs2 ++ passed_fs2.
Definition hand_fs2 : list bitem := Eval vm_compute in bd_subst s_fs2 (nd_bd FS.nd0).
Definition VPsh2 : list bitem := Eval vm_compute in firstn 2 (skipn 12 bd_rest).
Definition FINi2 : list bitem := Eval vm_compute in firstn 2 (skipn 36 bd_rest).
Definition bdrest_fs2 : list bitem := Eval vm_compute in (firstn 12 bd_rest ++ firstn 22 (skipn 14 bd_rest) ++ skipn 38 bd_rest).
Definition brest_fs2 : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS69S23Z362A2A1S4SfS1eS69S24Z44A2A1S27A3A3").
Definition payX_fs2 : list bitem := ltac2:(tb__ "0|0|
S5SfS47S5SfS48S4SfS1fS23A1S4SfS1eS24A1S6SfA1A3A3A3A3").
Definition payY_fs2 : list bitem := ltac2:(tb__ "0|0|
S5SfS3eS4SfS1fS69S23Z362A2A1S4SfS1eS69S24Z44A2A1S6SfA1A3A3A3").
Definition Xk_fs2 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_fs2)) (ax_X E_fs2).

Lemma epiS1_checks_fs : ltac2:(tb__ "0|c|
S1S0SbS7S6aS7bA2M0A1S85S15G0S15S8S6aS7bS73S14S19R1A1A1A1S18R1A1A4LL;S87U12cSa5Sa9A3A4S4G0S8S6aS7bSa8S7cA4S6G0A1A3A3S1S0ScS13A1S7eS46S53A2S9S13S28A2A3S1S0S13SabS28S5S6dS4S6dS4eS6S6dA1A3S6eS14S28A1M1A1A3M2A2S1cA3S1S0S3Sa2S6dS79S72G1A1A1G2A3S2A3S1S0ScSbS78A1M3A1S97S1cS54S1bA3S9G3S1dA2A3S1S0S3S96S1cS54S1bS1dS85S7S7S13S63A2M4S74S74OF_;F_;M5A2M6S13G6SaS13S63SaG4G5R1A3A3Ld;S3aA4A5S2A3S1S0S3SacS83S1bA2S2A3S1S0S3SaaS1bS58A2S2A3S1S0S3S99S1bS4fS65S5cA1A3S2A3S1S0S3S66S62S1bS64S5cA1A2S60S88S2A2M7A2S2A3S1S0S3Sa2S7S8eG5A2M8G8S8fS54S58S1bS72S14S1cA1M9A1MaSaS8eG5R1A3A5Ld;S3aA3S2A3S1S0S3S91S5fS35A2S2A3S1S0S3S91S35S5fA2S2A3S1S0S3S90S21S1aS1cA1A2S2A3S1S0S3S92S31S5SfS27S3fA3A2S2A3S1S0S3S92S5SfS27S40A3S5SfS3eS22A3A2S2A3S1S0S3S12S27A1S2A3S1S0S3Sa1S6eG9A1S6cZ0MbA1GbS3fS40A5S2A3S1S0S3S68GaS61S35S5eS31G7A4A2S2A3S1S0S3S11GaS22A2S2A3S0S3SadS83GaA2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition xfb_fs2 (T : axst) : list axform := ltac2:(tb__ "0|3|
S4S7dS7fU1M0Z100A2S4S7dS81S4SdG0S4SdU0M1S86U2M2Sa4Sa7VT;A1G2A2A2A3A3A1S4S7dS80G1A1S6S7dA1A3A3A3").
Definition T_nop20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_nop Xk_fs2.
Definition T_ok20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_ok Xk_fs2.
Definition T_f20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_fail Xk_fs2.
Definition T_fz20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_failz Xk_fs2.
Definition B_nop2 : axst := Eval vm_compute in optL (apply_axforms T_nop20 (xfb_fs2 T_nop20)).
Definition B_ok2 : axst := Eval vm_compute in optL (apply_axforms T_ok20 (xfb_fs2 T_ok20)).
Definition B_fz2 : axst := Eval vm_compute in optL (apply_axforms T_fz20 (xfb_fs2 T_fz20)).
Definition T_nop2 : axst := Eval vm_compute in ax_tidy B_nop2.
Definition T_ok2 : axst := Eval vm_compute in ax_tidy B_ok2.
Definition T_fz2 : axst := Eval vm_compute in ax_tidy B_fz2.
Definition isub_nop2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_nop E_fs2.
Definition isub_ok2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_ok E_fs2.
Definition isub_fz2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_failz E_fs2.
Definition qHn2 : sv := Eval vm_compute in sv_subst isub_nop2 FS.vHD.
Definition qHk2 : sv := Eval vm_compute in sv_subst isub_ok2 FS.qHD.
Definition qHz2 : sv := Eval vm_compute in sv_subst isub_fz2 FS.qHD.
Definition tv_nop2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_nop2 (nd_tv FS.nd_nop)).
Definition bd_nop2 : list bitem := Eval vm_compute in (bd_subst isub_nop2 (nd_bd FS.nd_nop) ++ brest_fs2).
Definition tv_ok2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_ok2 (nd_tv FS.nd_ok)).
Definition bd_ok2 : list bitem := Eval vm_compute in (bd_subst isub_ok2 (nd_bd FS.nd_ok) ++ brest_fs2).
Definition tv_fz2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_fz2 (nd_tv FS.nd_fail_f)).
Definition bd_fz2 : list bitem := Eval vm_compute in (bd_subst isub_fz2 (nd_bd FS.nd_fail_f) ++ brest_fs2).
Definition nd_nop2 : ndesc := ltac2:(tb__ "0|0|
S61S44S5eS3cS60S42S2A2A4").
Definition nd_ok2 : ndesc := ltac2:(tb__ "0|0|
S61S45S5eS3dS60S41S2A2A4").
Definition nd_fz2 : ndesc := ltac2:(tb__ "0|0|
S61S52S5eS49S60S51SeA2A4").
Definition f_absurd : sprop := ltac2:(tb__ "0|1|
S76S75S9cS6cZ0A1M0G0A3A1").

Lemma epiS1_checks_nd : ltac2:(tb__ "0|5|
S1S0S63S61S5S7S6fS6fA2M0S34S98S95S1bS54S5aS1cA4M1S65S56A1A2A3S5eS5SfS10G1S67S56A1A2S22A3S62G1S64S56A1A2A4S4cA3S1S0S63S61S5G0S34S98S95S1bS54S5bS1cA4M2S65S57A1A2A3S5eS5SfS10G2S67S57A1A2S22A3S62G2S64S57A1A2A4S4dA3S1S0S63S61S5G0S34S98S95S1bS54S59S1cA4M3S65S55A1A2A3S5eS5SfS10G3S67S55A1A2S22A3S62G3S64S55A1A2A4S4bA3S1S0S13S8dS54S1cS1bS1dS5aS21A6S2eA3S1S0S13S8dS54S1cS1bS1dS5bS21A6S30A3S1S0S13S8dS54S1cS1bS1dS5dS21A6S3bA3S1S0S13S8dS54S1cS1bS1dS59S21A6S2cA3S1S0ScS13A1M4S7eS2eS36S2eA1A2S9S13S38A2A3S1S0G4S7eS30S36S30A1A2S9S13S39A2A3S1S0G4S7eS2cS36S2cA1A2S9S13S37A2A3S1S0S13S93S38A1S2dA3S1S0S13S93S39A1S2fA3S1S0S13S93S37A1S2bA3S1S0S3S16S2dA1S2A3S1S0S3S16S2fA1S2A3S1S0S3S16S2bA1S2A3S0S3Sa3S6dS7aS4aA1S6eS14S3bA1A1A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition L_sn : axst := Eval vm_compute in leafL (runL 300 cps_s T_nop2) pc_succ 0.
Definition L_sk : axst := Eval vm_compute in leafL (runL 300 cps_s T_ok2) pc_succ 0.
Definition L_dz : axst := Eval vm_compute in leafL (runL 300 cps_s T_fz2) pc_disp 0.
Definition K_succ : axst := Eval vm_compute in ax_with_facts L_sn (List.filter (fun f => negb (sprop_eqb f nnPhi)) (ss_facts (ax_S L_sn))).
Definition s_kn : wsub := ltac2:(tb__ "0|0|
S94S83S14S29A1S14S20A1A3").
Definition s_nn : wsub := ltac2:(tb__ "0|0|
S94S83S14S2aA1S14S20A1A3").
Definition bd_succ : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS69S69S23Z362A2Z100A2A1S4SfS1eS69S69S24Z44A2Z200A2A1S9eA3A3").
Definition nd_succ : ndesc := ltac2:(tb__ "0|0|
S61S5fS5eS32S60S88S2A2A4").
Definition tvL_k : list (sv * sv) := Eval vm_compute in map (fun t => (sv_subst s_kn (fst t), sv_subst s_kn (snd t))) tvL.

Lemma epiS1_checks_succ : ltac2:(tb__ "0|7|
S1S0SbS7S6aS7bA2M0A1M1S85S15G0S15S8S6aS7bS73S14S19R1A1A1A1S18R1A1A4LL;M2S87U12cM3S33S2dA3A4S4G0S8S6aS7bS50S7cA4S6G0A1M4A3M5A3S1S0G1S85S15G0G2S87G3S33S2fA3A4G5A3S1S0G1S85S15G0G2S87G3S33S2bA3A4S4G0S8S6aS7bSa6S7cA4G4A3A3S1S0S3S16S20A1S2A3S1S0S3S17S2aS20S26A3S2A3S1S0S3S9fS26S83A2S2A3S1S0S3S17S29S20S25A3S2A3S1S0S3S9fS25S83A2S2A3S1S0S3S91S44S5fA2S2A3S1S0S3S91S45S43A2S2A3S1S0S3S99S25S43S5fA3S2A3S1S0S3S99S26S5fS5fA3S2A3S1S0S3Sa0S6eS14S2aA1A1S10S26S32A2S3cA3S2A3S1S0S3Sa0S6eS14S29A1A1S10S25S32A2S3dA3S2A3S1S0S3S66S62S25S60S88S2A2M6A2S60S41S2A2A2S2A3S0S3S66S62S26G6A2S60S42S2A2A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
