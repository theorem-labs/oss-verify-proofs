(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "app"; "nat"; "pair"; "prod"; "nil"; "Some"; "option"; "list"; "fst"; "length"; "false"; "andb"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSplit"; "AXUnbase"; "AXSelect"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "sprop"; "ss_facts"; "valuation"; "SAlu"; "ss_next"; "ss_objs"; "SMd"; "sv_eqb"; "SPBranch"; "SPNot"; "SPUle"; "ob_base"; "ob_lo"; "sprop_below"; "sprop_eqb"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago"; "s_fs"; "E_fs"; "s_go"; "E_go"; "brest_go"; "oidxG"; "R_fs"; "Xk_fs"; "brest_fs"; "R_go"; "bdrest_fs"; "s1A"; "E_fs0"; "E_fs1"; "LAr1"; "LAr1K"; "T_fs_fz0"; "T_fs_nop0"; "T_fs_ok0"; "T_go_f0"; "T_go_ok0"; "Xk_go"; "kept_fs"; "tv_fs"; "xfb_fs"; "B_fs_fz"; "B_fs_nop"; "B_fs_ok"; "B_go_f"; "B_go_ok"; "LAr2"; "LAr2K"; "PDk_fs"; "PDk_go"; "T_fs_f0"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "T_go_f"; "T_go_ok"; "bd_go_f"; "bd_go_ok"; "hand_fs"; "hand_go"; "kept_go"; "payX_fs"; "payX_go"; "payY_fs"; "payY_go"; "qH1"; "sel_frontG"; "tv_fs_fz"; "tv_fs_nop"; "tv_fs_ok"; "tv_go"; "tv_go_f"; "tv_go_ok"; "xfb_go"; "FINi"; "VPsh"; "bd_fs_fz"; "bd_fs_nop"; "bd_fs_ok"; "f_absurd"; "nd_fs_fz"; "nd_fs_nop"; "nd_fs_ok"; "nd_go_f"; "nd_go_ok"; "nnPhi"; "passed_fs"; "passed_go"; "qHk"; "qHn"; "qHz"; "tvL_ok"; "xf_fs"; "xf_go"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago.FS"; "Pre_fs"; "nd_fail_f"; "nd_nop"; "nd_ok"; "NP"; "P_failz"; "P_nop"; "P_ok"; "nd0"; "P_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago.IR"; "Pre_ir"; "ndF"; "ndK"; "P_fail"; "P_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "bd_rest"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "vDp"; "optL"; "vBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pLNL"; "pNX"; "HNEXT"; "bA"; "pH"; "cA"; "pE"; "t_c"; "t_k"; "v_sh"; "vsP"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"; "mul"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL";
"BC_EQ"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "combine"; "filter"; "find"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_loopEf Lib_load_obj_armkit Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module IR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest. End IR.  Module IRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_pf. End IRP.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf. End FSP.

Definition oidxG (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
SbS8S6S28A2M0A1S6Lx;SceG0G0S10S30S34S12S6S28R1A3M1A1Vb;A2S30S35G1A1Vlo;A2A2Lp;SccS6S28Sd1U0SeS28S2eS1bVT;A1A1M2A2A2G2A4A3G0G0S6Lp;R1S6S28R2Ls;Li;X8x1Lp;U3e7Xbx2").
Definition s1A : sv := SAlu ALU_ADD (SVar 10) (SLit (-640)).
Definition sel_frontG (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S23S5S6Vsel;ScdS6S6S11ScbS6SdbR1A1Vsel;A3A1Li;Sd1U0Vn;A2A3A3A1").

Definition xf_go : list axform := ltac2:(tb__ "0|2|
S2S1eS21UdS26Z10A1A2S2S1eS21U7M0S26N70M1A1A2S2S1eS22G0G1A2S2S1eS20U3A1S9S1eA1A3A3A3A3").
Definition E_go : axst := Eval vm_compute in optL (apply_axforms E_ir xf_go).
Definition s_go : wsub := ltac2:(tb__ "0|1|
S2S8S25S27A2M0S7S25S27PfSb0A4S2G0S7S25S27P12SacA4S2G0S7S25S27P11SbfA4S2G0S7S25S27P13S2cSc7SaeS26Z70A1A3A4Sd3PaS1bS3cA1S1bS9eA1A3A3A3A3A3").
Definition R_go : list sobj := Eval vm_compute in optR (entails_frA E_go IR.Pre_ir s_go).
Definition PDk_go : list pdescK := liftPD IRP.PD_ir.
Definition passed_go : list (sv * sv) := [blkAR].
Definition kept_go : list (sv * sv) := Eval vm_compute in removelast tvL.
Definition tv_go : list (sv * sv) := kept_go ++ passed_go.

Definition hand_go : list bitem := Eval vm_compute in bd_subst s_go (nd_bd IR.nd0).
Definition LAr1 : bitem := ltac2:(tb__ "0|1|
S17Z1Z0S2S8S24S14A2M0S7S24S14S88S15SacA1A4S2G0S7S24S14Sc4S88A1S15SbaA1A4S2G0S7S24S14N2S15Sb9A1A4S9G0A1A3A3A3Sc5S88Z62A2A4").
Definition LAr1K : bitem := ltac2:(tb__ "0|1|
S17Z0Z1S2S8S24S14A2M0S7S24S14Sa4S15SacA1A4S2G0S7S24S14Sc4Sa4A1S15SbaA1A4S2G0S7S24S14N4S15Sb9A1A4S9G0A1A3A3A3Sc5Sa4Z44A2A4").
Definition brest_go : list bitem := ltac2:(tb__ "0|0|
S2S13S47S2S13S48Sa5A3A3").
Definition payX_go : list bitem := ltac2:(tb__ "0|0|
S2S13S8aS88A1S2S13Sa6Sa4A1S9S13A1A3A3").
Definition payY_go : list bitem := ltac2:(tb__ "0|0|
S5S13S64S2S13S47S2S13S48S9S13A1A3A3A3").
Definition Xk_go : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) vARn)) (ax_X E_go).

Lemma ago_checks1 : ltac2:(tb__ "0|a|
S1S0SbS1aA1S1fSd8S86A2SaS1aS3cA2A3S1S0SbScS28A1M0A1Sb4S3cS9eS3bA3SaG0S42A2A3S1S0S4Sb3S3cS9eS3bS42Sd0S8S8S1aS8cA2M1S2bS2bOF_;F_;M2A2M3S1aG3SdS1aS8cSdG1G2R1A3A3Ld;S5aA4A5S3A3S1S0S4Sd7SadS3bA2S3A3S1S0S4Sd4S3bSd5A2S3A3S1S0S4Sb6S3bS80S90Sa3A1A3S3A3S1S0S4S92S8eS3bS8fSa3A1A2S8dSbdS3A2M4A2S3A3S1S0S4ScaS8Sa9G2A2M5G5SaaS9eSd5S3bS2dS1bS3cA1M6A1M7SdSa9G2R1A3A5Ld;S5aA3S3A3S1S0ScS8S27S27A2A1S6fS89A3S1S0S4SabS4eS1dS3cA1A2S3A3S1S0S4Sb8Sa7S88A1M8S5S13Sa5S67A3A2S3A3S1S0S4Sb8S5S13Sa5S69A3S5S13S64S3dA3A2S3A3S1S0S4S19Sa5A1S3A3S1S0S4Sd6S2aG6A1S26Z0M9A1G9S67S69A5S3A3S1S0S4S93G7S8bS6fS87G8G4A4A2S3A3S1S0S4S18G7S3dA2S3A3S1S0S4ScfSadG7A2S3A3S0S25G7SbbA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_go_ok0 : axst := Eval vm_compute in T_afterA3 IR.Pre_ir E_go s_go R_go IR.P_ok Xk_go.
Definition T_go_f0 : axst := Eval vm_compute in T_afterA3 IR.Pre_ir E_go s_go R_go IR.P_fail Xk_go.
Definition isub_ok_go : wsub := Eval vm_compute in import_subA s_go IR.Pre_ir IR.P_ok E_go.
Definition isub_f_go : wsub := Eval vm_compute in import_subA s_go IR.Pre_ir IR.P_fail E_go.

Definition qH1 : sv := Eval vm_compute in sv_subst isub_ok_go (SVar 141).
Definition tv_go_ok : list (sv * sv) := Eval vm_compute in (kept_go ++ import_tv isub_ok_go (nd_tv IR.ndK)).
Definition bd_go_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_go (nd_bd IR.ndK) ++ brest_go).
Definition tv_go_f : list (sv * sv) := Eval vm_compute in (kept_go ++ import_tv isub_f_go (nd_tv IR.ndF)).
Definition bd_go_f : list bitem := Eval vm_compute in (bd_subst isub_f_go (nd_bd IR.ndF) ++ brest_go).
Definition nd_go_ok : ndesc := ltac2:(tb__ "0|0|
S8bS71S87S62S8dS6aS3A2A4").
Definition nd_go_f : ndesc := ltac2:(tb__ "0|0|
S8bS70S87S61S8dSbdSfA2A4").

Definition xfb_go (T : axst) : list axform := ltac2:(tb__ "0|3|
S2S1eS22U1M0Z70A2S9S1eA1M1A3ScS1eA1SafS1fVT;R1A2A1S1aSeS28S2eS1bR1A1A1A2S6S5S1eR3S2S1eS6bS2S6S3eS44SaeR2A3S2S6S3eS44S26N70A1R2A3S2S6S3eSbcS26Z8A1M2R2A3S2S6S3eSbcS26Z10A1R2A3S2S6S3eSbeS26Z0A1R2A3S9S6A1A3A3A3A3A3R1A2S2S1eS20U0A1S2S1eS20G0A1S2S1eS21U2G2A2G1A3A3A3A3A3Tn;TT1;Tpre;").
Definition B_go_ok : axst := Eval vm_compute in optL (apply_axforms T_go_ok0 (xfb_go T_go_ok0)).
Definition B_go_f : axst := Eval vm_compute in optL (apply_axforms T_go_f0 (xfb_go T_go_f0)).
Definition T_go_ok : axst := Eval vm_compute in ax_tidy B_go_ok.
Definition T_go_f : axst := Eval vm_compute in ax_tidy B_go_f.

Lemma ago_checks1_nd : ltac2:(tb__ "0|6|
S1S0S8cS8bS5S8S27S27A2M0S65Sb5Sb2S3bS9eSa2S3cA4M1S90Sa0A1A2A3S87S5S13S16G1S91Sa0A1A2S3dA3S8eG1S8fSa0A1A2A4S7dA3S1S0S8cS8bS5G0S65Sb5Sb2S3bS9eSa1S3cA4M2S90S9fA1A2A3S87S5S13S16G2S91S9fA1A2S3dA3S8eG2S8fS9fA1A2A4S7cA3S1S0S1aSa8S9eS3cS3bS42Sa2S4eA6S4dA3S1S0S1aSa8S9eS3cS3bS42Sa1S4eA6S4cA3S1S0SbS1aA1M3S1fS4dS72S4dA1A2SaS1aS56A2A3S1S0G3S1fS4cS72S4cA1A2SaS1aS55A2A3S1S0S1aSb1S56A1S60A3S1S0S1aSb1S55A1S5fA3S1S0ScG0A1M4S71S89A3S1S0G4S70S89A3S1S0ScS13A1M5S62S3dA3S1S0G5S61S3dA3S1S0S4S1cS60A1S3A3S0S4S1cS5fA1S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fs0 : axst := Eval vm_compute in leafL_at (c_fs :: cps_arm) T_go_ok c_fs 0.
Definition xf_fs : list axform := ltac2:(tb__ "0|2|
S2S1eS21U0M0S26N100M1A1A2S2S1eS22G0G1A2S9S1eA1A3A3").
Definition E_fs1 : axst := Eval vm_compute in optL (apply_axforms E_fs0 xf_fs).

Definition nnPhi : sprop := ltac2:(tb__ "0|2|
S33S2fSc8S26Z4A1Sd2Z80M0Sc1Sc2Sc3A1M1A1A2A3S2cSc7S2fSc8S26Z6A1Sd2G0Sc0G1A1A2A3S26Z1000A1A3A2").
Definition E_fs : axst := Eval vm_compute in ax_add_facts [nnPhi] E_fs1.
Definition s_fs : wsub := ltac2:(tb__ "0|0|
S2S8S25S27A2S7S25S27P13S2cSc7SaeS26Z100A1A3A4Sd3PaS1bS3aA1S1bS94A1A3A3").
Definition R_fs : list sobj := Eval vm_compute in optR (entails_frA E_fs FS.Pre_fs s_fs).
Definition PDk_fs : list pdescK := liftPD FSP.PD_fs.

Definition passed_fs : list (sv * sv) := Eval vm_compute in import_tv s_fs (nd_tv FS.nd0).
Definition kept_fs : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (existsb (fun p => sv_eqb (fst p) (fst t)) passed_fs)) tvL.
Definition tv_fs : list (sv * sv) := kept_fs ++ passed_fs.
Definition hand_fs : list bitem := Eval vm_compute in bd_subst s_fs (nd_bd FS.nd0).

Definition VPsh : list bitem := Eval vm_compute in firstn 2 (skipn 12 bd_rest).
Definition FINi : list bitem := Eval vm_compute in firstn 2 (skipn 36 bd_rest).
Definition bdrest_fs : list bitem := Eval vm_compute in (firstn 12 bd_rest ++ firstn 22 (skipn 14 bd_rest) ++ skipn 38 bd_rest).
Definition LAr2 : bitem := ltac2:(tb__ "0|2|
S17Z1Z0S2S8S24S14A2M0S7S24S14S88S15SacA1A4S2G0S7S24S14Sc4S88A1M1S15SbaA1A4S2G0S7S24S14G1S15Sb9A1A4S9G0A1A3A3A3Sc5Sc6Z2S88A2Z3c6A2A4").
Definition LAr2K : bitem := ltac2:(tb__ "0|1|
S17Z0Z1S2S8S24S14A2M0S7S24S14Sa4S15SacA1A4S2G0S7S24S14Sc4Sa4A1S15SbaA1A4S2G0S7S24S14N4S15Sb9A1A4S9G0A1A3A3A3Sc5Sa4Z88A2A4").
Definition brest_fs : list bitem := ltac2:(tb__ "0|0|
S2S13S57S2S13S58S43A3A3").
Definition payX_fs : list bitem := ltac2:(tb__ "0|0|
S5S13S73S5S13S74S2S13S47S2S13S48S9S13A1A3A3A3A3").
Definition payY_fs : list bitem := ltac2:(tb__ "0|0|
S5S13S63S2S13S57S2S13S58S9S13A1A3A3A3").
Definition Xk_fs : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_fs)) (ax_X E_fs).

Lemma ago_checks2 : ltac2:(tb__ "0|b|
S1S0S24S38S1bS45A1A1Sd9A3S1S0S4S1cS45A1S3A3S1S0SbS1aA1S1fS45S85A2SaS1aS46A2A3S1S0S1aSdaS46S5S29S2S29S7eS9S29A1A3S2aS1bS46A1M0A1A3M1A2S3aA3S1S0S4ScaS29S36S2dG0A1A1G1A3S3A3S1S0SbScS28A1M2A1Sb4S3aS94S39A3SaG2S3fA2A3S1S0S4Sb3S3aS94S39S3fSd0S8S8S1aS8cA2M3S2bS2bOF_;F_;M4A2M5S1aG5SdS1aS8cSdG3G4R1A3A3Ld;S59A4A5S3A3S1S0S4Sd7SadS39A2S3A3S1S0S4Sd4S39S98A2S3A3S1S0S4Sb6S39S7fS90S9cA1A3S3A3S1S0S4S92S8eS39S8fS9cA1A2S8dS6aS3A2M6A2S3A3S1S0S4ScaS8Sa9G4A2M7G7SaaS94S98S39S2dS1bS3aA1M8A1M9SdSa9G4R1A3A5Ld;S59A3S3A3S1S0S4Sb7S89S50A2S3A3S1S0S4Sb7S50S89A2S3A3S1S0S4SabS40S1dS3aA1A2S3A3S1S0S4Sb8S3dS5S13S43S66A3A2S3A3S1S0S4Sb8S5S13S43S68A3S5S13S63S41A3A2S3A3S1S0S4S19S43A1S3A3S1S0S4Sd6S2aG8A1S26Z0MaA1GaS66S68A5S3A3S1S0S4S93G9S8bS50S87S3dG6A4A2S3A3S1S0S4S18G9S41A2S3A3S1S0S4ScfSadG9A2S3A3S0S4ScfSbbG9A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_fs_nop0 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs s_fs R_fs FS.P_nop Xk_fs.
Definition T_fs_ok0 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs s_fs R_fs FS.P_ok Xk_fs.
Definition T_fs_f0 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs s_fs R_fs FS.P_fail Xk_fs.
Definition T_fs_fz0 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs s_fs R_fs FS.P_failz Xk_fs.
Definition isub_nop : wsub := Eval vm_compute in import_subA s_fs FS.Pre_fs FS.P_nop E_fs.
Definition isub_ok : wsub := Eval vm_compute in import_subA s_fs FS.Pre_fs FS.P_ok E_fs.
Definition isub_fz : wsub := Eval vm_compute in import_subA s_fs FS.Pre_fs FS.P_failz E_fs.
Definition qHn : sv := Eval vm_compute in sv_subst isub_nop FS.vHD.
Definition qHk : sv := Eval vm_compute in sv_subst isub_ok FS.qHD.
Definition qHz : sv := Eval vm_compute in sv_subst isub_fz FS.qHD.
Definition tv_fs_nop : list (sv * sv) := Eval vm_compute in (kept_fs ++ import_tv isub_nop (nd_tv FS.nd_nop)).
Definition bd_fs_nop : list bitem := Eval vm_compute in (bd_subst isub_nop (nd_bd FS.nd_nop) ++ brest_fs).
Definition tv_fs_ok : list (sv * sv) := Eval vm_compute in (kept_fs ++ import_tv isub_ok (nd_tv FS.nd_ok)).
Definition bd_fs_ok : list bitem := Eval vm_compute in (bd_subst isub_ok (nd_bd FS.nd_ok) ++ brest_fs).
Definition tv_fs_fz : list (sv * sv) := Eval vm_compute in (kept_fs ++ import_tv isub_fz (nd_tv FS.nd_fail_f)).
Definition bd_fs_fz : list bitem := Eval vm_compute in (bd_subst isub_fz (nd_bd FS.nd_fail_f) ++ brest_fs).
Definition nd_fs_nop : ndesc := ltac2:(tb__ "0|0|
S8bS6dS87S76S8dS82S3A2A4").
Definition nd_fs_ok : ndesc := ltac2:(tb__ "0|0|
S8bS6eS87S77S8dS81S3A2A4").
Definition nd_fs_fz : ndesc := ltac2:(tb__ "0|0|
S8bS6cS87S75S8dS83SfA2A4").
Definition xfb_fs (T : axst) : list axform := ltac2:(tb__ "0|1|
S2S1eS22U1Z100A2S9S1eA1M0A3ScS1eA1SafS1fVT;R1A2A1S1aSeS28S2eS1bR1A1A1A2S6S5S1eR3S2S1eS6bS2S6S3eS44SaeR2A3S2S6S3eS44S26N100A1R2A3S9S6A1A3A3R1A2S2S1eS20U0A1G0A3A3A3Tn;TT1;Tpre;").
Definition B_fs_nop : axst := Eval vm_compute in optL (apply_axforms T_fs_nop0 (xfb_fs T_fs_nop0)).
Definition B_fs_ok : axst := Eval vm_compute in optL (apply_axforms T_fs_ok0 (xfb_fs T_fs_ok0)).
Definition B_fs_fz : axst := Eval vm_compute in optL (apply_axforms T_fs_fz0 (xfb_fs T_fs_fz0)).
Definition T_fs_nop : axst := Eval vm_compute in ax_tidy B_fs_nop.
Definition T_fs_ok : axst := Eval vm_compute in ax_tidy B_fs_ok.
Definition T_fs_fz : axst := Eval vm_compute in ax_tidy B_fs_fz.

Definition sh_ent_ok : sv * sv := Eval vm_compute in nth 7 (import_tv isub_ok (nd_tv FS.nd_ok)) (SLit 0, SLit 0).
Definition tvL_ok : list (sv * sv) := Eval vm_compute in map (fun t => if sv_eqb (fst t) (t_d (v_sh vsP)) then sh_ent_ok else t) tvL.

Definition f_absurd : sprop := ltac2:(tb__ "0|1|
S32S31Sc9S26Z0A1M0G0A3A1").

Lemma ago_checks2_nd : ltac2:(tb__ "0|5|
S1S0S8cS8bS5S8S27S27A2M0S4fSb5Sb2S39S94S9aS3aA4M1S90S96A1A2A3S87S5S13S16G1S91S96A1A2S41A3S8eG1S8fS96A1A2A4S7aA3S1S0S8cS8bS5G0S4fSb5Sb2S39S94S9bS3aA4M2S90S97A1A2A3S87S5S13S16G2S91S97A1A2S41A3S8eG2S8fS97A1A2A4S7bA3S1S0S8cS8bS5G0S4fSb5Sb2S39S94S99S3aA4M3S90S95A1A2A3S87S5S13S16G3S91S95A1A2S41A3S8eG3S8fS95A1A2A4S79A3S1S0S1aSa8S94S3aS39S3fS9aS40A6S4aA3S1S0S1aSa8S94S3aS39S3fS9bS40A6S4bA3S1S0S1aSa8S94S3aS39S3fS9dS40A6S5bA3S1S0S1aSa8S94S3aS39S3fS99S40A6S49A3S1S0SbS1aA1M4S1fS4aS51S4aA1A2SaS1aS53A2A3S1S0G4S1fS4bS51S4bA1A2SaS1aS54A2A3S1S0G4S1fS49S51S49A1A2SaS1aS52A2A3S1S0S1aSb1S53A1S5dA3S1S0S1aSb1S54A1S5eA3S1S0S1aSb1S52A1S5cA3S1S0S4Sb7S6dS89A2S3A3S1S0S4Sb7S6eS84A2S3A3S1S0S4Sb7S6cS89A2S3A3S1S0S4ScbS29S37S78A1S2aS1bS5bA1A1A3S3A3S1S0S4S1cS5dA1S3A3S1S0S4S1cS5eA1S3A3S0S4S1cS5cA1S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
