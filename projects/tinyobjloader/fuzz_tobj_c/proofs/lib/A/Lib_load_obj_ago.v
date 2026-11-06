(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_034.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "app"; "nat"; "prod"; "nil"; "pair"; "Some"; "option"; "list"; "fst"; "length"; "false"; "andb"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSplit"; "AXSelect"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "sprop"; "ss_facts"; "valuation"; "SAlu"; "ss_next"; "ss_objs"; "SMd"; "sv_eqb"; "SPBranch"; "SPNot"; "SPUle"; "ob_base"; "ob_lo"; "sprop_below"; "sprop_eqb"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago"; "s_fs"; "E_fs"; "s_go"; "E_go"; "brest_go"; "R_fs"; "oidxG"; "Xk_fs"; "brest_fs"; "R_go"; "bdrest_fs"; "s1A"; "E_fs0"; "E_fs1"; "LAr1"; "LAr1K"; "T_fs_fz0"; "T_fs_nop0"; "T_fs_ok0"; "T_go_f0"; "T_go_ok0"; "Xk_go"; "kept_fs"; "tv_fs"; "xfb_fs"; "B_fs_fz"; "B_fs_nop"; "B_fs_ok"; "B_go_f"; "B_go_ok"; "LAr2"; "LAr2K"; "PDk_fs"; "PDk_go"; "T_fs_f0"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "T_go_f"; "T_go_ok"; "bd_go_f"; "bd_go_ok"; "hand_fs"; "hand_go"; "kept_go"; "payX_fs"; "payX_go"; "payY_fs"; "payY_go"; "qH1"; "sel_frontG"; "tv_fs_fz"; "tv_fs_nop"; "tv_fs_ok"; "tv_go"; "tv_go_f"; "tv_go_ok"; "xfb_go"; "FINi"; "VPsh"; "bd_fs_fz"; "bd_fs_nop"; "bd_fs_ok"; "f_absurd"; "nd_fs_fz"; "nd_fs_nop"; "nd_fs_ok"; "nd_go_f"; "nd_go_ok"; "nnPhi"; "passed_fs"; "passed_go"; "qHk"; "qHn"; "qHz"; "tvL_ok"; "xf_fs"; "xf_go"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_tv"; "nd_bd"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago.FS"; "Pre_fs"; "nd_fail_f"; "nd_nop"; "nd_ok"; "NP"; "P_failz"; "P_nop"; "P_ok"; "nd0"; "P_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_ago.IR"; "Pre_ir"; "ndF"; "ndK"; "P_fail"; "P_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "bd_rest"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "optL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pLNL"; "pNX"; "HNEXT"; "bA"; "pH"; "t_c"; "t_k"; "v_sh"; "vsP"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "sub"; "mul"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_EQ";
"@Stdlib.Lists.List"; "forallb"; "existsb"; "combine"; "filter"; "find"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_ir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "c_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_finalize_shape Lib_finalize_shape_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module IR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest. End IR.  Module IRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_pf. End IRP.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include Lib_finalize_shape_pf. End FSP.

Definition oidxG (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
SbS7S6S28A2M0A1S6Lx;ScbG0G0S10S30S34S12S6S28R1A3M1A1Vb;A2S30S35G1A1Vlo;A2A2Lp;Sc9S6S28SceU0SeS28S2eS1bVT;A1A1M2A2A2G2A4A3G0G0S6Lp;R1S6S28R2Ls;Li;X7x1Lp;U3e7Xbx2").
Definition s1A : sv := SAlu ALU_ADD (SVar 10) (SLit (-512)).
Definition sel_frontG (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S23S5S6Vsel;ScaS6S6S11Sc8S6Sd8R1A1Vsel;A3A1Li;SceU0Vn;A2A3A3A1").

Definition xf_go : list axform := ltac2:(tb__ "0|2|
S3S1eS22UdS26Z10A1A2S3S1eS22U7M0S26N50M1A1A2S3S1eS20G0G1A2S8S1eA1A3A3A3").
Definition E_go : axst := Eval vm_compute in optL (apply_axforms E_ir xf_go).
Definition s_go : wsub := ltac2:(tb__ "0|0|
S3S7S25S27A2S9S25S27P13S2cSc4Sb5S26Z50A1A3A4Sd0PaS1bS3cA1S1bS9eA1A3A3").
Definition R_go : list sobj := Eval vm_compute in optR (entails_frA E_go IR.Pre_ir s_go).
Definition PDk_go : list pdescK := liftPD IRP.PD_ir.
Definition passed_go : list (sv * sv) := [blkAR].
Definition kept_go : list (sv * sv) := Eval vm_compute in removelast tvL.
Definition tv_go : list (sv * sv) := kept_go ++ passed_go.

Definition hand_go : list bitem := Eval vm_compute in bd_subst s_go (nd_bd IR.nd0).
Definition LAr1 : bitem := ltac2:(tb__ "0|1|
S17Z1Z0S3S7S24S14A2M0S9S24S14S88S15Sb6A1A4S3G0S9S24S14Sc1S88A1S15Sb9A1A4S3G0S9S24S14N2S15Sb8A1A4S8G0A1A3A3A3Sc2S88Z62A2A4").
Definition LAr1K : bitem := ltac2:(tb__ "0|1|
S17Z0Z1S3S7S24S14A2M0S9S24S14Sa4S15Sb6A1A4S3G0S9S24S14Sc1Sa4A1S15Sb9A1A4S3G0S9S24S14N4S15Sb8A1A4S8G0A1A3A3A3Sc2Sa4Z44A2A4").
Definition brest_go : list bitem := ltac2:(tb__ "0|0|
S3S13S47S3S13S48Sa5A3A3").
Definition payX_go : list bitem := ltac2:(tb__ "0|0|
S3S13S8aS88A1S3S13Sa6Sa4A1S8S13A1A3A3").
Definition payY_go : list bitem := ltac2:(tb__ "0|0|
S5S13S64S3S13S47S3S13S48S8S13A1A3A3A3").
Definition Xk_go : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) vARn)) (ax_X E_go).

Lemma ago_checks1 : ltac2:(tb__ "0|a|
S1S0SbS1aA1S1fSd5S86A2SaS1aS3cA2A3S1S0SbScS28A1M0A1SafS3cS9eS3bA3SaG0S42A2A3S1S0S4SaeS3cS9eS3bS42ScdS7S7S1aS8cA2M1S2bS2bOF_;F_;M2A2M3S1aG3SdS1aS8cSdG1G2R1A3A3Ld;S5aA4A5S2A3S1S0S4Sd4Sb4S3bA2S2A3S1S0S4Sd1S3bSd2A2S2A3S1S0S4Sb1S3bS80S90Sa3A1A3S2A3S1S0S4S92S8eS3bS8fSa3A1A2S8dSbcS2A2M4A2S2A3S1S0S4Sc7S7Sa9G2A2M5G5SaaS9eSd2S3bS2dS1bS3cA1M6A1M7SdSa9G2R1A3A5Ld;S5aA3S2A3S1S0ScS7S27S27A2A1S6fS89A3S1S0S4SabS4eS1dS3cA1A2S2A3S1S0S4Sb3Sa7S88A1M8S5S13Sa5S67A3A2S2A3S1S0S4Sb3S5S13Sa5S69A3S5S13S64S3dA3A2S2A3S1S0S4S19Sa5A1S2A3S1S0S4Sd3S2aG6A1S26Z0M9A1G9S67S69A5S2A3S1S0S4S93G7S8bS6fS87G8G4A4A2S2A3S1S0S4S18G7S3dA2S2A3S1S0S4SccSb4G7A2S2A3S0S25G7SbaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
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
S8bS71S87S62S8dS6aS2A2A4").
Definition nd_go_f : ndesc := ltac2:(tb__ "0|0|
S8bS70S87S61S8dSbcSfA2A4").

Definition xfb_go (T : axst) : list axform := ltac2:(tb__ "0|2|
S3S1eS20U1M0Z50A2S8S1eA1M1A3ScS1eA1Sb7S1fVT;R1A2A1S1aSeS28S2eS1bR1A1A1A2S6S5S1eR3S3S1eS6bS3S6S3fS44Sb5R2A3S3S6S3fS44S26N50A1R2A3S3S6S3fSbbS26Z8A1R2A3S3S6S3fSbbS26Z10A1R2A3S8S6A1A3A3A3A3R1A2S3S1eS21U0A1S3S1eS21G0A1G1A3A3A3A3Tn;TT1;Tpre;").
Definition B_go_ok : axst := Eval vm_compute in optL (apply_axforms T_go_ok0 (xfb_go T_go_ok0)).
Definition B_go_f : axst := Eval vm_compute in optL (apply_axforms T_go_f0 (xfb_go T_go_f0)).
Definition T_go_ok : axst := Eval vm_compute in ax_tidy B_go_ok.
Definition T_go_f : axst := Eval vm_compute in ax_tidy B_go_f.

Lemma ago_checks1_nd : ltac2:(tb__ "0|6|
S1S0S8cS8bS5S7S27S27A2M0S65Sb0SadS3bS9eSa2S3cA4M1S90Sa0A1A2A3S87S5S13S16G1S91Sa0A1A2S3dA3S8eG1S8fSa0A1A2A4S7dA3S1S0S8cS8bS5G0S65Sb0SadS3bS9eSa1S3cA4M2S90S9fA1A2A3S87S5S13S16G2S91S9fA1A2S3dA3S8eG2S8fS9fA1A2A4S7cA3S1S0S1aSa8S9eS3cS3bS42Sa2S4eA6S4dA3S1S0S1aSa8S9eS3cS3bS42Sa1S4eA6S4cA3S1S0SbS1aA1M3S1fS4dS72S4dA1A2SaS1aS56A2A3S1S0G3S1fS4cS72S4cA1A2SaS1aS55A2A3S1S0S1aSacS56A1S60A3S1S0S1aSacS55A1S5fA3S1S0ScG0A1M4S71S89A3S1S0G4S70S89A3S1S0ScS13A1M5S62S3dA3S1S0G5S61S3dA3S1S0S4S1cS60A1S2A3S0S4S1cS5fA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fs0 : axst := Eval vm_compute in leafL_at (c_fs :: cps_arm) T_go_ok c_fs 0.
Definition xf_fs : list axform := ltac2:(tb__ "0|2|
S3S1eS22U0M0S26Nd0M1A1A2S3S1eS20G0G1A2S8S1eA1A3A3").
Definition E_fs1 : axst := Eval vm_compute in optL (apply_axforms E_fs0 xf_fs).

Definition nnPhi : sprop := ltac2:(tb__ "0|2|
S33S2fSc5S26Z4A1ScfZ80M0SbeSbfSc0A1M1A1A2A3S2cSc4S2fSc5S26Z6A1ScfG0SbdG1A1A2A3S26Z1000A1A3A2").
Definition E_fs : axst := Eval vm_compute in ax_add_facts [nnPhi] E_fs1.
Definition s_fs : wsub := ltac2:(tb__ "0|0|
S3S7S25S27A2S9S25S27P13S2cSc4Sb5S26Zd0A1A3A4Sd0PaS1bS3aA1S1bS94A1A3A3").
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
S17Z1Z0S3S7S24S14A2M0S9S24S14S88S15Sb6A1A4S3G0S9S24S14Sc1S88A1M1S15Sb9A1A4S3G0S9S24S14G1S15Sb8A1A4S8G0A1A3A3A3Sc2Sc3Z2S88A2Z3c6A2A4").
Definition LAr2K : bitem := ltac2:(tb__ "0|1|
S17Z0Z1S3S7S24S14A2M0S9S24S14Sa4S15Sb6A1A4S3G0S9S24S14Sc1Sa4A1S15Sb9A1A4S3G0S9S24S14N4S15Sb8A1A4S8G0A1A3A3A3Sc2Sa4Z88A2A4").
Definition brest_fs : list bitem := ltac2:(tb__ "0|0|
S3S13S57S3S13S58S43A3A3").
Definition payX_fs : list bitem := ltac2:(tb__ "0|0|
S5S13S73S5S13S74S3S13S47S3S13S48S8S13A1A3A3A3A3").
Definition payY_fs : list bitem := ltac2:(tb__ "0|0|
S5S13S63S3S13S57S3S13S58S8S13A1A3A3A3").
Definition Xk_fs : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_fs)) (ax_X E_fs).

Lemma ago_checks2 : ltac2:(tb__ "0|b|
S1S0S24S38S1bS45A1A1Sd6A3S1S0S4S1cS45A1S2A3S1S0SbS1aA1S1fS45S85A2SaS1aS46A2A3S1S0S1aSd7S46S5S29S3S29S7eS8S29A1A3S2aS1bS46A1M0A1A3M1A2S3aA3S1S0S4Sc7S29S36S2dG0A1A1G1A3S2A3S1S0SbScS28A1M2A1SafS3aS94S39A3SaG2S3eA2A3S1S0S4SaeS3aS94S39S3eScdS7S7S1aS8cA2M3S2bS2bOF_;F_;M4A2M5S1aG5SdS1aS8cSdG3G4R1A3A3Ld;S59A4A5S2A3S1S0S4Sd4Sb4S39A2S2A3S1S0S4Sd1S39S98A2S2A3S1S0S4Sb1S39S7fS90S9cA1A3S2A3S1S0S4S92S8eS39S8fS9cA1A2S8dS6aS2A2M6A2S2A3S1S0S4Sc7S7Sa9G4A2M7G7SaaS94S98S39S2dS1bS3aA1M8A1M9SdSa9G4R1A3A5Ld;S59A3S2A3S1S0S4Sb2S89S50A2S2A3S1S0S4Sb2S50S89A2S2A3S1S0S4SabS40S1dS3aA1A2S2A3S1S0S4Sb3S3dS5S13S43S66A3A2S2A3S1S0S4Sb3S5S13S43S68A3S5S13S63S41A3A2S2A3S1S0S4S19S43A1S2A3S1S0S4Sd3S2aG8A1S26Z0MaA1GaS66S68A5S2A3S1S0S4S93G9S8bS50S87S3dG6A4A2S2A3S1S0S4S18G9S41A2S2A3S1S0S4SccSb4G9A2S2A3S0S4SccSbaG9A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
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
S8bS6dS87S76S8dS82S2A2A4").
Definition nd_fs_ok : ndesc := ltac2:(tb__ "0|0|
S8bS6eS87S77S8dS81S2A2A4").
Definition nd_fs_fz : ndesc := ltac2:(tb__ "0|0|
S8bS6cS87S75S8dS83SfA2A4").
Definition xfb_fs (T : axst) : list axform := ltac2:(tb__ "0|1|
S3S1eS20U1Zd0A2S8S1eA1M0A3ScS1eA1Sb7S1fVT;R1A2A1S1aSeS28S2eS1bR1A1A1A2S6S5S1eR3S3S1eS6bS3S6S3fS44Sb5R2A3S3S6S3fS44S26Nd0A1R2A3S8S6A1A3A3R1A2S3S1eS21U0A1G0A3A3A3Tn;TT1;Tpre;").
Definition B_fs_nop : axst := Eval vm_compute in optL (apply_axforms T_fs_nop0 (xfb_fs T_fs_nop0)).
Definition B_fs_ok : axst := Eval vm_compute in optL (apply_axforms T_fs_ok0 (xfb_fs T_fs_ok0)).
Definition B_fs_fz : axst := Eval vm_compute in optL (apply_axforms T_fs_fz0 (xfb_fs T_fs_fz0)).
Definition T_fs_nop : axst := Eval vm_compute in ax_tidy B_fs_nop.
Definition T_fs_ok : axst := Eval vm_compute in ax_tidy B_fs_ok.
Definition T_fs_fz : axst := Eval vm_compute in ax_tidy B_fs_fz.

Definition sh_ent_ok : sv * sv := Eval vm_compute in nth 7 (import_tv isub_ok (nd_tv FS.nd_ok)) (SLit 0, SLit 0).
Definition tvL_ok : list (sv * sv) := Eval vm_compute in map (fun t => if sv_eqb (fst t) (t_d (v_sh vsP)) then sh_ent_ok else t) tvL.

Definition f_absurd : sprop := ltac2:(tb__ "0|1|
S32S31Sc6S26Z0A1M0G0A3A1").

Lemma ago_checks2_nd : ltac2:(tb__ "0|5|
S1S0S8cS8bS5S7S27S27A2M0S4fSb0SadS39S94S9aS3aA4M1S90S96A1A2A3S87S5S13S16G1S91S96A1A2S41A3S8eG1S8fS96A1A2A4S7aA3S1S0S8cS8bS5G0S4fSb0SadS39S94S9bS3aA4M2S90S97A1A2A3S87S5S13S16G2S91S97A1A2S41A3S8eG2S8fS97A1A2A4S7bA3S1S0S8cS8bS5G0S4fSb0SadS39S94S99S3aA4M3S90S95A1A2A3S87S5S13S16G3S91S95A1A2S41A3S8eG3S8fS95A1A2A4S79A3S1S0S1aSa8S94S3aS39S3eS9aS40A6S4aA3S1S0S1aSa8S94S3aS39S3eS9bS40A6S4bA3S1S0S1aSa8S94S3aS39S3eS9dS40A6S5bA3S1S0S1aSa8S94S3aS39S3eS99S40A6S49A3S1S0SbS1aA1M4S1fS4aS51S4aA1A2SaS1aS53A2A3S1S0G4S1fS4bS51S4bA1A2SaS1aS54A2A3S1S0G4S1fS49S51S49A1A2SaS1aS52A2A3S1S0S1aSacS53A1S5dA3S1S0S1aSacS54A1S5eA3S1S0S1aSacS52A1S5cA3S1S0S4Sb2S6dS89A2S2A3S1S0S4Sb2S6eS84A2S2A3S1S0S4Sb2S6cS89A2S2A3S1S0S4Sc8S29S37S78A1S2aS1bS5bA1A1A3S2A3S1S0S4S1cS5dA1S2A3S1S0S4S1cS5eA1S2A3S0S4S1cS5cA1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
