(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "pair"; "nil"; "app"; "prod"; "option"; "list"; "Some"; "fst"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "sprop"; "SLit"; "sobj"; "ss_next"; "valuation"; "SPUle"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "ax_X"; "la_state"; "sym_runA"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af"; "s_f"; "E_f"; "E_f1"; "R_f"; "brest_f"; "qAf"; "T_f_f"; "T_f_f0"; "T_f_ok"; "T_f_ok0"; "Xk_f"; "bd_f"; "hand_f"; "payC_f"; "tv_f"; "B_f_f"; "B_f_ok"; "LAr_f"; "PDk_f"; "gsub_f"; "kept_f"; "payY_f"; "xfb_f"; "bd_f_f"; "bd_f_ok"; "bdrest_f"; "nd_f_f"; "nd_f_ok"; "passed_f"; "payX_f"; "qCURf"; "room_f"; "tv_f_f"; "tv_f_ok"; "xf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "bd_wpos"; "BI"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af.HF"; "Pre_hf"; "cVF"; "nd0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "h0"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "A1"; "tvL"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "gCO"; "gMI"; "gRP"; "gTR"; "gTS"; "pCP"; "HNEXT"; "gFV"; "gMM"; "gSG"; "pLNL"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "am_eqb"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "NPH"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af.HFE"; "P_fail"; "P_ok"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vDp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af.HFI"; "PD_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "AK1"; "LAK"; "bdA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_latch";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_armkit Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Module HF. Include Lib_handle_f_defs. End HF.
Module HF2. Include Lib_handle_f_s2. End HF2.
Module HFE. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi. End HFE.
Module HFI. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o0.Lib_handle_f_iface. End HFI.

Definition xf_f : list axform := ltac2:(tb__ "0|2|
S0S53S58U7M0S12N180M1A1A2S0S53S55G0G1A2S5S53A1A3A3").
Definition E_f1 : axst := Eval vm_compute in optL (apply_axforms E_hf xf_f).
Definition gsub_f : wsub := ltac2:(tb__ "0|1|
S0S7S22SfA2M0S4S22SfP81S60A4S0G0S4S22SfP84S62A4S0G0S4S22SfP87S63A4S0G0S4S22SfP8aS64A4S0G0S4S22SfP8dS61A4S0G0S4S22SfP8eS67A4S0G0S4S22SfP8fS68A4S0G0S4S22SfP95S69A4S5G0A1A3A3A3A3A3A3A3A3").
Definition s_f1 : wsub := ltac2:(tb__ "0|1|
S6S7S22SfA2M0S37S0G0S4S22SfS59S5fA4S0G0S4S22SfP13S10S51S83S12Z180A1A3A4S86PaS1cS26A1S1cS4eA1A3A3A3A3").
Definition optP (x : option sprop) : sprop := ltac2:(tb__ "0|1|
S8S11A1S11Lx;Vx;S11R1Lp;S16S12Z0A1M0G0A2X8x2").

Definition room_f : list sprop := Eval vm_compute in map (fun p => optP (sprop_subst s_f1 p)) [HF.room_r 12 3 36 HF.mi_c tI; HF.room_r 12 3 36 HF.mi_n tI; HF.room_r 1 37 37 HF.ts_n tI].
Definition E_f : axst := Eval vm_compute in ax_add_facts room_f E_f1.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S6S7S22SfA2M0S37S0G0S4S22SfS59S5fA4S0G0S4S22SfP13S10S51S83S12Z180A1A3A4S86PaS1cS25A1S1cS4eA1A3A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_f HF.Pre_hf s_f).
Definition PDk_f : list pdescK := ltac2:(tb__ "0|0|
S9dS7dS94S59S2A3A1").

Definition idx_p : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U7S0S1U8S0S1U9S0S1UaS0S1UeS0S1UfS0S1U10S0S1U11S5S1A1A3A3A3A3A3A3A3A3A3").
Definition passed_f : list (sv * sv) := Eval vm_compute in map (fun i => nth i tvL (SLit 0, SLit 0)) idx_p.
Definition kept_f : list (sv * sv) := Eval vm_compute in map (fun i => nth i tvL (SLit 0, SLit 0)) (List.filter (fun i => negb (existsb (Nat.eqb i) idx_p)) (seq 0 (length tvL))).
Definition tv_f : list (sv * sv) := kept_f ++ passed_f.

Definition idx_b : list nat := ltac2:(tb__ "0|0|
S0S1UeS0S1UfS0S1U10S0S1U11S0S1U12S0S1U13S0S1U14S0S1U15S0S1U1cS0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U22S0S1U23S5S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition bdpass_f : list bitem := Eval vm_compute in map (fun i => nth i bd_rest (LA 0)) idx_b.
Definition bdrest_f : list bitem := Eval vm_compute in map (fun i => nth i bd_rest (LA 0)) (List.filter (fun i => negb (existsb (Nat.eqb i) idx_b)) (seq 0 (length bd_rest))).
Definition LAr_f : bitem := ltac2:(tb__ "0|1|
S4cZ1Z0S0S7S23S48A2M0S4S23S48S5cS49S84A1A4S0G0S4S23S48S91S5cA1S49S6bA1A4S0G0S4S23S48S91S4fA1S49S6aA1A4S5G0A1A3A3A3S5cA4").
Definition brest_f : list bitem := ltac2:(tb__ "0|0|
S0S47S35S0S47S96S95A1S3dA3A3").
Definition hand_f : list bitem := Eval vm_compute in bd_subst s_f (nd_bd (ndh h0 true HF.nd0)).
Definition bd_f : list bitem := Eval vm_compute in (bdpass_f ++ LA A1 :: LAK AK1 :: bdrest_f).
Definition Xk_f : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_f)) (ax_X E_f).

Definition payX_f : list bitem := [LA A1].
Definition payY_f : list bitem := ltac2:(tb__ "0|0|
S0S47S35S0S47S78S47U0S30S5eZ0A1A4S5S47A1A3A3").
Definition payC_f : list bitem := Eval vm_compute in (bdpass_f ++ LAK AK1 :: bdrest_f).

Lemma af_checks : ltac2:(tb__ "0|a|
SeSdS8S1bA1S54S98S46A2SaS1bS26A2A3SeSdS1bS9cS26S6S11S43S18S1cS26A1M0A1A3M1A2S25A3SeSdS3S90S11S17S14G0A1A1G1A3S2A3SeSdS8S9S13A1M2A1S89S25S4eS24A3SaG2S27A2A3SeSdS3S88S25S4eS24S27S77S7S7S1bS6dA2M3S15S15OF_;F_;M4A2M5S1bG5SbS1bS6dSbG3G4R1A3A3Ld;S36A4A5S2A3SeSdS3S9eS82S24A2S2A3SeSdS3S9bS24S76A2S2A3SeSdS3S8bS24S40S72S7cS59S2S50A3M6A1A3S2A3SeSdS3S73S6fS24S70G6A1A2S6eS5fS2A2M7A2S2A3SeSdS3S90S7S8dG4A2M8G8S8eS4eS76S24S14S1cS25A1A1M9SbS8dG4R1A3A5Ld;S36A3S2A3SeSdS3S7bS5dS32A2S2A3SeSdS3S7bS32S5dA2S2A3SeSdS3S7aS97S5cA1S2fA2S2A3SeSdS3S8fS2eS1fS25A1A2S2A3SeSdS9S47A1S4aS24S71G6A1A2S30A3SeSdS3S7aS2fS6S47S31S41A3A2S2A3SeSdS3S7aS6S47S31S39A3S6S47S30S28A3A2S2A3SeSdS3S4bS31A1S2A3SeSdS3S4bS39A1S2A3SeSdS3S74G9S6cS32S5bS2fG7A4A2S2A3SeSdS3S4dG9S28A2S2A3SeSdS3S9fS82G9A2S2A3SeSdS22G9S66A3SdSfS9aS24P10A2S65A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_f_ok0 : axst := Eval vm_compute in T_afterA3 HF.Pre_hf E_f s_f R_f HFE.P_ok Xk_f.
Definition T_f_f0 : axst := Eval vm_compute in T_afterA3 HF.Pre_hf E_f s_f R_f HFE.P_fail Xk_f.
Definition isub_ok_f : wsub := Eval vm_compute in import_subA s_f HF.Pre_hf HFE.P_ok E_f.
Definition isub_f_f : wsub := Eval vm_compute in import_subA s_f HF.Pre_hf HFE.P_fail E_f.
Definition tv_f_ok : list (sv * sv) := Eval vm_compute in (kept_f ++ import_tv isub_ok_f (nd_tv HFE.nd_ok)).
Definition bd_f_ok : list bitem := Eval vm_compute in (bd_subst isub_ok_f (nd_bd HFE.nd_ok) ++ brest_f).
Definition tv_f_f : list (sv * sv) := Eval vm_compute in (kept_f ++ import_tv isub_f_f (nd_tv HFE.nd_fail)).
Definition bd_f_f : list bitem := Eval vm_compute in (bd_subst isub_f_f (nd_bd HFE.nd_fail) ++ brest_f).
Definition nd_f_ok : ndesc := ltac2:(tb__ "0|0|
S6cS45S5bS3cS6eS5fS2A2A4").
Definition nd_f_f : ndesc := ltac2:(tb__ "0|0|
S6cS44S5bS3bS6eS5fS2A2A4").
Definition xfb_f (T : axst) : list axform := ltac2:(tb__ "0|2|
S0S53S55U0M0Z180A2S0S53S57S0S1G0S0S1U3S0S1U1S0S1U2S79U4M1S92ScS13S19S1cVT;A1A1A2G1A2A2A3A3A3A3A1S0S53S56G0A1S5S53A1A3A3A3").
Definition B_f_ok : axst := Eval vm_compute in optL (apply_axforms T_f_ok0 (xfb_f T_f_ok0)).
Definition B_f_f : axst := Eval vm_compute in optL (apply_axforms T_f_f0 (xfb_f T_f_f0)).
Definition T_f_ok : axst := Eval vm_compute in ax_tidy B_f_ok.
Definition T_f_f : axst := Eval vm_compute in ax_tidy B_f_f.

Definition qCURf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCUR.
Definition qAf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qA.
Definition gMI' : sv := ltac2:(tb__ "0|0|
S10S51S61S75Z3S29A2A3").   Definition gFV' : sv := SAlu ALU_ADD gFV qAf.   Definition gMM' : sv := SAlu ALU_ADD gMM qAf.   Definition gSG' : sv := SAlu ALU_ADD gSG qAf.
Definition gCO' : sv := ltac2:(tb__ "0|0|
S10S51S60S10S52S42S65A3A3").
Definition gRP' : sv := ltac2:(tb__ "0|0|
S10S51S62S75Z3S29A2A3").   Definition gTR' : sv := ltac2:(tb__ "0|0|
S10S51S63S75Z3S29A2A3").   Definition gTS' : sv := ltac2:(tb__ "0|0|
S10S51S64S75Z25S29A2A3").
Lemma af_checks_nd : ltac2:(tb__ "0|9|
SeSdS6dS6cS6S7SfSfA2M0S38S8aS87S24S4eS7fS25A4M1S72S7cS59S2S81A3M2A1A2A3S5bS6S47S4aG1S71G2A1A2S28A3S6fG1S70G2A1A2A4S3fA3SeSdS6dS6cS6G0S38S8aS87S24S4eS7eS25A4M3S72S7cS59S2S80A3M4A1A2A3S5bS6S47S4aG3S71G4A1A2S28A3S6fG3S70G4A1A2A4S3eA3SeSdS1bS8cS4eS25S24S27S7fS2eA6S2dA3SeSdS1bS8cS4eS25S24S27S7eS2eA6S2bA3SeSdS8S1bA1M5S54S2dS3aS2dA1A2SaS1bS34A2A3SeSdG5S54S2bS3aS2bA1A2SaS1bS33A2A3SeSdS1bS85S34A1S2cA3SeSdS1bS85S33A1S2aA3SeSdS3S1eS2cA1S2A3SeSdS3S1eS2aA1S2A3SdS9S9S23A1M6A1S77S1bG6S1bS77S1dS23S1dS1aS1cS20R1A1A1A1LL;S8S9S1dA1M7A1G7Lx;S21S93Uc8S5aR1S2A5G7R1Ll;S5S1dA1X8x2A4LT;S0S1bS2cS0S1bS2aS5S1bA1A3A3A4S0G6S0S23S99S5S23A1A3M8S0G6G8S5G6A1A3A3A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
