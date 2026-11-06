(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ey.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.

(* [comment removed for export] *)
Module Lib_handle_f_g9.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "DUnknown"; "ss_facts"; "ss_objs"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "cons"; "list"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w"; "E_mi4_0_0"; "E_mi4_0_4"; "G3back"; "E_mi4_1w"; "Xw"; "L_win"; "T_g3_0"; "T_g3_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "E_mi4_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_X"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "objs_butlast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_tv"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_handle_f_g9"; "cells_w0"; "cells_w4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "vlF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs5"; "releaseP_chk"; "reopenC_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_shx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ey.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs5.
Module AR. Include Lib_handle_f_arith. End AR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Definition cells_w0 : list cell := Eval vm_compute in ob_cells (sh_last E_mi4_0_0).
Definition cells_w4 : list cell := Eval vm_compute in ob_cells (sh_last E_mi4_0_4).

Section G.
Variable XGL : list (Z * Z).

Lemma G3back_eq : T_g3w = G3back. Proof. vmr. Qed.
Lemma g3_roC : ltac2:(tb__ "0|0|
S0S5S20VXGL;SdSfSdA1S1aS17A1Z1cZ27Ze0Z24A8S6A3"). Proof. vmr. Qed.
Lemma T_g3_0_eq : ltac2:(tb__ "0|0|
S0S16S22SdSfSdA1S18Z1cZ27S21Ze0Z24Z0A3A6S11A3"). Proof. vmr. Qed.
Lemma T_g3_4_eq : ltac2:(tb__ "0|0|
S0S16S22SdSfSdA1S18Z1cZ27S21Ze0Z24Z4A3A6S12A3"). Proof. vmr. Qed.

Lemma w0_robjs : ltac2:(tb__ "0|0|
S0S9S1A1S4S15SbA1A1S7S1S19SbA1S8S1S25S18Z1cZ27S1cS2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma w0_rel : ltac2:(tb__ "0|0|
S0S5S1fSbS19SbA1Z1cZ27S1cS2S10S1aS17A1S1bS17A1A9S6A3"). Proof. vmr. Qed.
Lemma w0_eq : ltac2:(tb__ "0|0|
S0S16S23SeSbA1S14S13A1A2S13A3"). Proof. vmr. Qed.
Lemma w0_incl : ltac2:(tb__ "0|0|
S0S5S24S14S13A1S14SeSbA1A1A2S6A3"). Proof. vmr. Qed.
Lemma w0_vlF : ltac2:(tb__ "0|0|
S0S5S1eS3S15SbA1A1A1S6A3"). Proof. vmr. Qed.
Lemma w4_robjs : ltac2:(tb__ "0|0|
S0S9S1A1S4S15ScA1A1S7S1S19ScA1S8S1S25S18Z1cZ27S1dS2A5SaS1A1A3A3A3"). Proof. vmr. Qed.
Lemma w4_rel : ltac2:(tb__ "0|0|
S0S5S1fScS19ScA1Z1cZ27S1dS2S10S1aS17A1S1bS17A1A9S6A3"). Proof. vmr. Qed.
Lemma w4_eq : ltac2:(tb__ "0|0|
S0S16S23SeScA1S14S13A1A2S13A3"). Proof. vmr. Qed.
Lemma w4_incl : ltac2:(tb__ "0|0|
S0S5S24S14S13A1S14SeScA1A1A2S6A3"). Proof. vmr. Qed.
Lemma w4_vlF : ltac2:(tb__ "0|0|
S0S5S1eS3S15ScA1A1A1S6A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g9.

(* [comment removed for export] *)
Module Lib_handle_f_g8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "xr_below"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "cons"; "Some"; "option"; "pair"; "prod"; "app"; "nil"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_facts"; "sv"; "ss_next"; "sprop"; "ss_objs"; "obj_wf"; "sprop_below"; "sstate"; "DUnknown"; "SLit"; "SPUle"; "sprop_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "E_pg4"; "T_pgi0"; "T_pgo0"; "E_pg0"; "xRFX"; "s_pg"; "xPRV"; "Xk_pg"; "xNXT"; "E_pg"; "E_pg3"; "objs_butlast"; "xP2D"; "O_nxt'"; "O_prv'"; "O_rfx'"; "R_pg"; "xOUT"; "E_pg1"; "xPTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "pgF"; "E_pg0r"; "E_pg3a"; "E_pg3b"; "T_pgi3"; "T_pgia"; "T_pgib"; "T_pgo3"; "T_pgoa"; "T_pgob"; "T_pgi2"; "T_pgi4"; "T_pgiR1"; "T_pgic"; "T_pgo2"; "T_pgo4"; "T_pgoR1"; "O_nxt1"; "O_prv1"; "O_rfx1"; "cells_pg"; "O_nxt"; "O_prv"; "O_rfx"; "cs_pgi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "reshapeA"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "XT"; "T_pgi1"; "O_nxt0"; "O_prv0"; "O_rfx0"; "XT6"; "T_pgi"; "T_pgo"; "T_pgo1"; "xf_pgb1"; "xf_pgb2"; "T_pgiR"; "T_pgoR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs4"; "F_pg"; "E_pgF"; "Pre_pgF"; "E_pgS"; "Pre_pgS"; "facts_sub"; "R_pgF"; "T_pgi0F"; "T_pgo0F"; "F_pgC"; "P_invF"; "P_okF"; "pgEF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xr_eqb"; "T_afterA3"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pKts"; "pDts"; "needA"; "pDrp"; "pKrp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_tv"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_handle_f_g8.AR"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "reopen_chk"; "xff_chk"; "release_chk"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA"; "arr_merge_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ey.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs4.
Module AR. Include Lib_handle_f_arith. End AR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).
Lemma pg_robjs : ltac2:(tb__ "0|0|
S0S10S11A1S16S1S22A1A1SeS11S2aS22A1S9S11S83S5fZ14Z17S47S1aA5SfS11A1A3A3A3"). Proof. vmr. Qed.
Lemma pg_rel : ltac2:(tb__ "0|1|
S0S6S87S22S2aS22A1Z14Z17S47S1aS9SdS50S50A2M0ScS50S50Za0Z18A4SfG0A1A3S7cS6dA1S7dS6dA1A9S7A3"). Proof. vmr. Qed.
Lemma E_pg0r_eq : ltac2:(tb__ "0|1|
S0S2S82S22S2aS22A1Pa0S9SdS50S50A2M0ScS50S50Za0Z18A4SfG0A1A3A4S34A3"). Proof. vmr. Qed.
Lemma E_pg1_eq2 : ltac2:(tb__ "0|0|
S0S2S8aS84S34A2S31A3"). Proof. vmr. Qed.
Lemma pg_xff : ltac2:(tb__ "0|0|
S0S6S86S34S84A2S7A3"). Proof. vmr. Qed.
Lemma pg_tsF : ltac2:(tb__ "0|1|
S0S6S8S88S12S1S34A1A1M0A1S4eS15S1dS1cS77S75A2A1G0A3A2S7A3"). Proof. vmr. Qed.
Lemma pg_o43 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S29A1A1U2bA3SaS11S48A2A3"). Proof. vmr. Qed.
Lemma pg_wf43 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S29A1M0A1S2cA2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg3a_eq : ltac2:(tb__ "0|0|
S0S2S4cS29U2bS2cA3S35A3"). Proof. vmr. Qed.
Lemma pg_o45 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S35A1A1U2dA3SaS11S49A2A3"). Proof. vmr. Qed.
Lemma pg_wf45 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S35A1M0A1S2dA2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg3b_eq : ltac2:(tb__ "0|0|
S0S2S4cS35U2dS2dA3S36A3"). Proof. vmr. Qed.
Lemma pg_o47 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S36A1A1U2fA3SaS11S4aA2A3"). Proof. vmr. Qed.
Lemma pg_wf47 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S36A1M0A1S2eA2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma E_pg4_eq2 : ltac2:(tb__ "0|0|
S0S2S4cS36U2fS2eA3S1fA3"). Proof. vmr. Qed.
Lemma pg_pgF4 : ltac2:(tb__ "0|0|
S0S6S33S12S1S1fA1A1A1S7A3"). Proof. vmr. Qed.

Lemma pgx_rfx : ltac2:(tb__ "0|0|
S0S6S8S4eSdS13S13A2S72ScS13S13S76S5eZ1S75A2A4A1S3S1fA1A3S4S14S1S1fA1A1S23A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_prv : ltac2:(tb__ "0|1|
S0S6S8S4eSdS13S13A2M0S72ScS13S13S76S5eZ1S75A2A4A1S9G0S23S3S1fA1A3A3S4S14S1S1fA1A1S25A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_nxt : ltac2:(tb__ "0|1|
S0S6S8S4eSdS13S13A2M0S72ScS13S13S76S5eZ1S75A2A4A1S9G0S25S9G0S23S3S1fA1A3A3A3S4S14S1S1fA1A1S27A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_p2d : ltac2:(tb__ "0|1|
S0S6S8S4eSdS13S13A2M0S72ScS13S13S76S5eZ1S75A2A4A1S9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3S4S14S1S1fA1A1S2bA2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_out : ltac2:(tb__ "0|1|
S0S6S8S4eSdS13S13A2M0S72ScS13S13S8cS5eZ4S8dA2A4A1S9G0S2bS9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3A3S4S14S1S1fA1A1S30A2A2S7A3"). Proof. vmr. Qed.
Lemma pgx_pts : ltac2:(tb__ "0|1|
S0S6S8S4eSdS13S13A2M0S72ScS13S13S78S5eZ4S79A2A4A1S9G0S30S9G0S2bS9G0S27S9G0S25S9G0S23S3S1fA1A3A3A3A3A3A3S4S14S1S1fA1A1S32A2A2S7A3"). Proof. vmr. Qed.

Lemma E_pgS_eq : ltac2:(tb__ "0|0|
S0SbS2A1S6eS28S9S6fS71U5S1bZ10A1A2SfS6fA1A3A2SaS2S63A2A3"). Proof. vmr. Qed.
Lemma E_pgF_eq : ltac2:(tb__ "0|0|
S0S2S8aS69S63A2S61A3"). Proof. vmr. Qed.
Lemma pgF_xff : ltac2:(tb__ "0|0|
S0S6S86S63S69A2S7A3"). Proof. vmr. Qed.
Lemma pgF_site : ltac2:(tb__ "0|1|
S0S6S8S33S12S1S63A1A1M0A1S6cG0A1A2S7A3"). Proof. vmr. Qed.
Lemma pgF_callF : ltac2:(tb__ "0|0|
S0S6S33S12S1S61A1A1A1S7A3"). Proof. vmr. Qed.
Lemma pg_chkF : pg_call_chkF XGL = true. Proof. vmr. Qed.
Lemma R_pgF_eq : ltac2:(tb__ "0|1|
S0SbS10S11A1M0A1S8eS61S62S24A3SaG0S66A2A3"). Proof. vmr. Qed.
Lemma Pre_pg_merge : ltac2:(tb__ "0|0|
S0SbS2A1S6eS64S9S6fS70U3A1SfS6fA1A3A2SaS2S80A2A3"). Proof. vmr. Qed.
Lemma Pre_pgS_drop : ltac2:(tb__ "0|0|
S0S2S7aS62S12S1S64A1A1A2S64A3"). Proof. vmr. Qed.
Lemma Pre_pgS_chk : ltac2:(tb__ "0|3|
S0S6S8S8S8S4fS15S18S14S1S62A1M0A1A1S12S1S64A1A1M1A3S65G1S12G0A1M2A2A2S65S60G2A2A2S4fS15S18S8fA1S60A3A2S7A3"). Proof. vmr. Qed.
Lemma P_okF_eq : ltac2:(tb__ "0|0|
S0S2S7aS7fSeS15S60S12S1S7fA1A1A3A2S6bA3"). Proof. vmr. Qed.
Lemma P_invF_eq : ltac2:(tb__ "0|0|
S0S2S7aS7eSeS15S60S12S1S7eA1A1A3A2S6aA3"). Proof. vmr. Qed.
Lemma P_F_below : ltac2:(tb__ "0|2|
S0S6S8S4fS15S18S14S1S7fA1M0A1A1SeS15S60S12G0A1A3A3S4fS15S18S14S1S7eA1M1A1A1SeS15S60S12G1A1A3A3A2S7A3").
Proof. vmr. Qed.
Lemma T_pgo0F_ta : ltac2:(tb__ "0|0|
S0S2S73S62S61S24S66S6bS26A6S68A3"). Proof. vmr. Qed.
Lemma T_pgi0F_ta : ltac2:(tb__ "0|0|
S0S2S73S62S61S24S66S6aS26A6S67A3"). Proof. vmr. Qed.
Lemma T_pgo0_drop : ltac2:(tb__ "0|0|
S0S2S7aS68S12S1S21A1A1A2S21A3"). Proof. vmr. Qed.
Lemma T_pgi0_drop : ltac2:(tb__ "0|0|
S0S2S7aS67S12S1S20A1A1A2S20A3"). Proof. vmr. Qed.
Lemma T_pg0_chk : ltac2:(tb__ "0|4|
S0S6S8S8S8S4fS15S18S14S1S68A1M0A1A1S12S1S21A1A1M1A3S65G1S12G0A1A2A2S4fS15S18S14S1S67A1M2A1A1S12S1S20A1A1M3A3A2S65G3S12G2A1A2A2S7A3"). Proof. vmr. Qed.

Lemma T_pgo0_ta : ltac2:(tb__ "0|0|
S0S2S73S80S28S24S2fS7fS26A6S21A3"). Proof. vmr. Qed.
Lemma pgo_o8 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S21A1A1U8A3SaS11S44A2A3"). Proof. vmr. Qed.
Lemma pgo_wf8 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S21A1M0A1S53A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgoa_eq : ltac2:(tb__ "0|0|
S0S2S4cS21U8S53A3S3bA3"). Proof. vmr. Qed.
Lemma pgo_o9 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S3bA1A1U9A3SaS11S45A2A3"). Proof. vmr. Qed.
Lemma pgo_wf9 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3bA1M0A1S54A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgob_eq : ltac2:(tb__ "0|0|
S0S2S4cS3bU9S54A3S3cA3"). Proof. vmr. Qed.
Lemma pgo_o10 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S3cA1A1UaA3SaS11S46A2A3"). Proof. vmr. Qed.
Lemma pgo_wf10 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S3cA1M0A1S55A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgo1_eq2 : ltac2:(tb__ "0|0|
S0S2S4cS3cUaS55A3S59A3"). Proof. vmr. Qed.
Lemma T_pgo2_eq : ltac2:(tb__ "0|0|
S0SbS2A1S6eS59S5aA2SaS2S41A2A3"). Proof. vmr. Qed.
Lemma T_pgo3_am : ltac2:(tb__ "0|0|
S0SbS19A1S8bS1S41A1U22A2SaS19S1S3aA1A2A3"). Proof. vmr. Qed.
Lemma T_pgo3_eq2 : ltac2:(tb__ "0|0|
S0S2S5S41S1S3aA1A2S3aA3"). Proof. vmr. Qed.
Lemma T_pgo4_eq : ltac2:(tb__ "0|0|
S0SbS2A1S6eS3aS5bA2SaS2S42A2A3"). Proof. vmr. Qed.
Lemma T_pgo_eq2 : ltac2:(tb__ "0|0|
S0S2S7bS42S56A2S58A3"). Proof. vmr. Qed.
Lemma pgo_xsub : ltac2:(tb__ "0|0|
S0S6S74S56S3S42A1A2S7A3"). Proof. vmr. Qed.
Lemma pgo_ro1 : ltac2:(tb__ "0|0|
S0S6S85VXGL;S58S51S7cS6dA1Z6ZfA6S7A3"). Proof. vmr. Qed.
Lemma T_pgoR1_eq : ltac2:(tb__ "0|0|
S0S2S81S58S51S5fZ6ZfA5S43A3"). Proof. vmr. Qed.
Lemma pgo_ro2 : ltac2:(tb__ "0|0|
S0S6S89VXGL;S43S51S7cS6dA1Z14Z17A6S7A3"). Proof. vmr. Qed.
Lemma T_pgoR_eq2 : ltac2:(tb__ "0|0|
S0S2S81S43S51S5fZ14Z17A5S5dA3"). Proof. vmr. Qed.

Lemma T_pgi0_ta : ltac2:(tb__ "0|0|
S0S2S73S80S28S24S2fS7eS26A6S20A3"). Proof. vmr. Qed.
Lemma pgi_o8 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S20A1A1U8A3SaS11S44A2A3"). Proof. vmr. Qed.
Lemma pgi_wf8 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S20A1M0A1S53A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgia_eq : ltac2:(tb__ "0|0|
S0S2S4cS20U8S53A3S38A3"). Proof. vmr. Qed.
Lemma pgi_o9 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S38A1A1U9A3SaS11S45A2A3"). Proof. vmr. Qed.
Lemma pgi_wf9 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S38A1M0A1S54A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgib_eq : ltac2:(tb__ "0|0|
S0S2S4cS38U9S54A3S39A3"). Proof. vmr. Qed.
Lemma pgi_o10 : ltac2:(tb__ "0|0|
S0SbS11A1S4dS11S16S1S39A1A1UaA3SaS11S46A2A3"). Proof. vmr. Qed.
Lemma pgi_wf10 : ltac2:(tb__ "0|1|
S0S6S8S17S14S1S39A1M0A1S55A2S33S12G0A1A1A2S7A3"). Proof. vmr. Qed.
Lemma T_pgic_eq2 : ltac2:(tb__ "0|0|
S0S2S4cS39UaS55A3S40A3"). Proof. vmr. Qed.
Lemma T_pgi1_zc : ltac2:(tb__ "0|0|
S0SbS19A1S90S1S40A1U3S4bA3SaS19S1S52A1A2A3"). Proof. vmr. Qed.
Lemma T_pgi1_wf : ltac2:(tb__ "0|0|
S0S6S1eS1S52A1A1S7A3"). Proof. vmr. Qed.
Lemma T_pgi1_eq2 : ltac2:(tb__ "0|0|
S0S2S5S40S1S52A1A2S52A3"). Proof. vmr. Qed.
Lemma T_pgi2_eq : ltac2:(tb__ "0|0|
S0SbS2A1S6eS52S5aA2SaS2S3dA2A3"). Proof. vmr. Qed.
Lemma T_pgi3_am : ltac2:(tb__ "0|0|
S0SbS19A1S8bS1S3dA1U22A2SaS19S1S37A1A2A3"). Proof. vmr. Qed.
Lemma T_pgi3_eq2 : ltac2:(tb__ "0|0|
S0S2S5S3dS1S37A1A2S37A3"). Proof. vmr. Qed.
Lemma T_pgi4_eq : ltac2:(tb__ "0|0|
S0SbS2A1S6eS37S5bA2SaS2S3eA2A3"). Proof. vmr. Qed.
Lemma T_pgi_eq2 : ltac2:(tb__ "0|0|
S0S2S7bS3eS56A2S57A3"). Proof. vmr. Qed.
Lemma pgi_xsub : ltac2:(tb__ "0|0|
S0S6S74S56S3S3eA1A2S7A3"). Proof. vmr. Qed.
Lemma pgi_ro1 : ltac2:(tb__ "0|0|
S0S6S85VXGL;S57S51S7cS6dA1Z6ZfA6S7A3"). Proof. vmr. Qed.
Lemma T_pgiR1_eq : ltac2:(tb__ "0|0|
S0S2S81S57S51S5fZ6ZfA5S3fA3"). Proof. vmr. Qed.
Lemma pgi_ro2 : ltac2:(tb__ "0|0|
S0S6S89VXGL;S3fS51S7cS6dA1Z14Z17A6S7A3"). Proof. vmr. Qed.
Lemma T_pgiR_eq2 : ltac2:(tb__ "0|0|
S0S2S81S3fS51S5fZ14Z17A5S5cA3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g8.

(* [comment removed for export] *)
Module Lib_load_obj_epiS5_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "Some"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_objs"; "swf"; "sprop"; "ss_next"; "ss_facts"; "SPUle"; "dflt_writable"; "ob_cells"; "ob_dflt"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "tvA"; "nd_d2"; "nd_z"; "KU1"; "PhisD"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "g5_facts"; "shape_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5"; "Es_sfA"; "Es_sf"; "Es_s80"; "Es_sfD"; "Ts_s81"; "Ts_s82"; "Es_s8"; "s_perr"; "Es_mc"; "Es_sfB"; "P_okM"; "Rs_sf"; "Ts_sf"; "nd_okL"; "Es_s8a"; "Es_sf0"; "P_errM"; "P_okF"; "P_okL"; "Rs_mc"; "Rs_s8"; "Ts_mc"; "Ts_s8"; "Ts_s8r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "objs_butlast"; "g5"; "L_f8"; "Pre_f8"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5.IF"; "nd_lo_err"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "Pre_mc48"; "vARn"; "L_mc48"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS5_chk"; "Ts_sf0"; "shs"; "cutsS5"; "exitsS5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "flag_carve_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "cps_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "L_sf"; "Pre_sf"; "X_sx"; "s_s8"; "s_sf"; "sx_sfB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "ejcertAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_FL"; "@Stdlib.Lists.List";
"existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5.

Definition cutsS5 : list efnode := ltac2:(tb__ "0|5|
S5S7S7S7ScS44A2M0S6A2M1S7S24S11A2M2A2M3S4G1G2S4G0S6S4ScS44S41S20A4U1M4A4S4S24S11Z163S55A4A4S5G3S4G1G2S4G0S6S4ScS44S42S20A4G4A4S4S24S11Z15eS55A4A4S5G3S4G1G2S4G0S6S4ScS44S38S39A4G4A4S4S24S11Z159S55A4A4S8G3A1A3A3A3").
Definition exitsS5 : list efnode := ltac2:(tb__ "0|5|
S5S7S7S7ScS44A2M0S6A2M1S7S24S11A2M2A2M3S4G1G2S4G0S6S4ScS44S2eS20A4U1M4A4S4S24S11Z162S55A4A4S5G3S4G1G2S4G0S6S4ScS44S3bS20A4G4A4S4S24S11Z15dS55A4A4S5G3S4G1G2S4G0S6S4ScS44S3eS39A4G4A4S4S24S11Z158S55A4A4S8G3A1A3A3A3").
Lemma ecertS5_ok : ltac2:(tb__ "0|0|
S0S2S7bS6eS4eS23U12cS6fS4eS63S64A8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma epiS5_chk_mc : ltac2:(tb__ "0|2|
S1S0S2S5dS4eS29S34A1M0A2S3A3S1S0S2S45G0S20A2S3A3S1S0S2S66G0S22A2S3A3S1S0S2S68S22A1S3A3S1S0S2S2bS58S5ScS5aS8ScA1A3A2S3A3S1S0S25S17SdS58A1A1S77A3S1S0S11SeS58A1S12S5cA1A3S1S0S2S5eS28S34A1M1S1fS26S27S3fA5S3A3S0S2S60G1S1fS26S5fSfS34A1A5S3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_chk_s8 : ltac2:(tb__ "0|6|
S1S0S11SeS2eA1S12S5cA1M0A3S1S0S2S10S2aS28S2eA1M1A2S3A3S1S0S2S56G1S1fS26S27S14SdS2eA1A1A5S3A3S1S0S2S69S4eS73S32A1A2S3A3S1S0S2S5dS4eS29S32A1M2A2S3A3S1S0S2S45G2S20A2S3A3S1S0S2S2bS52S5ScS51S8ScA1A3A2S3A3S1S0S2S5eS28S32A1M3S1fS26S27S40A5S3A3S1S0S2S60G3S1fS26S5fSfS32A1A5S3A3S1S0S11SeS30A1G0A3S1S0S2S10S2aS28S30A1M4A2S3A3S1S0S2S45S29S30A1S20A2S3A3S1S0S2S56G4S1fS26S27S4fS30A1A5S3A3S1S0S11SeS31A1G0A3S1S0S2S10S2aS28S31A1M5A2S3A3S1S0S2S56G5S1fS26S27S14SdS31A1A1A5S3A3S0S2S66G2S22A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Definition shs : sobj := Eval vm_compute in last (ss_objs (ax_S Es_sfA)) dflt_obj.
Definition Ts_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf Es_sf (s_sf Es_sf) Rs_sf L_sf (ax_X Es_sf).
Lemma epiS5_chk_sf : ltac2:(tb__ "0|7|
S1S0S11SeS2cA1S12S5cA1M0A3S1S0SbS13A1S14SdS2cA1A1S9S13S4fS2cA1M1S5S13S6dS50Z20Z40S1bS62A1S1cS62A1M2A5S8S13A1A3A3A3S1S0S2S1aG2A1S3A3S1S0S2S10S2aS28S2cA1M3A2S3A3S1S0S2S45S29S2cA1S20A2S3A3S1S0S2S56G3S1fS26S27G1A5S3A3S1S0ScS75S2cA1S35A3S1S0S11SeS2fA1G0A3S1S0ScS6aS2fP78A2S2dA3S1S0S2S15SdS2dA1A1S3A3S1S0S2S56S28S2fA1M4S1fS26S27S14SdS2fA1A1A5S3A3S1S0S2S7cG4S1fSfS2fA1A3S3A3S1S0S2S69S4eS74S2dA1M5A2S3A3S1S0S2S5dS4eS29S2dA1M6A2S3A3S1S0S2S45G6S20A2S3A3S1S0S11S65G5PcA2S53A3S1S0S11S65G5S7eA2S54A3S1S0S2S7dS28S2dA1S1fS26SaS6U0A2S27S37A6S3A3S1S0ScS79S71S2dG5S37S70SfS2dA1A6S61A3S0ScS5bS61A1S38A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS5_chk_sx : ltac2:(tb__ "0|4|
S1S0ScS6cS2eS72S2eA1S50Z44Ze7A5M0S3aA3S1S0S2S15SdG0A1A1S3A3S1S0ScS6bS30S4fS30A1P6eM1S8S7S24S24A2A1M2A4S31A3S1S0ScS6cS31SfS31A1S50Z20Z40A5M3S43A3S1S0S2S15SdG3A1A1S3A3S1S0ScS6bS2cS4fS2cA1G1G2A4S35A3S0S2S15SdS6aS2fP78A2A1A1S3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_chk_post : ltac2:(tb__ "0|4|
S1S0S2S80S16S1dS17SdS36A1M0A1A1S9S16S4dS4S11S11S59S12Z40A1A4A1S18G0A1M1A3M2A3S3A3S1S0ScS76S36G2A2S3dA3S1S0S2S7fS16S1eS19S12Z1000A1S59A2A1G1A3S3A3S1S0S2S45S17SdS3cA1M3A1S21A2S3A3S1S0S2S78S33S49S21A1S49S57A1A3S3A3S1S0S2S4cS33S48S21A1S48S57A1A3S3A3S1S0S2S7aS18G3A1S67S33S47S57A1A2S47S21A1A3S3A3S0S2S4aS4bS33S46S57A1A2S46S21A1A2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS5_chk.

(* [comment removed for export] *)
Module Lib_load_obj_epiS5_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "cons"; "nil"; "bool"; "true"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sobj"; "holds"; "sprop"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "ok_frameKA"; "tvinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "PhisD"; "nd_d2"; "nd_d0"; "tvA"; "nd_z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_pure_pre"; "JL_stack_free"; "J_stack_free_pre"; "V_FL"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "L_f8"; "Pre_f8"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "L_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "ldef"; "P0_lo"; "extraLO"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5"; "Es_s80"; "Es_sf"; "Es_sf0"; "P_okL"; "Ts_s82"; "nd_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "L_sf"; "Pre_sf"; "P_errL"; "X_sx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5.IF"; "P_err"; "P_ok"; "nd_lo_err"; "nd_lo_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS5_chk"; "cutsS5"; "exitsS5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "L_mc48"; "Pre_mc48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "al48_cells";
"memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "extraXlo"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "remove_nth"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "robjs_okL"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS5_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiD_pf. End DP.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S3fS11S3S18Q40A1A1S49OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S54S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S10S7cVCST;R1A2S33S45Z0R2A2S46R2S85A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S10S7cVXGL;R1A2S33S45Z0R2A2S46R2S85A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S10S88R1A1S7cVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S2S2S10S10A2S10A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S5dVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1bVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aVPhi;Vnd;Ad").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S23SdS11S3S18Q40A1A1S3dS60S16S15R3A1S13SeR4A1A1A3VTR;S22S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S3dS3dS3dS3eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S23S23SdSdS6aS3S14A1M0S3S2SdS25A2M1A1S3S2S12S12A2M2A1S3dS11S3S18Q40A1A1M3G2S42G2R1R5A3S42G2R2SfRbA1A3F_;Fr;S32SbG0A1S29RaR9R8A3S9G0R7A2A3S32S7S28RbRaR9R8S5fG1SdSaSdS25A2R7A4A5S8A3S11G3VTR;S22S0RfRdR2R1A5S26S0S17SeRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S4aA1M4S6cS49S24S0R9R8R10S1G4S6dR3S6eR2R1A2A4A5R13RaR9R4R2A4R13S68S67RbRfS4bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SdS25G4S6cS49S11G3G4S6cS49S42G1S1SdS25RaR9A4R14A3S24S0R12R11R19S1G4S6dR9S6eR8R7A2A4A5R1cR13R12RaR8A4S82S17SeR1aA1A1S68S67R14R18S4bR9R13RaA3A3R19A2R8A3S24S0R9R8ReS1G4S6dR7S6eR6R5A2A4A5ReS68S67R16R1aS4bRbR15RcA3A3R1bA2R15RaR9R8R6A6S33S91R17S4bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S83R18S4bRdR17ReA3R1cR1dSeR1eA1SeR1fA1SeR11A1R1RcA9VTR;S22S0S27R11S68S67R19R1dS4bReR18RfA3A3R1eA2R18RdRcA5S92R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S22S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S19SdS11S3S18Q40A1A1S3dR6R3A1VTR;S22S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S22S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CMC48 : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1VTR;S22S0S4eVAInv;R3VKc;A3S7bR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S7aS4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1VTR;S22S0S4eVAInv;R3VKc;A3S57R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S56S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1VTR;S22S0S50VAInv;Z5M0R3VKc;A4S71R2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S70S4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CUT5 : ltac2:(tb__ "0|5|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1S10G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R8R7A4R6A4R5A4S78A3S2bS36R7R5A3S33S45Z0S2aS1G3G0S1G2S4S1SdS19RaR9A4R8A4R7A4R6A2M4A2S46G4R4A2A2VTR;S22S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Hypothesis XPK : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S77A1S75R3R2A5VFAM;S47Z158S48Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis XPE : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S76A1S74R3R2A5VFAM;S47Zd1S48Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").

Lemma CXR_s8aS : ltac2:(tb__ "0|0|
S32S7S81VXGL;S13SeS61A1A1S39Z44Ze7S73S61A1A6S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_s8rS : ltac2:(tb__ "0|0|
S32S7S81VXGL;S13SeS65A1A1S39Z20Z40SfS65A1A6S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXL_sfS : ltac2:(tb__ "0|0|
S32S7S84VXGL;S13SeS62A1A1S39S5bS9S4U0A2S6S14A1S80SfS62A1A8S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma c5_ok : 0 <= 5 <= 6. Proof using . lia. Qed.
Lemma k68 : 0 <= 68. Proof using . lia. Qed.
Lemma k32 : 0 <= 32. Proof using . lia. Qed.
Lemma k68_231 : 68 <= 231 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma k32_64 : 32 <= 64 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Ltac meas_z0 := rewrite !DP.efmeas_z0; vm_compute; split; [discriminate | reflexivity].

Lemma X_L_ok : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S37A1S5aR3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S5aS37A4U1A4S1S10S12Z167S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  pose proof epiS5_checks_mc as (Cx1 & Cx2 & Cx3 & Cent & Cchk & Cta & CT0 & CxB & Ctidy & Cwf & _).
  pose proof epiS5_chk_mc as (Cnp & Cnb & Cbb & Cwp & Cshape & Cnf & Cbp & CR & CX).
  apply (TR_pre (SPA segs (JAv nd_d2) Es_mc rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_d2) _ rho Es_mc2 Es_mc tp w Cx3). apply (SPA_axforms segs (JAv nd_d2) _ rho Es_mc1 Es_mc2 tp w Cx2).
    exact (SPA_axforms segs (JAv nd_d2) _ rho L_ok Es_mc1 tp w Cx1 Hw). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_mc48 [L_mc48] Es_mc s_mcS Rs_mc rho tp nd_d2 KU1 (FAM (efmeasA (L_ok, nd_d2, 1%nat, (359, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CMC48.
  - exact Cnf.
  - exact Cbp.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply DP.payA_same. exact Cwp.
  - exact Cshape.
  - exact (DP.site_rt_lo0 AInv CST XGL ALA HCST HXlits FB FF rho0 Es_mc s_mcS Rs_mc rho tvA KU1 (AHead pH false) CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_d2 ndEp]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) Ts_mc rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_d2) (xfb_mcS Ts_mc0) rho' Ts_mc0 Bs_mc tp' w CxB Hw). }
    apply (CUT5 Ts_mc nd_d2 1%nat (355, z0) rho' tp'); [left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_Es_s80 : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S37A2S61R3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S61S37A4G1A4S1S10S12Z162S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_s8 as (CwfA & CeqA & Cxf & Cent & Cchk & CT0 & Cxb & Cobjs & Ceq82 & Cwf82 & CeqR & CwfR & Ctidy & CwfT & _).
  pose proof epiS5_chk_s8 as (Cbase0 & Chf0 & CR0 & Cta & Cnp & Cnb & Cshape & CR & CX & Cbase1 & Chf1 & Cnb1 & CR1 & Cbase2 & Chf2 & CR2 & Cbb).
  pose proof epiS5_chk_sx as (XeqA & XwfA & Xeq82 & XeqR & XwfR & _).
  apply (TR_pre (SPA segs (JAv nd_d2) Es_s8 rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_d2) (xf_shcall Es_s8a 68) rho Es_s8a Es_s8 tp w Cxf). rewrite <- XeqA.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 68 231 Es_s80 (X_sx Es_s80) rho tp w eq_refl c5_ok Cbase0 k68
             k68_231 Chf0 (DP.X_sx_incl Es_s80) XwfA); [|exact Hw].
    intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0).
    - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvA (X_sx Es_s80) rho3 tp3 md3 68 231 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8aS). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] Es_s8 (s_s8 Es_s8) Rs_s8 rho tp nd_d2 KU1 (FAM (efmeasA (Es_s80, nd_d2, 1%nat, (354, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply DP.payA_same. reflexivity.
  - exact Cshape.
  - exact (DP.site_rt_lo0 AInv CST XGL ALA HCST HXlits FB FF rho0 Es_s8 (s_s8 Es_s8) Rs_s8 rho tvA KU1 (AHead pH false) CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_d2 ndEp]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) Ts_s81 rho' tp')).
    { intros w Hw. exact (SPA_axforms segs (JAv nd_d2) (xf_shback Ts_s80) rho' Ts_s80 Ts_s81 tp' w Cxb Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_d2) Ts_s8 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj g5 68 231 [] DUnknown] (vms md tp' ms)).
      rewrite <- Ctidy. apply SPA_tidy. rewrite <- XeqR.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 32 64 Ts_s82 (ax_X Ts_s82) _ tp' (tr, mkCfg ms md) eq_refl c5_ok Cbase2 k32
               k32_64 Chf2 (fun r H => H) XwfR).
      - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
        + exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai _ _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR2).
        + exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai _ _ tvA (ax_X Ts_s82) rho3 tp3 md3 32 64 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8rS).
      - rewrite <- Xeq82.
        apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                 tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 68 231 [] DUnknown Ts_s81 (objs_butlast Ts_s81) [] rho' tp' tr ms md
                 eq_refl c5_ok Cbase1 Cobjs k68 k68_231 eq_refl Chf1 eq_refl Cnb1); [|exact Hw].
        intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho' _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR1). }
    apply TR_exw. intros rho2.
    apply (CUT5 Ts_s8 nd_d2 1%nat (350, z0) rho2 tp'); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma site_sfT : ltac2:(tb__ "0|7|
S3S2S12S12A2A1SdS6aS3S14A1S11S32S7S95S13SeR4A1A1R5S5bS9S4U0M0A2M1S5eR2A6S8A3S32S7S84VXGL;S13SeR5A1A1R6S5bG1S6S14A1S80SfR5A1A8S8A3S32S12S69R5PcM2A2S58A3S32S12S69R6S51A2S59A3S3fS60S16S15R6A1S13SeR9A1A1A3VP0;Vrho0;A1S82S55Vrho0;R8A3S1dVFB;R4A2S1eVFF;R5A2S21VFB;R6RbRfA4S8dRcR10A2S8eRdR11A2S1fVFF;R9ReS5bA4S34S11S11S34S3S18Q40A1A1M3G3S34S49S49VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S1cVrho0;RbA2S8bR11S41S40RcA1A1A2S33S93VCST;Vrho0;VFB;VFF;R12R16S8cS2S2S12S10A2M4S12A2G0S5bA3M5R13A8S33S94VCST;VXGL;Vrho0;VFB;VFF;R12R16G5SfR15A1A9S33S32S10S6bR12S69R14G2A2A2S6bR12SaS12S10SaG4S12S1G4S12S1S12S10S58Z5A4S59A4M6A3A3A2A3S32S10S6bR12S69R14S51A2A2S6bR12ScG4S12G6A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;Frho;FR;Fs;FE;Ftv;").
Proof using ALA HXlits.
  intros tv E s R rho HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr.
    apply (TobjJAT.robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ tv frL (Some 0%nat) extraLO R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HR) with (o := o); [| exact Ho | exact Hr].
    intros o' a' _ HE Hr'. exact (extraLO_pclMA CST rho0 FB FF rho tv _ o' a' Hav HP0 HE Hr').
  - apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ tv frL (Some 0%nat) [] extraXlo (ax_X E) rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HX).
    intros r' a' _ HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho tv _ r' a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r' rho a' HE Ha).
Qed.

Lemma X_Es_sf0 : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S37A2S63R3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S63S37A4G1A4S1S10S12Z15dS44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_sf as (CxfA & CwfB & CxfC & CxfD & CwfE & Cent & Cchk & CwfT & _).
  pose proof epiS5_chk_sf as (CbaseA & CobjsA & Cdw & ChfA & CnbA & CRA & CeqB & CbaseD & CeqF & CswfF & CRD & CXD & Cta & Cnp & Cnb & C12 & C16 & CRsf & CT0 & Ctidy).
  pose proof epiS5_chk_sx as (_ & _ & _ & _ & _ & XeqB & XwfF).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_d2) Es_sf rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 32 64 (ob_cells shs) (ob_dflt shs)] (vms md tp ms)).
    rewrite <- CeqF.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive Es_sfD _ tp (tr, mkCfg ms md) eq_refl c5_ok CbaseD XwfF).
    - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      + intros o a Ho Hr. destruct (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai _ _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRD o a Ho Hr) as [X|X]; [left; exact X | right; left; exact X].
      + exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai _ _ tvA _ rho3 tp3 md3 HM HF HN HZ CXD).
    - apply (SPA_axforms segs (JAv nd_d2) (xf_merge Es_sfC) _ Es_sfC Es_sfD tp _ CxfD).
      apply (SPA_axforms segs (JAv nd_d2) (xf_rebase Es_sfB) _ Es_sfB Es_sfC tp _ CxfC).
      rewrite <- XeqB.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 32 64 (ob_cells shs) (ob_dflt shs) Es_sfA (objs_butlast Es_sfA) [] rho tp tr ms md
               eq_refl c5_ok CbaseA CobjsA k32 k32_64 Cdw ChfA eq_refl CnbA).
      + intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRA).
      + exact (SPA_axforms segs (JAv nd_d2) (xf_sh Es_sf0) rho Es_sf0 Es_sfA tp _ CxfA Hw). }
  apply TR_exw. intros rho1.
  unfold Pre_sf, L_sf in Cent, Cchk.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 Es_sf (s_sf Es_sf) Rs_sf (ax_X Es_sf) rho1 tp nd_d2 0%nat (vF, 5, vFL) (FAM (efmeasA (Es_sf0, nd_d2, 1%nat, (349, z0)) rho) tp0) CSF c5_ok).
  - intros r H. exact H.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A A' _. exact I.
  - exact (site_sfT tvA Es_sf (s_sf Es_sf) Rs_sf rho1 CRsf CXL_sfS C12 C16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am nd_d2 ndEp remove_nth frL]. unfold Pre_sf, L_sf in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_okL) Ts_sf rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT5 Ts_sf nd_okL 1%nat (345, z0) rho' tp'); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_P_okL : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S66A2S64R3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S64S66A4G1A4S1S10S12Z158S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_post as (CxR & CxM & _ & Cent & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  pose proof epiS5_chk_post as (Cfb & Cwf & C4096 & _).
  rewrite DP.efmeas_z0.
  apply (TR_pre (SPA segs (JAv IF.nd_lo_ok) IF.P_ok (rho_sub rho s_pok) tp)); [|apply XPK].
  intros w Hw.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc P_okF IF.P_ok s_pok nd_okL IF.nd_lo_ok rho tp w Cent Cid Cnp Cnb Ctv Cfr Cbd Cam).
  rewrite <- Cwf. apply (SPA_refacts_JA segs); [| exact Cfb |].
  - apply (SPA_axforms segs (JAv nd_okL) (xf_mergeR P_okR) rho P_okR P_okM tp w CxM). exact (SPA_axforms segs (JAv nd_okL) (xf_rebaseR P_okL) rho P_okL P_okR tp w CxR Hw).
  - intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    apply (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA _ _ _ _ _ (vARn, SLit 64) eq_refl HJ); [left; reflexivity|].
    exact (DP.tnz_of_ule4096 rho _ (vARn, SLit 64) HF C4096).
Qed.
Lemma X_P_errL : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S3aA1S72R3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S72S3aA4U1A4S1S10S12Zd1S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  pose proof epiS5_checks_post as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CxR & CxM & Cent & Cid & Cnp).
  pose proof epiS5_chk_post as (_ & _ & _ & Cnb & Ctv & Cfr & Cbd & Cam).
  rewrite DP.efmeas_z0.
  apply (TR_pre (SPA segs (JAv IF.nd_lo_err) IF.P_err (rho_sub rho s_perr) tp)); [|apply XPE].
  intros w Hw.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc P_errM IF.P_err s_perr nd_z IF.nd_lo_err rho tp w Cent Cid Cnp Cnb Ctv Cfr Cbd Cam).
  apply (SPA_axforms segs (JAv nd_z) (xf_mergeR P_errR) rho P_errR P_errM tp w CxM). exact (SPA_axforms segs (JAv nd_z) (xf_rebaseR P_errL) rho P_errL P_errR tp w CxR Hw).
Qed.

Lemma exitsS5_ok : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S79A3VTR;S22S0VJAFv;S2bS36R6A2R7A2R8R4R3A5VFAM;S2aS1G3G0S1G2S4S1SdS19R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS5 In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  - apply X_Es_s80.
  - apply X_Es_sf0.
  - apply X_P_okL.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S20S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S52S0S4cVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S10S42S10R1S5S10Z0S5S10Zf5S5S10Zf8S6S10A1A3A3A3A3S86S0S4cVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
S7eS0S4cVAInv;VCST;VXGL;S7dA6").
Variable FAMQ : list word -> assn.
Hypothesis XPK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S77A1S75R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S76A1S74R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CMC48_T : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S4eVAInv;R3VKc;A3S7bR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S7aS4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48; [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CF8_T : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S4eVAInv;R3VKc;A3S57R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S56S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CSF_T : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S50VAInv;Z5M0R3VKc;A4S71R2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S70S4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3eS35S90S0S5fS2dS8aS31VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aS36AcS5fS2cS2dS2fVcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S3S2S2S2SdS19A2M0S4A2M1S2S10S12A2M2A2M3A1S3S18Q40A1A1M4SdS19S4G2S11G4S10G4S42G3S1G1G2S1G0S4S1SdS19R8R7A4R6A4R5A4RaA3S2bS36R7R5A3S33S45Z0S2aS1G1G2S1G0S4S1SdS19RaR9A4R8A4R7A4R6A2M5A2S46G5R4A2A2S3cS0Vok;S22S0VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S3S2cA1S3S18Q40A1A1M0S3dS10G0S3cS0Vok;R3VFAMQ;R4A1A4S3cS0Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma S5_T : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S78A3S2bS36R6R4A3S3cS0Vok;S22S0VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads 300%nat cps_ad NP (map efdrop cutsS5) (map efdrop exitsS5) ok (FAMQ tp0) Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertS5_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS5_ok (triple segs ok) (famS cutsS5 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CF8_T CSF_T (reenterS cutsS5 tp0)
           (fun rho tp tp0' => rightS cutsS5 tp0 _ _ tp0' (XPK_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S37A1S5aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (X_L_ok (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok) CMC48_T
           (fun T nd k rv rho tp b tp0' Hi Hp _ => S5_T T nd k rv rho tp tp0' Hi Hp) rho tp tp0).
Qed.

Theorem epiDK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S5cR3A1S3cS0Vok;S22S0VJAv;S38A1S6fR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DP.epiD_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC FAMQ epiK_T
           (fun rho tp tp0 => X_P_errL (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_pre segs ok) (fun rho tp tp0' => XPE_T rho tp tp0') rho tp tp0)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S53S0S4cVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S10S42S10R1S5S10Z0S5S10Zf5S5S10Zf8S6S10A1A3A3A3A3S87S0S4cVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
S7fS0S4cVAInv;VCST;VXGL;S7dA6").
Variable FAM : ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3dF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S10S10S3S18Q40A1A1S3eS45R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XPK_E : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S77A1S75R3R2A5VFAM;S47Z158S48Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S76A1S74R3R2A5VFAM;S47Zd1S48Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CMC48_E : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3bS0S22S0S4eVAInv;R3VKc;A3S7bR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S7aS4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48X. exact HKc. Qed.
Lemma CF8_E : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3bS0S22S0S4eVAInv;R3VKc;A3S57R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S56S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CSF_E : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1S3bS0S22S0S50VAInv;Z5M0R3VKc;A4S71R2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S70S4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3eS35S8fS0S5fS2cS89S30VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aS36AcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S3S2S2S2SdS19A2M0S4A2M1S2S10S12A2M2A2M3A1S3S18Q40A1A1M4SdS19S4G2S11G4S10G4S42G3S1G1G2S1G0S4S1SdS19R8R7A4R6A4R5A4RaA3S2bS36R7R5A3S33S45Z0S2aS1G1G2S1G0S4S1SdS19RaR9A4R8A4R7A4R6A2M5A2S46G5R4A2A2S3bS0S22S0VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S3S2cA1S3S18Q40A1A1M0S3dS10S10G0S45R3R2A2S3bS0R5VFAM;R4R6A2A3S3bS0R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma S5_E : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S78A3S2bS36R6R4A3S3bS0S22S0VJAv;R8A1R9R5R4A5VFAM;S2aS1G3G0S1G2S4S1SdS19R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads 300%nat cps_ad NP cutsS5 exitsS5 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS5_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS5_ok (etriple segs) (famE cutsS5 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CF8_E CSF_E (reenterE cutsS5 tp0)
           (fun rho tp tp0' => rightE cutsS5 tp0 _ _ _ tp0' (Z.le_refl _) (XPK_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiK_E : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S37A1S5aR3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S5aS37A4U1A4S1S10S12Z167S44A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (X_L_ok (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs) CMC48_E).
  intros T nd k rv rho1 tp1 b tp0' Hi Hp Hm.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w (Z.lt_le_incl _ _ (proj2 Hm)) Hw) | exact (S5_E T nd k rv rho1 tp1 tp0' Hi Hp)].
Qed.

Theorem epiDK_E : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0S5cR3A1S3bS0S22S0VJAv;S38A1S6fR4R3A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S6fS38A4U0A4S1S10S12Z186S44A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DP.epiD_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX FAM FAM_mono epiK_E
           (fun rho tp tp0 => X_P_errL (etriple segs) FAM (TRe_pre segs) XPE_E rho tp tp0)).
Qed.
End Existence.
End Sum.
End Lib_load_obj_epiS5_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_blk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "ss_next"; "holds"; "sprop_eqb"; "SLit"; "SPUle"; "sobj"; "SPBranch"; "SPNot"; "agree_below"; "sprop_below"; "@Corelib.Init.Datatypes"; "true"; "list"; "bool"; "prod"; "app"; "pair"; "Some"; "cons"; "fst"; "nil"; "option"; "false"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "s_ad"; "kept_ad"; "Xk_ad"; "PDk_ad"; "go_fact"; "B32m"; "xfb_ad"; "xf_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "uval"; "BUD"; "bd_subst"; "BXok_d"; "bd_below"; "bd_wpos"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "AHead"; "amode"; "JA"; "PTrue"; "am_subst"; "ndesc"; "JAi"; "nd_tv"; "tvinA"; "JA_pre"; "TPA"; "am_eqb"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "nd_bd"; "nd_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs"; "nx500"; "ldef_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "ldefR"; "V_ldR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.ADP"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ";
"@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "import_tv"; "tvz"; "T_ok"; "tv_sub_eqb"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "T_afterA3"; "pdescA"; "pclMA"; "pd_okA"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "keptK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_load_obj_epiS_kit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiD_pf. End DP.

Section Le2.
Variable segs' : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S66S3S11S43Q40A1A1S44OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S11S13S13S20S20A2S20A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma BUD_le2 : ltac2:(tb__ "0|1|
S11S4A1S11S2aA1M0G0S13S20S20A2S20S20S20S3S5bS4S7R1A1R8A3S0S12S80R9R8R7A3S10A3S2cR8R7R6R5R4R3A6S2cRaR8R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;FBXv;Fbfrom;Fbto;Ffacts;").
Proof.
  intros facts bto bfrom BXv V Km Kf rho HF Hle H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  destruct (bud_le2_sound facts _ _ rho HF Hn Hle) as (L1 & L2 & L3 & L4 & L5).
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.
Lemma JAi_le2 : ltac2:(tb__ "0|1|
S11S4A1S11S13S2S2A2A1S11S13S13S2S20A2S2A2A1S11S2aA1M0G0S4aS66S20S3S11S43Q40A1A1S11S45A1S44S5bS4S7R4A1RcA3S0S12S80RdR9RaA3S10A3S4fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S48RdRcRbR9A4R8R7R6R5R4R3A12S4fVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S48ReRdRbRaA4R9R8R7R6R5R4A12F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fam;Fbd';Fbd;Ffr;Ftv;Ffacts;").
Proof.
  intros facts tv fr bd bd' am Ai kc rho tp tr md HF Hle HJ.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|].
  split; [|split; [exact HPA | split; [exact HCK | exact HCN]]].
  exact (BUD_le2 facts bd' bd _ _ _ _ rho HF Hle HBU).
Qed.
Lemma SPA_JA_le2 : ltac2:(tb__ "0|1|
S11S13S2S2A2A1S11S13S13S2S20A2S2A2A1S11S2aA1M0G0S4aS1dS3S11S43Q40A1A1S47S0S12S80S5S1eR4A1A1R6R7A3S10A3S3dVsegs';S4bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S48RaR9R8R6A4AcR5R4R3R2A6S3dVsegs';S4bVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S48RbRaR8R7A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fam;Fbd';Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd bd' am A rho tp [tr [ms md]] Hle [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  exact (JAi_le2 _ tv fr bd bd' am Ai kc rho tp tr md (smatchA_facts segs' _ _ _ _ Hsm) Hle HJ).
Qed.
End Le2.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S66S3S11S43Q40A1A1S44OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa0S32VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S20S82VCST;R1A2S1S5dZ0R2A2S5eR2S98A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S20S82VXGL;R1A2S1S5dZ0R2A2S5eR2S98A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S20S99R1A1S82VXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S11S13S13S20S20A2S20A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S35VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S4bVAInv;VCST;VXGL;S6aVKc;Vrho0;VP0;VFB;VFF;VBX;S4cVnd;Ac").

Lemma go_holdsL : ltac2:(tb__ "0|0|
S4eS3S11S43Q40A1A1S11S45A1S44S2S20S2S2S11S4A1VJAv;RaR9R8R7R6A5S40S13S2S2A2S15S2S2R6S61R5R3A2A4S50RbA1A3S1S5dZ1R6A2S5dR6Z80A2A2S5bS4S7RcA1R4A3S0S12S41S4S8SdScS83R7S9Z0A1A3A1A1R5A3S10A3S0S12S41S4S8SaR8R7A2A1R6A3S10A3S0S12S41S4S8SaR8S9S27A1A2A1R7A3S10A3S5bS4S7R10A1S17S4S26RcA1S19S4A1A3A3F_;F_;F_;F_;F_;F_;F_;FF;Fk;Fc;Fe;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof using ALA.
  intros nd rho tp tr md d e c k F HJ Hin He HF H0 H1 H2.
  pose proof (holds_mem _ _ _ HF H0) as F0. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  apply (proj1 (holds_nbeq _ _ _)) in F0. rewrite h_ule in F1, F2.
  change (bv_unsigned (eval rho c)) with (uval rho c) in F0. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in F0.
  rewrite uval_lit in F0 by lia. unfold B32m in F2. rewrite uval_lit in F2 by lia.
  assert (TNZ : tnz rho (d, kb e k)).
  { intros Hd.
    pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue nd rho tp tr md (d, kb e k) HJ Hin Hd) as Z0.
    cbn [snd] in Z0. change (bv_unsigned (eval rho (kb e k))) with (uval rho (kb e k)) in Z0.
    unfold kb in Z0. pose proof (uval_range rho k). pose proof (uval_range rho c). rewrite uval_mul_lit in Z0 by nia. assert (uval rho k = 0) by nia. lia. }
  pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA _ _ _ _ _ (d, kb e k) eq_refl HJ Hin TNZ) as TF.
  constructor; [|constructor].
  apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, go_fact. cbn [fst snd]. do 3 right. left. reflexivity.
Qed.

Lemma block_pclMAL : ltac2:(tb__ "0|2|
S66S3S11S13S2S2A2M0A1G0S20S51VFB;R5R4R3A4S8bR5R4A2S40G0R4R5A3S1S5dS2bR7S18S2S2R5A3A2M1R4A2S5eR4S5fG1S2bR7S1cS2S2R5A3A2A2A2A2S3S92VCST;R1S89VFB;R9R8A3S8fVFF;R9S33A3R6A5Fr0;F_;F_;F_;F_;Fa;Ft;Fkept;Frho;FAi;").
Proof using .
  intros Ai rho kept t a HN HZ Hin Ha r0.
  destruct (Z.eq_dec (uval rho (fst t)) 0) as [Hz|Hnz].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
    specialize (X ltac:(intros Y; apply Y; exact Hz)). unfold uval in Ha. lia.
  - right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split.
    + apply In_FBx. right. exists t. split; [exact Hin|]. split; [exact Hnz | symmetry; apply surjective_pairing].
    + unfold tvv. cbn [fst snd]. unfold uval in Ha. exact Ha.
Qed.

Lemma V_ldR_500 : V_below 500 V_ldR = true. Proof using . reflexivity. Qed.
Lemma V_ldR_lt : ltac2:(tb__ "0|0|
S1dS21S0S12S6bR2A1S10A3S40S21R2S6eA3Sa2R3S6S1eR4A1A1A2F_;F_;Fv;FA;").
Proof using . intros A v CV Hv. pose proof (proj1 (forallb_forall _ _) V_ldR_500 v Hv) as X. cbv beta in X. apply Pos.ltb_lt in X. apply Pos.leb_le in CV. lia. Qed.

Lemma ldefR_pure : ltac2:(tb__ "0|1|
S1dS3S3S0S12S6bR3A1S10A3SeS6S1eR4A1A1R3R2A3S6dR4A1M0G0F_;F_;F_;Frho';Frho;FA;").
Proof using . intros A rho rho' CV (H1 & H2 & H3) HP. exact (ldefR_reads rho rho' (fun v Hv => H1 v (V_ldR_lt A v CV Hv)) H2 H3 HP). Qed.
Lemma ldefR_call : ltac2:(tb__ "0|3|
S1dS11S13S2S2A2M0A1S3S3S5bS4S7R2A1S5S1eR4A1A1A3S0S12S6cS5S1eR5A1A1A1S10A3S0S12S6bR6A1S10A3S7bS6S1eR7A1A1R5R4A3S9eVCST;Vrho0;VFB;VFF;R6R7S33R5A8S40G0S15S2S2S79S77A4R8A3S0S20S2bR8S79A2Z0M1A3S0S20S2bR9S77A2G1A3F_;S6dR9A1M2G2F_;F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fkept;FA;").
Proof using .
  intros A kept rho rho' HF CF CV Hag HK Hin Hnull HP.
  unfold ldef_facts in CF. apply lazy_andb_prop in CF as [F1 CF]. apply lazy_andb_prop in CF as [F2 CF]. apply lazy_andb_prop in CF as [F3 CF].
  apply lazy_andb_prop in CF as [F4 F6].
  pose proof (holds_mem _ _ _ HF F1) as H1. rewrite h_ule, uval_lit in H1 by lia.
  pose proof (holds_mem _ _ _ HF F2) as H2. rewrite h_ule, uval_lit in H2 by lia.
  pose proof (holds_mem _ _ _ HF F3) as H3. rewrite h_ule, uval_lit in H3 by lia.
  pose proof (holds_mem _ _ _ HF F4) as H4. rewrite h_ule in H4.
  pose proof (holds_mem _ _ _ HF F6) as H6. rewrite h_ule, uval_lit in H6 by lia.
  pose proof (uval_range rho xLK) as RK. pose proof (uval_range rho xLD) as RD.
  assert (ESZ : uval rho szL = 16 * uval rho xLK) by (unfold szL, kb; apply uval_mul_lit; lia).
  fold szL in H1, H4. rewrite (uval_add_small rho xLD szL) in H4 by lia.
  apply (ldefR_keep rho rho'); [| | exact HP].
  - intros v Hv. apply (proj1 Hag). pose proof (proj1 (forallb_forall _ _) V_ldR_500 v Hv) as X. cbv beta in X. apply Pos.ltb_lt in X. apply Pos.leb_le in CV. lia.
  - intros z Hz.
    destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
    exact (keptK_lines CST FB FF rho0 rho kept frL rho' HK Hin Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz).
Qed.

Lemma HIN_ad : ltac2:(tb__ "0|2|
S1dS11SbA1S65S2S20S2S3S69S66S3S11S43Q40A1A1S44S0S12S84S5S1eRcA1A1S23S33S34RbA5S10A3S0S12S86S5S1eRdA1A1S23S33S85S24RdRaA2A5S10A3S0S2S64RcPdA2RbA3S0S2S64RdP10A2S61RbRaA2A3S40S13S2S2A2M0S15S2S2RdS61RcRbA2A4S23A3S5bS4S7RbA1S5S1eR11A1A1A3VP0;Vrho0;A1S7bS6aVrho0;RdA3VAInv;RcRbRaR9A4S53Vrho0;RdA2S8cR10S68S67ReA1A1A2S55VFB;RfA2S56VFF;R10A2S51VFB;R11R13S14G0S23S17G0S88S19G0A1A3A3M1A4S8eR14G1A2S8bR15G1A2S57VFF;R14R16S33A4S1S94VCST;Vrho0;VFB;VFF;R17S23S33R1cA8S1S96VCST;VXGL;Vrho0;VFB;VFF;R17S23S33S24R1dR1aA2A9S78VCST;S89VFB;R17S23A3S8fVFF;R17S33A3S63S62R17R1cR16A3R1bA2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;Fk;Fe;Fd;Fs;FR;FE;").
Proof using ALA HCST HXlits.
  intros E R s d e k rho ms Ai rho1 tp1 md1 CR CX Hs13 Hs16 Hin HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  assert (HNk : tvinA FB Ai rho kept_ad) by (apply (tvinA_sublist FB Ai rho (kept_ad ++ [blkAR])); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_ad) by (exact (tvd_app_l rho kept_ad [blkAR] HD)).
  assert (HZk : tvz rho kept_ad) by (apply (tvz_sublist rho (kept_ad ++ [blkAR])); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (DP.lo_robjsF0 AInv CST ALA HCST FB FF rho0 Ai rho _ kept_ad R rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_ad (Xk_ad E d) rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold ADP.P0_ad. intros a Ha. unfold uval, AD.vSRC, AD.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    exact (block_pclMAL Ai rho kept_ad (d, kb e k) a HNk HZk Hin Ha _).
Qed.

Lemma lines_in_kept_ad : ltac2:(tb__ "0|0|
S40S13S2S2A2S15S2S2S79S77A4S23A3").
Proof using . vm_compute. repeat (first [left; reflexivity | right]). Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S3eS1dS3S11S43Q40A1A1S46S5bS4S7R3A1S5S1eR4A1A1A3VTR;S3dS32R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S46S46S46S47R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S46OS46S47R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S3eS3eS1dS1dS65S11SbA1M0S11S13S1dS70A2M1A1S11S13S2S2A2M2A1S46S3S11S43Q40A1A1M3G2S40G2R1R5A3S40G2R2S1fRbA1A3F_;Fr;S0S1aG0A1S73RaR9R8A3S16G0R7A2A3S0S12S72RbRaR9R8S5cG1S1dS18S1dS70A2R7A4A5S10A3S3G3VTR;S3dS32RfRdR2R1A5S71S32S6S1eRdA1A1R2R1RaA5A2Ftp1;Frho1;S11S45A1M4S69S44S3fS32R9R8R10S15G4S75R3S76R2R1A2A4A5R13RaR9R4R2A4R13S63S62RbRfS60R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1dS70G4S69S44S3G3G4S69S44S40G1S15S1dS70RaR9A4R14A3S3fS32R12R11R19S15G4S75R9S76R8R7A2A4A5R1cR13R12RaR8A4S7bS6S1eR1aA1A1S63S62R14R18S60R9R13RaA3A3R19A2R8A3S3fS32R9R8ReS15G4S75R7S76R6R5A2A4A5ReS63S62R16R1aS60RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S9bR17S60RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S7cR18S60RdR17ReA3R1cR1dS1eR1eA1S1eR1fA1S1eR11A1R1RcA9VTR;S3dS32S74R11S63S62R19R1dS60ReR18RfA3A3R1eA2R18RdRcA5S9cR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S3dS32R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CAD : ltac2:(tb__ "0|1|
S11S13S20S20A2M0A1S11S13G0S20A2A1S31S3S11S43Q40A1A1S2eZ3R3A2VTR;S3dS32S52VAInv;VCST;VXGL;VKc;S78VCST;R6R5A3R6R5R4S4cS37AaS36R3R2A5S71S32S7eR3R2S9dVAInv;VCST;VXGL;VKc;S78VCST;A1S4cS25R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma X_BLK : ltac2:(tb__ "0|17|
S1dS1dS1dS1dS1dS1dS1dS1dS11SbA1M0S2S20S2S2S11S2aA1M1G1G1S2S46S3S11S43Q40A1A1M2S40S13S2S2A2M3S15S2S2RbS61RaR8A2A4S23A3S1S5dZ1RbA2S5dRbZ80A2A2S0S12S42S4SfS6S1eR16A1M4A1A1S14S4S17S4S26RdA1S19S4A1M5A3S5G4A1A3A3S10A3S0S12S41S4S8SdScS83RcS9Z0M6A1M7A3A1A1S5S1eR17A1A1A3S10A3S0S12S41S4S8SaRdRcA2A1S5S1eR18A1A1A3S10A3S0S12S41S4S8SaRdS9S27A1A2A1S5S1eR19A1A1A3S10A3S0S1aS1dA1M8S7fS9aS17S4S26R11A1G5A3R1aA2S29R1aA1A2S16S1dR19A2A3S0S12S95S24R1aR12A2S1fR1aA1A2S10A3S0S1aG0A1S73R1bS36S22R1bA1A3S16G0R14A2A3S0S12S72R1cS36S22R1cA1R15S5cS13S13S1dS4eA2M9S3S3OF_;F_;MaA2MbS1dGbS18S1dS4eS18G9GaR1A3A3Lp;S25A4A5S10A3S0S12S9fS6aS22R1dA1A2S10A3S0S12S7dS22R1eA1S7eA2S10A3S0S12Sa1S6aS6S1eR1fA1A1A2S10A3S0S12S5aS6S1eR20A1A1S48S14G3S23S17G3S88S19G3A1A3McA3MdS33S14S2aR14R13A3S49S7aS10A2MeA4A2S10A3S0S12S2fS6S1eR21A1A1S14S2aR15R13A3A2S10A3S0S12S8dS22R22A1GcS50S37A1A3S10A3S0S12S54S4dS22R23A1S58S37A1A2GeA2S10A3S0S12S97S14S2aR18R17A3MfGfA2S10A3S0S12S97S14S2aR19S14S2aS2dS22R25A1S59S37A1M10A2M11R17A3A3S14S2aG11S14S2aR19R17A3A3A2S10A3S0S12S30R1aA1S10A3S0S12S81S5S1eR27A1A1G7G6R1aS14S2aS2dS22R27A1G10A2R19A3A5S10A3S0S12S42S13S91GaA2M12G12S93S36S7eS22R29A1S6S1eR29A1M13A1S18S91GaR1A3A5Lp;S25A3S10A3S0S12S84S5G13A1S23S33S34R22A5S10A3S0S12S86S5S1eR2aA1A1S23S33S85S24R2aR22A2A5S10A3S0S2S64S22R2bA1PdA2R23A3S0S2S64S22R2cA1P10A2S61R23R21A2A3S0S12S6cS5S1eR2dA1A1A1S10A3S0S12S6bR2eA1S10A3S0S1dS90S36R2fS22R2fA1R28S39S24R2fR27A2A6R2eA3S0G8S7fR2fS28R2fA1A2S16S1dR2eA2A3S0S1dS87R2fA1R2eA3S0S11G3A1M14S8aS6fS22R32A1S36S39R32A4S3aA2GcA3S0S4aS4dS6fS22R33A1S36S39R33A4S3cA2S49R24S10A2A3S0S1dS90S36R34S22R34A1R2dS38S24R34R2cA2A6R30A3S0G8S7fR31S28R31A1A2S16S1dR30A2A3S0S1dS87R31A1R30A3S0G14S8aS6fS22R37A1S36S38R37A4S3aA2GcA3S0S4aS4dS6fS22R38A1S36S38R38A4S3bA2S49S7aS1bA2M15A3S3G2S6dR2A1M16VTR;S3dS32VJAv;S48GdS33S14S2aR30R2eA3S49R2dS10A2A4A1R39R3R2A5R2cA2F_;Ftp';Frho';S3G2G16VTR;S3dS32VJAv;S48GdS33S14S2aR31R2fA3G15A4A1R37R3R2A5R2dA2F_;Ftp';Frho';S6dR2aA1VTR;S3dS32VJAv;S48GdS33S14S2aR30R2fA3GeA4A1R3dR2bR2aA5R2cA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FqHk;Fdupn;Fdupj;Fbcom;Fk;Fc;Fe;Fd;FR;FTf;FTfB;FTf0;FTk;FTkB;FTk0;FE;FE0;").
Proof using ALA HCST HXGL HXlits HKc HBX TR_facts TR_ex TR_pre TR_pureP TR_callP CAD.
  intros E0 E Tk0 TkB Tk Tf0 TfB Tf R d e c k bcom dupj dupn qHk Q rho tp
         Hin He Hgb Hc0 Hck HkB HE HXk Hent Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham PP1 PP2 PWc PPay Hpd CR CX Hs13 Hs16 CF CV
         HTk0 HTkB HTk Itk Iak HTf0 HTfB HTf Itf Iaf HOk HFail HPHI.
  set (ndj := NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupj) (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndj) E rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndj) (xf_ad E0) rho (ax_add_facts [go_fact d] E0) E tp w HE).
    apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    apply (go_holdsL ndj rho tp tr md d e c k (ss_facts (ax_S E0)) HJ); [unfold ndj; cbn [nd_tv]; apply in_or_app; left; exact Hin | exact He | exact HF | exact Hc0 | exact Hck | exact HkB]. }
  apply TR_facts. intros HF.

  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndj] in HZ. intros E0'.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [apply in_or_app; left; exact lines_in_kept_ad|].
    unfold tnz. cbn [fst]. intros H. exact (H E0'). }
  intros Hnull.

  unfold ndj.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (ADP.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           AD.Pre_ad AD.nd0 PDk_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD eq_refl
           E (s_ad E) R (Xk_ad E d) rho tp kept_ad [blkAR] frL (bcom ++ dupj) (bcom ++ dupn) (AHead pH true) Q
           HXk Hent Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - unfold payA. exact (pay_okF_split _ _ _ _ (bcom ++ dupj) _ bcom dupj (bd_subst (s_ad E) (nd_bd AD.nd0) ++ dupn) PP1 PP2 PWc PPay).
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_ad E R (s_ad E) d e k rho ms Ai rho1 tp1 md1 CR CX Hs13 Hs16 Hin HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndLd] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : ldefR rho') by exact (ldefR_call E kept_ad rho rho' HF CF CV Hag HK lines_in_kept_ad Hnull HPHI).
    cbn [PDk_ad liftPD ADP.PD_ad map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-;
      cbn [fst snd nd_tv nd_bd nd_am AD.ndF AD.ndK].
    +
      rewrite HTf0, Itf, Iaf. change (bd_subst _ [] ++ ?r) with r.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead pH false))) Tf rho' tp')); [|exact (HFail rho' tp' HPHI')].
      intros w Hw. rewrite <- HTf. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_ad Tf0) rho' Tf0 TfB tp' w HTfB Hw).
    +
      rewrite HTk0, Itk, Iak. change (bd_subst _ [] ++ ?r) with r.
      apply (TR_pre (SPA segs (JAv (NDA (kept_ad ++ [blkAR]) frL (bcom ++ dupn) (AHead qHk true))) Tk rho' tp')); [|exact (HOk rho' tp' HPHI')].
      intros w Hw. rewrite <- HTk. apply SPA_tidy. exact (SPA_axforms segs _ (xfb_ad Tk0) rho' Tk0 TkB tp' w HTkB Hw).
Qed.
End X.
End Sum.
End Lib_load_obj_epiS_blk.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "true"; "app"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "SVar"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS_eqs"; "RB"; "zl"; "ndK"; "cutsS1"; "cutsS2a"; "cutsS2b"; "cutsS4"; "exitsS1"; "exitsS2a"; "exitsS2b"; "exitsS4"; "ndF"; "H_ecertS1_ok"; "H_ecertS2a_ok"; "H_ecertS2b_ok"; "H_ecertS4_ok"; "keep_ecertS1_ok"; "keep_ecertS2a_ok"; "keep_ecertS2b_ok"; "keep_ecertS4_ok"; "ndK8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "ndAt"; "brestAt"; "cps_b"; "B_1"; "B_2"; "B_3"; "B_4"; "B_5"; "B_6"; "B_7"; "L_cf0"; "L_v0a"; "L_v0b"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_succ"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "nd_s0"; "Es_fs0"; "K_succ"; "L_dz"; "L_sk"; "L_sn"; "T_fz2"; "T_nop2"; "T_ok2"; "cps_s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "PhisS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4"; "nd9"; "nd8"; "B_8"; "B_9"; "E_fu0"; "L_d6f"; "L_d7"; "L_land"; "T_fu"; "brest8"; "cps_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st1"; "E0_1"; "E0_2"; "E0_3"; "Tf_1"; "Tf_2"; "Tf_3"; "Tk_1"; "Tk_2"; "Tk_3"; "qHk_1"; "qHk_2"; "qHk_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st2"; "E0_4"; "E0_5"; "E0_6"; "Tf_4"; "Tf_5"; "Tf_6"; "Tk_4"; "Tk_5"; "Tk_6"; "qHk_4"; "qHk_5"; "qHk_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiS_st3"; "E0_8"; "Tf_8"; "Tk_8"; "qHk_8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiS_st3.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition zl (k : Z) : sv := SLit k.
Definition RB : Z := 391.

Definition ndK (j : nat) (qh : sv) : ndesc := ltac2:(tb__ "0|0|
ScS59S58S2bVj;A1SbVqh;S5A2A4").
Definition ndF (j : nat) : ndesc := ltac2:(tb__ "0|0|
ScS59S58S2bVj;A1SbS77S8A2A4").
Definition ndK8 : ndesc := ltac2:(tb__ "0|0|
ScS59S58S56SbS75S5A2A4").

Definition cutsS1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS76S40A4U0M4A4S0SdSeZ18fS39A4A4S1G3S0G1G2S0G0S2S0S9SaS47S3eA4G4A4S0SdSeZ18dS39A4M5A4S1G3S0G1G2S0G0S2S0S9SaS48S3fA4G4A4G5A4S1G3S0G1G2S0G0S2S0S9SaS46S3dA4G4A4G5A4S4G3A1A3A3A3A3").
Definition exitsS1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS41S40A4U0M4A4S0SdSeZ18eS39A4A4S1G3S0G1G2S0G0S2S0S9SaS45S3eA4G4A4S0SdSeZ18cS39A4M5A4S1G3S0G1G2S0G0S2S0S9SaS44S3fA4G4A4G5A4S1G3S0G1G2S0G0S2S0S9SaS43S3dA4G4A4G5A4S4G3A1A3A3A3A3").

Definition cutsS2a : list efnode := ltac2:(tb__ "0|4|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS42S3cA4U0A4S0SdSeZ18bS39A4A4S4G3A1A3").
Definition cutsS2b : list efnode := ltac2:(tb__ "0|16|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS2dS2aU1M4A1A4U0M5A4S0SdSeS13S14Z37aA1A4A4S1G3S0G1G2S0G0S2S0S9SaS60S15G4S63A2A4G5A4S0SdSeS13S14Z378A1A4M6A4S1G3S0G1G2S0G0S2S0S9SaS5dS2aU2M7A1M8A4G5A4G6A4S1G3S0G1G2S0G0S2S0S9SaS2eG8A4G5A4S0SdSeS13S14Z370A1A4A4S1G3S0G1G2S0G0S2S0S9SaS61S15G7S64A2A4G5A4S0SdSeS13S14Z36eA1A4M9A4S1G3S0G1G2S0G0S2S0S9SaS5eS2aU3MaA1MbA4G5A4G9A4S1G3S0G1G2S0G0S2S0S9SaS2fGbA4G5A4S0SdSeS13S14Z366A1A4A4S1G3S0G1G2S0G0S2S0S9SaS62S15GaS65A2A4G5A4S0SdSeS13S14Z364A1A4McA4S1G3S0G1G2S0G0S2S0S9SaS5fS2aU4MdA1MeA4G5A4GcA4S1G3S0G1G2S0G0S2S0S9SaS30GeA4G5A4S0SdSeS13S14Z35cA1A4A4S1G3S0G1G2S0G0S2S0S9SaS6cS15GdS6fA2A4G5A4S0SdSeS13S14Z35aA1A4MfA4S1G3S0G1G2S0G0S2S0S9SaS69S2aU5M10A1M11A4G5A4GfA4S1G3S0G1G2S0G0S2S0S9SaS31G11A4G5A4S0SdSeS13S14Z352A1A4A4S1G3S0G1G2S0G0S2S0S9SaS6dS15G10S70A2A4G5A4S0SdSeS13S14Z350A1A4M12A4S1G3S0G1G2S0G0S2S0S9SaS6aS2aU6M13A1M14A4G5A4G12A4S1G3S0G1G2S0G0S2S0S9SaS32G14A4G5A4S0SdSeS13S14Z348A1A4A4S1G3S0G1G2S0G0S2S0S9SaS6eS15G13S71A2A4G5A4S0SdSeS13S14Z346A1A4M15A4S1G3S0G1G2S0G0S2S0S9SaS6bS1eG13A1A4G5A4G15A4S1G3S0G1G2S0G0S2S0S9SaS33S2aU7A1A4G5A4S0SdSeS13S14Z33eA1A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsS2a : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS35S3cA4U0M4A4S0SdSeZ18aS39A4M5A4S1G3S0G1G2S0G0S2S0S9SaS34S3cA4G4A4G5A4S1G3S0G1G2S0G0S2S0S9SaS36S3cA4G4A4G5A4S4G3A1A3A3A3").
Definition exitsS2b : list efnode := ltac2:(tb__ "0|8|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS5aS2aU1A1A4U0M4A4S0SdSeS13S14Z379A1A4A4S1G3S0G1G2S0G0S2S0S9SaS5bS2aU2A1A4G4A4S0SdSeS13S14Z36fA1A4A4S1G3S0G1G2S0G0S2S0S9SaS5cS2aU3A1A4G4A4S0SdSeS13S14Z365A1A4A4S1G3S0G1G2S0G0S2S0S9SaS66S2aU4A1A4G4A4S0SdSeS13S14Z35bA1A4A4S1G3S0G1G2S0G0S2S0S9SaS67S2aU5A1A4G4A4S0SdSeS13S14Z351A1A4A4S1G3S0G1G2S0G0S2S0S9SaS68S2aU6M5A1A4G4A4S0SdSeS13S14Z347A1A4A4S1G3S0G1G2S0G0S2S0S9SaS52S1eG5A1A4G4A4S0SdSeS13S14Z345A1A4A4S1G3S0G1G2S0G0S2S0S9SaS53S2aU7A1M6A4G4A4S0SdSeS13S14Z33dA1A4M7A4S1G3S0G1G2S0G0S2S0S9SaS51G6A4G4A4G7A4S4G3A1A3A3A3A3A3A3A3A3A3").

Definition cutsS4 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS55S2aU7A1A4U0M4A4S0SdSeS13S14Z33cA1A4A4S1G3S0G1G2S0G0S2S0S9SaS4fS4eA4G4A4S0SdSeS13S14Z334A1A4A4S1G3S0G1G2S0G0S2S0S9SaS74S27A4G4A4S0SdSeS13S14Z332A1A4M5A4S1G3S0G1G2S0G0S2S0S9SaS73S4dA4G4A4G5A4S1G3S0G1G2S0G0S2S0S9SaS50S4dA4G4A4S0SdSeS13S14Z32aA1A4A4S4G3A1A3A3A3A3A3").
Definition exitsS4 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S9SaA2M0S2A2M1S3SdSeA2M2A2M3S0G1G2S0G0S2S0S9SaS72S4eA4U0M4A4S0SdSeS13S14Z333A1A4A4S1G3S0G1G2S0G0S2S0S9SaS54S4dA4G4A4S0SdSeS13S14Z329A1A4A4S4G3A1A3A3").

Definition keep_ecertS1_ok : list sprop := [].
Definition H_ecertS1_ok : list sprop := ltac2:(tb__ "0|0|
S4cS23S6S28S16S1aA3A2").
Lemma ecertS1_ok : ltac2:(tb__ "0|1|
S3aS7S29S3bS38S4aU12cS49S38S37S28S28S4bS1fA1M0S16A4S37S28S28G0S1aA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertS2a_ok : list sprop := ltac2:(tb__ "0|0|
S1SfS10S11P191A1S12Z10000000000A1A2S1SfS10S11PfA1S12Z800000000000A1A2S4SfA1A3A3").
Definition H_ecertS2a_ok : list sprop := ltac2:(tb__ "0|0|
S4cS24S6S28S17S1bA3A2").
Lemma ecertS2a_ok : ltac2:(tb__ "0|1|
S3aS7S29S3bS38S4aU12cS2cS38S37S28S28S4bS20A1M0S17A4S37S28S28G0S1bA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertS2b_ok : list sprop := ltac2:(tb__ "0|6|
S1SfS10S11P19aA1S12ZffffffffA1M0A2S1SfS10S11P191A1S12Z10000000000A1A2S1SfS10S11P197A1S11P198A1M1A2S1SfS10G1G0A2S1SfS10S11P1d1A1M2S12Z7fffff800000A1M3A2S1SfS10S11PcA1S12Z800000000000A1A2S1SfS10G2S11P1eA1M4A2S1SfS10G4G3A2S1SfS10S11P1a3A1S11P1a4A1M5A2S1SfS10G5G0A2S4SfA1A3A3A3A3A3A3A3A3A3A3").
Definition H_ecertS2b_ok : list sprop := ltac2:(tb__ "0|0|
S4cS25S6S28S18S1cA3A2").
Lemma ecertS2b_ok : ltac2:(tb__ "0|1|
S3aS7S29S3bS38S4aU12cS2cS38S37S28S28S4bS21A1M0S18A4S37S28S28G0S1cA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertS4_ok : list sprop := ltac2:(tb__ "0|4|
S1SfS10S11P1d1A1M0S12Z7fffff800000A1M1A2S1SfS10S11PcA1S12Z800000000000A1A2S1SfS10G0S11P1eA1M2A2S1SfS10G2G1A2S1SfS10S11P1a3A1S11P1a4A1M3A2S1SfS10G3S12ZffffffffA1A2S4SfA1A3A3A3A3A3A3").
Definition H_ecertS4_ok : list sprop := ltac2:(tb__ "0|0|
S4cS26S6S28S19S1dA3A2").
Lemma ecertS4_ok : ltac2:(tb__ "0|1|
S3aS7S29S3bS38S4aU12cS57S38S37S28S28S4bS22A1M0S19A4S37S28S28G0S1dA4A8S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_epiS_eqs.

