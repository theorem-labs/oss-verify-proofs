(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_shx f3.

(* [comment removed for export] *)
Module Lib_handle_f_s8w.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "negb"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w"; "G3back"; "L_win"; "Xw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "objs_butlast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xr_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "xlocal"; "@Stdlib.Lists.List"; "filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_shx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition G3back : axst := Eval vm_compute in g_back (T_afterA Pre_mc E_g3 (s_g E_g3) R_g3 L_mc1) E_g3_0 248.
Goal reopenX 38 39 G3back = T_g3. Proof. vmc. Qed.

Definition Xw (A : axst) : list (sv * sv) := ltac2:(tb__ "0|1|
S12S3S9S9A2M0G0S4SfR1S11Pa0S1S0S0Ze0Z24A4A2A2A1Lr;SeVA;A1A3").
Definition T_g3win (bL : Z) : axst := ltac2:(tb__ "0|0|
SdS6S8S6A1SaZ1cZ27ScZe0Z24VbL;A3A6").
Definition T_g3_0 : axst := Eval vm_compute in T_g3win 0.
Definition T_g3_4 : axst := Eval vm_compute in T_g3win 4.
Goal lvs T_g3_0 = [(vr_entry, RsCut)] /\ lvs T_g3_4 = [(vr_entry, RsCut)]. Proof. conj_vmc. Qed.

Definition E_mi4_0_0 : axst := Eval vm_compute in leaf_at T_g3_0 vr_entry 0.
Definition E_mi4_0_4 : axst := Eval vm_compute in leaf_at T_g3_4 vr_entry 0.
Definition L_win : list (Z * Z) := ltac2:(tb__ "0|1|
S2S3S0S0A2M0S1S0S0Z130Z4A4S2G0S1S0S0Ze0Z24A4S5G0A1A3A3").
Goal forallb (local_okP (ob_cells (sh_last E_mi4_0_0)) DUnknown 28 39) L_win = true /\ forallb (local_okP (ob_cells (sh_last E_mi4_0_4)) DUnknown 28 39) L_win = true.
Proof. conj_vmc. Qed.

Definition E_mi4_1w (E0 : axst) : axst := ltac2:(tb__ "0|0|
S10VE0;SbVE0;A1Pa0S7A4").
Goal (ax_setX (E_mi4_1w E_mi4_0_0) (ax_X E_mi4_1) = E_mi4_1 /\ ax_setX (E_mi4_1w E_mi4_0_4) (ax_X E_mi4_1) = E_mi4_1)
  /\ (xrs_inclb (ax_X E_mi4_1) (ax_X (E_mi4_1w E_mi4_0_0)) = true /\ xrs_inclb (ax_X E_mi4_1) (ax_X (E_mi4_1w E_mi4_0_4)) = true).
Proof. conj_vmc. Qed.
End Lib_handle_f_s8w.

(* [comment removed for export] *)
Module Lib_load_obj_hvpk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "sobj"; "SVar"; "ss_facts"; "SLit"; "SPEq"; "SPUle"; "cell"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "pair"; "cons"; "nil"; "fst"; "snd"; "Some"; "nat"; "None"; "andb"; "option"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tblB"; "P0_lo"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "True"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "div"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "xLK"; "xLC"; "pI"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "TPA"; "frinA"; "tvinA"; "JAi"; "NDA"; "PTrue"; "amode"; "nd_fr"; "nd_tv"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "xextraLO"; "robjs_chkC"; "xrs_chkC"; "xr_inlits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "extra_hv"; "PhisH"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "g8"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "wclear"; "xlocal"; "shobj"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.Sum"; "extraXlo"; "f5_locals"; "xr_f5local"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xr_eqb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import LOAddr LOLAddr.

Lemma PhisH_reads : ltac2:(tb__ "0|3|
S3aSfSeS1A1M0S3OF_;M1A2M2G2S71S15G0G1R1A3S16G0G1R1A3A2Lp;S57A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S2fS3SeS39Q40A1A1S32OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S74S64VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S50VCST;R1A2S21S26Z0R2A2S27R2S62A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S50VXGL;R1A2S21S26Z0R2A2S27R2S62A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S65R1A1S50VXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SeSfSfS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S3OFr;") := ltac2:(tb__ "0|0|
S1fVCST;VFB;VFF;A3").

Lemma lo_robjsF : ltac2:(tb__ "0|1|
S2fS3SeS4A1SeSfS2S2A2M0A1SeS6A1S3SeS39Q40A1A1S32VAInv;R8R3R2R1A4S3aS4S5R8A1R7A3VP0;Vrho0;A1S40S34Vrho0;RaA3S46Vrho0;RcA2S41RcS31S30RdA1A1A2S48VFB;ReRdRbA4S42ReRcA2S43RfRdA2S47VFF;R11R10S1dA4S20S10S51R10A1S11A3S3bG0S12S2S2S35S3fZ10S36A2A4R10A3S20S10S53R12R11S1dS56R10A5S11A3S6eVCST;Vrho0;VFB;VFF;R14R12S1dR11A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extra_hv R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. unfold extra_hv in HE. apply lazy_orb_prop in HE as [HE|HE].
  - exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
  - exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tv frL o a HF CLN HT0 HZ Hlin HE Hr).
Qed.
Lemma lo_xrsF : ltac2:(tb__ "0|1|
S2fS3SeS4A1SeSfS2S2A2A1M0G0S3SeS39Q40A1A1S32VAInv;R8R3R2R1A4S3aS4S5R8A1R7A3VP0;Vrho0;A1S40S34Vrho0;RaA3S46Vrho0;RcA2S41RcS31S30RdA1A1A2S48VFB;ReRdRbA4S42ReRcA2S43RfRdA2S47VFF;R11R10S1dA4S20S10S54R10RfS1dS52ReA5S11A3S70VCST;VXGL;Vrho0;VFB;VFF;R12R10S1dRfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv frL xextraLO X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tv frL r a Hav HP0 HE Ha).
Qed.
Lemma lo_robjsR : ltac2:(tb__ "0|1|
S2fS3SeS4A1SeSfS2S2A2M0A1SeS6A1S3SeS39Q40A1A1S32VAInv;R8R3R2R1A4S3aS4S5R8A1R7A3VP0;Vrho0;A1S40S34Vrho0;RaA3S46Vrho0;RcA2S41RcS31S30RdA1A1A2S48VFB;ReRdRbA4S42ReRcA2S43RfRdA2S47VFF;R11R10S1dA4S20S10S51R10A1S11A3S3bG0S12S2S2S35S3fZ10S36A2A4R10A3S20S10S58R12R11S1dS56R10A5S11A3S73VCST;Vrho0;VFB;VFF;R14R12S1dR11A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkR_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extra_hv R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. unfold extra_hv in HE. apply lazy_orb_prop in HE as [HE|HE].
  - exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
  - exact (robj_ent_pclMA CST rho0 FB FF rho _ _ tv frL o a HF CLN HT0 HZ Hlin HE Hr).
Qed.

Lemma site_rt_lo : ltac2:(tb__ "0|1|
S5bS6bSeS6A1S3SeSfS2S2A2M0A1SeS2eA1S4cS20S10S53S8S59R7A1A1R3S1dS56R5A5S11A3S20S10S54S8S59R8A1A1R4S1dS52S5aR8A1A5S11A3S20S10S51S8S59R9A1A1A1S11A3S3bG0S12S2S2S35S3fZ10S36A2A4R6A3S72VAInv;VCST;VXGL;S34Vrho0;VP0;VFB;VFF;RbRaR9R8S4aR7S1dR6R5A4S19S0A1S2fS5dS24L_;L_;AfF_;F_;F_;F_;Fam;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof using ALA HCST HXlits.
  intros E s R rho tv bd am CR CX CLN Hlin Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  pose proof (lo_robjsF Ai rho _ tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CLN Hlin CR) as HRF.
  pose proof (lo_xrsF Ai rho _ tv (ax_X E) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX) as HXF.
  assert (HN' : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.fbinA_FBx FB Ai rho tv [] HBf HN') as FBX. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.ffinA_FFx FF Ai rho frL HFF HFR) as FFX.
  split; [|split; [|exact I]].
  - intros o a Ho Hr. eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact (HRF o a Ho Hr)].
  - intros r a Hr Ha. destruct (HXF r a Hr Ha) as [Hc|Hc]; [left | right; exact Hc].
    eapply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA_cmaddrA CST rho0); [exact FBX | exact FFX | exact HT | exact Hc].
Qed.

Definition f5_locals : list (Z * Z) := ltac2:(tb__ "0|1|
S13SfS0S0A2M0S12S0S0Z1d0Z30A4S13G0S12S0S0Z220Z518A4S14G0A1A3A3").
Definition xr_f5local (k1 k2 : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|1|
S3cSfS0S0A2M0G0S1aS6fVr;S5fP6eR1A2A2S5eVk1;Vk2;S15S0S0R1A3S16S0S0R1A3A4A2Lol;S67A3").
Definition extraXlo (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S10S10L_;S52Vr;A1S11S55Vr;A1X10x2").
Definition xrs_chkRo (facts : list sprop) (tv : list (sv * sv)) (k1 k2 : Z) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S3dSfS2S2A2M0G0S1cS68Vk1;Vk2;R1A3S61VXGL;Vfacts;Vtv;S1dS17S18U0A2S14S6A1S66S13G0R1S14G0A1A3A8A2Lr;VX;A3").

Lemma lo_xrsRo : ltac2:(tb__ "0|3|
S2fS3SeS4A1SeSfS2S2A2M0A1M1G1S3SeS39Q40A1A1S32S0S0VAInv;RaR5R4R3A4S3aS4S5RaA1R9A3VP0;Vrho0;A1S40S34Vrho0;RcA3S46Vrho0;ReA2S41ReS31S30RfA1A1A2S48VFB;R10RfRdA4S42R10ReA2S43R11RfA2S47VFF;R13R12S1dA4S20S10S69R12R11RcRbR10A5S11A3G0S0S3bG0R2R13A3S21S26S2dR17S15S2S2R3A3A2M2R2A2S27R2S28G2S2dR17S16S2S2R3A3A2A2A2A2S23S23S6dVCST;Vrho0;S44VFB;R18R16A3S6cVFF;R18S45SfSfS2S0A2S2A2U0S1dA3A3R3A5S50VXGL;R3A2A2S22S0S0S22S0S0S21S20G0R6S5fP6eS12S0S0R2R1A4A2A3S21S26Z0R2A2S21S26Z1R1A2S21S26S28R2R1A2S63Z5A1A2S20S10S5eR13R12R2R1A4S11A3A2A2A2A2Llen;A2Loff;A2A2F_;F_;Fy;Fr;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk2;Fk1;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 k1 k2 HM HF HP0 Hav HT HTK HN HD HZ HFR Hchk r y Hr Hy.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  unfold xrs_chkRo in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. cbv beta in Hc. apply orb_prop in Hc as [Hc|Hc].
  - right. unfold xr_f5local in Hc. apply existsb_exists in Hc as ([off len] & Hin & Hc). apply andb_prop in Hc as [He Hw]. apply xr_eqb_sound in He.
    exists off, len. split; [exact He|]. cbn [fst snd] in Hw. change (fs_frame_size 5) with 2048.
    cbn [f5_locals In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | split; [lia | split; [lia | exact Hw]]]).
  - left.
    apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv frL (Some 0%nat) [] extraXlo [r] rho1 tp1 md1 HM HF HT0 HN HD HZ HFR Hc) with (r := r);
      [| left; reflexivity | exact Hy].
    intros r' a' [<-|[]] HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho tv _ r a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r rho a' HE Ha).
Qed.

Lemma tblB_absorb_sh : ltac2:(tb__ "0|5|
S4fS2fS0S3SeS39Q40A1A1SeS33A1S32S18S1S0S1S1S0S0SeScA1SdS5dS49VAInv;VCST;VXGL;S34VKc;Vrho0;VP0;VFB;VFF;VBX;S4bR11R10RfReRdRcRbA12S20S1bSfSfS2S0A2M0S2A2M1A1S3eG1S4dR12A1RbA3S17G1S12G0S2S12S2S0S7RaA1R9A4S7R8A1A4A2A3S21S26Z0M2RaA2S26RaZ6A2A2S26G2R8A2S21S26R9R8A2S26R8S2aS63RcA1Z8A2A2A2S5R13SaS5cRbA1S7ReA1A2A2S5R14SbS7RcA1S9S2cS29Z2M3Z3dA2Z1A2A1A2A2S3bSfS2S2A2S12S2S2S35S3fZ10M4S36A2A4S4eR18A1A3S25S20S0S2dR16S35A2G2A3A1S26S28S2dR17S35A2S2bG4S2dR17S36A2A2A2S29G3Z2fA2A2S27S2dR18S38A2S2dR18S37A2A2S26S2dR19S37A2S2dR19S36A2A2S1eR1aA1S1eS6aR1bS13S6S60R13R12R11R10RfA5S14S6A1A3ReA3A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fvm;Fd;Fcells;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;").
Proof using ALA HCST.
  intros nd Ai kc rho tp tr md i pR c pF g k1 k2 cells d vm HJ Hnth Hc6 Hk1 Hk2 HG1 HG2 Hlin Hnz Hk64 HiC Hck HPHI.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & _).
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md (nd_fr nd) fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & _).
  cbn [frv fst snd fe] in E1, F1, F2, F3, F4, F5. set (sz := fs_frame_size c) in *. set (p := uval rho (SVar pR)) in *.
  pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END, SHADOW_OFF, IMG_HI in F4; lia).
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia. change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  set (sh := shobj g k1 k2 cells d).
  assert (Hrng : obj_range rho sh = (Sh p + k1, Sh p + k2)).
  { unfold obj_range, obj_lo_of, obj_hi_of, sh, shobj. cbn [ob_base ob_lo ob_hi eval]. rewrite Ug. unfold Sh, SHADOW_OFF in *. rewrite !soff_lit_small by lia. f_equal; lia. }
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SHAD : forall z, Sh p + k1 <= z < Sh p + k2 -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }

  pose proof (proj1 (Forall_forall _ _) HN _ Hlin) as HL. cbv beta in HL.
  assert (Htnz : tnz rho (xLD, kb 16 xLK)) by (unfold tnz; cbn [fst]; exact Hnz).
  destruct (HL Htnz) as (_ & Hlive & _).
  assert (Ekb : uval rho (kb 16 xLK) = 16 * uval rho xLK).
  { unfold kb. pose proof (uval_range rho xLK). pose proof (uval_range rho xLD). apply uval_mul_lit; lia. }
  unfold tvv in Hlive. cbn [fst snd] in Hlive. change (bv_unsigned (eval rho xLD)) with (uval rho xLD) in Hlive.
  change (bv_unsigned (eval rho (kb 16 xLK))) with (uval rho (kb 16 xLK)) in Hlive. rewrite Ekb in Hlive.
  apply (tblB_kept rho (rho_absorb rho [sh] vm)); [intros v _; reflexivity | | exact HiC | exact Hck | exact HPHI].
  intros z Hz. apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr.
  pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho xLK) as RK.
  rewrite u64_lit in Hr by lia. cbn [fst snd] in Hr.
  apply (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None z rho tp md HM); [|exact (SHAD z Hr)].
  right; right; left. exists (uval rho xLD), (16 * uval rho xLK). split; [exact Hlive|]. split; [discriminate | lia].
Qed.
End Sum.
End Lib_load_obj_hvpk.

(* [comment removed for export] *)
Module Lib_fuzz_one_epi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "bool"; "true"; "nil"; "Some"; "prod"; "list"; "option"; "pair"; "app"; "fst"; "negb"; "orb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "has_facts"; "ax_setS"; "axwf"; "entailsA"; "g8"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sv"; "sprop"; "ss_objs"; "DUnknown"; "SVar"; "mkObj"; "obj_wf"; "SPEq"; "SPUle"; "cell"; "sv_eqb"; "swf"; "DZero"; "SAlu"; "ob_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_fuzz_one_epi"; "K_sx"; "K_sx2"; "X_u1"; "X_u3"; "C_epi"; "X_fin"; "X_rl1"; "C_rl"; "K_sx3"; "K_sx1"; "X_sx2"; "X_u2"; "X_u4"; "cfg_mid"; "s_fin"; "s_sxE"; "s_sxK"; "X_ret"; "X_rl"; "X_sx"; "sel_rel"; "xf_sx"; "xf_un1"; "xf_un2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one"; "gF"; "Fx"; "nx"; "vF"; "oBack"; "pFL"; "runF"; "showL"; "body_shape"; "cfg_obj"; "glob_shape"; "oH"; "pF"; "pc_rel"; "shapes"; "vCFG"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Stdlib.Lists.List"; "nth_error"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "O_W_fz"; "fz_facts"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "P_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad"; "L_sxE"; "L_sxK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue"; "vDN"; "vH"; "al_facts"; "vG10"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "fz_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.LD"; "cfg_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "flag_carve_stateA"; "release_objs_ok"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_one.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.

Definition K_sx : axst := Eval vm_compute in upd_obj_at (keep_below 184 (junkRN [1; 19]%nat L_sxK)) 1 nocells_obj.
Definition s_sxE : wsub := ltac2:(tb__ "0|0|
S5cS47S16S65A1S16S2fA1A3").
Definition s_sxK : wsub := ltac2:(tb__ "0|0|
S5cS47S16S66A1S16S2fA1A3").

Definition cfg_mid : sobj := ltac2:(tb__ "0|0|
S25S4bS1fZ20A1S1fZb0A1S4S29A1S23A5").
Definition xf_sx : list axform := ltac2:(tb__ "0|2|
S0S10S12S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U6S0S1U5M0S0S1U7S0S1U8S0S1U9S0S1UaS4S1A1A3A3A3A3A3A3A3A3A3A3A3A1S0S10S13G0A1M1S0S10G1S4S10A1A3A3A3").
Definition X_sx (A : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S60S6S20S20A2M0G0ScSdS2aSbS20S20R1A3M1S4bA2S2aG1S57A2A2A1Lr;S1cVA;A1A3").
Definition K_sx1 : axst := Eval vm_compute in ax_setS K_sx (reshape_obj_at (ax_S K_sx) 5 cfg_mid).
Definition K_sx2 : axst := Eval vm_compute in optL (apply_axforms K_sx1 xf_sx).
Definition X_sx2 : list (sv * sv) := Eval vm_compute in X_sx K_sx2.
Definition K_sx3 : axst := Eval vm_compute in shadow_reopen_stateA K_sx2 X_sx2 gF 0 32.
Definition C_epi : axst := Eval vm_compute in flag_carve_stateA K_sx3 pFL.

Definition X_rl : axst := Eval vm_compute in leafF (runF C_epi) pc_rel 0.

Definition sel_rel : list nat := ltac2:(tb__ "0|0|
S0S1U0S0S1U1S0S1U2S0S1U3S0S1U4S0S1U7S0S1U8S0S1U5S0S1U6S0S1U9S0S1UaS4S1A1A3A3A3A3A3A3A3A3A3A3A3").
Definition X_rl1 : axst := Eval vm_compute in optL (apply_axforms X_rl [AXSelect sel_rel]).
Definition C_rl : axst := Eval vm_compute in ax_setS X_rl1 (set_objs (ax_S X_rl1) (firstn 7 (ss_objs (ax_S X_rl1)))).
Definition X_ret : axst := Eval vm_compute in leafF (runF C_rl) fz_ret 0.

Definition xf_un1 : list axform := ltac2:(tb__ "0|2|
S0S10S12S0S1U2S0S1U0M0S0S1U1S0S1U3S0S1U4S0S1U5S0S1U6S4S1A1A3A3A3A3A3A3A3A1S0S10S13G0A1M1S0S10G1S4S10A1A3A3A3").
Definition X_u1 : axst := Eval vm_compute in optL (apply_axforms X_ret xf_un1).
Definition X_u2 : axst := Eval vm_compute in ax_setS X_u1 (reshape_obj_at (ax_S X_u1) 0 oBack).
Definition xf_un2 : list axform := ltac2:(tb__ "0|1|
S0S10S13U0M0A1S0S10S14G0S1fN180A1A2S4S10A1A3A3").
Definition X_u3 : axst := Eval vm_compute in optL (apply_axforms X_u2 xf_un2).
Definition X_u4 : axst := Eval vm_compute in ax_setS X_u3 (reshape_obj_at (ax_S X_u3) 0 O_W_fz).
Definition X_fin : axst := Eval vm_compute in optL (apply_axforms X_u4 [AXSelect [1;0;2;3;4]%nat]).
Definition s_fin : wsub := ltac2:(tb__ "0|0|
S5cS47S16S34A1S16S64A1A3").

Lemma fz_checks_sx : ltac2:(tb__ "0|5|
SfSeS2S19S2fA1S3A3SfSeS2S1aS65S2fS3eA3S3A3SfSeS2S1aS66S2fS3fA3S3A3SfSeS2S5dS3eS47A2S3A3SfSeS2S5dS3fS47A2S3A3SfSeS7S6S6S20S20A2M0S20A2M1A1S56S2fA1SaG1S50S52A3A3SfSeS8S1eA1S5fS1eS22S16S2fA1M2A1U5M3A3S5S1eS51S72S2cA2A2A3SfSeS2S26S4aS2fA1S3cA2S3A3SfSeS15S18S2fS5eG2G3S3cA3A2S38A3SfSeS8S15A1S11S38S44A2S5S15S30A2A3SfSeS7G0A1S42S30A1S39A3SfSeS20S1dS30A1S1fS76A1A3SfSeS2S17S0S21S27S1bS48A1S4bA2S0S21S28S24S48A1S1fS6cS6bZ2Z3dA2Z1A2A1A2S4S21A1A3A3S49S30A1A2S3A3SfSeS15S75S30S39S48Z0Z20A5S37A3SfSeS2S2bS16S37A1A1S3A3SfSeS15S73S37S4dA2S33A3SfSeS2S2bS16S33A1A1S3A3SfSeS2S19S33A1S3A3SeS7S6S58S59A2M4A1S4fS4eS33A1A1S0G4S9S58S59S55S5aA4S4G4A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_checks_rl : ltac2:(tb__ "0|e|
SfSeS8S15A1M0S11S41S0S10S12S43A1S4S10A1M1A3A2S5S15S35A2A3SfSeS15S18S35S5bS16S35A1M2S6dS1eU7M3S22G2A1M4A3A2A2S36A3SfSeS2S74S54S4dS48Z2M5S6fS1eG3G4A3A5S3A3SfSeS2S17S0S21S27S1bS48A1S4bA2S0S21S28S24S48A1S1fS6cS6bG5Z3dA2Z1A2A1A2S4S21A1A3A3S49S35A1A2S3A3SfSeS2S19S36A1S3A3SfSeS7S6S58S59A2M6A1S4fS4eS36A1A1S0G6S9S58S59S71S5aA4S4G6A1A3A3SfSeG0S11S40S45A2S5S15S31A2A3SfSeS8S1eA1M7S5fS1eS22S16S31A1M8A1M9U0MaA3S5S1eS25S68S67S1fZ118A1S2eS6eS1eGaG9S53A4A1S23A5A2A3SfSeS2S26S4aS31A1S4cA2S3A3SfSeS2S17S62S49S31A1MbA2S3A3SfSeS2S17S69S68S67S6aA3GbA2S3A3SfSeS15S18S31S5eG8GaS4cA3A2S3aA3SfSeG0S11S3aS46A2S5S15S32A2A3SfSeG7S5fS1eS22S16S32A1McA1GaA3S5S1eS25S24PaA1S2dS70S63S1fN180A1MdA3GdS4S29A1S23A5A2A3SfSeS2S26S4aS32A1S61A2S3A3SfSeS2S17S62S49S32A1A2S3A3SfSeS15S18S32S5eGcGaS61A3A2S3bA3SfSeG0S11S3bS0S10S12S0S1U1S0S1GaS0S1U2S0S1U3S0S1U4S4S1A1A3A3A3A3A3A1G1A3A2S5S15S34A2A3SfSeS2S1aS34S64S3dA3S3A3SfSeS2S5dS3dS47A2S3A3SeS2S77S47S4aS34A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_fuzz_one_epi.

(* [comment removed for export] *)
Module Lib_load_obj_loopEf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "list"; "nat"; "bool"; "nil"; "true"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SAlu"; "SLit"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndE0f"; "ndXEf"; "ndLf"; "cutsE2f"; "exitsE2f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "uval"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "JA"; "NDA"; "am_eqb"; "am_subst"; "nd_below"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblL"; "tblB"; "s_loop"; "P0_lo"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "LAX"; "LAXK"; "RL"; "VLA"; "ndL"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "K_afterE2"; "X_bodyE2"; "X_latchE2"; "K_loopE2"; "ndE0"; "PhisE"; "X_errxE2"; "X_latchE2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "pI"; "xLC"; "HNEXT"; "cps_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "JAF"; "bud_le2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition ndLf (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S21S2bS2aVbd;S1fS3dS8A2A4").
Definition ndXEf : ndesc := ltac2:(tb__ "0|1|
S16S2S1bS2fZ0M0A1S2S1bS30G0A1S6S1bA1A3A3A1").
Definition ndE0f : ndesc := ndLf [].

Definition cutsE2f : list efnode := ltac2:(tb__ "0|5|
S2S1S1S1S19S1eA2M0S4A2M1S1S9ScA2M2A2M3S0G1G2S0G0S4S0S19S1eS38S14A4U0M4A4S0S9ScS31S32Z1aS2eA2A4A4S2G3S0G1G2S0G0S4S0S19S1eS36S14A4G4A4S0S9ScS31S32Z19S2eA2A4A4S6G3A1A3A3").
Definition exitsE2f : list efnode := ltac2:(tb__ "0|6|
S2S1S1S1S19S1eA2M0S4A2M1S1S9ScA2M2A2M3S0G1G2S0G0S4S0S19S1eS35S14A4U0M4A4S0S9ScZ190S2eA4M5A4S2G3S0G1G2S0G0S4S0S19S1eS3bS14A4G4A4G5A4S6G3A1A3A3").
Lemma ecertE2f_ok : ltac2:(tb__ "0|0|
S12S5S4aSaS2dS3aU96S41S2dS17S18A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma loopEf_checks : ltac2:(tb__ "0|3|
S11S12S5S24S40S15A2S7A3S11S12S5S49SfS1aS3cA1A1S1dS28S6S1bA1M0A2S2S1bS2fZ0M1A1S2S1bS30G1A1G0A3A3A3S7A3S12S5S22S23S28S1fS3dS8A2M2A2G2A2S7A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4cSbS3S25Q40A1A1S46OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4bSaVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S43VCST;R1A2S11S44Z0R2A2S45R2S42A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S43VXGL;R1A2S11S44Z0R2A2S45R2S42A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
SbOFr;") := ltac2:(tb__ "0|0|
S29VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S20VAInv;VCST;VXGL;S2dVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;S2dVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;VPhi;Vnd;Ad").

Lemma pot_dropF : ltac2:(tb__ "0|0|
SbOF_;S3S1bA1S19SbS3S25Q40A1A1S2cS10SaVJAFv;R6S33R5A1A2R4R3R2R1A6S10SaVJAFv;R7S16R6A1A2R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fbd;FPhi;").
Proof.
  intros Phi bd A rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA Phi (ndL bd) A rho tp w Hw) as [HS HP].
  apply (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA Phi (ndLf bd) A rho tp w); [|exact HP].
  exact (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvL frL bd pH A rho tp w HS).
Qed.
Lemma relaxF_latchE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2cS10SaVJAFv;S27S34A2S37R3R2R1A6S10SaVJAFv;S27S15A2S37R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblB [LAX 0; LAXK 0] X_latchE2 rho tp w). Qed.
Lemma relaxF_bodyE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2cS10SaVJAFv;S26S39A2S36R3R2R1A6S10SaVJAFv;S26S14A2S36R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblL [] X_bodyE2 rho tp w). Qed.
Lemma relaxF_afterE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2cS10SaVJAFv;S26S39A2S35R3R2R1A6S10SaVJAFv;S26S14A2S35R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblL [] K_afterE2 rho tp w). Qed.

Lemma latch_absorbE2f : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2cS27R3A1S10SaVJAv;S15A1S37R4R3R2A6S13SbSbS11S26R1A1S11S10SaVJAv;S14A1S38R1R5R4A6S11S12S9S1cR1S3fA2S1cR6S3fA2A3S12S9S1cR1S3eA2S1cR6SdS47S3eSeZ1A1A3A2A3A2A2A2Lrho2;A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof loopEf_checks as (Cnb & Cbud & Cam).
  exact (latch_absorbE2 AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX PA rho0 [LAX 0; LAXK 0] [] (AHead pH false) rho tp w Cnb Cbud Cam HP HS).
Qed.
End Sum.
End Lib_load_obj_loopEf.

(* [comment removed for export] *)
Module Lib_load_obj_certA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "SVar"; "SLit"; "SAlu"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "ndA1"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_certA"; "cutsA"; "exitsA"; "FUEL_A"; "H_ecertA_ok"; "PhisA"; "keep_ecertA_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "X_dp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "K_after0R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "V_L"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "K_body"; "K_l2l"; "K_loop"; "K_tk"; "K_ws"; "X_bodyN"; "X_latch"; "X_latch7"; "cps_loop"; "pE"; "pQ"; "pR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition PhisA : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S1S3S7ScA1M0S13OFrho;M1A2M2S0G0G1S29S2bA4S1G2S0G0G1S28S2aA4S4G2A1A3A3").

Definition cutsA : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S9SaA2M0S2A2M1S3SbSdA2M2A2M3S0G1G2S0G0S2S0S9SaS2eS16A4U0A4S0SbSdS14S15Z1aS17A2A4A4S1G3S0G1G2S0G0S2S0S9SaS2cS16A4U1M4A4S0SbSdS14S15Z18S17A2A4A4S1G3S0G1G2S0G0S2S0S9SaS30S16A4G4A4S0SbSdS14S15Z17M5S37A2A4A4S1G3S0G1G2S0G0S2S0S9SaS2fS16A4G4A4S0SbSdS14S15Z16S12S24S35S36A3A2A4A4S1G3S0G1G2S0G0S2S0S9SaS2dS16A4G4A4S0SbSdS14S15G5S17A2A4A4S4G3A1A3A3A3A3A3").
Definition exitsA : list efnode := ltac2:(tb__ "0|7|
S1S3S3S3S9SaA2M0S2A2M1S3SbSdA2M2A2M3S0G1G2S0G0S2S0S9SaS31S16A4U0M4A4S0SbSdS14S15Z19S17A2A4A4S1G3S0G1G2S0G0S2S0S9SaS27S16A4G4A4S0SbSdZ190S17A4A4S1G3S0G1G2S0G0S2S0S9SaS26S16A4U1M5A4S0SbSdS14S15Z15S17A2A4A4S1G3S0G1G2S0G0S2S0S9SaS32S18A4G5A4S0SbSdS14S15Z1S17A2A4M6A4S1G3S0G1G2S0G0S2S0S9SaS33S18A4G5A4G6A4S4G3A1A3A3A3A3A3").
Definition FUEL_A : nat := 150%nat.

Definition keep_ecertA_ok : list sprop := ltac2:(tb__ "0|4|
S1SeSfS10P1d3A1M0S10P1d4A1M1A2S1SeSfS10P1d2A1S11Z800000000000A1M2A2S1SeSfG1S11ZffffffffA1A2S1SeSfG0S10PeA1M3A2S1SeSfS10PdA1G2A2S1SeSfG3S11Z4000000A1A2S4SeA1A3A3A3A3A3A3").
Definition H_ecertA_ok : list sprop := ltac2:(tb__ "0|0|
S39S21S5S19S1cS1dA3A2").
Lemma ecertA_ok : ltac2:(tb__ "0|1|
S23S6S1aS25S22S20S1eS34S22S1bS19S19S38S1fA1M0S1cA4S1bS19S19G0S1dA4A8S8A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_certA.

(* [comment removed for export] *)
Module Lib_load_obj_hv1e.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hv1e"; "sde"; "sdm"; "cutsH1"; "exitsH1"; "H_ecertH1_ok"; "keep_ecertH1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SVar"; "SPUle"; "SLit"; "sv"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "mH"; "PhisH"; "@Corelib.Lists.ListDef"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "E_da1"; "E_da2"; "E_da3"; "E_sd1r"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "K_hv0c"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition sdm (k : Z) : Z * sv := mH 16 (40 - 4 * k).
Definition sde (k : Z) : Z * sv := mH 16 (42 - 4 * k).
Definition cutsH1 : list efnode := ltac2:(tb__ "0|d|
S1S3S3S3S8S9A2M0S2A2M1S3S1cS15A2M2A2M3S0G1G2S0G0S2S0S8S9S2bSaA4U1M4A4S19Z10Z28A2A4S1G3S0G1G2S0G0S2S0S8S9S2cSaA4G4A4ScZ1A1M5A4S1G3S0G1G2S0G0S2S0S8S9S2dSaA4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S2eSaA4G4A4ScZ2A1M6A4S1G3S0G1G2S0G0S2S0S8S9S2fSaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S30SaA4G4A4ScZ3A1M7A4S1G3S0G1G2S0G0S2S0S8S9S31SaA4G4A4G7A4S1G3S0G1G2S0G0S2S0S8S9S32SaA4G4A4ScZ4A1M8A4S1G3S0G1G2S0G0S2S0S8S9S33SaA4G4A4G8A4S1G3S0G1G2S0G0S2S0S8S9S34SaA4G4A4ScZ5A1M9A4S1G3S0G1G2S0G0S2S0S8S9S35SaA4G4A4G9A4S1G3S0G1G2S0G0S2S0S8S9S36SaA4G4A4ScZ6A1MaA4S1G3S0G1G2S0G0S2S0S8S9S37SaA4G4A4GaA4S1G3S0G1G2S0G0S2S0S8S9S38SaA4G4A4ScZ7A1MbA4S1G3S0G1G2S0G0S2S0S8S9S39SaA4G4A4GbA4S1G3S0G1G2S0G0S2S0S8S9S3aSaA4G4A4ScZ8A1McA4S1G3S0G1G2S0G0S2S0S8S9S3bSaA4G4A4GcA4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsH1 : list efnode := ltac2:(tb__ "0|7|
S1S3S3S3S8S9A2M0S2A2M1S3S1cS15A2M2A2M3S0G1G2S0G0S2S0S8S9S23SaA4U1M4A4SbZ1A1A4S1G3S0G1G2S0G0S2S0S8S9S24SaA4G4A4SbZ2A1A4S1G3S0G1G2S0G0S2S0S8S9S25SaA4G4A4SbZ3A1A4S1G3S0G1G2S0G0S2S0S8S9S26SaA4G4A4SbZ4M5A1A4S1G3S0G1G2S0G0S2S0S8S9S27SaA4G4A4SbZ5A1A4S1G3S0G1G2S0G0S2S0S8S9S28SaA4G4A4SbZ6A1A4S1G3S0G1G2S0G0S2S0S8S9S29SaA4G4A4SbZ7A1A4S1G3S0G1G2S0G0S2S0S8S9S2aSaA4G4A4SbZ8A1A4S1G3S0G1G2S0G0S2S0S8S9S20SaA4G4A4S19Z10G5A2M6A4S1G3S0G1G2S0G0S2S0S8S9S21SaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S22SaA4G4A4G6A4S1G3S0G1G2S0G0S2S0S8S9S3dSaA4G4A4S19ZfZ64A2A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3A3").

Definition keep_ecertH1_ok : list sprop := ltac2:(tb__ "0|2|
S1S11S16S12P1ccA1S12P1d3A1M0A2S1S11S13S12P191A1S14Z10000000000A1A2S1S11S13G0S12PeA1M1A2S1S11S13G1S14Z4000000A1A2S4S11A1A3A3A3A3").
Definition H_ecertH1_ok : list sprop := ltac2:(tb__ "0|0|
S3fS10S5S17SdSeA3A2").
Lemma ecertH1_ok : ltac2:(tb__ "0|1|
S1eS6S18S1fS1dS1aU258S3cS1dS1bS17S17S3eSfA1M0SdA4S1bS17S17G0SeA4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_hv1e.

