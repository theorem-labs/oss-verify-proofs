(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh na.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "SLit"; "dflt_writable"; "ob_base"; "ob_hi"; "ob_lo"; "ss_objs"; "sv_eqb"; "swf"; "@Corelib.Init.Datatypes"; "andb"; "false"; "bool"; "prod"; "nat"; "negb"; "None"; "Some"; "orb"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "fr_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "feF"; "bF"; "fF"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "is_shx"; "xloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robjs_checkF"; "shadow_reopen_stateA"; "wclear"; "xrs_checkL"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.

Definition release0_chk (A : axst) (k1 k2 : Z) (d : odefault) : bool := ltac2:(tb__ "0|0|
SbSbSbSbS14Z0Vk1;A2S14Vk1;Vk2;A2A2S14Vk2;Z40A2A2S4Vd;A1A2S21S2S1cVA;A1A1A1A2").

Definition is_shx (k1 k2 : Z) (o : sobj) : bool := ltac2:(tb__ "0|7|
S0SdLx;M0S5Vo;A1S16ScLz;S17G0S7Vo;A1S16G0S6Vo;A1S16SbSbSbSbS25R3S1fA2S14S1bR2A2A2S14R2R1A2A2S14R1S15S1bZ40A2A2A2S13S14R1S15S1bVk1;A2A2S14S15S1bVk2;A2R2A2A2A2Lhi;S17ScLi;M1S19S0S0ScLb;La;M2Lop;M3G3S1aG2Lop;M4G4SdS18S0ScLa;Lw;Lsgn;M5S17S0S16ScLk;Li;Ll;M6X0x8Llo;G1G3G3G4G4G5G6X0x8Lg;G3G3G4G4G5G6X0x8").

Definition xloc_ok (k1 k2 : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|9|
SeS0S0A2SdLr;Vr;S0S0S0SdLs;R2S16ScLz;M0S17ScLi;M1S19S0S0S19SdLop;R3S0SdLa;R2G0S17S0SdLb;R2S16S0SdLs0;R6S16SbSbSbSbS25R3Pa0A2S14Z0R2A2A2S14Z1R1A2A2S14S15R2R1A2Z200A2A2S2dVk1;Vk2;R2R1A4A2Llen;G1S19S0S0ScLb0;La0;M2Lop0;M3G3S1aG2Lop0;M4G4SdS18S0ScLa0;Lw;Lsgn;M5S17S0S16ScLk;Li;Ll;M6X0x8Loff;G1G3G3G4G4G5G6X0x8Lp;G3G3G4G4G5G6X0x8ScScScScScScScScScX19xaLb;La;Lop;S19S0S0ScLb;La;M7Lop;S1aG7Lop;M8G8SdS18S0ScLa;Lw;Lsgn;G6X0x8Ls0;Ls;Xex1").

Definition reopenS_chk (XGL : list (Z * Z)) (A : axst) (X' : list (sv * sv)) (tv : list (sv * sv)) (k1 k2 : Z) : bool := ltac2:(tb__ "0|4|
SbSbSbSbSbSbSbSbSbSbS9S1eVA;A1S3S1bA1A2S14Z0Vk1;A2A2S14Vk1;Vk2;A2A2S14Vk2;Z40A2A2S21S2S1cVA;A1M0A1M1A1A2S2aVX';S1dVA;A1A2A2SaS1cS2cVA;VX';S1fVk1;Vk2;A5A1A1A2S22G1A1A2S23G1A1A2S2bG1Vtv;S20S11SfA1S26S24S1S1S10S28Vk1;Vk2;R1A3A1Lo;S8G0A1M2A3A6A2S2eVXGL;G1Vtv;S20S12SfU0A2G2S27S24SeS0S0A2M3G3S10S29Vk1;Vk2;R1A3A1Lr;VX';A3A8A2").
End Lib_handle_f_gdefs3.

(* [comment removed for export] *)
Module Lib_handle_f_g1b.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "E_co0"; "T_cok"; "pA"; "pKco"; "pQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "E_co1"; "coF"; "liveF"; "vrF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.
Lemma co_coF : ltac2:(tb__ "0|0|
S2S0SbS3S4SaA1A1A1S1A3"). Proof. vmr. Qed.
Lemma cok_live : ltac2:(tb__ "0|0|
S2S0ScS7Z1S8S3S4S6A1A1A4S1A3"). Proof. vmr. Qed.
Lemma co_vrF : ltac2:(tb__ "0|0|
S2S0SdS9S3S4S5A1A1A2S1A3"). Proof. vmr. Qed.
End Lib_handle_f_g1b.

(* [comment removed for export] *)
Module Lib_handle_f_g2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "Some"; "option"; "andb"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pD2"; "pA"; "pQ"; "X_body"; "pK2"; "ndR"; "pDco"; "pKco"; "pT0"; "reshapeA"; "slot_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "E_pc2"; "T_da2"; "T_dg2"; "T_pc2"; "pure_chk"; "rsF"; "vrF"; "slotF"; "xff_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_facts"; "ss_next"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "sv_below"; "SPUle"; "obj_wf"; "sprop"; "sprop_eqb"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "tE"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "E_pc1"; "E_pc"; "T_pc0"; "xslot"; "E_da"; "pc_need"; "sel_da"; "E_da0"; "E_pc0"; "R_da"; "R_pc"; "T_da"; "T_da0"; "T_pc"; "T_pc1"; "s_da"; "s_pc"; "sel_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "xr_eqb"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "E_dg"; "R_dg"; "T_dg"; "T_dg0"; "ndXA"; "s_dg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2"; "P_ret"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_pc2_eq : ltac2:(tb__ "0|0|
S0S16S13S3aU22S14SaSbA2A3S1dA3"). Proof. vmr. Qed.
Lemma E_pc_eq3 : ltac2:(tb__ "0|0|
S0S16S5aS3fS12ScA2S38S1dS3S8S26S26A2S3dSaSbA2S17S1dA1A3A2A2S3bA3"). Proof. vmr. Qed.
Lemma pc_o34 : ltac2:(tb__ "0|2|
S0S6S28A1S4fS28S34S15S3aA1A1U22A3S5S28S2eSaS35ZcM0SbA2M1S2cS39G1S27G0A1A3S4S2dA1S2bA5A2A3"). Proof. vmr. Qed.
Lemma pc_wf : ltac2:(tb__ "0|1|
S0S1S31S2aS15S3aA1A1S2eS2cS39SaS35ZcM0SbA2A3S27Z0A1S27G0A1S4S2dA1S2bA5A2S2A3"). Proof. vmr. Qed.
Lemma pc_rs : ltac2:(tb__ "0|0|
S0S1S22SaS35ZcSbA2S29S15S3aA1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xin : ltac2:(tb__ "0|0|
S0S1S4eS8S26S26A2S4dS9S26S26SaS35ZcSeA2A4A1S17S1dA1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xb : ltac2:(tb__ "0|0|
S0S1S18S2aS15S1dA1A1S3dSaSbA2A2S2A3"). Proof. vmr. Qed.
Lemma pc_slotF : ltac2:(tb__ "0|0|
S0S1S24SbSeS29S15S1dA1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xff : ltac2:(tb__ "0|0|
S0S1S25S38S1dS3S8S26S26A2S3dSaSbA2S17S1dA1A3A2S3fS12ScA2A2S2A3"). Proof. vmr. Qed.
Lemma pc_pcF : ltac2:(tb__ "0|1|
S0S1S7S4eS32S33S30ScS36A2A1S29S15S1dA1A1M0A3S4eS32S33S30S36S37A2A1G0A3A2S2A3"). Proof. vmr. Qed.
Lemma pc_chk : ltac2:(tb__ "0|0|
S0S1S21S59S58S3bSfS4aS44A6S2A3"). Proof. vmr. Qed.
Lemma T_pc2_eq : ltac2:(tb__ "0|1|
S0S6S16A1S1cS48S3S19S1bS4bA1S3S19S1aU0A1S3S19S1aU20A1M0S3S19G0S4S19A1A3A3A3A3A2S5S16S20A2A3"). Proof. vmr. Qed.
Lemma T_pc_eq2 : ltac2:(tb__ "0|0|
S0S16S38S20SdSaSeA2A2S47A3"). Proof. vmr. Qed.
Lemma tpc_o2 : ltac2:(tb__ "0|1|
S0S6S28A1S4fS28S34S15S3cA1A1U2A3S5S28S2eS2cS39SaS35ZcM0SbA2A3S27Z0A1S27G0A1S4S2dA1S2bA5A2A3"). Proof. vmr. Qed.
Lemma tpc_wf : ltac2:(tb__ "0|2|
S0S1S31S2aS15S3cA1A1S2eSaS35ZcM0SbA2M1S2cS39G1S27G0A1A3S4S2dA1S2bA5A2S2A3"). Proof. vmr. Qed.
Lemma tpc_rs : ltac2:(tb__ "0|0|
S0S1S22SaS35ZcSbA2S29S15S3cA1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xsub : ltac2:(tb__ "0|0|
S0S1S4cSdSaSeA2S17S20A1A2S2A3"). Proof. vmr. Qed.
Lemma pc_vrF : ltac2:(tb__ "0|0|
S0S1S23ScS29S15S42A1A1A2S2A3"). Proof. vmr. Qed.
Lemma pc_meas : ltac2:(tb__ "0|1|
S0S1S7S2fS2aS15S3bA1A1M0S36A2S2fG0ScA2A2S2A3"). Proof. vmr. Qed.

Lemma da_chk : ltac2:(tb__ "0|0|
S0S1S21S51S50S3eSfS49S43A6S2A3"). Proof. vmr. Qed.
Lemma T_da2_eq : ltac2:(tb__ "0|0|
S0S6S16A1S1cS46S3S19S1bS40A1S3S19S1aU0A1S4S19A1A3A3A2S5S16S1eA2A3"). Proof. vmr. Qed.
Lemma T_da_eq2 : ltac2:(tb__ "0|0|
S0S16S38S1eSdSaSeA2A2S45A3"). Proof. vmr. Qed.
Lemma da_xsub : ltac2:(tb__ "0|0|
S0S1S4cSdSaSeA2S17S1eA1A2S2A3"). Proof. vmr. Qed.
Lemma da_vrF : ltac2:(tb__ "0|0|
S0S1S23ScS29S15S41A1A1A2S2A3"). Proof. vmr. Qed.
Lemma da_meas : ltac2:(tb__ "0|1|
S0S1S7S2fS2aS15S3eA1A1M0S36A2S2fG0ScA2A2S2A3"). Proof. vmr. Qed.
Lemma dg_chk : ltac2:(tb__ "0|0|
S0S1S21S51S50S52S56S57S53A6S2A3"). Proof. vmr. Qed.
Lemma T_dg2_eq : ltac2:(tb__ "0|0|
S0S6S16A1S1cS55S3S19S1bS40A1S3S19S1aU0A1S4S19A1A3A3A2S5S16S1fA2A3"). Proof. vmr. Qed.
Lemma T_dg_eq2 : ltac2:(tb__ "0|0|
S0S16S38S1fSdS10S11A2A2S54A3"). Proof. vmr. Qed.
Lemma dg_xsub : ltac2:(tb__ "0|0|
S0S1S4cSdS10S11A2S17S1fA1A2S2A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g2.

(* [comment removed for export] *)
Module Lib_handle_f_g1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sv_eqb"; "SVar"; "SLit"; "ss_next"; "ss_objs"; "sprop"; "ss_facts"; "DZero"; "cell"; "sv_below"; "SPAlign"; "SPUle"; "mkCell"; "sprop_eqb"; "swf"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "andb"; "nil"; "cons"; "prod"; "bool"; "list"; "true"; "app"; "pair"; "Some"; "nat"; "None"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pQ"; "pDco"; "E_co"; "pKco"; "s_co"; "pK2"; "E_sm0"; "T_sm1"; "s_sm"; "tv0"; "tv_body"; "bd_loop"; "pD2"; "JR_co"; "L_sm"; "Pre_sm"; "R_sm"; "X_hf0"; "X_pro"; "co_need"; "nd0"; "objs_pro"; "objs_sm1"; "C_pro0"; "E_co0"; "JF_co"; "R_co"; "T_cof"; "T_cog"; "T_cok"; "T_coks"; "Xkeep"; "cVF"; "fr_hf"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "tE"; "NPH"; "PROG"; "hF"; "hFL"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "tv0"; "P_fail"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "brest_co"; "kept_co"; "s_cog"; "s_cok"; "E_co1"; "land_chk"; "bF"; "bd2_cog"; "bd2_cok"; "bdG_co"; "bdK_co"; "cells_pro"; "s_cof"; "xff_chk"; "release_chk"; "tv2_cof"; "tv2_cog"; "tv2_cok"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_get"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_below"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraXH"; "extraOH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "frame_open_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_FLAG"; "V_RES"; "flagbyte_obj"; "@Stdlib.Lists.List"; "existsb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma sm_chk : ltac2:(tb__ "0|8|
S11S16S12S12S12S12S12S12S12S12S12S12S12S12S50S25S2eS27S2fS14S4dS2dS13S4dA1A3A5S80S47S27A2A2S70S47S5S4cS25A1M0A1M1A2A2S75G1S33A2A2S44S74S33A1A1A2S2S6fS4fS27S2eS2dS25A4M2S84A2S3Pa0M3A1A2A2S70G1G3A2A2S2S6fG2S83A2S3PaaM4A1A2A2S70G1G4A2A2S61S8G0A1M5A1A2S81G5S28S13S15S15S0S72A2S0A2A1M6S1dS1cA1M7S78S2fA6A2S7aVXGL;G5S28G6G7S6G0A1S77S4eS25A1A8A2S2S6fS27PcA2S4Z140A1A2A2S18A3").
Proof. vmr. Qed.

Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S11S17S1A1S6S4cS26A1A1S19S1S35S14S1S85S4aS14SaSeS4Z0A1Z1M0S4G0A1A3S13SaA1A3A2S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S4eS26A1S19G0S30S14G0S1aS0S0S49S4Z200A1A4S13G0A1A3A3A3"). Proof. vmr. Qed.
Lemma sm1_chk : ltac2:(tb__ "0|7|
S11S16S12S12S12S12S12S12S10S4cS7bS26S35S19S15S0S0A2M0S30S13G0A1A3M1Pa0M2Z200A5A1A1S70S47S5S4cS26A1M3A1M4A2A2S75G4S79A2A2S61S8G3A1M5A1A2S7aVXGL;G5S28S40S1bS1cU0A2S6G3A1S77G1A8A2S86S7SfScG2Z5A2A1S8S4cS36A1M6A1A3A2S71G2S5G6A1A2A2S18A3").
Proof. vmr. Qed.

Lemma X_pro_objs : ltac2:(tb__ "0|0|
S11S17S1A1S6S4cS31A1A1S19S1S34S14S1S7cS4bZ0Z40S66S9A5S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma pro_chk : ltac2:(tb__ "0|0|
S11S16S69S31S34Z0Z40S66S9S13S15S72S72A2A1S28S74S79A1A9S18A3"). Proof. vmr. Qed.

Lemma E_co1_eq : ltac2:(tb__ "0|0|
S11S1eS4dA1S7eS37S41U13Z2d0A2A2S1bS4dS5fA2A3"). Proof. vmr. Qed.
Lemma E_co_eq2 : ltac2:(tb__ "0|0|
S11S4dS7dS32S1fA1S5fA2S21A3"). Proof. vmr. Qed.
Lemma co_xff : ltac2:(tb__ "0|0|
S11S16S68S5fS32S1fA1A2S18A3"). Proof. vmr. Qed.
Lemma co_tvp : ltac2:(tb__ "0|1|
S11S16S7fS29S20S22A2S19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3A2S18A3"). Proof. vmr. Qed.
Lemma co_chk : ltac2:(tb__ "0|0|
S11S16S6dVXGL;S21S5cS20S22ZcZ2d0S2aS1fS22A2S5bS23S39S3eS20A1AcS18A3"). Proof. vmr. Qed.
Lemma co_iK : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S53S21A4S54A2S14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_iF : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S55S21A4S54A2S14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_iG : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S52S21A4S58A2S14G0S1aS0S0S3P208A1S45ZcS3P209A1A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_bK : ltac2:(tb__ "0|0|
S11S17S42A1S43S4fS23S51S53S21A4S74S57A1A2S65A3"). Proof. vmr. Qed.
Lemma co_bG : ltac2:(tb__ "0|0|
S11S17S42A1S43S4fS23S51S52S21A4S56S5aS59A2A2S64A3"). Proof. vmr. Qed.

Lemma cok_xff : ltac2:(tb__ "0|0|
S11S16S68S3cS14S7SdS4S82A1S20A2S13S7A1A3A2S18A3"). Proof. vmr. Qed.
Lemma cok_land : ltac2:(tb__ "0|1|
S11S16S60S3dS2cS5eS19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3S6cS19S42S65S5bA3S63S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cok_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S5eS2aS1fS24A2A2S63A3"). Proof. vmr. Qed.
Lemma cog_land : ltac2:(tb__ "0|1|
S11S16S60S3bS2cS5dS19S15S0S0A2M0S5cS14G0S1aS0S0S3P208A1S45ZcS3P209A1A2A4S13G0A1A3A3S6bS19S42S64S5bA3S62S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cog_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S5dS2aS1fS24A2A2S62A3"). Proof. vmr. Qed.
Lemma cof_land : ltac2:(tb__ "0|2|
S11S16S60S3aS38S67S19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3S6aS76S42U1S5bA3M1G1S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cof_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S67S14S42S48S3fS1fA2S13S42A1A3A2S76S42U1S5bA3A3"). Proof. vmr. Qed.
Lemma cof_wp : bd_wpos brest_co = true. Proof. vmr. Qed.

Lemma co_meas : ltac2:(tb__ "0|1|
S11S16S12S12S12S12S12S2S6eS5eS46A2S46A2S2S6eS5eS1fA2S1fA2A2S2S6eS5dS46A2S46A2A2S2S6eS5dS1fA2S1fA2A2SbS5S4cS21A1A1M0S46A2A2SbG0S1fA2A2S18A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g1.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "cons"; "nil"; "nat"; "None"; "app"; "pair"; "prod"; "Some"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sprop_eqb"; "SPUle"; "cell"; "sv_eqb"; "DUnknown"; "mkObj"; "mkCell"; "SAlu"; "ss_facts"; "ss_objs"; "sv"; "SPBranch"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "s_pg"; "E_pg"; "R_pg"; "Xk_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "pDts"; "pKrp"; "needA"; "pDrp"; "pKts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "fr_hf"; "pA"; "am2"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "nd_bd"; "nd_below"; "nd_tv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pKtr"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.PG"; "Pre_pg"; "P_inv"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.PGC"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "bF"; "fF"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "off_g1"; "off_g2"; "off_g3"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6.AR"; "o4A"; "o16A"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "flag_carve_stateA"; "robjs_checkF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "co_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "XLJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs.

Definition cs_md : list cell := ltac2:(tb__ "0|2|
S1SeS12SaZ70A1Z8M0SaZ0A1M1A3S1SeS12SaZ48A1Z4G1A3S1SeS12SaZ40A1G0G1A3S2SeA1A3A3A3").

Definition cells_g1a : list cell := Eval vm_compute in ob_cells (sh_last E_g1_1).
Definition cells_g1b : list cell := Eval vm_compute in ob_cells (sh_last E_g1_2).
Definition off_g1 : sv := Eval vm_compute in off_of E_g1_3.
Definition xf_g1 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZe0A1A2S1S1aS1bU2SaZecA1A2S1S1aS1bU22S45A2S1S1aS1bU23S13S38S45SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g1a : axst := Eval vm_compute in optAp (apply_axforms E_g1_3 xf_g1).
Definition E_g1b : axst := Eval vm_compute in reshapeA E_g1a 2 (mkObj (xfo 224) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g1c : axst := Eval vm_compute in reshapeA E_g1b 35 (mkObj (SAlu ALU_ADD pDco off_g1) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g1t : axst := Eval vm_compute in T_afterA Pre_mc E_g1 (s_g E_g1) R_g1 L_mc1.
Definition T_g1u : axst := Eval vm_compute in reshapeA T_g1t 1 (mkObj hF (SLit 224) (SLit 236) [] DUnknown).
Definition T_g1v : axst := Eval vm_compute in reshapeA T_g1u 2 (mkObj pDco off_g1 (SAlu ALU_ADD off_g1 (SLit 12)) [] DUnknown).

Definition off_g2 : sv := Eval vm_compute in off_of E_g2_0.
Definition xf_g2 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZecA1A2S1S1aS1bU2SaZf8A1A2S1S1aS1bU22S46A2S1S1aS1bU23S13S38S46SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g2a : axst := Eval vm_compute in optAp (apply_axforms E_g2_0 xf_g2).
Definition E_g2b : axst := Eval vm_compute in reshapeA E_g2a 2 (mkObj (xfo 236) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g2c : axst := Eval vm_compute in reshapeA E_g2b 35 (mkObj (SAlu ALU_ADD pDco off_g2) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g2t : axst := Eval vm_compute in T_afterA Pre_mc E_g2 (s_g E_g2) R_g2 L_mc1.
Definition T_g2u : axst := Eval vm_compute in reshapeA T_g2t 1 (mkObj hF (SLit 236) (SLit 248) [] DUnknown).
Definition T_g2v : axst := Eval vm_compute in reshapeA T_g2u 2 (mkObj pDco off_g2 (SAlu ALU_ADD off_g2 (SLit 12)) [] DUnknown).

Definition off_g3 : sv := Eval vm_compute in off_of E_g3_0.
Definition xf_g3 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZf8A1A2S1S1aS1bU2SaZ104A1A2S1S1aS1bU22S47A2S1S1aS1bU23S13S38S47SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g3a : axst := Eval vm_compute in optAp (apply_axforms E_g3_0 xf_g3).
Definition E_g3b : axst := Eval vm_compute in reshapeA E_g3a 2 (mkObj (xfo 248) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g3c : axst := Eval vm_compute in reshapeA E_g3b 35 (mkObj (SAlu ALU_ADD pDco off_g3) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g3t : axst := Eval vm_compute in T_afterA Pre_mc E_g3 (s_g E_g3) R_g3 L_mc1.
Definition T_g3u : axst := Eval vm_compute in reshapeA T_g3t 1 (mkObj hF (SLit 248) (SLit 260) [] DUnknown).
Definition T_g3v : axst := Eval vm_compute in reshapeA T_g3u 2 (mkObj pDco off_g3 (SAlu ALU_ADD off_g3 (SLit 12)) [] DUnknown).
Definition T_g3w : axst := Eval vm_compute in optAp (apply_axforms T_g3v [AXSelect sel_g; AXMerge 1; AXMerge 1; AXMerge 32; AXMerge 32]).

Definition T_tdg2 : axst := Eval vm_compute in optAp (apply_axforms T_tdg0 [AXSelect sel_da; AXMerge 0]).
Definition T_wdg2 : axst := Eval vm_compute in optAp (apply_axforms T_wdg0 [AXSelect sel_wdg; AXMerge 0]).

Definition objs_XJ : list sobj := Eval vm_compute in removelast (ss_objs (ax_S XJ)).
Definition objs_J : list sobj := Eval vm_compute in removelast objs_XJ.
Definition XJ1 : axst := Eval vm_compute in shadow_release_stateA XJ objs_XJ 160 [].
Definition XLJf : axst := ltac2:(tb__ "0|0|
S63S1SbS60S2SbA1A3S61A2").
Definition XLJ1 : axst := Eval vm_compute in shadow_reopen_stateA XLJf (ax_X XLJf) hG 28 33.

Definition objs_E (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Definition objs_Ef42 : list sobj := Eval vm_compute in objs_E XEf42.
Definition objs_Eo42 : list sobj := Eval vm_compute in objs_E XEo42.
Definition objs_Ef6a : list sobj := Eval vm_compute in objs_E XEf6a.
Definition XEf6a1 : axst := Eval vm_compute in shadow_release_stateA XEf6a objs_Ef6a 160 [].
Definition objs_Ef6a1 : list sobj := Eval vm_compute in objs_E XEf6a1.
Definition objs_Ef6b : list sobj := Eval vm_compute in objs_E XEf6b.
Definition XEf6b1 : axst := Eval vm_compute in shadow_release_stateA XEf6b objs_Ef6b 160 [].
Definition objs_Ef6b1 : list sobj := Eval vm_compute in objs_E XEf6b1.
Definition objs_Eo6 : list sobj := Eval vm_compute in objs_E XEo6.
Definition XEo61 : axst := Eval vm_compute in shadow_release_stateA XEo6 objs_Eo6 160 [].
Definition objs_Eo61 : list sobj := Eval vm_compute in objs_E XEo61.

Definition E_f5o1 : axst := Eval vm_compute in shadow_reopen_stateA E_f5o0 (XR E_f5o0) hG 0 64.
Definition E_f5f1 : axst := Eval vm_compute in shadow_reopen_stateA E_f5f0 (XR E_f5f0) hG 0 64.
Definition T_f5o1 : axst := Eval vm_compute in optAp (apply_axforms T_f5o0 (xf_shback T_f5o0)).
Definition T_f5f1 : axst := Eval vm_compute in optAp (apply_axforms T_f5f0 (xf_shback T_f5f0)).
Definition objs_f5o1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_f5o1)).
Definition objs_f5f1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_f5f1)).
Definition sh_f5o1 : sobj := Eval vm_compute in sh_last T_f5o1.
Definition sh_f5f1 : sobj := Eval vm_compute in sh_last T_f5f1.
Definition X_rlo1 : axst := Eval vm_compute in optAp (apply_axforms X_rlo [AXSelect sel_rel]).
Definition X_rlf1 : axst := Eval vm_compute in optAp (apply_axforms X_rlf [AXSelect sel_rel]).

Definition liveLF (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S1cSbScSdS2bVk;A2A1VF;A3S1cSbScS17S39SaZ2A1S2bA3A1VF;A3A2S1cSbScSdVk;SaS55A1A2A1VF;A3A2").

Definition carve_chk (XGL : list (Z * Z)) (A : axst) (objs : list sobj) (tv : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0SfS31VA;A1SaS6bA1A2S19S2fS5dVA;PaaA2A1A1A2S42S14S2fVA;A1M0A1M1A1A2S43G1A1A2S5eG1Vtv;S2aS4S3A1S3cVobjs;A6A2S5cVXGL;G1Vtv;S2aS8S3U0A2S15G0A1S3dS30VA;A1A8A2").

Definition cells_pg : list cell := Eval vm_compute in ob_cells (sh_last E_pg0).
Definition E_pg0r : axst := Eval vm_compute in shadow_release_stateA E_pg0t (objs_butlast E_pg0t) 160 [(160, 24); (48, 72)].
Definition E_pg3a : axst := Eval vm_compute in reshapeA E_pg3 43 O_nxt'.
Definition E_pg3b : axst := Eval vm_compute in reshapeA E_pg3a 45 O_prv'.
Definition O_nxt : sobj := ltac2:(tb__ "0|0|
S11S25S4bS4cS2SeA1S10A5").
Definition O_prv : sobj := ltac2:(tb__ "0|0|
S11S25S4dS4eS2SeA1S10A5").
Definition O_rfx : sobj := ltac2:(tb__ "0|0|
S11S25S4fS50S2SeA1S10A5").
Definition O_nxt1 : sobj := ltac2:(tb__ "0|0|
S11S52SaZ0A1S4aS2SeA1S10A5").
Definition O_prv1 : sobj := ltac2:(tb__ "0|0|
S11S53SaZ0A1S4aS2SeA1S10A5").
Definition O_rfx1 : sobj := ltac2:(tb__ "0|0|
S11S54SaZ0A1S51S2SeA1S10A5").
Definition pgF (F : list sprop) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S44VF;A1S1cSbScSdS25SaS56A1A2A1VF;A3A2S1cSbScSdS22Z3M0S2bA2S26A2A1VF;A3A2S1cSbScSdS26SaS55A1M1A2A1VF;A3A2S1cSbScSdS22G0S2cA2S3aA2A1VF;A3A2S1cSbScSdS3aG1A2A1VF;A3A2S1cSbScSdS27S29A2A1VF;A3A2").
Definition pg0F (F : list sprop) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S43VF;A1S1cSbScSdSaS6aA1M0S28A2A1VF;A3A2S1cSbScSdG0S3bA2A1VF;A3A2S1cSbScSdG0S25A2A1VF;A3A2S1cSbScSdS22ZcS2bA2S22Z4M1S26A2A2A1VF;A3A2S1cSbScSdS22G1S22Z3S2cA2A2S22G1S3aA2A2A1VF;A3A2").

Definition pg_call_chk (XGL : list (Z * Z)) : bool := ltac2:(tb__ "0|9|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S67S21S30S1fA1A2S64S1fS3eS1eS20S5fS7S2eS32A2M0S2eS9S2eS32A2S1G0S6S2eS32S3fS41A4S1G0S6S2eS32S40S41A4S2G0A1A3A3M1A4A5A2S68S23S1eA2A2S62S1eS57A2A2S6cS23S18S2fS1fA1M2A1M3A2A2S36G3S34S5S7S16S16A2M4S37S49A1M5S2G4A1A3S2aS5S58S5aS1eS2S58A1A2S35S49A1M6A3S33A4A2A2S59G3G6A2A2S5bG6A1A2S1dS66S65S3eS57S1eG3A4G1A3A2S42S14G2A1M7A1A2S69G7G5S2aS4S3A1M8S3cS20A6A2S5cVXGL;G7G5S2aG8S15G2A1S3dS21A8A2SfS24S1ePcA2S2dZ30A1A2A2SfS24S1ePdA2S2dZa0A1A2A2SfS24S1ePeA2S2bA2A2SfS24S1ePfA2S28A2A2SfS24S1eP10A2S3bA2A2SfS24S1eP11A2S25A2A2SfS24S1eP12A2S27A2A2S48G7A1A2").

Definition T_pgoa : axst := Eval vm_compute in reshapeA T_pgo0 8 O_nxt0.
Definition T_pgob : axst := Eval vm_compute in reshapeA T_pgoa 9 O_prv0.
Definition T_pgo2 : axst := Eval vm_compute in optAp (apply_axforms T_pgo1 xf_pgb1).
Definition T_pgo3 : axst := Eval vm_compute in pg_back1 T_pgo1.
Definition T_pgo4 : axst := Eval vm_compute in optAp (apply_axforms T_pgo3 xf_pgb2).
Definition T_pgoR1 : axst := Eval vm_compute in shadow_reopen_stateA T_pgo XT hG 6 15.
Definition T_pgia : axst := Eval vm_compute in reshapeA T_pgi0 8 O_nxt0.
Definition T_pgib : axst := Eval vm_compute in reshapeA T_pgia 9 O_prv0.
Definition T_pgic : axst := Eval vm_compute in pg_back0 T_pgi0.
Definition cs_pgi : list cell := ltac2:(tb__ "0|0|
S1SeS12SaZ8A1Z4SaZ0A1A3S2SeA1A3").
Definition T_pgi2 : axst := Eval vm_compute in optAp (apply_axforms T_pgi1 xf_pgb1).
Definition T_pgi3 : axst := Eval vm_compute in pg_back1 T_pgi1.
Definition T_pgi4 : axst := Eval vm_compute in optAp (apply_axforms T_pgi3 xf_pgb2).
Definition T_pgiR1 : axst := Eval vm_compute in shadow_reopen_stateA T_pgi XT hG 6 15.
End Lib_handle_f_gdefs2.

(* [comment removed for export] *)
Module Lib_handle_f_chk0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "nat"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "FUEL_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "cutpcs_hfF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA"; "cut_okE"; "etargets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert"; "eecheckJA'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "edescA"; "eecheckJA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.

Abbreviation TG := (etargets cutsF2 exitsF2).
Abbreviation PE := (eecheckJA NPH (cutsF2 ++ exitsF2)).
Abbreviation PE' := (eecheckJA' NPH (cutsF2 ++ exitsF2)).
Abbreviation CC i T := (cut_okE segs FUEL_hf cutpcs_hfF NPH PE i T TG).
Abbreviation CC' i T := (cut_okE segs FUEL_hf cutpcs_hfF NPH PE' i T TG).
Lemma CC_fast : ltac2:(tb__ "0|2|
S4SeS5S1SbS6S7S8S0SdS0S3SfS9SaA3M0A2R2R1ScS9SaA2M1A8S2A3S5S1SbS6S7S8S0S10S0G0A2R3R2G1A8S2A3F_;FT;Fi;").
Proof. intros i T H. rewrite (cut_okE_ext segs FUEL_hf cutpcs_hfF NPH PE PE' i T TG (fun e => eq_sym (eecheckJA'_eq NPH (cutsF2 ++ exitsF2) e))). exact H. Qed.
End Lib_handle_f_chk0.

