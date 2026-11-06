(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "alloc_lawsA"; "alloc_contractsA"; "alloc_contractsA_ex"; "@Corelib.Init.Datatypes"; "cons"; "list"; "prod"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Logic"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "white_hv"; "white_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "Pre_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_iface"; "P0_los"; "Posts_loJ"; "nd_lo0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA_pre"; "PTrue"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "law_flag_stmt"; "law_fshadow_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_p0 Lib_load_obj_iface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import LOAddr.

Definition load_obj_stmtL : Prop := ltac2:(tb__ "0|6|
S27ScS9S2bQ40A1A1M0SfOF_;F_;F_;F_;S9SaS0S0A2M1A1M2G2S5S1R3R2A3S0SdR4R1A2SeS29Z0M3R2A2S2aR2S26A2A2F_;Fa;M4G4S0S17R1A1SdR6R2A2F_;Fa;S24R7A1S25R8A1S3S4R1A1G2S9SaG1S0A2A1S20S1fZ7R1A2ScS30OF_;S23S1R8R1A3S6S1S2R12R11R10A5S0S28S0R1S8S0G3S8S0Zf5S8S0Zf8SbS0A1A3A3A3A3S2cS1S2R15R14R13R2A6F_;Fxx;S11S1S2R14R13R12S10A6S13S1S2R15R14R13S15ZcM5A7S13S1S2R16R15R14S16G5A7G0S2fS1R8S1dS1S21R18R17R16RfS1aR17RdRcA3RdRcRbS22S1cAaS19R9R1A5S1eS1S18R9R1S1bR18R17R16RfRdRcRbA7A5A4Ftp0;FMCROML;FMCROM;FMC48;FSSC;FAC;FHok;Fok;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
Definition load_obj_stmt_exL : Prop := ltac2:(tb__ "0|6|
S27ScS9S2bQ40A1A1M0SfOF_;F_;F_;F_;S9SaS0S0A2M1A1M2G2S5S1R3R2A3S0SdR4R1A2SeS29Z0M3R2A2S2aR2S26A2A2F_;Fa;M4G4S0S17R1A1SdR6R2A2F_;Fa;S24R7A1S25R8A1S3S4R1A1G2S9SaG1S0A2A1S20S1fZ7R1A2ScS7S1S2R10RfReA5S0S28S0R1S8S0G3S8S0Zf5S8S0Zf8SbS0A1A3A3A3A3S2dS1S2R13R12R11R2A6F_;Fxx;S12S1S2R12R11R10S10A6S14S1S2R13R12R11S15ZcM5A7S14S1S2R14R13R12S16G5A7G0S2eS1S1dS1S21R16R15R14RdS1aR15RbRaA3RbRaR9S22S1cAaS19R7R1A5S1eS1S18R7R1S1bR16R15R14RdRbRaR9A7A5A3Ftp0;FMCROMLX;FMCROMX;FMC48X;FSSCX;FACX;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
