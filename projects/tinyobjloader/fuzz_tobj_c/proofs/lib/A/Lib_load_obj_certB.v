(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "app"; "nil"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "sv"; "SPUle"; "SAlu"; "SLit"; "SPUlt"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "ndA1"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_certB"; "cutsB"; "exitsB"; "FUEL_B"; "H_ecertB_ok"; "PhisB"; "cps_B"; "keep_ecertB_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "pU"; "K_us1"; "K_us2"; "dp_cuts"; "h_exits"; "pW"; "pc_us1"; "pc_us2"; "us_exits"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "E_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0.HVAddr"; "hv_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "V_L"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "cps_loop"; "pE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition PhisB : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S1S2S7SbA1M0S13OFrho;M1A2M2S0G0G1S35S37A4S1G2S0G0G1S34S36A4S5G2A1A3A3").

Definition cutsB : list efnode := ltac2:(tb__ "0|5|
S4S2S2S2S9S14A2M0S3A2M1S2SaSeA2M2A2M3S1cS9G3S9S0G1G2S0G0S3S0S9S14R1S17A4U1M4A4S0SaSeS15S16Z14S18A2A4A4LA;S2aA4S1G3S0G1G2S0G0S3S0S9S14S28S17A4G4A4S0SaSeS15S16Z13S10S1dS3aS27A3A2A4A4S1G3S0G1G2S0G0S3S0S9S14S29S17A4G4A4S0SaSeS15S16Z12S10S1dS2cS27A3A2A4A4S5G3A1A3A3A3").
Definition exitsB : list efnode := ltac2:(tb__ "0|5|
S4S2S2S2S9S14A2M0S3A2M1S2SaSeA2M2A2M3S1cS9G3S9S0G1G2S0G0S3S0S9S14R1S17A4U1M4A4S0SaSeS15S16Z11S18A2A4A4LA;S4S9S2bS4S9S2fS1S9S32S5S9A1A3A3A3A4S1G3S0G1G2S0G0S3S0S9S14S38S19A4G4A4S0SaSeS15S16Z1S18A2A4A4S5G3A1A3A3").
Definition FUEL_B : nat := 150%nat.
Definition cps_B : list Z := ltac2:(tb__ "0|0|
S1SaS33S1SaS2dS1SaS2eS39A3A3A3").

Definition keep_ecertB_ok : list sprop := ltac2:(tb__ "0|4|
S1SdS12ScP1ccA1ScP1d3A1M0A2S1SdSfS10S1eScP1e0A1M1ScP1e1A1A3ScPeA1M2A2S1SdSfScP1eaA1G1A2S1SdSfG0G2A2S1SdSfScPdA1S11Z800000000000A1M3A2S1SdSfG2S11Z4000000A1A2S1SdSfScPfA1G3A2S5SdA1A3A3A3A3A3A3A3").
Definition H_ecertB_ok : list sprop := ltac2:(tb__ "0|0|
S3cS25S4S1aS1fS20A3A2").
Lemma ecertB_ok : ltac2:(tb__ "0|1|
S30S6S1bS31S26S23S21S24S26S1cS1aS1aS3bS22A1M0S1fA4S1cS1aS1aG0S20A4A8S8A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
