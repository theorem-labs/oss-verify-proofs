(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "ex"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "alloc_group"; "ameta"; "kreq"; "region"; "st_regions"; "IB"; "am_last"; "am_sc"; "stride_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sstate"; "@Corelib.Init.Datatypes"; "prod"; "list"; "Some"; "pair"; "nat"; "option"; "None"; "S"; "cons"; "length"; "nil"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "layout_extends"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "rd_of"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.ContractG"; "canary_bytes"; "JLg_fail"; "JLg_failG"; "JLg_ok"; "JLg_okG"; "Posts_ag"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "MInvIR"; "L_as_fail"; "L_as_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "le_byte"; "yields"; "active_hd"; "usedX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_chk_guard"; "mc_chk_guard_got"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocIfaceI MallocWfFrame MallocWfGroup MallocWfArith Contract ContractI Zones2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section ContractG.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ientry_consts.

Definition canary_bytes (gd : Z) (m1 : word -> option byte) : Prop := ltac2:(tb__ "0|8|
S0S17S2dR1U8M0A2M1S2S18S20Q8M2A1M3A1M4S2fVsegs;Vm1;S1fQ40M5S29S44VC;A1S2bR2A1M6A2A2A3S15G3S1fG2S3aS43VC;A1M7G0R2A3A2A2A3F_;Fk;S17G1S2G4S2fVsegs;Vm1;S1fG5S29G7G6A2A2A3S15G3S1fG2S3aVgd;G0R2A3A2A2A3F_;Fk;A2").

Definition JLg_fail (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
SfSfS14S26A1S25S1eQ40M0S10R4PcA2A2S3S1eG0S10R5PdA2A2S3S1S22S22S0S37Vsegs;VC;VX;S19S13S4S3A2A1VU;R1R6R4A8S0S41VX;S21R1A1M1A2S0S24S23VA;A1S23R1A1S1cS9SaS21VA;A1M2A1A2A3S0S40G2G1R3A3S0S3fG2G1A2S0S2eVsegs;VC;VA;R1S11R7A1S11R6A1M3A6S0S31S1eG0S10R7PaeA2A2G3A2S0S17S2cS3eR4A1S1aR1A1A2S1S14S13S8S3A2A1M4G4S3bS13S18S4A1M5S5A2S6R3R6R5G2A4R1S16G5S5S19S4A1S21R4A1A4A4Lktr;A2F_;Ffuel;VKc;R5R4A2A2A2A2A2A2A2A2A2LA';A2Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition JLg_ok (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|7|
SfSfS14S26A1S25S1eQ40M0S10R4PcA2A2S3S1eG0S10R5PdA2A2S3S0S2S3S1eG0S10R5S30A2A2Z0M1A3S1S22S22S1S4S4S1S7S7S0S37Vsegs;VC;VX;S15S13S4S3A2S16S4S3R2G1A4A2VU;R3R8R6A8S0S41VX;S21R3A1M2A2S0S24S23VA;A1S23R3A1S1cS9SaS21VA;A1M3A1A2A3S0S2S18S4A1M4S3cG2R5A2S15S4R2A2A3S0S3dVX;G2R2R1A4S0S2S3SdR1A1R5A3S0S2aS29R4SbA2SeR1A1A2S0S2aG1ScR1A1A2S0S40G3G2R5A3S0S3fG3G2A2S0S2eVsegs;VC;VA;R3S11R9A1S11R8A1M5A6S0S31S1eG0S10R9PaeA2A2G5A2S0S17S2cS3eR6A1S1aR1A1A2S1S14S13S8S3A2A1M6G6S3bS13G4S5A2S6R3R8R7G3A4R1S16G4S5S15S4R5A2S21R6A1A4A4Lktr;A2F_;Ffuel;VKc;R7R6A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lam;A2Lg;A2LA';A2A2Treq;Tsc;Lmd;Ltr;Lrho';Lrho0;").

Definition JLg_failG (Nf : Prop) X U A Kc : jpost := ltac2:(tb__ "0|0|
SfSfS14S26A1S25S0VNf;S32VX;VU;VA;VKc;R4R3R2R1A8A2Lmd;Ltr;Lrho';Lrho0;").
Definition JLg_okG (Og : Prop) X U A Kc : jpost := ltac2:(tb__ "0|0|
SfSfS14S26A1S25S0VOg;S34VX;VU;VA;VKc;R4R3R2R1A8A2Lmd;Ltr;Lrho';Lrho0;").
Definition Posts_ag (Nf Og : Prop) X U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S1bS13S12S27A2M0S16S12S27S38VE;A1S33VNf;VX;VU;VA;VKc;A5A4S1bG0S16S12S27S39VE;A1S35VOg;VX;VU;VA;VKc;A5A4S1dG0A1A3A3").

Definition QG (Nf Og : Prop) X U A Kc (rhoG : valuation) : assn := ltac2:(tb__ "0|0|
S28Vsegs;S42VrhoG;S36VNf;VOg;VX;VU;VA;VKc;A6A4").
End ContractG.
