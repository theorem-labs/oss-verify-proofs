(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nil"; "cons"; "prod"; "app"; "list"; "pair"; "None"; "bool"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "SVar"; "sprop"; "valuation"; "DUnknown"; "FcsrFrm0"; "SPUle"; "cell"; "mkObj"; "mkSS"; "DZero"; "odefault"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "cut_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "J_pure_pre"; "JL_pure"; "KcA"; "Kc_ok"; "pre_facts"; "stack_win"; "NPOSTM"; "ae_set_shadow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.WithSegs.Contracts"; "L_set_shadow"; "Pre_set_shadow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_depth"; "musl_memset_ret_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition musl_memset_ret_A : Z := 0xde46c.
Definition set_shadow_depth : Z := 0.

Section WithSegs.
Variable segs : list Segment.
Section Contracts.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S28SfS4S29Q40A1A1S32OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition Pre_set_shadow (xx : Z) : axst := ltac2:(tb__ "0|2|
S2fS15S27VE;Vxx;A2S1eS1cS11S6SbA1S3SaS1SaS25S1SaS14SdPcA1M0ScZ0A1SdPdA1M1S0S13A1S10A5S0SaA1A3A3S2eA3S3SeS1SeS12G1ScS38Z2Z28A2A1A2S1SeS12ScS36A1G0A2S0SeA1A3A3S24S2cA1A3S1bS8A9S0S2SbSbA2A1A2").
Definition L_set_shadow (xx : Z) : axst := ltac2:(tb__ "0|3|
S2fS15S2dS1fS1dS1bA1S1S2S9SbA2M0S5S9SbUaSdPcA1M1A4S0G0A1A3A2S1cS11S6SbA1S3SaS1SaS25S1SaS14G1ScZ0M2A1SdPdA1S0S13A1S7S17L_;S37Vxx;G2A2S16S10X7x2A5S0SaA1A3A3S2eA3S24S2cA1S26S8A9S0S2SbSbA2A1A2").

Definition set_shadow_contractA (xx : Z) : Prop := ltac2:(tb__ "0|1|
S35OF_;S28S22SfS4S29Q40A1A1S23R3A1S31Vsegs;R6S20VAInvA;R5R4A3A3S34Vsegs;R7S30Vsegs;S20VAInvA;R6R5A3S2bVxx;A1R4R3A5S1aVsegs;S1bR4R3S1S2S18S19A2M0S5S18S19S2aVxx;A1S21VAInvA;VCST;VXGL;R6R5A5A4S0G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition set_shadow_contractA_ex (xx : Z) : Prop := ltac2:(tb__ "0|1|
S28S22SfS4S29Q40A1A1S23R3A1S33Vsegs;S30Vsegs;S20VAInvA;R5R4A3S2bVxx;A1R3R2A5S1aVsegs;S1bR3R2S1S2S18S19A2M0S5S18S19S2aVxx;A1S21VAInvA;VCST;VXGL;R5R4A5A4S0G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
End Contracts.
End WithSegs.
