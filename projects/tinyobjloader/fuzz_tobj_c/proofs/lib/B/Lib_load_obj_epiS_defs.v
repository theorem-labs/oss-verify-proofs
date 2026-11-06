(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SPUle"; "sprop"; "sprop_eqb"; "SLit"; "SAlu"; "SVar"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_builderH_defs Lib_load_obj_defs Lib_load_obj_loop.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.

Definition ldef_facts (F : list sprop) : bool := ltac2:(tb__ "0|4|
S0S0L_;M0S8S3S4S2ScZ10SaA2M1S5ZffffffffA1M2A2A1VF;A3G0S8S3S4S2SaG2A2A1VF;A3G0S8S3S4S2S9S5Z800000000000A1A2A1VF;A3G0S8S3S4S2S6SbS9G1A3S7P1eA1M3A2A1VF;A3S8S3S4S2G3S5Z7fffff800000A1A2A1VF;A3S1X0x2S1X0x2S1X0x2S1X0x2").

Definition nx500 (A : axst) : bool := (500 <=? ss_next (ax_S A))%positive.
