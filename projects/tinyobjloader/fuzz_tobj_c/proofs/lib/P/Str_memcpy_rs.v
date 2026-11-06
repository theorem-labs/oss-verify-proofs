(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.StrAddr"; "memcpy_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memcpy_rs"; "read_stage"; "Posts_rsB"; "Posts_rsS"; "Pre_rsB"; "Pre_rsS"; "P_rsA_c"; "P_rsA_t"; "P_rsB_c"; "P_rsB_t"; "P_rsZ"; "@Corelib.Init.Datatypes"; "list"; "cons"; "bool"; "true"; "nil"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "FUELRS"; "cutpcs_rsB"; "cutpcs_rsS"; "cuts_rsB"; "cuts_rsS"; "exits_rsB"; "exits_rsS"; "vcuts_rsB"; "vcuts_rsS"; "vexits_rsB"; "vexits_rsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "check_cfg"; "check_ecfg"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemcpyRS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition read_stage : Z := 0x29889.

Definition Pre_rsS : sstate := MuslMemcpyRS.Pre_rsS memcpy_entry read_stage.
Definition Pre_rsB : sstate := MuslMemcpyRS.Pre_rsB memcpy_entry read_stage.
Definition Posts_rsS : list leaf := MuslMemcpyRS.Posts_rsS memcpy_entry read_stage.
Definition Posts_rsB : list leaf := MuslMemcpyRS.Posts_rsB memcpy_entry read_stage.

Lemma check_rsS : ltac2:(tb__ "0|0|
S15S12S2aS0S1cS1eS5S20S1S6A2S22S1S6A2A6S13A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma echeck_rsS : ltac2:(tb__ "0|0|
S15S12S2bS0S1cS1eS5S24S1S6A2S26S1S6A2A6S13A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_ecfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma check_rsB : ltac2:(tb__ "0|0|
S15S12S2aS0S1cS1dS1A1S5S1fS1S6A2S21S1S6A2A6S13A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma echeck_rsB : ltac2:(tb__ "0|0|
S15S12S2bS0S1cS1dS1A1S5S23S1S6A2S25S1S6A2A6S13A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_ecfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem memcpy_rsS_sum : ltac2:(tb__ "0|0|
S29OF_;S10S17A1S16OF_;F_;S1bS1aS0R3R2A3S28S0R4S19S0R3SaR2A4S18S0R3S5R2S8A5A4F_;Frho;FK;Fok;").
Proof. exact (MuslMemcpyRS.memcpy_rsS_sum segs memcpy_entry read_stage check_rsS). Qed.
Theorem memcpy_rsS_sum_ex : ltac2:(tb__ "0|0|
S10S17A1S16OF_;F_;S1bS27S0S19S0R2SaR1A4S18S0R2S5R1S8A5A3Frho;FK;").
Proof. exact (MuslMemcpyRS.memcpy_rsS_sum_ex segs memcpy_entry read_stage echeck_rsS). Qed.
Theorem memcpy_rsB_sum : ltac2:(tb__ "0|0|
S29OF_;S10S17A1S16OF_;F_;S1bS1aS0R3R2A3S28S0R4S19S0R3S9R2A4S18S0R3S5R2S7A5A4F_;Frho;FK;Fok;").
Proof. exact (MuslMemcpyRS.memcpy_rsB_sum segs memcpy_entry read_stage check_rsB). Qed.
Theorem memcpy_rsB_sum_ex : ltac2:(tb__ "0|0|
S10S17A1S16OF_;F_;S1bS27S0S19S0R2S9R1A4S18S0R2S5R1S7A5A3Frho;FK;").
Proof. exact (MuslMemcpyRS.memcpy_rsB_sum_ex segs memcpy_entry read_stage echeck_rsB). Qed.

Definition P_rsA_t : sstate := MuslMemcpyRS.P_rsA_t memcpy_entry read_stage.
Definition P_rsB_t : sstate := MuslMemcpyRS.P_rsB_t memcpy_entry read_stage.
Definition P_rsZ : sstate := MuslMemcpyRS.P_rsZ memcpy_entry read_stage.
Definition P_rsA_c : sstate := MuslMemcpyRS.P_rsA_c memcpy_entry read_stage.
Definition P_rsB_c : sstate := MuslMemcpyRS.P_rsB_c memcpy_entry read_stage.
Lemma Posts_rsS_eq : ltac2:(tb__ "0|0|
S15S10S2A1S8S11S2S4ScS3A2S11S2S4SeS3A2S11S2S4SfS3A2S14S2A1A3A3A3A3"). Proof. reflexivity. Qed.
Lemma Posts_rsB_eq : ltac2:(tb__ "0|0|
S15S10S2A1S7S11S2S4SbS3A2S11S2S4SdS3A2S14S2A1A3A3A3"). Proof. reflexivity. Qed.
