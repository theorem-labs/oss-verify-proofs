(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memset_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "@Corelib.Init.Logic"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "FUEL_MS"; "cutpcs_memset"; "C_164_0"; "C_loop_0"; "E_164"; "E_in"; "cuts_memset"; "exits_memset"; "s164"; "s_in"; "vcuts_memset"; "vexits_memset"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memset"; "Posts_memset"; "Pre_memset"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "check_cfg"; "check_ecfg"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Pre_memset : sstate := MuslMemset.Pre_memset memset_entry.
Definition Posts_memset : list leaf := MuslMemset.Posts_memset memset_entry.

Lemma check_memset : ltac2:(tb__ "0|0|
S5S2S1fS1SeSfS0A1S6S14S0A1S15S0A1A6S3A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma echeck_memset : ltac2:(tb__ "0|0|
S5S2S20S1SeSfS0A1S6S18S0A1S19S0A1A6S3A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_ecfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_164 : ltac2:(tb__ "0|0|
S5S2S9S12S0A1S10S0A1S16S0A1A3S3A3").
Proof. vm_compute. reflexivity. Qed.
Lemma ent_in : ltac2:(tb__ "0|0|
S5S2S9S13S0A1S11S0A1S17S0A1A3S3A3").
Proof. vm_compute. reflexivity. Qed.

Theorem memset_sum : ltac2:(tb__ "0|0|
S1eOF_;S4S8A1S7OF_;F_;SdScS1R3R2A3S1dS1R4SbS1R3S1bR2A4SaS1R3S6R2S1aA5A4F_;Frho;FK;Fok;").
Proof. exact (MuslMemset.memset_sum segs memset_entry check_memset ent_164 ent_in). Qed.
Theorem memset_sum_ex : ltac2:(tb__ "0|0|
S4S8A1S7OF_;F_;SdS1cS1SbS1R2S1bR1A4SaS1R2S6R1S1aA5A3Frho;FK;").
Proof. exact (MuslMemset.memset_sum_ex segs memset_entry ent_164 ent_in echeck_memset). Qed.
