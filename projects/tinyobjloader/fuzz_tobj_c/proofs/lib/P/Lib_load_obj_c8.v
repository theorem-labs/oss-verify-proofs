(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs"; "NP"; "FUEL"; "VLp"; "amL"; "cps"; "tvL"; "z0"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "ejcutA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes"; "nodesE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2"; "T_sd1a"; "T_sd1b"; "T_sd1c"; "T_sd1n"; "T_sd2a"; "T_sd2b"; "T_sd2c"; "T_sd2n"; "T_sd3a"; "T_sd3b"; "T_sd3c"; "T_sd3n"; "T_sd4a"; "T_sd4b"; "T_sd4c"; "T_sd4n"; "T_sd5a"; "T_sd5b"; "T_sd5c"; "T_sd5n"; "T_sd6a"; "T_sd6b"; "T_sd6c"; "T_sd6n"; "T_sd7a"; "T_sd7b"; "T_sd7c"; "T_sd7n"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA TobjJVAx TobjJVAy BuilderDispose ArenaDestroy.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_build__G1.Lib_build_line_index.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle_f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G1.Lib_load_obj_sites1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_sites2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load_obj_sites3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_load__G2.Lib_load_obj_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import P.Lib_scan__G1.Lib_scan_double.ScanDoubleAddr.
Lemma ec_T_sd1n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U3eS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S17S0G0S8SeScA4A4S0S7S5Z1f4SbZ29SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd1a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U3fS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S14S0G0S8SeScA4A4S0S7S5Z1f4SbZ29SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd1b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U40S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S15S0G0S8SeScA4A4S0S7S5Z1f4SbZ29SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd1c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U41S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S16S0G0S8SeScA4A4S0S7S5Z1f4SbZ29SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd2n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U42S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1bS0G0S8SeScA4A4S0S7S5Z1f4SbZ27SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd2a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U43S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S18S0G0S8SeScA4A4S0S7S5Z1f4SbZ27SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd2b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U44S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S19S0G0S8SeScA4A4S0S7S5Z1f4SbZ27SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd2c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U45S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1aS0G0S8SeScA4A4S0S7S5Z1f4SbZ27SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd3n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U46S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1fS0G0S8SeScA4A4S0S7S5Z1f4SbZ25SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd3a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U47S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1cS0G0S8SeScA4A4S0S7S5Z1f4SbZ25SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd3b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U48S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1dS0G0S8SeScA4A4S0S7S5Z1f4SbZ25SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd3c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U49S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S1eS0G0S8SeScA4A4S0S7S5Z1f4SbZ25SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd4n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4aS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S23S0G0S8SeScA4A4S0S7S5Z1f4SbZ23SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd4a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4bS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S20S0G0S8SeScA4A4S0S7S5Z1f4SbZ23SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd4b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4cS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S21S0G0S8SeScA4A4S0S7S5Z1f4SbZ23SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd4c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4dS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S22S0G0S8SeScA4A4S0S7S5Z1f4SbZ23SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd5n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4eS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S27S0G0S8SeScA4A4S0S7S5Z1f4SbZ21SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd5a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U4fS0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S24S0G0S8SeScA4A4S0S7S5Z1f4SbZ21SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd5b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U50S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S25S0G0S8SeScA4A4S0S7S5Z1f4SbZ21SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd5c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U51S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S26S0G0S8SeScA4A4S0S7S5Z1f4SbZ21SfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd6n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U52S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2bS0G0S8SeScA4A4S0S7S5Z1f4SbZ1fSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd6a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U53S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S28S0G0S8SeScA4A4S0S7S5Z1f4SbZ1fSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd6b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U54S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S29S0G0S8SeScA4A4S0S7S5Z1f4SbZ1fSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd6c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U55S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2aS0G0S8SeScA4A4S0S7S5Z1f4SbZ1fSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd7n : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U56S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2fS0G0S8SeScA4A4S0S7S5Z1f4SbZ1dSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd7a : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U57S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2cS0G0S8SeScA4A4S0S7S5Z1f4SbZ1dSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd7b : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U58S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2dS0G0S8SeScA4A4S0S7S5Z1f4SbZ1dSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ec_T_sd7c : ltac2:(tb__ "0|2|
S10S2S11S12S9SaSdS9S13U59S0S1S6S1S3S1S5S5A2A1M0S8A2M1A2S1S7S5A2S0S6G1S2eS0G0S8SeScA4A4S0S7S5Z1f4SbZ1dSfA2A4A4A8S4A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcutA_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
