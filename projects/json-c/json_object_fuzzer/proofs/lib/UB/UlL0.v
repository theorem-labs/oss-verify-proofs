(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require UB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB5o. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require UJtP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJtP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require U5CJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5CJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require UzyB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzyB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x5958c QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x5958c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x5958c /\ 0x5958c + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp sgw w6 : word).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qy8Z.divtf3_post) (@UB5o.divtf3_post) (Q6nq.gwt_def (@QVbl.divtf3_post) (@UB5o.divtf3_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma L6r : ltac2:(Q6nq.tyx '(@Qy8Z.L6r rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-122484); (-112); 4096; 32766; 367136; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.L6r rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32). Qed.

#[using="Type"] Lemma L5r : ltac2:(Q6nq.tyx '(@Qy8Z.L5r rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-20000); (-112); 4096; 60000; 366820; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_mid2_pc) (Q6nq.gwt_unf (@MASK48) gwt_X))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.L5r rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32). Qed.

#[using="Type"] Lemma divtf3_core : ltac2:(Q6nq.tyx '(@Qy8Z.divtf3_core rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-1024); (-112); 1024; 4096; 32768; 366100; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_core_pc) (Q6nq.gwt_unf (@MASK48) gwt_X))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Qy8Z.divtf3_core rsegs 0x5958c gw_code gw_base4 gw_baser land_ones_l mulhu_shl32). Qed.
End Walk.
