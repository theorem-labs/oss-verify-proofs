(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhQ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwbh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjxo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjxo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB5o. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJtP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJtP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5CJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5CJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzyB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzyB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlL0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlL0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmhw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmhw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x57804 QVbl.divtf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x57804 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x57804 /\ 0x57804 + 2308 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.divtf3_post) (@QB5o.divtf3_post) (Q6nq.gwt_def (@QVbl.divtf3_post) (@QB5o.divtf3_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma Lbchk : ltac2:(Q6nq.tyx '(@QQRC.Lbchk rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-600); (-112); 4096; 360444]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Lbchk rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.

#[using="Type"] Lemma Lp2r : ltac2:(Q6nq.tyx '(@QQRC.Lp2r rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-112); 4096; 359772]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Lp2r rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.

#[using="Type"] Lemma Linfr : ltac2:(Q6nq.tyx '(@QQRC.Linfr rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-112); 4096; 359428]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Linfr rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.

#[using="Type"] Lemma Lbr : ltac2:(Q6nq.tyx '(@QQRC.Lbr rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-112); 4096; 359404; 9223372036854775807]%Z : list Z) '(Q6nq.gwt_unf (@ABS_HI) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Lbr rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.

#[using="Type"] Lemma Lspec : ltac2:(Q6nq.tyx '(@QQRC.Lspec rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]; [@gw_eq_saved12__3; @gw_eq_saved12__2; @gw_eq_saved12]] '([(-112); 4096; 359376]%Z : list Z) 'gwt_X).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Lspec rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.

#[using="Type"] Lemma divtf3_walk : ltac2:(Q6nq.tyx '(@QQRC.divtf3_walk rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64) [[@gw_eq_divtf3_post__3; @gw_eq_divtf3_post__2; @gw_eq_divtf3_post]] '([(-112); 4096; 358404]%Z : list Z) '(Q6nq.gwt_unf (@divtf3_entry) gwt_X)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.divtf3_walk rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.
End Walk.

Theorem divtf3_spec : divtf3_stmt.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.divtf3_spec rsegs 0x57804 gw_code gw_base4 gw_baser mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64). Qed.
