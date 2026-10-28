(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhQ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhQ1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwbh.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma gw_code : CodeAt.code_at rsegs 0x582ac QQLG.multf3_code.  Proof. StepGen.code_at_vm. Qed.
Lemma gw_base4 : (0x582ac mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma gw_baser : (0 <= 0x582ac /\ 0x582ac + 1792 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Lemma sra63_K_neg : ltac2:(Q6nq.tyx '(@Q8QT.sra63_K_neg rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.sra63_K_neg rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma sra63_K_pos : ltac2:(Q6nq.tyx '(@Q8QT.sra63_K_pos rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil)))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.sra63_K_pos rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Lemma ndr_lt64 : ltac2:(Q6nq.tyx '(@Q8QT.ndr_lt64 rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([4294967295; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@M32) Q6nq.gwt_nil))))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.ndr_lt64 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.
Lemma ndr_ge64 : ltac2:(Q6nq.tyx '(@Q8QT.ndr_ge64 rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([4294967295; 9223372036854775808; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@SIGN64) (Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@M32) Q6nq.gwt_nil))))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.ndr_ge64 rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

Section Norm.
Variables (sp : word).

#[using="Type"] Lemma LnormA : ltac2:(Q6nq.tyx '(@Q8QT.LnormA rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([362128; 362656]%Z : list Z) 'Q6nq.gwt_nil).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.LnormA rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

#[using="Type"] Lemma LnormB : ltac2:(Q6nq.tyx '(@Q8QT.LnormB rsegs 0x582ac gw_code gw_base4 gw_baser) [] '([(-1024); 1024; 361260; 362664]%Z : list Z) '(Q6nq.gwt_unf (@multf3_core_pc) Q6nq.gwt_nil)).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.LnormB rsegs 0x582ac gw_code gw_base4 gw_baser). Qed.

End Norm.
