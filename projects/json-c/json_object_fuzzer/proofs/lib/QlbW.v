(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA QM7w Q8P7 QTyG QFqQ QkLq QdZ1 Qv4L QmBS Q4KR QnkH QYbl QYnB Qi8L Q1u2 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QytA QM7w Q8P7 QTyG.Mq1.
Import QFqQ.Mq0 QkLq.Mq2 QdZ1.Mq4 Qv4L.Mq0 QmBS.Mq3 Q4KR.Mq7 QnkH.Mq2 QYbl.Mq0 QYnB.Mq6 Qi8L.Mq3 QmBS.Mq2.

Import Q6q3. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mcz_proof : malloc_core_allzero_stmt.
Proof. exact (@Q1u2.malloc_core_allzero_ctrl _ mem pans_mem pupd_mem pans_mem_range). Qed.

#[using="Type"] Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof.
exact (rmalloc_impl_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

#[using="Type"] Theorem rmalloc_spec : rmalloc_stmt.
Proof.
exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4KR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4KR.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYbl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mcz_proof : malloc_core_allzero_stmt.
Proof. exact (@Q1u2.malloc_core_allzero_ctrl _ mem pans_mem pupd_mem pans_mem_range). Qed.

#[using="Type"] Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof.
exact (rmalloc_impl_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

#[using="Type"] Theorem rmalloc_spec : rmalloc_stmt.
Proof.
exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec mcz_proof ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End RC__1.
