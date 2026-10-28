(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Upt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Upt0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UotY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UotY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGNu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGNu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgTW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UB4o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UB4o.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition S4_heap (B : Z) (HBlt : (alloc_ceiling < B)%Z) : heap_iface S4L :=
S4_heap_iface B HBlt rmalloc_impl_spec rfree_impl_spec_proof (rcalloc_spec_proof rmalloc_impl_spec) (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec_proof).

End RC__1.
