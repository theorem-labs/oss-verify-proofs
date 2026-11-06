(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKNz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXT6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnip. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpt0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QotY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QotY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGNu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGNu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB4o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB4o.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmAj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdkw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition S4_heap (B : Z) (HBlt : (alloc_ceiling < B)%Z) : heap_iface S4L :=
S4_heap_iface B HBlt rmalloc_impl_spec rfree_impl_spec_proof (rcalloc_spec_proof rmalloc_impl_spec) (rrealloc_spec_proof rmalloc_impl_spec rfree_impl_spec_proof).

End RC__1.
