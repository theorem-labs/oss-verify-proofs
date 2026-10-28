(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwKH.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTea.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTea. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwKH.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwKH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKmQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKmQ.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwKH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKmQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKmQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SerAll.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

#[using="MEMMOVE HEXP HT63 HGOT"] Theorem serval : SERVAL HIx.
Proof.
unfold SERVAL.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; cbn [fn_of].
- exact (ser_bool HIx MEMMOVE).
- destruct u; [exact (ser_ud HIx MEMMOVE) | exact (ser_dbl HIx MEMMOVE HT63)].
- exact (ser_int HIx MEMMOVE HT63).
- destruct h; [exact (ser_str_heap HIx MEMMOVE HEXP HT63 HGOT) | exact (ser_str_inline HIx MEMMOVE HEXP HT63 HGOT)].
- exact (ser_obj HIx MEMMOVE HEXP HT63 HGOT kids IHk).
- exact (ser_arr HIx MEMMOVE kids IHk).
Qed.
End SerAll.

End RC__1.
