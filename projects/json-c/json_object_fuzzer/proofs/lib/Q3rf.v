(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLch.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTea.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTea. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKmQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKmQ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKmQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKmQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SerAll.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x63d90 (le8 (wz JHEX_SLOT)).

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
