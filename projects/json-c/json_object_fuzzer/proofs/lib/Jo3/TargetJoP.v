(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjk3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY9Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY9Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qyk8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvMd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvMd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFNY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFNY.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHdY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHdY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qh14. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIjw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIjw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGEL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGEL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZYZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZYZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmtA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIjw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIjw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEE7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEE7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6Vi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6Vi.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN7A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN7A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBOJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBOJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEE7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEE7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEE7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEE7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6Vi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6Vi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdgq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrIB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qilj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qilj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHNo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHNo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qytz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qytz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma HEXP_ok2 (HIx : heap_iface S4L) : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (Z_to_bv 64 JHEX)).
Proof.
intros A LB m md HP. pose proof (heap_consts S4L HIx A LB m md HP) as HC. cbn [hl_consts S4L] in HC.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons_iff in HC as [H2 _]. cbn [fst snd] in H2. exact H2.
Qed.
#[using="Type"] Lemma HGOT_ok2 (HIx : heap_iface S4L) : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x63d90 (le8 (Z_to_bv 64 JHEX_SLOT)).
Proof.
intros A LB m md HP. pose proof (heap_consts S4L HIx A LB m md HP) as HC. cbn [hl_consts S4L] in HC.
apply Forall_cons_iff in HC as [H1 _]. cbn [fst snd] in H1. exact H1.
Qed.

#[using="Type"] Lemma get_string_P (HIx : heap_iface S4L) : hi_top S4L HIx < 2^62 -> get_string_stmt_P HIx.
Proof.
intros HT62. unfold get_string_stmt_P. intros.
eapply (get_string_cps HIx memmove_spec (HEXP_ok2 HIx) ltac:(lia) (HGOT_ok2 HIx)); eassumption.
Qed.

#[using="Type"] Lemma get_string_null_P2 (HIx : heap_iface S4L) : get_string_null_P HIx.
Proof. unfold get_string_null_P. intros. eapply (get_string_null HIx); eassumption. Qed.

End RC__1.

Theorem target_P2_proof : target_P.
Proof.
intros RC__ HIx.
apply (harness_P2 HIx).
all: first
[ exact (get_boolean_P HIx)
| intros H62; exact (jo_get_double_P HIx H62 scan_strtod_h_total_proof rstrtod_total_proof)
| intros H62; exact (get_int_P HIx H62)
| intros H62; exact (get_int64_P HIx H62)
| intros H62; exact (get_uint64_P HIx H62)
| exact (get_string_P HIx)
| exact (get_string_null_P2 HIx)
| exact (get_string_len_P HIx)
| exact (get_object_P HIx)
| exact (get_array_P HIx)
| exact (get_type_P HIx)
| exact (json_c_visit_P HIx)
| exact (set_int_P HIx)
| exact (set_int64_P HIx)
| exact (set_uint64_P HIx)
| exact (set_boolean_P HIx)
| exact (jo_set_double_P HIx)
| exact cfp_P
| exact crls_spec_P
| exact (set_string_P HIx)
| exact (set_string_len_P HIx)
| exact (json_tokener_parse_P HIx)
| exact (deep_copy_P_inst HIx)
| exact (json_object_put_P HIx)
| exact (put_xleaf_P HIx) ].
Qed.

