(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Import QXup QRjH QHnV QCcH QfLs Q0Ek QYIF Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dw QmtA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Import UEQM UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI Ujk3 Uh14 UmtA UGEL UHdY UHNo Uytz UEE7 UN7A UY9Y Udgq UrIB U6Vi UBOJ UFNY Uyk8 UzWc UIjw Uuoa UZYZ Uilj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopFdp.
Import UC8c.Mq0 UPZI.Mq0 UPZI.Mq4 Ujk3 Uh14 UmtA UGEL UHNo Uytz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma HEXP_ok2 (HIx : heap_iface S4L) : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m Uuoa.JHEX_SLOT (le8 (Z_to_bv 64 Uuoa.JHEX)).
Proof.
intros A LB m md HP. pose proof (heap_consts S4L HIx A LB m md HP) as HC. cbn [hl_consts S4L] in HC.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons_iff in HC as [H2 _]. cbn [fst snd] in H2. exact H2.
Qed.
#[using="Type"] Lemma HGOT_ok2 (HIx : heap_iface S4L) : forall A LB m md, HEAP S4L HIx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (Z_to_bv 64 Uuoa.JHEX_SLOT)).
Proof.
intros A LB m md HP. pose proof (heap_consts S4L HIx A LB m md HP) as HC. cbn [hl_consts S4L] in HC.
apply Forall_cons_iff in HC as [H1 _]. cbn [fst snd] in H1. exact H1.
Qed.

#[using="Type"] Lemma get_string_P (HIx : heap_iface S4L) : hi_top S4L HIx < 2^62 -> get_string_stmt_P HIx.
Proof.
intros HT62. unfold get_string_stmt_P. intros.
eapply (UY9Y.get_string_cps HIx UzWc.memmove_spec (HEXP_ok2 HIx) ltac:(lia) (HGOT_ok2 HIx)); eassumption.
Qed.

#[using="Type"] Lemma get_string_null_P2 (HIx : heap_iface S4L) : get_string_null_P HIx.
Proof. unfold get_string_null_P. intros. eapply (UY9Y.get_string_null HIx); eassumption. Qed.

End RC__1.

Theorem target_P2_proof : UHdY.target_P.
Proof.
intros RC__ HIx.
apply (harness_P2 HIx).
all: first
[ exact (UEE7.get_boolean_P HIx)
| intros H62; exact (UBOJ.jo_get_double_P HIx H62 UFNY.Mq0.scan_strtod_h_total_proof UFNY.Mq0.rstrtod_total_proof)
| intros H62; exact (U6Vi.Mq0.get_int_P HIx H62)
| intros H62; exact (UN7A.get_int64_P HIx H62)
| intros H62; exact (UN7A.get_uint64_P HIx H62)
| exact (get_string_P HIx)
| exact (get_string_null_P2 HIx)
| exact (UEE7.get_string_len_P HIx)
| exact (UEE7.get_object_P HIx)
| exact (UEE7.get_array_P HIx)
| exact (UEE7.get_type_P HIx)
| exact (Udgq.json_c_visit_P HIx)
| exact (UEE7.Mq1.set_int_P HIx)
| exact (UEE7.Mq1.set_int64_P HIx)
| exact (UEE7.Mq1.set_uint64_P HIx)
| exact (UEE7.Mq1.set_boolean_P HIx)
| exact (UEE7.Mq0.jo_set_double_P HIx)
| exact UIjw.Mq0.cfp_P
| exact UIjw.crls_spec_P
| exact (U6Vi.Mq1.set_string_P HIx)
| exact (U6Vi.Mq1.set_string_len_P HIx)
| exact (UZYZ.Mq0.json_tokener_parse_P HIx)
| exact (Uilj.deep_copy_P_inst HIx)
| exact (Uyk8.json_object_put_P HIx)
| exact (UrIB.put_xleaf_P HIx)
| exact TopFdp.cii_int_U_spec
| exact TopFdp.cii_i64_U_spec
| exact TopFdp.cii_u64_U_spec ].
Qed.
