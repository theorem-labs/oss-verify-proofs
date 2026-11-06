(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q751. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QP9l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcmL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFZX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhls. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QI0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0.
Open Scope Z_scope.

Section Closed.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : Qhd4.heap_iface_A Qwm6.Mq4.A4L.

Lemma rtc_lheq_closed : QsKa.Mqe.rtc_lheq_stmt HIx.
Proof.
intros A LB LM FR B m md HP. apply (Qw5U.Mq5.rtc_cell HIx _ _ _ _ _ _ _ _ _ HP).
unfold Qwm6.Mq4.a4_rt_consts. repeat (first [left; reflexivity | right]).
Qed.
Lemma rtc_freeud_closed : QW22.Mq4.rtc_freeud_stmt HIx.
Proof.
intros A LB LM FR B m md HP. apply (Qw5U.Mq5.rtc_cell HIx _ _ _ _ _ _ _ _ _ HP).
unfold Qwm6.Mq4.a4_rt_consts. repeat (first [left; reflexivity | right]).
Qed.

Definition TP_HD : Z := 4368.

Theorem tokparse_A_closed : Q751.heap_loop_rule5 Qwm6.Mq4.A4L HIx ->
QJZd.Mq9.jo_tokparse_A_stmt HIx QC6R.JO_TOKPARSE_A QC6R.JO_TOKPARSE_STK_A QC6R.JO_TOKPARSE_URA_A QI0U.tokparse_costB QI0U.tokparse_costD.
Proof.
intros OBL_LOOP.

pose proof Qzkn.Mq2.errno_location_A_ok as ERRNOL.
pose proof (QP9l.Mq2.memappend_A_cps_c HIx) as MAPP.
pose proof (QnDr.Mq6.json_object_array_shrink_A2J_cps HIx) as SHRINK.
pose proof (QnDr.Mq6.json_object_array_add_A2J_cps HIx) as AADD.
pose proof (Qhls.put_A_closed HIx) as PUT.
pose proof (QnDr.Mq5.json_object_new_array_A3_cps HIx) as NEWARR.
pose proof (Qmgs.Mq0.json_object_new_object_A3_cps HIx (QpNt.Mq8.amemset_A HIx) rtc_lheq_closed) as NEWOBJ.
assert (HHD : 112 + QcmL.Mq2.GRS_STK <= TP_HD) by (unfold TP_HD, QcmL.Mq2.GRS_STK; lia).
pose proof (Qhls.object_add_A_closed HIx OBL_LOOP TP_HD HHD) as OADD.
assert (USE : QlKV.Mqe.uselocale_A_stmt) by (first [exact Qzkn.Mq2.uselocale_A_ok | exact (Qzkn.Mq2.uselocale_A_ok HIx)]).
pose proof (Qzkn.Mq2.duplocale_A_ok HIx) as DUP.
pose proof (Qzkn.Mq2.newlocale_A_ok HIx) as NEWL.
pose proof (Qzkn.Mq2.freelocale_A_ok HIx) as FREEL.
pose proof (QFZX.Mq5.json_object_new_double_A HIx) as NEWDBL.
pose proof (QFZX.Mq5.json_object_new_boolean_A HIx) as NEWBOOL.
pose proof (QFZX.Mq5.json_object_new_string_len_A HIx) as NEWSTR.
pose proof (Qvmy.json_parse_int64_A HIx Qzkn.istrtoll_sound_U ERRNOL) as PARSEI.
pose proof (QLHv.json_parse_uint64_A HIx ERRNOL) as PARSEU.
pose proof (Qhls.strtod_A_closed HIx) as STRTOD.
pose proof (QFZX.Mq5.json_object_new_int64_A HIx) as NEWINT.
pose proof (QFZX.Mq5.json_object_new_uint64_A HIx) as NEWUINT.
pose proof (QW22.Mq4.json_object_new_double_s_A_cps HIx (QpNt.Mq8.amemset_A HIx) rtc_freeud_closed) as NEWDBLS.
eapply (QI0U.json_tokener_parse_B_cps HIx) with (HD := TP_HD).
all: first [ exact MAPP | exact SHRINK | exact AADD | exact PUT | exact NEWARR | exact NEWOBJ | exact OADD | exact USE | exact ERRNOL | exact DUP | exact NEWL | exact FREEL
| exact NEWDBL | exact NEWBOOL | exact NEWSTR | exact PARSEI | exact PARSEU | exact STRTOD | exact NEWINT | exact NEWUINT | exact NEWDBLS
| unfold TP_HD; lia ].
Qed.
End Closed.

Section Cost.
Context {RC__ : Q6q3.RunConsts}.
Lemma tokparse_cost_nonneg : forall n, 0 <= n <= 20 -> 0 <= QI0U.tokparse_costB n /\ 0 <= QI0U.tokparse_costD n.
Proof. intros n Hn. pose proof (QI0U.tokparse_cost_le n Hn) as [H1 H2]. split; lia. Qed.
End Cost.
