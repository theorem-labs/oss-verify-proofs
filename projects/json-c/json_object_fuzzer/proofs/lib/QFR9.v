(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCVR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QP9l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcmL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFZX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhls. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOmG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRcT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0.
Open Scope Z_scope.

Section Closed.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : Qhd4.heap_iface_A Qwm6.Mq0.A4L.

Lemma rtc_lheq_closed : QsKa.Mq5.rtc_lheq_stmt HIx.
Proof.
intros A LB LM FR B m md HP. apply (Qw5U.Mq0.rtc_cell HIx _ _ _ _ _ _ _ _ _ HP).
unfold Qwm6.Mq0.a4_rt_consts. repeat (first [left; reflexivity | right]).
Qed.
Lemma rtc_freeud_closed : QW22.Mq0.rtc_freeud_stmt HIx.
Proof.
intros A LB LM FR B m md HP. apply (Qw5U.Mq0.rtc_cell HIx _ _ _ _ _ _ _ _ _ HP).
unfold Qwm6.Mq0.a4_rt_consts. repeat (first [left; reflexivity | right]).
Qed.

Definition TP_HD : Z := 4336.

Theorem tokparse_A_closed : QCVR.heap_loop_rule5 Qwm6.Mq0.A4L HIx ->
QJZd.Mq0.jo_tokparse_A_stmt HIx QOmG.JO_TOKPARSE_A QOmG.JO_TOKPARSE_STK_A QOmG.JO_TOKPARSE_URA_A QRcT.Mq0.tokparse_costB QRcT.Mq0.tokparse_costD.
Proof.
intros OBL_LOOP.

pose proof Qzkn.Mq0.errno_location_A_ok as ERRNOL.
pose proof (QP9l.Mq0.memappend_A_cps_c HIx) as MAPP.
pose proof (QnDr.Mq3.json_object_array_shrink_A2J_cps HIx) as SHRINK.
pose proof (QnDr.Mq3.json_object_array_add_A2J_cps HIx) as AADD.
pose proof (Qhls.Mq0.put_A_closed HIx) as PUT.
pose proof (QnDr.Mq2.json_object_new_array_A3_cps HIx) as NEWARR.
pose proof (Qmgs.json_object_new_object_A3_cps HIx (QpNt.Mq4.amemset_A HIx) rtc_lheq_closed) as NEWOBJ.
assert (HHD : 80 + QcmL.Mq1.GRS_STK <= TP_HD) by (unfold TP_HD, QcmL.Mq1.GRS_STK; lia).
pose proof (Qhls.Mq0.object_add_A_closed HIx OBL_LOOP TP_HD HHD) as OADD.
assert (USE : QlKV.Mq4.uselocale_A_stmt) by (first [exact Qzkn.Mq0.uselocale_A_ok | exact (Qzkn.Mq0.uselocale_A_ok HIx)]).
pose proof (Qzkn.Mq0.duplocale_A_ok HIx) as DUP.
pose proof (Qzkn.Mq0.newlocale_A_ok HIx) as NEWL.
pose proof (Qzkn.Mq0.freelocale_A_ok HIx) as FREEL.
pose proof (QFZX.Mq0.json_object_new_double_A HIx) as NEWDBL.
pose proof (QFZX.Mq0.json_object_new_boolean_A HIx) as NEWBOOL.
pose proof (QFZX.Mq0.json_object_new_string_len_A HIx) as NEWSTR.
pose proof (Qvmy.Mq0.json_parse_int64_A HIx Qzkn.Mq1.istrtoll_sound_U ERRNOL) as PARSEI.
pose proof (QLHv.Mq0.json_parse_uint64_A HIx ERRNOL) as PARSEU.
pose proof (Qhls.Mq0.strtod_A_closed HIx) as STRTOD.
pose proof (QFZX.Mq0.json_object_new_int64_A HIx) as NEWINT.
pose proof (QFZX.Mq0.json_object_new_uint64_A HIx) as NEWUINT.
pose proof (QW22.Mq0.json_object_new_double_s_A_cps HIx (QpNt.Mq4.amemset_A HIx) rtc_freeud_closed) as NEWDBLS.
eapply (QRcT.Mq0.json_tokener_parse_A_cps HIx) with (HD := TP_HD).
all: first [ exact MAPP | exact SHRINK | exact AADD | exact PUT | exact NEWARR | exact NEWOBJ | exact OADD | exact USE | exact ERRNOL | exact DUP | exact NEWL | exact FREEL
| exact NEWDBL | exact NEWBOOL | exact NEWSTR | exact PARSEI | exact PARSEU | exact STRTOD | exact NEWINT | exact NEWUINT | exact NEWDBLS
| unfold TP_HD; lia ].
Qed.
End Closed.

Section Cost.
Context {RC__ : Q6q3.RunConsts}.
Lemma tokparse_cost_nonneg : forall n, 0 <= n <= 20 -> 0 <= QRcT.Mq0.tokparse_costB n /\ 0 <= QRcT.Mq0.tokparse_costD n.
Proof. intros n Hn. pose proof (QRcT.Mq0.tokparse_cost_le n Hn) as [H1 H2]. split; lia. Qed.
End Cost.
