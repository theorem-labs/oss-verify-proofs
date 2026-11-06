(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi Qwm6 QB6X Qoif Qxmm_c1 Q7UD Qhd4 QJZd Qzkn QpNt Qz87 Qw5U QL3k QkXq Qiiq Q228 Qeia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH Q8tj QKdB QlKV Q30W QV7s Qylf_c1 QCVR QcmL QtyQ Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.

Import Qwm6.Mq2 QB6X Qoif.Mq2 Qxmm_c1.Mq0.
Import Q7UD Qhd4 Qwm6.Mq0 QJZd.Mq0 Qzkn.Mq0 QpNt.Mq4 Qz87.Mq1.
Import Qw5U.Mq3 QL3k.Mq2 QkXq.Mq4 Qiiq.Mq6 Q228.Mq8 Qoif.Mq3 Qeia.Mq5.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QCcH Q8tj QKdB.
Import QlKV.Mq5 Q30W.Mq1 Qoif.Mq0 QpNt.Mq3 QV7s.Mq2 QlKV.Mq3 Qylf_c1 Qeia.Mq2 QkXq.Mq1 QCVR QcmL.Mq1 QtyQ.Mq7. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Closed.
Variable HIx : heap_iface_A A4L.

Theorem get_double_A_closed : jo_get_double_A_stmt HIx 0x9dde4 GD_STK_A 512 0.
Proof. exact (get_double_A HIx errno_location_A_ok scan_total_proofA astrtod_total_proof). Qed.

Theorem set_double_A_closed : jo_set_double_A_stmt HIx 0x9e384 SD_STK_A 512 1.
Proof. exact (set_double_A HIx (amemset_A HIx)). Qed.

Theorem set_string_len_A_closed : jo_set_string_len_A_stmt HIx 0x9eb28 SS_STK_A 2 ss_costB.
Proof. exact (set_string_len_A HIx amemcpy_U). Qed.

Theorem set_string_A_closed : jo_set_string_A_stmt HIx 0x9e890 SS_STK_A 2 ss_costB.
Proof. exact (set_string_A HIx amemcpy_U astrlen_U). Qed.

Theorem strtod_A_closed : strtod_A_stmt HIx.
Proof. exact (strtod_A_of_musl HIx scan_total_proofA astrtod_total_proof). Qed.

Theorem visit_A_closed : jo_visit_A_stmt HIx 0xa3f28 0x925a4 (16 + 176 + 4096) 176.
Proof. exact (json_c_visit_A HIx). Qed.

Theorem lh_delete_A_closed : lh_delete_tail_A_stmt HIx.
Proof. exact (lh_delete_tail_A_cps HIx (amemset_A HIx)). Qed.

Theorem put_A_closed : put_stmt_A HIx.
Proof. exact (json_object_put_A_cps HIx lh_delete_A_closed). Qed.

Theorem hash_A_closed : heap_loop_rule5 A4L HIx -> forall HD, 80 + GRS_STK <= HD ->
lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Proof.
intros OBL_LOOP HD HHD.
exact (lh_char_hash_A_cps HIx _ (fun md => model_vm_only_refl (cfg_model md)) (astrlen_any_A HIx)
(fun A LB LM FR B m md a n HP Hin => heapA_blk_lt40 A4L HIx A LB LM FR B m md a n HP Hin)
GRS_STK ltac:(unfold GRS_STK; lia) (seed_settle_A_lh HIx OBL_LOOP GRS_STK ltac:(lia)) HD HHD).
Qed.

Theorem object_add_A_closed : heap_loop_rule5 A4L HIx -> forall HD, 80 + GRS_STK <= HD -> jo_object_add_A HIx HD.
Proof.
intros OBL_LOOP HD HHD.
exact (json_object_object_add_A_cps HIx put_A_closed lf_test_spec_proof (amemset_A HIx) istrcmp_sound_U HD ltac:(unfold GRS_STK in HHD; lia) (hash_A_closed OBL_LOOP HD HHD)).
Qed.
End Closed.

Section ClosedV6.
Variable H6 : QZsi.heap_iface_A A4L.
Let HIx : heap_iface_A A4L := hi5_of_v6 A4L H6.

Theorem deep_copy_A_closed : heap_loop_rule5 A4L HIx ->
jo_deep_copy_A_stmt HIx 0x9f694 0x9edbc (32 + 192 + 8784) 192 (fun w => 646 * w) (fun w => w).
Proof.
intros OBL_LOOP.
pose proof (Qxmm_c1.Mq0.deep_copy_A HIx (QB6X.shallow_A HIx (Qwm6.Mq2.malloc_nf_v6 A4L H6) (amemset_A HIx) (amemcpy_any_A HIx))
(put_A_closed HIx) (Qwm6.Mq2.strdup_nf_v6 A4L H6) lf_test_spec_proof (amemset_A HIx) istrcmp_sound_U 4336
ltac:(lia) ltac:(unfold Qoif.Mq2.DC_C; lia) (hash_A_closed HIx OBL_LOOP 4336 ltac:(unfold GRS_STK; lia))) as X.
unfold Qoif.Mq2.DC_A, QB6X.SH_A, Qoif.Mq2.DC_F, Qoif.Mq2.DC_C, Qoif.Mq2.DC_KB in X. exact X.
Qed.
End ClosedV6.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC0u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC0u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB6X.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgwQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgwQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qxmm_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qxmm_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzkn.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qz87.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qz87.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL3k. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkXq.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKdB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKdB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qylf_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qylf_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkXq.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q751.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q751. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcmL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcmL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mqd. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Closed.
Variable HIx : heap_iface_A A4L.

Lemma rtc_lheq_B : QsKa.Mqe.rtc_lheq_stmt HIx.
Proof.
intros A LB LM FR B m md HP. apply (Qw5U.Mq5.rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold Qwm6.Mq4.a4_rt_consts. repeat (first [left; reflexivity | right]).
Qed.

Theorem get_double_A_closed : jo_get_double_A_stmt HIx 0x9f8e4 GD_STK_A 512 0.
Proof. exact (get_double_A HIx errno_location_A_ok scan_total_proofA astrtod_total_proof). Qed.

Theorem set_double_A_closed : jo_set_double_A_stmt HIx 0x9fedc SD_STK_A 512 1.
Proof. exact (set_double_A HIx (amemset_A HIx)). Qed.

Theorem set_string_len_A_closed : jo_set_string_len_A_stmt HIx 0xa0748 SS_STK_A 2 ss_costB.
Proof. exact (set_string_len_A HIx amemcpy_U). Qed.

Theorem set_string_A_closed : jo_set_string_A_stmt HIx 0xa0484 SS_STK_A 2 ss_costB.
Proof. exact (set_string_A HIx amemcpy_U astrlen_U). Qed.

Theorem strtod_A_closed : strtod_A_stmt HIx.
Proof. exact (strtod_A_of_musl HIx scan_total_proofA astrtod_total_proof). Qed.

Theorem visit_A_closed : jo_visit_A_stmt HIx 0xa65d4 0x92a2c (16 + 176 + 4096) 176.
Proof. exact (json_c_visit_A HIx). Qed.

Theorem lh_delete_A_closed : lh_delete_tail_A_stmt HIx.
Proof. exact (lh_delete_tail_A_cps HIx (amemset_A HIx)). Qed.

Theorem put_A_closed : put_stmt_A HIx.
Proof. exact (json_object_put_A_cps HIx lh_delete_A_closed). Qed.

Theorem hash_A_closed : heap_loop_rule5 A4L HIx -> forall HD, 112 + GRS_STK <= HD ->
lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Proof.
intros OBL_LOOP HD HHD.
exact (lh_char_hash_A_cps HIx _ (fun md => model_vm_only_refl (cfg_model md)) (astrlen_any_A HIx)
(fun A LB LM FR B m md a n HP Hin => heapA_blk_lt40 A4L HIx A LB LM FR B m md a n HP Hin)
GRS_STK ltac:(unfold GRS_STK; lia) (seed_settle_A_lh HIx OBL_LOOP GRS_STK ltac:(lia)) HD HHD).
Qed.

Theorem object_add_A_closed : heap_loop_rule5 A4L HIx -> forall HD, 112 + GRS_STK <= HD -> jo_object_add_A HIx HD.
Proof.
intros OBL_LOOP HD HHD.
exact (json_object_object_add_A_cps HIx put_A_closed lf_test_spec_proof (amemset_A HIx) istrcmp_sound_U HD ltac:(unfold GRS_STK in HHD; lia) (hash_A_closed OBL_LOOP HD HHD)).
Qed.
End Closed.

Section ClosedV6.
Variable H6 : QZsi.heap_iface_A A4L.
Let HIx : heap_iface_A A4L := hi5_of_v6 A4L H6.

Theorem deep_copy_A_closed : heap_loop_rule5 A4L HIx ->
jo_deep_copy_A_stmt HIx 0xa14d8 0xa0a78 (32 + 192 + 8784) 192 (fun w => 646 * w) (fun w => w).
Proof.
intros OBL_LOOP.
pose proof (QB6X.Mq0.shallow_A HIx (Qwm6.Mq2.malloc_nf_v6 A4L H6) (amemcpy_any_A HIx)
(QC0u.json_object_new_object_A3ok_cps HIx (amemset_A HIx) (rtc_lheq_B HIx))) as SHALLOW.
pose proof (QgwQ.dcopy_A HIx SHALLOW (put_A_closed HIx) (Qwm6.Mq2.strdup_nf_v6 A4L H6) lf_test_spec_proof (amemset_A HIx) istrcmp_sound_U 4368
ltac:(lia) ltac:(unfold Qoif.Mq6.DC_C; lia) (hash_A_closed HIx OBL_LOOP 4368 ltac:(unfold GRS_STK; lia))) as DCA.
pose proof (Qxmm_c1.deep_copy_A HIx (put_A_closed HIx) DCA) as X.
unfold Qoif.Mq6.DC_A, QB6X.Mq0.SH_A, Qoif.Mq6.DC_F, Qoif.Mq6.DC_C, Qoif.Mq6.DC_KB in X. exact X.
Qed.
End ClosedV6.
End RC__1.
