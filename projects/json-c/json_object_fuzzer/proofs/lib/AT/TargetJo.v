(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOmG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1H. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCVR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhls. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRcT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8dS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUil. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx84. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjTU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoL1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcN3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG1H. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDDG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcN3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFR9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Mono.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : Qhd4.heap_iface_A Qwm6.Mq0.A4L.
Lemma jo_preA_mono : forall A LBall LM FRS B m md sp tp ra lo stkb stkb' errv, stkb <= stkb' ->
QsKa.Mq4.jo_preA HIx A LBall LM FRS B m md sp tp ra lo stkb' errv ->
QsKa.Mq4.jo_preA HIx A LBall LM FRS B m md sp tp ra lo stkb errv.
Proof. intros until errv. intros H (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia | exact P5]. Qed.
Ltac stk_mono H S := intros; eapply S; try eassumption; eapply jo_preA_mono; [exact H | eassumption].
Lemma get_num_mono : forall entry stkb stkb', stkb <= stkb' -> QJZd.Mq0.jo_get_num_A_stmt HIx entry stkb -> QJZd.Mq0.jo_get_num_A_stmt HIx entry stkb'.
Proof. intros entry stkb stkb' H S. unfold QJZd.Mq0.jo_get_num_A_stmt in *. stk_mono H S. Qed.
Lemma get_double_mono : forall entry stkb stkb' cb cd, stkb <= stkb' -> QJZd.Mq0.jo_get_double_A_stmt HIx entry stkb cb cd -> QJZd.Mq0.jo_get_double_A_stmt HIx entry stkb' cb cd.
Proof. intros entry stkb stkb' cb cd H S. unfold QJZd.Mq0.jo_get_double_A_stmt in *. stk_mono H S. Qed.
End Mono.

Section Assembly.

Variables (dcB dcD : Z -> Z).
#[local] Notation tpB := QRcT.Mq0.tokparse_costB (only parsing).
#[local] Notation tpD := QRcT.Mq0.tokparse_costD (only parsing).
Hypothesis OPEN_T5_DEEP : forall {RC__ : Q6q3.RunConsts} (H6 : QZsi.heap_iface_A Qwm6.Mq0.A4L),
QCVR.heap_loop_rule5 Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) ->
QJZd.Mq0.jo_deep_copy_A_stmt (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) QOmG.JO_DEEP_COPY_A QOmG.JO_SHALLOW_COPY_A QOmG.JO_DEEP_STK0_A QOmG.JO_DEEP_STK1_A dcB dcD.
Hypothesis OPEN_DCC : forall w, 0 <= w -> 0 <= dcB w /\ 0 <= dcD w.

Hypothesis OPEN_DC_TOTAL : forall s w BS, QYIF.odepth s <= 32 -> 0 <= w <= 610 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
dcB (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) + 512 * w <= 716689 /\
dcD (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) <= 133960294.

Lemma total_main : forall n s w BS, 0 <= n <= 20 -> QYIF.odepth s <= 32 -> 0 <= w <= 26 * (n + 1) + 64 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
tpB n + QOmG.JO_GETDBL_COSTB_A + QiVi.Mq3.gsB w + 2912 + dcB (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) + (1024 + 192 * w) + (1024 + 192 * w) <= QOmG.TGT_BB_A_jo /\
1 + tpD n + QOmG.JO_GETDBL_COSTD_A + 5 + dcD (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) + 4 <= QOmG.TGT_BD_A_jo.
Proof.
intros n s w BS Hn Hs Hw HJ.
pose proof (QRcT.Mq0.tokparse_cost_le n Hn) as [TB TD].
pose proof (OPEN_DC_TOTAL s w BS Hs ltac:(lia) HJ) as [DB DD].
unfold QOmG.JO_GETDBL_COSTB_A, QOmG.JO_GETDBL_COSTD_A, QiVi.Mq3.gsB, QW22.Mq2.pbnew32_costB, QOmG.TGT_BB_A_jo, QOmG.TGT_BD_A_jo.
split; lia.
Qed.

Section PerState.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : Qt8n.AX2.env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : QOTP.AP.acs.
Hypothesis HCL : QrQA.HSCLASS_S w ch.
Hypothesis CS : Q1LT.APS.cs_ok QLPb.JO6SEGS QCoy.AJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QLPb.JO6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QLPb.JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Let RCJ : Q6q3.RunConsts := QoL1.RCJ sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
#[local] Existing Instance RCJ.
#[local] Notation ARGS L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation H6 := (ARGS QDDG.H6_main).
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6).

Lemma loop5_main : QCVR.heap_loop_rule5 Qwm6.Mq0.A4L HIx.
Proof. apply QCVR.loop_rule5_of_6. unfold QDDG.H6_main, QcN3.H6_jo. apply QrOY.Mq0.loop_rule_jo. Qed.

Lemma gets_main : QJZd.Mq0.jo_get_string_A_stmt HIx QOmG.JO_GET_STRING_A QiVi.Mq3.AGET_STRING_STACK QiVi.Mq3.gsB.
Proof.
destruct (ARGS (@Qv81.Mq0.botj_cap)) as (BCAP & BJ).
refine (QcN3.Mq0.get_string_jo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BCAP _).
unfold Q6q3.alloc_ceiling. cbn. lia.
Qed.

Theorem callees_main : QOmG.jo_callees_A HIx tpB tpD dcB dcD QiVi.Mq3.AGET_STRING_STACK QiVi.Mq3.gsB.
Proof.
pose proof Qzkn.Mq0.errno_location_A_ok as ERRNOL.
constructor.
- exact (Q9O6.Mq0.get_boolean_A HIx).
- eapply get_double_mono; [| exact (Qhls.Mq0.get_double_A_closed HIx)]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (Qawr.Mq0.get_int_A HIx ERRNOL (Qvmy.Mq0.json_parse_int64_A HIx Qzkn.Mq1.istrtoll_sound_U ERRNOL))]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (QYZ0.Mq0.get_int64_A HIx ERRNOL (Qvmy.Mq0.json_parse_int64_A HIx Qzkn.Mq1.istrtoll_sound_U ERRNOL))]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (Q228.Mq1.get_uint64_A HIx ERRNOL (QLHv.Mq0.json_parse_uint64_A HIx ERRNOL))]. vm_compute. discriminate.
- exact gets_main.
- exact (QpNt.Mq2.get_string_null_A HIx).
- exact (Q9O6.Mq0.get_string_len_A HIx).
- exact (Q9O6.Mq0.get_object_A HIx).
- exact (Q9O6.Mq0.get_array_A HIx).
- exact (Q9O6.Mq0.get_type_A HIx).
- exact (Qhls.Mq0.visit_A_closed HIx).
- exact (Qekr.Mq0.set_int_A HIx).
- exact (QkXq.Mq0.set_int64_A HIx).
- exact (QkXq.Mq0.set_uint64_A HIx).
- exact (QkXq.Mq0.set_boolean_A HIx).
- exact (Qhls.Mq0.set_double_A_closed HIx).
- exact (Qhls.Mq0.set_string_A_closed HIx).
- exact (Qhls.Mq0.set_string_len_A_closed HIx).
- exact (QFR9.tokparse_A_closed HIx loop5_main).
- exact (@OPEN_T5_DEEP RCJ H6 loop5_main).
- exact (Qhls.Mq0.put_A_closed HIx).
- exact (@Qiiq.Mq7.put_xleaf_A RCJ HIx).
Qed.

Theorem target_main : QOmG.OBL_TARGET_jo HIx.
Proof.
refine (QtyQ.Mq1.harness_A HIx tpB tpD dcB dcD QiVi.Mq3.AGET_STRING_STACK QiVi.Mq3.gsB callees_main (QFR9.tokparse_cost_nonneg) _ _ OPEN_DCC total_main).
- intros sh Hd. unfold QiVi.Mq3.AGET_STRING_STACK, Q9O6.Mq2.ser_budgetA, Q9O6.Mq2.ASER_LEVEL, Q9O6.Mq2.ASER_LEAF. lia.
- intros w0 Hw. unfold QiVi.Mq3.gsB, QW22.Mq2.pbnew32_costB. lia.
Qed.
End PerState.

Theorem target_all : QDDG.OBL_TARGET_ALL_jo.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS. exact (target_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS). Qed.

Theorem json_object_asan_ba_assembled :
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (QDDG.json_object_asan_ba_target target_all). Qed.
End Assembly.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHdY. Require OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJur_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dcB_jo : Z -> Z := fun w => 646 * w.
Definition dcD_jo : Z -> Z := fun w => w.

Lemma dcc_jo : forall w, 0 <= w -> 0 <= dcB_jo w /\ 0 <= dcD_jo w.
Proof. intros w Hw. unfold dcB_jo, dcD_jo. lia. Qed.

Lemma dc_total_jo : forall s w BS, QYIF.odepth s <= 32 -> 0 <= w <= 610 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
dcB_jo (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) + 512 * w <= 716689 /\
dcD_jo (QtyQ.Mq1.dc_w (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)) w) <= 133960294.
Proof.
intros s w BS _ Hw _. unfold dcB_jo, dcD_jo, QtyQ.Mq1.dc_w.
destruct (Qt1H.Mq0.setters_root (QtyQ.Mq1.root_of s)); lia.
Qed.

Theorem json_object_asan_ba :
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (@json_object_asan_ba_assembled dcB_jo dcD_jo (@Qhls.Mq0.deep_copy_A_closed) dcc_jo dc_total_jo). Qed.

Theorem target_all_closed : QDDG.OBL_TARGET_ALL_jo.
Proof. exact (@target_all dcB_jo dcD_jo (@Qhls.Mq0.deep_copy_A_closed) dcc_jo dc_total_jo). Qed.

Theorem handoff_rest_all : QG1H.OBL_HANDOFF_REST_jo.
Proof.
apply QDDG.handoff_rest_of_driver_side.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (QDDG.driver_side_of_target sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(target_all_closed sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.

Theorem json_object_asan_ef :
strong_universal_error_free_T_scfg (alloc_only_cfg false)
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
exact (QJur_c1.strong_universal_error_free_of_mixed
Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs
(fun inp => QBxa.Mq5.spec (in_argv inp) (in_fs inp))
(QHdY.drv_realizes_P OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP.target_P2_proof)
(QG1H.jo_asan_tgt_srealizes handoff_rest_all)).
Qed.
