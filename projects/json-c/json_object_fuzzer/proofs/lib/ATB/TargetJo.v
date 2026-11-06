(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCVR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnmi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPhH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q751. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzkn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhls.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QI0U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8dS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7DP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi08.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWwJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx84. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjTU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoL1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcN3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGIC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDDG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAWc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Mono.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : Qhd4.heap_iface_A Qwm6.Mq4.A4L.
Lemma jo_preA_mono : forall A LBall LM FRS B m md sp tp ra lo stkb stkb' errv, stkb <= stkb' ->
QsKa.Mqd.jo_preA HIx A LBall LM FRS B m md sp tp ra lo stkb' errv ->
QsKa.Mqd.jo_preA HIx A LBall LM FRS B m md sp tp ra lo stkb errv.
Proof. intros until errv. intros H (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [lia | exact P5]. Qed.
Ltac stk_mono H S := intros; eapply S; try eassumption; eapply jo_preA_mono; [exact H | eassumption].
Lemma get_num_mono : forall entry stkb stkb', stkb <= stkb' -> QJZd.Mq9.jo_get_num_A_stmt HIx entry stkb -> QJZd.Mq9.jo_get_num_A_stmt HIx entry stkb'.
Proof. intros entry stkb stkb' H S. unfold QJZd.Mq9.jo_get_num_A_stmt in *. stk_mono H S. Qed.
Lemma get_double_mono : forall entry stkb stkb' cb cd, stkb <= stkb' -> QJZd.Mq9.jo_get_double_A_stmt HIx entry stkb cb cd -> QJZd.Mq9.jo_get_double_A_stmt HIx entry stkb' cb cd.
Proof. intros entry stkb stkb' cb cd H S. unfold QJZd.Mq9.jo_get_double_A_stmt in *. stk_mono H S. Qed.
End Mono.

Section Assembly.

Variables (dcB dcD : Z -> Z).
#[local] Notation tpB := QI0U.tokparse_costB (only parsing).
#[local] Notation tpD := QI0U.tokparse_costD (only parsing).
Hypothesis OPEN_T5_DEEP : forall {RC__ : Q6q3.RunConsts} (H6 : QZsi.heap_iface_A Qwm6.Mq4.A4L),
Q751.heap_loop_rule5 Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) ->
QJZd.Mq9.jo_deep_copy_A_stmt (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) QC6R.JO_DEEP_COPY_A QC6R.JO_SHALLOW_COPY_A QC6R.JO_DEEP_STK0_A QC6R.JO_DEEP_STK1_A dcB dcD.
Hypothesis OPEN_DCC : forall w, 0 <= w -> 0 <= dcB w /\ 0 <= dcD w.

Hypothesis OPEN_DC_TOTAL : forall s w BS, QYIF.odepth s <= 32 -> 0 <= w <= 610 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
dcB (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) + 512 * w <= 716689 /\
dcD (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) <= 133960293.

Lemma total_main : forall n s w BS, 0 <= n <= 20 -> QYIF.odepth s <= 32 -> 0 <= w <= 26 * (n + 1) + 64 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
tpB n + QC6R.JO_GETDBL_COSTB_A + QiVi.Mq6.gsB w + 2912 + dcB (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) + (1024 + 192 * w) + (1024 + 192 * w) <= QC6R.TGT_BB_A_jo /\
1 + tpD n + QC6R.JO_GETDBL_COSTD_A + 5 + dcD (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) + 4 <= QC6R.TGT_BD_A_jo.
Proof.
intros n s w BS Hn Hs Hw HJ.
pose proof (QI0U.tokparse_cost_le n Hn) as [TB TD].
pose proof (OPEN_DC_TOTAL s w BS Hs ltac:(lia) HJ) as [DB DD].
unfold QC6R.JO_GETDBL_COSTB_A, QC6R.JO_GETDBL_COSTD_A, QiVi.Mq6.gsB, QW22.Mq7.pbnew32_costB, QC6R.TGT_BB_A_jo, QC6R.TGT_BD_A_jo.
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
Hypothesis HCL : Q45h.HSCLASS_S w ch.
Hypothesis CS : Q1LT.APS.cs_ok QXVi.JOB6SEGS QyaF.BJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QXVi.JOB6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QXVi.JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Let RCJ : Q6q3.RunConsts := QoL1.Mq0.RCJ sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
#[local] Existing Instance RCJ.
#[local] Notation ARGS L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation H6 := (ARGS QDDG.Mq0.H6_main).
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6).

Lemma loop5_main : Q751.heap_loop_rule5 Qwm6.Mq4.A4L HIx.
Proof.
apply Q751.loop_rule5_of_6.
assert (R6 : QCVR.heap_loop_rule6 Qwm6.Mq4.A4L H6).
{ unfold QDDG.Mq0.H6_main, QcN3.Mq1.H6_jo. apply QrOY.loop_rule_jo. }

intros VV T c0 ms0 V STEP. apply (R6 VV T c0 ms0 V). intros K c ms Vc.
destruct K as [kJ kwit kTw kTn kw kn kck kcn kex kbk kt1 kgr].
exact (STEP (Q751.LK6 _ _ VV T kJ kwit kTw kTn kw kn kck kcn kex kbk kt1 kgr) c ms Vc).
Qed.

Lemma gets_main : QJZd.Mq9.jo_get_string_A_stmt HIx QC6R.JO_GET_STRING_A QiVi.Mq6.AGET_STRING_STACK QiVi.Mq6.gsB.
Proof.
destruct (ARGS (@Qv81.Mq1.botj_cap)) as (BCAP & BJ).
refine (QAWc.get_string_jo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BCAP _).
unfold Q6q3.alloc_ceiling. cbn. lia.
Qed.

Theorem callees_main : QC6R.jo_callees_A HIx tpB tpD dcB dcD QiVi.Mq6.AGET_STRING_STACK QiVi.Mq6.gsB.
Proof.
pose proof Qzkn.Mq2.errno_location_A_ok as ERRNOL.
constructor.
- exact (Q9O6.Mq4.get_boolean_A HIx).
- eapply get_double_mono; [| exact (Qhls.get_double_A_closed HIx)]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (Qawr.get_int_A HIx ERRNOL (Qvmy.json_parse_int64_A HIx Qzkn.istrtoll_sound_U ERRNOL))]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (QYZ0.Mq5.get_int64_A HIx ERRNOL (Qvmy.json_parse_int64_A HIx Qzkn.istrtoll_sound_U ERRNOL))]. vm_compute. discriminate.
- eapply get_num_mono; [| exact (Q228.get_uint64_A HIx ERRNOL (QLHv.json_parse_uint64_A HIx ERRNOL))]. vm_compute. discriminate.
- exact gets_main.
- exact (QpNt.Mq6.get_string_null_A HIx).
- exact (Q9O6.Mq4.get_string_len_A HIx).
- exact (Q9O6.Mq4.get_object_A HIx).
- exact (Q9O6.Mq4.get_array_A HIx).
- exact (Q9O6.Mq4.get_type_A HIx).
- exact (Qhls.visit_A_closed HIx).
- exact (Qekr.set_int_A HIx).
- exact (QkXq.set_int64_A HIx).
- exact (QkXq.set_uint64_A HIx).
- exact (QkXq.set_boolean_A HIx).
- exact (Qhls.set_double_A_closed HIx).
- exact (Qhls.set_string_A_closed HIx).
- exact (Qhls.set_string_len_A_closed HIx).
- exact (Q0y7.tokparse_A_closed HIx loop5_main).
- exact (@OPEN_T5_DEEP RCJ H6 loop5_main).
- exact (Qhls.put_A_closed HIx).
- exact (@Qiiq.Mqe.put_xleaf_A RCJ HIx).
Qed.

Theorem target_main : QC6R.OBL_TARGET_jo HIx.
Proof.
refine (QPhH.harness_A HIx tpB tpD dcB dcD QiVi.Mq6.AGET_STRING_STACK QiVi.Mq6.gsB callees_main (Q0y7.tokparse_cost_nonneg) _ _ OPEN_DCC total_main).
- intros sh Hd. unfold QiVi.Mq6.AGET_STRING_STACK, Q9O6.Mq5.ser_budgetA, Q9O6.Mq5.ASER_LEVEL, Q9O6.Mq5.ASER_LEAF. lia.
- intros w0 Hw. unfold QiVi.Mq6.gsB, QW22.Mq7.pbnew32_costB. lia.
Qed.
End PerState.

Theorem target_all : QDDG.Mq0.OBL_TARGET_ALL_jo.
Proof. intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS. exact (target_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS). Qed.

Theorem json_object_both_ba_assembled :
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (QDDG.Mq0.json_object_both_ba_target target_all). Qed.
End Assembly.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHdY. Require OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJur_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dcB_jo : Z -> Z := fun w => 646 * w.
Definition dcD_jo : Z -> Z := fun w => w.

Lemma dcc_jo : forall w, 0 <= w -> 0 <= dcB_jo w /\ 0 <= dcD_jo w.
Proof. intros w Hw. unfold dcB_jo, dcD_jo. lia. Qed.

Lemma dc_total_jo : forall s w BS, QYIF.odepth s <= 32 -> 0 <= w <= 610 ->
(forall sh, s = Some sh -> QlKV.Mq2.jtx sh BS = Some (w, [])) ->
dcB_jo (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) + 512 * w <= 716689 /\
dcD_jo (QPhH.dc_w (QpFy.setters_root (QPhH.root_of s)) w) <= 133960293.
Proof.
intros s w BS _ Hw _. unfold dcB_jo, dcD_jo, QPhH.dc_w.
destruct (QpFy.setters_root (QPhH.root_of s)); lia.
Qed.

Theorem json_object_both_ba :
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (@json_object_both_ba_assembled dcB_jo dcD_jo (@Qhls.deep_copy_A_closed) dcc_jo dc_total_jo). Qed.

Theorem target_all_closed : QDDG.Mq0.OBL_TARGET_ALL_jo.
Proof. exact (@target_all dcB_jo dcD_jo (@Qhls.deep_copy_A_closed) dcc_jo dc_total_jo). Qed.

Theorem handoff_rest_all : QGIC.OBL_HANDOFF_REST_jo.
Proof.
apply QDDG.Mq0.handoff_rest_of_driver_side.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (QDDG.Mq0.driver_side_of_target sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(target_all_closed sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.

Theorem json_object_both_ef :
strong_universal_error_free_T_scfg (alloc_only_cfg false)
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
exact (QJur_c1.strong_universal_error_free_of_mixed
Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
(fun inp => QBxa.Mq5.spec (in_argv inp) (in_fs inp))
(QHdY.drv_realizes_P OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Jo3.TargetJoP.target_P2_proof)
(QGIC.jo_both_tgt_srealizes handoff_rest_all)).
Qed.
