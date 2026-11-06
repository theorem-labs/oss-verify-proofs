(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QEpW QsjA QCcH QbFI Qwm6 QZsi Qhd4 QupI QdM4 QaDa QOcx QscU QXcG QC6R Qsn5 QU91 QrOY Q8dS Q1LT QpvH Qt8n QOTP QVWI QXVi QyaF Q45h QOTx Q25t Q7DP QHqi Qi08 QWwJ Qx84 Qv81 QjTU QoL1 QcN3 QGIC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.

Import Qsn5.

Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Budget.
Context {RC__ : Q6q3.RunConsts}.
Lemma drva6_closed : forall t d : Z,
QXcG.Mq0.DRVA6_BQ t = 201383936 + 64 * t /\ QXcG.Mq0.DRVA6_BB t = 604326428 + 4 * t /\ QXcG.Mq0.DRVA6_BN t = 16 + t / 128 /\ QXcG.Mq0.DRVA6_BD d = 4 * d.
Proof.
intros t d. unfold QXcG.Mq0.DRVA6_BQ, QXcG.Mq0.DRVA6_BB, QXcG.Mq0.DRVA6_BN, QXcG.Mq0.DRVA6_BD.
unfold QscU.RDQ, QscU.RDB, QOcx.Mq0.BQR, QOcx.Mq0.BBR, QOcx.Mq0.BNR, QOcx.Mq0.BDR, QaDa.Mq0.TR_BQ, QaDa.Mq0.TR_BB, QaDa.Mq0.TR_BD, QaDa.Mq0.TRV_BB.
change (Z.of_nat 0) with 0. repeat split; lia.
Qed.

Lemma B0J_funds : forall t d : Z, 0 <= t <= 1047680 -> 0 <= d <= 2^28 ->
QXcG.Mq0.DRVA6_BQ t <= QZsi.bQ QjTU.Mq0.B0J /\ QXcG.Mq0.DRVA6_BB t <= QZsi.bB QjTU.Mq0.B0J /\ QXcG.Mq0.DRVA6_BN t <= QZsi.bN QjTU.Mq0.B0J /\ QXcG.Mq0.DRVA6_BD d <= QZsi.bD QjTU.Mq0.B0J
/\ QXcG.Mq0.DRVA6_BD d <= 134217728 * QZsi.bM QjTU.Mq0.B0J
/\ 1536 + 4 * t <= 2^30.
Proof.
intros t d Ht Hd. destruct (drva6_closed t d) as (-> & -> & -> & ->). unfold QjTU.Mq0.B0J. cbn [QZsi.bQ QZsi.bB QZsi.bN QZsi.bD QZsi.bM].
change (2^28) with 268435456 in *. change (2^30) with 1073741824 in *.
assert (t / 128 < 8186) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
End Budget.

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

Definition H6_main : QZsi.heap_iface_A Qwm6.Mq4.A4L :=
ARGS QcN3.Mq1.H6_jo (QWwJ.LA_main w E) (QHqi.PERM0_J E w)
Qi08.TMAX_J Qi08.NMAX_J
(Qx84.Mq0.REJ sp E w) (Qv81.Mq1.FR0J E w) (Qv81.Mq1.BAUXJ sp) (Qv81.Mq1.BOTJ sp E) (Qv81.Mq1.TOPJ sp)
(@Qv81.Mq1.HS_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq1.r1_main E RCJ) (@Qv81.Mq1.r2_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ) (@Qv81.Mq1.r3_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq1.r4_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl)
(@Qv81.Mq1.r5_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq1.r6_main sp RCJ) (@Qv81.Mq1.r7_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl).
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6_main).

Inductive driver_side : Prop :=
| DriverSide :
forall (GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : QupI.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @QupI.drvA_mem argv0 USP m -> Qhd4.HEAPA Qwm6.Mq4.A4L HIx A LB LM FR B m md -> GA m)
,
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A <= 1047680 -> 0 <= TGT_BD_A <= 2^28 ->
driver_side.

Theorem handoff_rest_main : driver_side -> QoL1.Mq0.handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
intros [GA TS TB TD TGT OGA HTS HTB HTD].
destruct (B0J_funds TB TD HTB HTD) as (BQ & BB & BN & BD & BM & TB6).
pose proof (ARGS Q7DP.atop_val) as AV.
destruct (@Qv81.Mq1.botj_cap sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) as (BCAP & BJ).
pose proof Hsp as (S1 & S2 & _). unfold sp_window_lo, sp_window_hi in S1, S2.
set (ms0 := QEpW.MS R bvmap_empty (Z_to_bv 64 0) (Z_to_bv 32 0) None FULL (QsjA.seg_rom QXVi.JOB6SEGS)).
refine (ARGS QcN3.Mq1.handoff_rest_jo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GA TS TB TD TGT OGA BCAP (QjTU.Mq0.LM0J E w) QjTU.Mq0.B0J (Qv81.Mq1.BOTJ sp E) ms0 eq_refl
(@QjTU.Mq0.HH_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl eq_refl (ARGS QoL1.Mq0.RCJ_sec) ms0 eq_refl)
(QjTU.Mq0.LM0J_40 E w) (ltac:(cbn; lia) : Z.of_nat (length (QjTU.Mq0.LM0J E w)) < 8)  QjTU.Mq0.B0J_bB39 QjTU.Mq0.B0J_bQ0 BQ BB BN BD BM HTS (proj1 HTB) TB6 (proj1 HTD) _ _ _ _).
- unfold Qv81.Mq1.TOPJ. lia.
- lia.
- lia.
- lia.
Qed.
End PerState.

Theorem driver_side_of_target : forall sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS,
QC6R.OBL_TARGET_jo (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L (H6_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)) ->
driver_side sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS TGT.
destruct QC6R.jo_envelope_ok as (E1 & E2 & E3).
refine (DriverSide sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
QC6R.GA_jo QC6R.TGT_STACK_A_jo
QC6R.TGT_BB_A_jo QC6R.TGT_BD_A_jo TGT _ E1 E2 E3).
intros argv0 USP A LB LM FR B m md D HP.
exact (QscU.Mq3.ga_jo_of_drv argv0 USP m D).
Qed.

Definition OBL_DRIVER_SIDE_jo : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
E R FULL mo w ch (HCL : Q45h.HSCLASS_S w ch)
(CS : Q1LT.APS.cs_ok QXVi.JOB6SEGS QyaF.BJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QXVi.JOB6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QXVi.JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
driver_side sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.

Theorem handoff_rest_of_driver_side : OBL_DRIVER_SIDE_jo -> QGIC.OBL_HANDOFF_REST_jo.
Proof.
intros OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (handoff_rest_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.

Theorem json_object_both_ba_driver : OBL_DRIVER_SIDE_jo ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. intros OBL. exact (QGIC.json_object_both_ba (handoff_rest_of_driver_side OBL)). Qed.

Definition OBL_TARGET_ALL_jo : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
E R FULL mo w ch (HCL : Q45h.HSCLASS_S w ch)
(CS : Q1LT.APS.cs_ok QXVi.JOB6SEGS QyaF.BJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QXVi.JOB6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QXVi.JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
QC6R.OBL_TARGET_jo (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L (H6_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).

Theorem json_object_both_ba_target : OBL_TARGET_ALL_jo ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
intros OBL. apply json_object_both_ba_driver.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (driver_side_of_target sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Plain.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaDa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOcx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOmG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8dS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUil. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx84. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjTU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoL1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcN3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG1H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Budget.
Context {RC__ : Q6q3.RunConsts}.
Lemma drva6_closed : forall t d : Z,
QXcG.DRVA6_BQ t = 201383936 + 64 * t /\ QXcG.DRVA6_BB t = 604326428 + 4 * t /\ QXcG.DRVA6_BN t = 16 + t / 128 /\ QXcG.DRVA6_BD d = 4 * d.
Proof.
intros t d. unfold QXcG.DRVA6_BQ, QXcG.DRVA6_BB, QXcG.DRVA6_BN, QXcG.DRVA6_BD.
unfold QscU.Mq1.RDQ, QscU.Mq1.RDB, QOcx.BQR, QOcx.BBR, QOcx.BNR, QOcx.BDR, QaDa.TR_BQ, QaDa.TR_BB, QaDa.TR_BD, QaDa.TRV_BB.
change (Z.of_nat 0) with 0. repeat split; lia.
Qed.

Lemma B0J_funds : forall t d : Z, 0 <= t <= 1047680 -> 0 <= d <= 2^28 ->
QXcG.DRVA6_BQ t <= QZsi.bQ QjTU.B0J /\ QXcG.DRVA6_BB t <= QZsi.bB QjTU.B0J /\ QXcG.DRVA6_BN t <= QZsi.bN QjTU.B0J /\ QXcG.DRVA6_BD d <= QZsi.bD QjTU.B0J
/\ QXcG.DRVA6_BD d <= 134217728 * QZsi.bM QjTU.B0J
/\ 1536 + 4 * t <= 2^30.
Proof.
intros t d Ht Hd. destruct (drva6_closed t d) as (-> & -> & -> & ->). unfold QjTU.B0J. cbn [QZsi.bQ QZsi.bB QZsi.bN QZsi.bD QZsi.bM].
change (2^28) with 268435456 in *. change (2^30) with 1073741824 in *.
assert (t / 128 < 8186) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
End Budget.

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

Definition H6_main : QZsi.heap_iface_A Qwm6.Mq0.A4L :=
ARGS QcN3.H6_jo (QUil.LA_main w E) (Q92D.PERM0_J E w)
QVyC.TMAX_J QVyC.NMAX_J
(Qx84.REJ sp E w) (Qv81.Mq0.FR0J E w) (Qv81.Mq0.BAUXJ sp) (Qv81.Mq0.BOTJ sp E) (Qv81.Mq0.TOPJ sp)
(@Qv81.Mq0.HS_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq0.r1_main E RCJ) (@Qv81.Mq0.r2_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ) (@Qv81.Mq0.r3_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq0.r4_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl)
(@Qv81.Mq0.r5_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl) (@Qv81.Mq0.r6_main sp RCJ) (@Qv81.Mq0.r7_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl).
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6_main).

Inductive driver_side : Prop :=
| DriverSide :
forall (GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : Q2y2.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @Q2y2.drvA_mem argv0 USP m -> Qhd4.HEAPA Qwm6.Mq0.A4L HIx A LB LM FR B m md -> GA m)
,
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A <= 1047680 -> 0 <= TGT_BD_A <= 2^28 ->
driver_side.

Theorem handoff_rest_main : driver_side -> QoL1.handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
intros [GA TS TB TD TGT OGA HTS HTB HTD].
destruct (B0J_funds TB TD HTB HTD) as (BQ & BB & BN & BD & BM & TB6).
pose proof (ARGS Q0Cb.atop_val) as AV.
destruct (@Qv81.Mq0.botj_cap sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) as (BCAP & BJ).
pose proof Hsp as (S1 & S2 & _). unfold sp_window_lo, sp_window_hi in S1, S2.
set (ms0 := QEpW.MS R bvmap_empty (Z_to_bv 64 0) (Z_to_bv 32 0) None FULL (QsjA.seg_rom QLPb.JO6SEGS)).
refine (ARGS QcN3.handoff_rest_jo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GA TS TB TD TGT OGA BCAP (QjTU.LM0J E w) QjTU.B0J (Qv81.Mq0.BOTJ sp E) ms0 eq_refl
(@QjTU.HH_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ eq_refl eq_refl (ARGS QoL1.RCJ_sec) ms0 eq_refl)
(QjTU.LM0J_40 E w) (ltac:(cbn; lia) : Z.of_nat (length (QjTU.LM0J E w)) < 8)  QjTU.B0J_bB39 QjTU.B0J_bQ0 BQ BB BN BD BM HTS (proj1 HTB) TB6 (proj1 HTD) _ _ _ _).
- unfold Qv81.Mq0.TOPJ. lia.
- lia.
- lia.
- lia.
Qed.
End PerState.

Theorem driver_side_of_target : forall sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS,
QOmG.OBL_TARGET_jo (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L (H6_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)) ->
driver_side sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS TGT.
destruct QOmG.jo_envelope_ok as (E1 & E2 & E3).
refine (DriverSide sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
QOmG.GA_jo QOmG.TGT_STACK_A_jo
QOmG.TGT_BB_A_jo QOmG.TGT_BD_A_jo TGT _ E1 E2 E3).
intros argv0 USP A LB LM FR B m md D HP.
exact (QscU.Mq0.ga_jo_of_drv argv0 USP m D).
Qed.

Definition OBL_DRIVER_SIDE_jo : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
E R FULL mo w ch (HCL : QrQA.HSCLASS_S w ch)
(CS : Q1LT.APS.cs_ok QLPb.JO6SEGS QCoy.AJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QLPb.JO6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QLPb.JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
driver_side sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.

Theorem handoff_rest_of_driver_side : OBL_DRIVER_SIDE_jo -> QG1H.OBL_HANDOFF_REST_jo.
Proof.
intros OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (handoff_rest_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.

Theorem json_object_asan_ba_driver : OBL_DRIVER_SIDE_jo ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. intros OBL. exact (QG1H.json_object_asan_ba (handoff_rest_of_driver_side OBL)). Qed.

Definition OBL_TARGET_ALL_jo : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
E R FULL mo w ch (HCL : QrQA.HSCLASS_S w ch)
(CS : Q1LT.APS.cs_ok QLPb.JO6SEGS QCoy.AJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QLPb.JO6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QLPb.JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
QOmG.OBL_TARGET_jo (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L (H6_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).

Theorem json_object_asan_ba_target : OBL_TARGET_ALL_jo ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
(mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
intros OBL. apply json_object_asan_ba_driver.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
exact (driver_side_of_target sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(OBL sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)).
Qed.
