(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5 QJFf Qknc QBrp Q1KO QOb0 QPa2 Q6sh QzgH Q7z8 QvDJ QKTr Qqcs QNLn QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QHqi Qi08 Qfya QUZl QXEH Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q1KO.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi.

Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Import Qb5q.Mq2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.

Section KlaMng.
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
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation h := (m_vmmaps mo).
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation GB := (GRPB E w) (only parsing).
#[local] Notation PERM0 := (PERM0_J E w) (only parsing).
#[local] Notation MTB := (4096 * bv_unsigned (ev E (fst (META_O w)))).

Lemma meta_entry : exists e, (exists p, In p PERM0 /\ e = QzgH.z2w p) /\ bv_unsigned (fst e) = MTB /\ bv_unsigned (snd e) = 8192.
Proof.
assert (Hin : In (META_O w) (OBJS_W w)) by (destruct w; cbn; tauto).
pose proof (MA u_obj_base _ Hin) as UB. pose proof (MA u_obj_len _ Hin) as UL.
pose proof (MA entry_top _ ((MA in_maps_obj) _ Hin)) as T. pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
exists (obj_e E (META_O w)). split; [|split; [exact UB | rewrite UL; destruct w; reflexivity]].
exists (wiv2z (obj_e E (META_O w))). split; [exact (MV4 meta_perm)|]. symmetry. apply (MA z2w_wiv2z). lia.
Qed.

Lemma oranges_cov : forall Lg0 : Qfya.mled, Qfya.ld_resv Lg0 = QXEH.ref_reserved ->
(Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None) ->
forall r, In r (QNLn.Mq0.oranges Lg0) -> QNLn.Mq0.ocov PERM0 h r.
Proof.
intros Lg0 HR HM r Hin. unfold QNLn.Mq0.oranges in Hin. rewrite HR in Hin. apply in_app_iff in Hin as [Hin|Hin].
-
exists (Z_to_bv 64 (fst r), Z_to_bv 64 (snd r)). unfold QXEH.ref_reserved in Hin. cbn [In] in Hin.
split; [left; rewrite (P co_res), asan_segments_reserved; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; tauto|].
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite !u64_lit by lia; lia.
- destruct meta_entry as (e & He & UB & UL). exists e. split; [right; exact He|]. rewrite UB, UL.
destruct HM as [[HM HB]|[HM HB]]; rewrite HM, HB in Hin; cbn [map app In fst snd] in Hin; destruct Hin as [<-|[]]; cbn [fst snd];
[change (QUZl.round_up_pg 8192) with 8192; unfold QUZl.PGSZ | change (QUZl.round_up_pg 8192) with 8192]; lia.
Qed.

Theorem KLA_main_mng : forall {RC__ : QNLn.Mq0.RC.RunConsts} (Lg0 : Qfya.mled) (g0 : QvDJ.ghost) (ms : machine_state),
QNLn.Mq0.RC.alloc_ceiling = atopE E -> ms_mem ms = FULL ->
Qfya.ld_resv Lg0 = QXEH.ref_reserved -> Qfya.ld_groups Lg0 = [(GB, 4096)] ->
(Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None) ->
QvDJ.g_chunks g0 = [] -> 0 <= QvDJ.g_spent g0 ->
QNLn.Mq0.KLA LV PERM0 Qi08.TMAX_J Qi08.NMAX_J (fun _ => false) Lg0 g0 (mkCfg ms mo) (QNLn.Mq0.in_sh GB 4096) (view LV mo FULL) BC_J TOT_J 22.
Proof.
intros RC__ Lg0 g0 ms HRC Hms HR HG HM Hch Hsp0.
exact ((MV4 KLA_main_J) Lg0 g0 ms HRC Hms HG Hch Hsp0 (oranges_cov Lg0 HR HM)).
Qed.
End KlaMng.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW7x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb5q. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.

Section KlaMng.
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
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation h := (m_vmmaps mo).
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation GB := (GRPB E w) (only parsing).
#[local] Notation PERM0 := (PERM0_J E w) (only parsing).
#[local] Notation MTB := (4096 * bv_unsigned (ev E (fst (META_O w)))).

Lemma meta_entry : exists e, (exists p, In p PERM0 /\ e = QzgH.z2w p) /\ bv_unsigned (fst e) = MTB /\ bv_unsigned (snd e) = 8192.
Proof.
assert (Hin : In (META_O w) (OBJS_W w)) by (destruct w; cbn; tauto).
pose proof (MA u_obj_base _ Hin) as UB. pose proof (MA u_obj_len _ Hin) as UL.
pose proof (MA entry_top _ ((MA in_maps_obj) _ Hin)) as T. pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
exists (obj_e E (META_O w)). split; [|split; [exact UB | rewrite UL; destruct w; reflexivity]].
exists (wiv2z (obj_e E (META_O w))). split; [exact (MV4 meta_perm)|]. symmetry. apply (MA z2w_wiv2z). lia.
Qed.

Lemma oranges_cov : forall Lg0 : Qfya.mled, Qfya.ld_resv Lg0 = QW7x.Mq0.ref_reserved ->
(Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None) ->
forall r, In r (QNLn.Mq0.oranges Lg0) -> QNLn.Mq0.ocov PERM0 h r.
Proof.
intros Lg0 HR HM r Hin. unfold QNLn.Mq0.oranges in Hin. rewrite HR in Hin. apply in_app_iff in Hin as [Hin|Hin].
-
exists (Z_to_bv 64 (fst r), Z_to_bv 64 (snd r)). unfold QW7x.Mq0.ref_reserved in Hin. cbn [In] in Hin.
split; [left; rewrite (P co_res), asan_segments_reserved; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; tauto|].
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite !u64_lit by lia; lia.
- destruct meta_entry as (e & He & UB & UL). exists e. split; [right; exact He|]. rewrite UB, UL.
destruct HM as [[HM HB]|[HM HB]]; rewrite HM, HB in Hin; cbn [map app In fst snd] in Hin; destruct Hin as [<-|[]]; cbn [fst snd];
[change (QUZl.round_up_pg 8192) with 8192; unfold QUZl.PGSZ | change (QUZl.round_up_pg 8192) with 8192]; lia.
Qed.

Theorem KLA_main_mng : forall {RC__ : QNLn.Mq0.RC.RunConsts} (Lg0 : Qfya.mled) (g0 : QvDJ.ghost) (ms : machine_state),
QNLn.Mq0.RC.alloc_ceiling = atopE E -> ms_mem ms = FULL ->
Qfya.ld_resv Lg0 = QW7x.Mq0.ref_reserved -> Qfya.ld_groups Lg0 = [(GB, 4096)] ->
(Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None) ->
QvDJ.g_chunks g0 = [] -> 0 <= QvDJ.g_spent g0 ->
QNLn.Mq0.KLA LV PERM0 QVyC.TMAX_J QVyC.NMAX_J (fun _ => false) Lg0 g0 (mkCfg ms mo) (QNLn.Mq0.in_sh GB 4096) (view LV mo FULL) BC_J TOT_J 22.
Proof.
intros RC__ Lg0 g0 ms HRC Hms HR HG HM Hch Hsp0.
exact ((MV4 KLA_main_J) Lg0 g0 ms HRC Hms HG Hch Hsp0 (oranges_cov Lg0 HR HM)).
Qed.
End KlaMng.
