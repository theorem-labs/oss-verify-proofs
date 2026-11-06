(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Qpj5 Q6sh QQwg QKTr QvDJ QJBH QlES QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk QV3O QpY2 Q9Ho QYyZ QnRU QOJv Qu3b QXcn QjgW QsJM Qx6U QcA6 Qo6W QmvA QpME QVo2 QFd5 QDpG_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QYyZ.Mqc QXcn QjgW QsJM Qx6U.Mq6 QcA6.Mq3 Qo6W QnRU.Mqm QmvA QpME.Mq9 QOJv QOJv.Mq7 QnRU.Mqe QmvA.Mq5 QpME.Mqc QVo2.Mq4 QOJv.Mq9 QFd5.Mq8 QDpG_c1.Mq1 QmvA.Mq6 QcA6.Mq4 Qo6W.Mq2 QpY2.Mqa.
Import ListNotations.
Open Scope Z_scope.

Section Comp.
Context {BAND : Band}.

Definition aC : arun_components.
Proof.
refine (@mkAC BAND RTconst RStats RPrim RChunks RSec RQuar RDepot RFake _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
try (intros; first [ eapply RTconst_frame | eapply RStats_frame | eapply RPrim_frame | eapply RChunks_frame
| eapply RSec_frame | eapply RQuar_frame | eapply RDepot_frame | eapply RFake_frame ]; eassumption).
- exact RTconst_shadow.
- intros; eapply RPrim_ext; eassumption.
- intros; eapply RChunks_ext; eassumption.
- intros; eapply RSec_ext; eassumption.
- intros; eapply RQuar_ext; eassumption.
- intros; eapply RQuar_alloc_sec; eassumption.
- intros; eapply RChunks_perm; eassumption.
- intros; eapply RSec_perm; eassumption.
- intros; eapply RQuar_perm; eassumption.
- intros; eapply RFake_perm; eassumption.
- intros; eapply RChunks_shadow; eassumption.
- intros; eapply RFake_release0; eassumption.
Defined.

Lemma aC_RT : ac_RTconst aC = RTconst. Proof. reflexivity. Qed.
Lemma aC_RS : ac_RStats aC = RStats. Proof. reflexivity. Qed.
Lemma aC_RP : ac_RPrim aC = RPrim. Proof. reflexivity. Qed.
Lemma aC_RC : ac_RChunks aC = RChunks. Proof. reflexivity. Qed.
Lemma aC_RSec : ac_RSec aC = RSec. Proof. reflexivity. Qed.
Lemma aC_RQ : ac_RQuar aC = RQuar. Proof. reflexivity. Qed.
Lemma aC_RD : ac_RDepot aC = RDepot. Proof. reflexivity. Qed.
Lemma aC_RF : ac_RFake aC = RFake. Proof. reflexivity. Qed.
Lemma aC_RT_iff : forall RE X m, ac_RTconst aC RE X m <-> RTconst RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RP_iff : forall a G RE X m, ac_RPrim aC a G RE X m <-> RPrim a G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RC_iff : forall a LB G RE X m, ac_RChunks aC a LB G RE X m <-> RChunks a LB G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RQ_iff : forall a LB G RE X m, ac_RQuar aC a LB G RE X m <-> RQuar a LB G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RF_iff : forall FS RE X m, ac_RFake aC FS RE X m <-> RFake FS RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RSec_ext : forall a a' LB LB' RE X m, ac_RSec aC a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec aC a' LB' RE X m.
Proof. intros a a' LB LB' RE X m H E1 E2 E3 _. exact (ac_RSec_ext aC a a' LB LB' RE X m H E1 E2 E3). Qed.
End Comp.

Section Inst.
Context {BAND : Band}.
Variable LV : lvp.
Local Notation atn := (at_nodeA LV asegs).

Hypothesis LV_SHOFF : lv_shoff LV = 0x7fff8000.

Let map_or_die_spec : forall RE X, map_or_die_stmt LV RE X := fun RE X => QFd5.Mq8.map_or_die_spec LV RE X.

Let large_alloc_specs : forall RE X, large_alloc_stmt RE X LV := fun RE X => large_alloc_spec LV RE X (map_or_die_spec RE X).
Let poison_zero_specs : forall RE X, poison_zero_stmt_lh RE X LV := fun RE X => poison_zero_spec_lh LV RE X.

Lemma free_null_A : afree_nullA_stmt asegs a_alayout (ARUN aC).
Proof.
pose proof (free_null_spec aC aC_RT aC_RS aC_RP aC_RC aC_RQ aC_RD) as H.
unfold afree_nullA_stmt6 in H. unfold afree_nullA_stmt. exact H.
Qed.

Lemma malloc_A : forall L, amallocA_stmt asegs atn a_alayout (ARUN aC) L.
Proof.
intros L. unfold amallocA_stmt. intros.
destruct (from_primary n) eqn:HP.
- eapply (malloc_prim_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RD); eassumption.
- eapply (malloc_sec_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RSec aC_RD large_alloc_specs poison_zero_specs); eassumption.
Qed.

Lemma calloc_A : forall L, acallocA_stmt asegs atn a_alayout (ARUN aC) L.
Proof.
intros L. unfold acallocA_stmt. intros.
destruct (from_primary (cnt * sz)) eqn:HP.
- eapply (calloc_prim_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RD); eassumption.
- eapply (calloc_sec_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RSec aC_RD large_alloc_specs poison_zero_specs); eassumption.
Qed.

Definition a_alloc_iface : alloc_ifaceA asegs atn a_alayout :=
{| ai_run := ARUN aC;
ai_run_ext := ARUN_ext aC;
ai_run_perm := ARUN_perm aC;
ai_run_frame := ARUN_frame aC;
ai_block_range := ARUN_block_range aC;
ai_block_small := ARUN_block_small aC;
ai_blocks_disjoint := ARUN_blocks_disjoint aC;
ai_blocks_nodup := ARUN_blocks_nodup aC;
ai_block_shadow := ARUN_block_shadow aC;
ai_fframe_range := ARUN_fframe_range aC;
ai_fframes_disjoint := ARUN_fframes_disjoint aC;
ai_fframe_block_disjoint := ARUN_fframe_block_disjoint aC;
ai_fframe_release0 := ARUN_fframe_releaseK aC aC_RF;
ai_fframe_flag0 := ARUN_fframe_flagK aC aC_RF;
ai_fframes_nodup := ARUN_fframes_nodup aC aC_RF;
ai_entry_facts := ARUN_entry_facts aC;
ai_shadow_base := ARUN_shadow_base aC;
ai_uar_on := ARUN_uar_on aC aC_RT;
ai_rt_consts := ARUN_rt_consts aC aC_RT;
ai_errno := ARUN_errno aC aC_RS;
ai_errno_frame := ARUN_errno_frame aC aC_RS;
ai_nbhd := ARUN_nbhd aC aC_RP aC_RC aC_RQ aC_RF;
ai_malloc := malloc_A;
ai_calloc := calloc_A;
ai_free := free_icpt_spec aC LV aC_RT aC_RS aC_RP aC_RC aC_RQ aC_RD aC_RSec_ext;
ai_free_null := free_null_A;
ai_stack_malloc_0 := stack_malloc_0_A aC aC_RT_iff aC_RF_iff;
ai_stack_malloc_1 := stack_malloc_1_A aC aC_RT_iff aC_RF_iff;
ai_stack_malloc_2 := stack_malloc_2_A aC aC_RT_iff aC_RF_iff;
ai_asan_memset := asan_memset_A aC aC_RT_iff aC_RP_iff aC_RC_iff aC_RQ_iff aC_RF_iff;
ai_set_shadow_00 := set_shadow_00_A aC aC_RT_iff;
ai_set_shadow_f8 := set_shadow_f8_A aC aC_RT_iff |}.
End Inst.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUnM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZbm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZbm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo6W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo6W.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFd5.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDpG_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDpG_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo6W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo6W.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section Comp.
Context {BAND : Band}.

Definition aC : arun_components.
Proof.
refine (@mkAC BAND RTconst RStats RPrim RChunks RSec RQuar RDepot RFake _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
try (intros; first [ eapply RTconst_frame | eapply RStats_frame | eapply RPrim_frame | eapply RChunks_frame
| eapply RSec_frame | eapply RQuar_frame | eapply RDepot_frame | eapply RFake_frame ]; eassumption).
- exact RTconst_shadow.
- intros; eapply RPrim_ext; eassumption.
- intros; eapply RChunks_ext; eassumption.
- intros; eapply RSec_ext; eassumption.
- intros; eapply RQuar_ext; eassumption.
- intros; eapply RQuar_alloc_sec; eassumption.
- intros; eapply RChunks_perm; eassumption.
- intros; eapply RSec_perm; eassumption.
- intros; eapply RQuar_perm; eassumption.
- intros; eapply RFake_perm; eassumption.
- intros; eapply RChunks_shadow; eassumption.
- intros; eapply RFake_release0; eassumption.
Defined.

Lemma aC_RT : ac_RTconst aC = RTconst. Proof. reflexivity. Qed.
Lemma aC_RS : ac_RStats aC = RStats. Proof. reflexivity. Qed.
Lemma aC_RP : ac_RPrim aC = RPrim. Proof. reflexivity. Qed.
Lemma aC_RC : ac_RChunks aC = RChunks. Proof. reflexivity. Qed.
Lemma aC_RSec : ac_RSec aC = RSec. Proof. reflexivity. Qed.
Lemma aC_RQ : ac_RQuar aC = RQuar. Proof. reflexivity. Qed.
Lemma aC_RD : ac_RDepot aC = RDepot. Proof. reflexivity. Qed.
Lemma aC_RF : ac_RFake aC = RFake. Proof. reflexivity. Qed.
Lemma aC_RT_iff : forall RE X m, ac_RTconst aC RE X m <-> RTconst RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RP_iff : forall a G RE X m, ac_RPrim aC a G RE X m <-> RPrim a G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RC_iff : forall a LB G RE X m, ac_RChunks aC a LB G RE X m <-> RChunks a LB G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RQ_iff : forall a LB G RE X m, ac_RQuar aC a LB G RE X m <-> RQuar a LB G RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RF_iff : forall FS RE X m, ac_RFake aC FS RE X m <-> RFake FS RE X m. Proof. intros; cbn; tauto. Qed.
Lemma aC_RSec_ext : forall a a' LB LB' RE X m, ac_RSec aC a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec aC a' LB' RE X m.
Proof. intros a a' LB LB' RE X m H E1 E2 E3 _. exact (ac_RSec_ext aC a a' LB LB' RE X m H E1 E2 E3). Qed.
End Comp.

Section Inst.
Context {BAND : Band}.
Variable LV : lvp.
Local Notation atn := (at_nodeA LV asegs).

Hypothesis LV_SHOFF : lv_shoff LV = 0x7fff8000.

Let map_or_die_spec : forall RE X, map_or_die_stmt LV RE X := fun RE X => QFd5.Mq4.map_or_die_spec LV RE X.

Let large_alloc_specs : forall RE X, large_alloc_stmt RE X LV := fun RE X => large_alloc_spec LV RE X (map_or_die_spec RE X).
Let poison_zero_specs : forall RE X, poison_zero_stmt_lh RE X LV := fun RE X => poison_zero_spec_lh LV RE X.

Lemma free_null_A : afree_nullA_stmt asegs a_alayout (ARUN aC).
Proof.
pose proof (free_null_spec aC aC_RT aC_RS aC_RP aC_RC aC_RQ aC_RD) as H.
unfold afree_nullA_stmt6 in H. unfold afree_nullA_stmt. exact H.
Qed.

Lemma malloc_A : forall L, amallocA_stmt asegs atn a_alayout (ARUN aC) L.
Proof.
intros L. unfold amallocA_stmt. intros.
destruct (from_primary n) eqn:HP.
- eapply (malloc_prim_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RD); eassumption.
- eapply (malloc_sec_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RSec aC_RD large_alloc_specs poison_zero_specs); eassumption.
Qed.

Lemma calloc_A : forall L, acallocA_stmt asegs atn a_alayout (ARUN aC) L.
Proof.
intros L. unfold acallocA_stmt. intros.
destruct (from_primary (cnt * sz)) eqn:HP.
- eapply (calloc_prim_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RD); eassumption.
- eapply (calloc_sec_A aC LV aC_RT aC_RS aC_RP aC_RC aC_RSec aC_RD large_alloc_specs poison_zero_specs); eassumption.
Qed.

Definition a_alloc_iface : alloc_ifaceA asegs atn a_alayout :=
{| ai_run := ARUN aC;
ai_run_ext := ARUN_ext aC;
ai_run_perm := ARUN_perm aC;
ai_run_frame := ARUN_frame aC;
ai_block_range := ARUN_block_range aC;
ai_block_small := ARUN_block_small aC;
ai_blocks_disjoint := ARUN_blocks_disjoint aC;
ai_blocks_nodup := ARUN_blocks_nodup aC;
ai_block_shadow := ARUN_block_shadow aC;
ai_fframe_range := ARUN_fframe_range aC;
ai_fframes_disjoint := ARUN_fframes_disjoint aC;
ai_fframe_block_disjoint := ARUN_fframe_block_disjoint aC;
ai_fframe_release0 := ARUN_fframe_releaseK aC aC_RF;
ai_fframe_flag0 := ARUN_fframe_flagK aC aC_RF;
ai_fframes_nodup := ARUN_fframes_nodup aC aC_RF;
ai_entry_facts := ARUN_entry_facts aC;
ai_shadow_base := ARUN_shadow_base aC;
ai_uar_on := ARUN_uar_on aC aC_RT;
ai_rt_consts := ARUN_rt_consts aC aC_RT;
ai_errno := ARUN_errno aC aC_RS;
ai_errno_frame := ARUN_errno_frame aC aC_RS;
ai_nbhd := ARUN_nbhd aC aC_RP aC_RC aC_RQ aC_RF;
ai_malloc := malloc_A;
ai_calloc := calloc_A;
ai_free := free_icpt_spec aC LV aC_RT aC_RS aC_RP aC_RC aC_RQ aC_RD aC_RSec_ext;
ai_free_null := free_null_A;
ai_stack_malloc_0 := stack_malloc_0_A aC aC_RT_iff aC_RF_iff;
ai_stack_malloc_1 := stack_malloc_1_A aC aC_RT_iff aC_RF_iff;
ai_stack_malloc_2 := stack_malloc_2_A aC aC_RT_iff aC_RF_iff;
ai_asan_memset := asan_memset_A aC aC_RT_iff aC_RP_iff aC_RC_iff aC_RQ_iff aC_RF_iff;
ai_set_shadow_00 := set_shadow_00_A aC aC_RT_iff;
ai_set_shadow_f8 := set_shadow_f8_A aC aC_RT_iff |}.
End Inst.
