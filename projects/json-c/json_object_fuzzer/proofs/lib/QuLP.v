(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RA := QDw3.

Section I.
Context {BAND : Band}.
Variable atn : node -> machine_state -> Prop.
Notation asegs := QvG1.asegs.
Variable AI : RA.alloc_ifaceA asegs atn RA.a_alayout.

Definition rtc_AR : list (Z * list byte) :=
[
(0x643120, QMow.cells_bytes [QMow.C8 (Z_to_bv 64 4096)]);
(0xe6b80, QMow.cells_bytes [QMow.C8 (Z_to_bv 64 0x642ea0)]);
(0x642ea0, QMow.cells_bytes [QMow.C8 band_guard]);
(0xe6928, le8 (Z_to_bv 64 0xf07d9));
(0xf07d9, [Z_to_bv 8 1]);
(0xf07d8, [Z_to_bv 8 1]);
(0xe7db0, le8 (Z_to_bv 64 0xdb750));
(0xe7da8, le8 (Z_to_bv 64 0xdb34c));
(0xe5da8, le8 (Z_to_bv 64 0x181628));
(0xe7c08, le8 (Z_to_bv 64 0xdb9b0));
(0x181723, [Z_to_bv 8 1]);
(0xe5dc0, le8 (Z_to_bv 64 0xf07e8));
(0xf07e8, le8 (Z_to_bv 64 0));
(0xe5dc8, le8 (Z_to_bv 64 0xf07f0));
(0xf07f0, le8 (Z_to_bv 64 0));
(0xe5dd0, le8 (Z_to_bv 64 0xf07e0));
(0xf07e0, le8 (Z_to_bv 64 0x7fffffffffff));
(0xe7c80, le8 (Z_to_bv 64 0xd385c));
(0xe7c88, le8 (Z_to_bv 64 0xd9004));
(0x18167c, [Z_to_bv 8 1]);
(0x18171d, [Z_to_bv 8 0]);
(0x181722, [Z_to_bv 8 1]);
(0xe5db0, le8 (Z_to_bv 64 0xed2f8));
(0xed315, [Z_to_bv 8 1]);
(0xe7d80, le8 (Z_to_bv 64 0xda7e8));
(0xe7d30, le8 (Z_to_bv 64 0xccddc));
(0xe6a98, le8 (Z_to_bv 64 0xa1d2c));
(0xec440, le8 (Z_to_bv 64 1));
(0xed3b0, le8 (Z_to_bv 64 0));
(0xed310, le4 (Z_to_bv 64 1));
(0xef35c, [Z_to_bv 8 1]);
(0x1816a0, le8 (Z_to_bv 64 0xffffffffffffffff));
(0xe6a20, le8 (Z_to_bv 64 0xe5cb0));
(0xe5cb0, le8 (Z_to_bv 64 0xea660));
(0xe6a28, le8 (Z_to_bv 64 0x0));
(0xe7c58, le8 (Z_to_bv 64 0xe1270));
(0xe6bb0, le8 (Z_to_bv 64 0xe2400) ++ le8 (Z_to_bv 64 0xe23f0));
(0xe23f0, le8 (Z_to_bv 64 0x99f88) ++ le8 (Z_to_bv 64 0x3dee0));
(0xe5d88, le8 (Z_to_bv 64 0xcc594) ++ le8 (Z_to_bv 64 0x0));
(0xe7c00, le8 (Z_to_bv 64 0xe7c00));
(0xe5d98, le8 (Z_to_bv 64 0x17f5a0) ++ le8 (Z_to_bv 64 0xe7de8) ++ le8 (Z_to_bv 64 0x181628) ++ le8 (Z_to_bv 64 0xed2f8) ++ le8 (Z_to_bv 64 0xefaf8) ++ le8 (Z_to_bv 64 0xf07e8) ++ le8 (Z_to_bv 64 0xf07f0) ++ le8 (Z_to_bv 64 0xf07e0) ++ le8 (Z_to_bv 64 0xe7db0));
(0xe6ab0, le8 (Z_to_bv 64 0xea960) ++ le8 (Z_to_bv 64 0xec420));
(0xe6a50, le8 (Z_to_bv 64 0x9dd64));
(0xe6a78, le8 (Z_to_bv 64 0x930e8));
(0x181725, [Z_to_bv 8 1]);
(0xe7c30, le8 (Z_to_bv 64 0xdb85c));
(0xe6a38, le8 (Z_to_bv 64 0x9c460));
(0xe6a40, le8 (Z_to_bv 64 0x9cb08));
(0xe6a48, le8 (Z_to_bv 64 0x9cf10));
(0xe6a60, le8 (Z_to_bv 64 0x9dde4));
(0xe6a88, le8 (Z_to_bv 64 0xa39f8));
(0xe6a90, le8 (Z_to_bv 64 0xa3c68));
(0xe6aa0, le8 (Z_to_bv 64 0xa2d9c));
(0xe6a58, le8 (Z_to_bv 64 0x9dd6c));
(0xe6a68, le8 (Z_to_bv 64 0x9edbc));
(0xe6a70, le8 (Z_to_bv 64 0xea520));
(0xe5c50, le8 (Z_to_bv 64 0x1485d));
(0xe2808, le8 (Z_to_bv 64 0x9ae48));
(0xe2810, le8 (Z_to_bv 64 0x9af30));
(0xe2818, le8 (Z_to_bv 64 0x9af3c));
(0xe2820, le8 (Z_to_bv 64 0x9b1a4));
(0xe2828, le8 (Z_to_bv 64 0x9b600));
(0xe2830, le8 (Z_to_bv 64 0x9ba30));
(0xe5db8, le8 (Z_to_bv 64 0xefaf8));
(0xefaf8, le8 (Z_to_bv 64 0x7fff8000));
(0xe5e10, le8 (Z_to_bv 64 0xefb00));
(0xefb00, le4 (Z_to_bv 64 1)) ].

Definition DL_AR : dlayout :=
mkDL (RA.ala_malloc RA.a_alayout) (RA.ala_free RA.a_alayout) (RA.ala_calloc RA.a_alayout)
(RA.ala_tp RA.a_alayout) (RA.ala_gp RA.a_alayout) (RA.ala_img_lo RA.a_alayout) (RA.ala_img_hi RA.a_alayout)
0x0e2000 QNwL.A_ERRNO RA.a_client_data
RA.DP_N
(RA.ala_malloc_stack RA.a_alayout) (RA.ala_free_stack RA.a_alayout) (RA.ala_calloc_stack RA.a_alayout)
rtc_AR.

Lemma bytes_at_slice : forall m A (bs : list byte) k n, bytes_at asegs m A bs -> (k + n <=? length bs)%nat = true ->
bytes_at asegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros m A bs k n HB Hl. apply Nat.leb_le in Hl.
rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB as [_ HB]. rewrite firstn_length_le in HB by lia.
rewrite <- (firstn_skipn n (skipn k bs)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

Ltac rtc_pick base k n :=
match goal with
| H : QoSL.ro_cells _ _ base _ |- _ => exact (bytes_at_slice _ _ _ k n (proj2 H) eq_refl)
| H : QoSL.rw_cells _ _ base _ |- _ => exact (bytes_at_slice _ _ _ k n (proj2 (proj1 H)) eq_refl)
end.

Lemma rt_consts_rtc : forall m, RA.rt_consts_at asegs m ->
Qp4j.shadow_base asegs m ->
(QoSL.ro_cells asegs m 0x0e5e10 [QMow.C8 (Z_to_bv 64 0x0efb00)] /\ QoSL.ro_cells asegs m 0x0efb00 [QMow.C4 (Z_to_bv 64 1)]) ->
Forall (fun c => bytes_at asegs m (fst c) (snd c)) rtc_AR.
Proof.
intros m RT SB UAR. unfold RA.rt_consts_at in RT. unfold Qp4j.shadow_base in SB.
pose proof (proj2 (proj1 SB)) as SB0. pose proof (proj2 (proj2 SB)) as SB1. pose proof (proj2 (proj1 UAR)) as UAR0. pose proof (proj2 (proj2 UAR)) as UAR1. clear SB UAR.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
unfold rtc_AR. repeat (apply Forall_cons; [| ]); [.. | apply Forall_nil]; cbn [fst snd].
- rtc_pick 0x643120 0%nat 8%nat.
- rtc_pick 0x0e6b80 0%nat 8%nat.
- rtc_pick 0x642ea0 0%nat 8%nat.
- rtc_pick 0x0e6928 0%nat 8%nat.
- rtc_pick 0x0f07d8 1%nat 1%nat.
- rtc_pick 0x0f07d8 0%nat 1%nat.
- rtc_pick 0x0e7da8 8%nat 8%nat.
- rtc_pick 0x0e7da8 0%nat 8%nat.
- rtc_pick 0x0e5da8 0%nat 8%nat.
- rtc_pick 0x0e7c08 0%nat 8%nat.
- rtc_pick 0x181723 0%nat 1%nat.
- rtc_pick 0x0e5dc0 0%nat 8%nat.
- rtc_pick 0x0f07e0 8%nat 8%nat.
- rtc_pick 0x0e5dc0 8%nat 8%nat.
- rtc_pick 0x0f07e0 16%nat 8%nat.
- rtc_pick 0x0e5dc0 16%nat 8%nat.
- rtc_pick 0x0f07e0 0%nat 8%nat.
- rtc_pick 0x0e7c78 8%nat 8%nat.
- rtc_pick 0x0e7c88 0%nat 8%nat.
- rtc_pick 0x18167c 0%nat 1%nat.
- rtc_pick 0x18171d 0%nat 1%nat.
- rtc_pick 0x181722 0%nat 1%nat.
- rtc_pick 0x0e5da8 8%nat 8%nat.
- rtc_pick 0x0ed315 0%nat 1%nat.
- rtc_pick 0x0e7d80 0%nat 8%nat.
- rtc_pick 0x0e7d30 0%nat 8%nat.
- rtc_pick 0x0e6a98 0%nat 8%nat.
- rtc_pick 0x0ec440 0%nat 8%nat.
- rtc_pick 0x0ed3b0 0%nat 8%nat.
- rtc_pick 0x0ed310 0%nat 4%nat.
- rtc_pick 0x0ef35c 0%nat 1%nat.
- rtc_pick 0x1816a0 0%nat 8%nat.
- rtc_pick 0x0e6a20 0%nat 8%nat.
- rtc_pick 0x0e5cb0 0%nat 8%nat.
- rtc_pick 0x0e6a20 8%nat 8%nat.
- rtc_pick 0x0e7c58 0%nat 8%nat.
- apply bytes_at_app; split; [rtc_pick 0x0e6bb0 0%nat 8%nat| rtc_pick 0x0e6bb0 8%nat 8%nat].
- apply bytes_at_app; split; [rtc_pick 0x0e23f0 0%nat 8%nat| rtc_pick 0x0e23f0 8%nat 8%nat].
- apply bytes_at_app; split; [rtc_pick 0x0e5d88 0%nat 8%nat| rtc_pick 0x0e5d88 8%nat 8%nat].
- rtc_pick 0x0e7c00 0%nat 8%nat.
- apply bytes_at_app; split; [rtc_pick 0x0e5d98 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e5da0 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e5da8 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e5da8 8%nat 8%nat| apply bytes_at_app; split; [exact SB0| apply bytes_at_app; split; [rtc_pick 0x0e5dc0 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e5dc0 8%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e5dc0 16%nat 8%nat| rtc_pick 0x0e5dc0 24%nat 8%nat]]]]]]]].
- apply bytes_at_app; split; [rtc_pick 0x0e6ab0 0%nat 8%nat| rtc_pick 0x0e6ab0 8%nat 8%nat].
- rtc_pick 0x0e6a50 0%nat 8%nat.
- rtc_pick 0x0e6a78 0%nat 8%nat.
- rtc_pick 0x181725 0%nat 1%nat.
- rtc_pick 0x0e7c30 0%nat 8%nat.
- rtc_pick 0x0e6a38 0%nat 8%nat.
- rtc_pick 0x0e6a40 0%nat 8%nat.
- rtc_pick 0x0e6a48 0%nat 8%nat.
- rtc_pick 0x0e6a60 0%nat 8%nat.
- rtc_pick 0x0e6a88 0%nat 8%nat.
- rtc_pick 0x0e6a90 0%nat 8%nat.
- rtc_pick 0x0e6aa0 0%nat 8%nat.
- rtc_pick 0x0e6a58 0%nat 8%nat.
- rtc_pick 0x0e6a68 0%nat 8%nat.
- rtc_pick 0x0e6a70 0%nat 8%nat.
- rtc_pick 0x0e5c50 0%nat 8%nat.
- rtc_pick 0x0e2808 0%nat 8%nat.
- rtc_pick 0x0e2810 0%nat 8%nat.
- rtc_pick 0x0e2818 0%nat 8%nat.
- rtc_pick 0x0e2820 0%nat 8%nat.
- rtc_pick 0x0e2828 0%nat 8%nat.
- rtc_pick 0x0e2830 0%nat 8%nat.
- exact SB0.
- exact SB1.
- exact UAR0.
- exact UAR1.
Qed.

Definition toRA (RE : aentry) : RA.aentry := RA.mkAE (ae_sp0 RE) (ae_stack_top RE) (ae_fs_base RE) (ae_L RE).

Definition run_AR (s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (m : word -> option byte) : Prop :=
RA.ai_run _ _ _ AI s LB FS (toRA RE) m.

Definition DCo_AR : donor_core band_lo asegs atn DL_AR.
Proof.
refine (mkDC band_lo asegs atn DL_AR run_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); unfold run_AR.
- intros s s' LB FS RE m. exact (RA.ai_run_ext _ _ _ AI s s' LB FS (toRA RE) m).
- intros s LB LB' FS FS' RE m. exact (RA.ai_run_perm _ _ _ AI s LB LB' FS FS' (toRA RE) m).
- intros s LB FS RE m m' W. exact (RA.ai_run_frame _ _ _ AI s LB FS (toRA RE) m m' W).
- intros s LB FS RE m b. exact (RA.ai_block_range _ _ _ AI s LB FS (toRA RE) m b).
- intros s LB FS RE m b. exact (RA.ai_block_small _ _ _ AI s LB FS (toRA RE) m b).
- intros s LB FS RE m b1 b2. exact (RA.ai_blocks_disjoint _ _ _ AI s LB FS (toRA RE) m b1 b2).
- intros s LB FS RE m. exact (RA.ai_blocks_nodup _ _ _ AI s LB FS (toRA RE) m).
- intros s LB FS RE m p A n. exact (RA.ai_block_shadow _ _ _ AI s LB FS (toRA RE) m p A n).
- intros s LB FS RE m. exact (RA.ai_errno _ _ _ AI s LB FS (toRA RE) m).
- intros s LB FS RE m m' v. exact (RA.ai_errno_frame _ _ _ AI s LB FS (toRA RE) m m' v).
- intros L. unfold amallocA_stmt. intros. eapply (RA.ai_malloc _ _ _ AI L) with (RE := toRA RE); eassumption.
- intros L. unfold acallocA_stmt. intros. eapply (RA.ai_calloc _ _ _ AI L) with (RE := toRA RE); eassumption.
- intros L. unfold afreeA_stmt. intros. eapply (RA.ai_free _ _ _ AI L) with (RE := toRA RE); eassumption.
- unfold afree_nullA_stmt. intros. eapply (RA.ai_free_null _ _ _ AI) with (RE := toRA RE); eassumption.
- intros s LB FS RE m Hrun. exact (rt_consts_rtc m (RA.ai_rt_consts _ _ _ AI s LB FS (toRA RE) m Hrun) (RA.ai_shadow_base _ _ _ AI s LB FS (toRA RE) m Hrun) (RA.ai_uar_on _ _ _ AI s LB FS (toRA RE) m Hrun)).
Defined.
End I.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition Band_RC {RC__ : Q6q3.RunConsts} (guard : word) : Band := mkBand Q6q3.alloc_ceiling Q6q3.alloc_ceiling_range guard.

Definition DCo_AR_rc {RC__ : Q6q3.RunConsts} (guard : word) (atn : node -> machine_state -> Prop)
(AI : @RA.alloc_ifaceA (Band_RC guard) QvG1.asegs atn RA.a_alayout) :
donor_core Q6q3.alloc_ceiling QvG1.asegs atn (@DL_AR (Band_RC guard)) :=
@DCo_AR (Band_RC guard) atn AI.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5bV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Definition DCo_jo {RC__ : Q6q3.RunConsts} (guard : word) (LV : Qsn5.lvp) :
donor_core Q6q3.alloc_ceiling QvG1.asegs
(QBrp.at_nodeA LV QvG1.asegs) (@DL_AR (Band_RC guard)) :=
DCo_AR_rc guard _ (@Q5bV.a_alloc_iface (Band_RC guard) LV).

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma DFs_jo {RC__ : Q6q3.RunConsts} (guard : word) (LV : Qsn5.lvp) :
donor_fs Q6q3.alloc_ceiling QvG1.asegs
(QBrp.at_nodeA LV QvG1.asegs) (@DL_AR (Band_RC guard)) (DCo_jo guard LV)
(fun k => if k =? 0 then 0x4a790 else if k =? 1 then 0x4a904 else if k =? 2 then 0x4aa94 else 0) 4096.
Proof.
pose (AIj := @Q5bV.a_alloc_iface (Band_RC guard) LV).
pose (aC := @Q5bV.aC (Band_RC guard)).
constructor; unfold DCo_jo, DCo_AR_rc, DCo_AR, run_AR; cbn [dc_run].
- intros s LB FS RE m H. pose proof (RA.ai_entry_facts _ _ _ AIj s LB FS (toRA RE) m H) as (_ & _ & E1 & E2 & _). split; [exact E1| exact E2].
- intros s LB FS RE m f. exact (RA.ai_fframe_range _ _ _ AIj s LB FS (toRA RE) m f).
- intros s LB FS RE m c0 f. exact (@QpY2.Mq0.ARUN_fframe_align (Band_RC guard) aC (@Q5bV.aC_RF (Band_RC guard)) c0 s LB FS (toRA RE) m f).
- intros s LB FS RE m f1 f2. exact (RA.ai_fframes_disjoint _ _ _ AIj s LB FS (toRA RE) m f1 f2).
- intros s LB FS RE m f b. exact (RA.ai_fframe_block_disjoint _ _ _ AIj s LB FS (toRA RE) m f b).
- intros s LB FS RE m b. exact (@QpY2.Mq0.ARUN_fs_block_disjoint (Band_RC guard) aC s LB FS (toRA RE) m b).
- intros s LB FS RE m. exact (RA.ai_fframes_nodup _ _ _ AIj s LB FS (toRA RE) m).
- intros c0 s LB FS RE m f flag. exact (RA.ai_fframe_release0 _ _ _ AIj c0 s LB FS (toRA RE) m f flag).
- intros c0 s LB FS RE m f. exact (RA.ai_fframe_flag0 _ _ _ AIj c0 s LB FS (toRA RE) m f).
- intros k Hk. assert (Ek : k = 0 \/ k = 1 \/ k = 2) by (destruct Hk as [Hk | [-> Hk3]]; [lia | exfalso; apply Hk3; reflexivity]). unfold astack_mallocA_stmt. destruct Ek as [-> | [-> | ->]]; cbn [Z.eqb]; intros.
+ eapply (RA.ai_stack_malloc_0 _ _ _ AIj) with (RE := toRA RE); eassumption.
+ eapply (RA.ai_stack_malloc_1 _ _ _ AIj) with (RE := toRA RE); eassumption.
+ eapply (RA.ai_stack_malloc_2 _ _ _ AIj) with (RE := toRA RE); eassumption.
- intros s LB FS RE m p A n. exact (@QNQk.Mq3.ARUN_blk_slack (Band_RC guard) aC (@Q5bV.aC_RC (Band_RC guard)) s LB FS (toRA RE) m p A n).
- intros s LB FS RE m p n. exact (RA.ai_nbhd _ _ _ AIj s LB FS (toRA RE) m p n).
Qed.
