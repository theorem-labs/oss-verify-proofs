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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RA := QWRO.

Section I.
Context {BAND : Band}.
Variable atn : node -> machine_state -> Prop.
Notation asegs := QZzg.asegs.
Variable AI : RA.alloc_ifaceA asegs atn RA.a_alayout.

Definition rtc_AR : list (Z * list byte) :=
[
(0x6457e0, QMow.cells_bytes [QMow.C8 (Z_to_bv 64 4096)]);
(0xe8f90, QMow.cells_bytes [QMow.C8 (Z_to_bv 64 0x645560)]);
(0x645560, QMow.cells_bytes [QMow.C8 band_guard]);
(0xe8d28, le8 (Z_to_bv 64 0xf2e99));
(0xf2e99, [Z_to_bv 8 1]);
(0xf2e98, [Z_to_bv 8 1]);
(0xea1d0, le8 (Z_to_bv 64 0xdde14));
(0xea1c8, le8 (Z_to_bv 64 0xdda10));
(0xe81a8, le8 (Z_to_bv 64 0x183ce8));
(0xea028, le8 (Z_to_bv 64 0xde074));
(0x183de3, [Z_to_bv 8 1]);
(0xe81c0, le8 (Z_to_bv 64 0xf2ea8));
(0xf2ea8, le8 (Z_to_bv 64 0));
(0xe81c8, le8 (Z_to_bv 64 0xf2eb0));
(0xf2eb0, le8 (Z_to_bv 64 0));
(0xe81d0, le8 (Z_to_bv 64 0xf2ea0));
(0xf2ea0, le8 (Z_to_bv 64 0x7fffffffffff));
(0xea0a0, le8 (Z_to_bv 64 0xd5f20));
(0xea0a8, le8 (Z_to_bv 64 0xdb6c8));
(0x183d3c, [Z_to_bv 8 1]);
(0x183ddd, [Z_to_bv 8 0]);
(0x183de2, [Z_to_bv 8 1]);
(0xe81b0, le8 (Z_to_bv 64 0xef9b8));
(0xef9d5, [Z_to_bv 8 1]);
(0xea1a0, le8 (Z_to_bv 64 0xdceac));
(0xea150, le8 (Z_to_bv 64 0xcf4a0));
(0xe8ea8, le8 (Z_to_bv 64 0xa4110));
(0xeeb00, le8 (Z_to_bv 64 1));
(0xefa70, le8 (Z_to_bv 64 0));
(0xef9d0, le4 (Z_to_bv 64 1));
(0xf1a1c, [Z_to_bv 8 1]);
(0x183d60, le8 (Z_to_bv 64 0xffffffffffffffff));
(0xe8e20, le8 (Z_to_bv 64 0xe80b0));
(0xe80b0, le8 (Z_to_bv 64 0xecd40));
(0xe8e28, le8 (Z_to_bv 64 0x0));
(0xea078, le8 (Z_to_bv 64 0xe3934));
(0xe8fc0, le8 (Z_to_bv 64 0xe4ac8) ++ le8 (Z_to_bv 64 0xe4ab8));
(0xe4ab8, le8 (Z_to_bv 64 0x9b3cc) ++ le8 (Z_to_bv 64 0x3e10c));
(0xe8188, le8 (Z_to_bv 64 0xcec58) ++ le8 (Z_to_bv 64 0x0));
(0xea020, le8 (Z_to_bv 64 0xea020));
(0xe8198, le8 (Z_to_bv 64 0x181c60) ++ le8 (Z_to_bv 64 0xea208) ++ le8 (Z_to_bv 64 0x183ce8) ++ le8 (Z_to_bv 64 0xef9b8) ++ le8 (Z_to_bv 64 0xf21b8) ++ le8 (Z_to_bv 64 0xf2ea8) ++ le8 (Z_to_bv 64 0xf2eb0) ++ le8 (Z_to_bv 64 0xf2ea0) ++ le8 (Z_to_bv 64 0xea1d0));
(0xe8ec0, le8 (Z_to_bv 64 0xed040) ++ le8 (Z_to_bv 64 0xeeb00));
(0xe8e58, le8 (Z_to_bv 64 0x9f854));
(0xe8e88, le8 (Z_to_bv 64 0x93a24));
(0x183de5, [Z_to_bv 8 1]);
(0xea050, le8 (Z_to_bv 64 0xddf20));
(0xe8e38, le8 (Z_to_bv 64 0x9dd50));
(0xe8e40, le8 (Z_to_bv 64 0x9e4a0));
(0xe8e48, le8 (Z_to_bv 64 0x9e8d8));
(0xe8e68, le8 (Z_to_bv 64 0x9f8e4));
(0xe8e98, le8 (Z_to_bv 64 0xa6060));
(0xe8ea0, le8 (Z_to_bv 64 0xa62ec));
(0xe8eb0, le8 (Z_to_bv 64 0xa53f4));
(0xe8e60, le8 (Z_to_bv 64 0x9f85c));
(0xe8e70, le8 (Z_to_bv 64 0xa0a78));
(0xe8e78, le8 (Z_to_bv 64 0xec940));
(0xe8050, le8 (Z_to_bv 64 0x1499c));
(0xe4ec8, le8 (Z_to_bv 64 0x9c508));
(0xe4ed0, le8 (Z_to_bv 64 0x9c600));
(0xe4ed8, le8 (Z_to_bv 64 0x9c60c));
(0xe4ee0, le8 (Z_to_bv 64 0x9c878));
(0xe4ee8, le8 (Z_to_bv 64 0x9cd50));
(0xe4ef0, le8 (Z_to_bv 64 0x9d200));
(0xe81d8, le8 (Z_to_bv 64 0xea1d0));
(0xe8e80, le8 (Z_to_bv 64 0x93680));
(0xe8e50, le8 (Z_to_bv 64 0x9edbc));
(0xe81b8, le8 (Z_to_bv 64 0xf21b8));
(0xf21b8, le8 (Z_to_bv 64 0x7fff8000));
(0xe8210, le8 (Z_to_bv 64 0xf21c0));
(0xf21c0, le4 (Z_to_bv 64 1)) ].

Definition DL_AR : dlayout :=
mkDL (RA.ala_malloc RA.a_alayout) (RA.ala_free RA.a_alayout) (RA.ala_calloc RA.a_alayout)
(RA.ala_tp RA.a_alayout) (RA.ala_gp RA.a_alayout) (RA.ala_img_lo RA.a_alayout) (RA.ala_img_hi RA.a_alayout)
0x0e4000 QFQR.A_ERRNO RA.a_client_data
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
Q61C.shadow_base asegs m ->
(QoSL.ro_cells asegs m 0x0e8210 [QMow.C8 (Z_to_bv 64 0x0f21c0)] /\ QoSL.ro_cells asegs m 0x0f21c0 [QMow.C4 (Z_to_bv 64 1)]) ->
Forall (fun c => bytes_at asegs m (fst c) (snd c)) rtc_AR.
Proof.
intros m RT SB UAR. unfold RA.rt_consts_at in RT. unfold Q61C.shadow_base in SB.
pose proof (proj2 (proj1 SB)) as SB0. pose proof (proj2 (proj2 SB)) as SB1. pose proof (proj2 (proj1 UAR)) as UAR0. pose proof (proj2 (proj2 UAR)) as UAR1. clear SB UAR.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
unfold rtc_AR. repeat (apply Forall_cons; [| ]); [.. | apply Forall_nil]; cbn [fst snd].
- rtc_pick 0x6457e0 0%nat 8%nat.
- rtc_pick 0x0e8f90 0%nat 8%nat.
- rtc_pick 0x645560 0%nat 8%nat.
- rtc_pick 0x0e8d28 0%nat 8%nat.
- rtc_pick 0x0f2e98 1%nat 1%nat.
- rtc_pick 0x0f2e98 0%nat 1%nat.
- rtc_pick 0x0ea1c8 8%nat 8%nat.
- rtc_pick 0x0ea1c8 0%nat 8%nat.
- rtc_pick 0x0e81a8 0%nat 8%nat.
- rtc_pick 0x0ea028 0%nat 8%nat.
- rtc_pick 0x183de3 0%nat 1%nat.
- rtc_pick 0x0e81c0 0%nat 8%nat.
- rtc_pick 0x0f2ea0 8%nat 8%nat.
- rtc_pick 0x0e81c0 8%nat 8%nat.
- rtc_pick 0x0f2ea0 16%nat 8%nat.
- rtc_pick 0x0e81c0 16%nat 8%nat.
- rtc_pick 0x0f2ea0 0%nat 8%nat.
- rtc_pick 0x0ea098 8%nat 8%nat.
- rtc_pick 0x0ea0a8 0%nat 8%nat.
- rtc_pick 0x183d3c 0%nat 1%nat.
- rtc_pick 0x183ddd 0%nat 1%nat.
- rtc_pick 0x183de2 0%nat 1%nat.
- rtc_pick 0x0e81a8 8%nat 8%nat.
- rtc_pick 0x0ef9d5 0%nat 1%nat.
- rtc_pick 0x0ea1a0 0%nat 8%nat.
- rtc_pick 0x0ea150 0%nat 8%nat.
- rtc_pick 0x0e8ea8 0%nat 8%nat.
- rtc_pick 0x0eeb00 0%nat 8%nat.
- rtc_pick 0x0efa70 0%nat 8%nat.
- rtc_pick 0x0ef9d0 0%nat 4%nat.
- rtc_pick 0x0f1a1c 0%nat 1%nat.
- rtc_pick 0x183d60 0%nat 8%nat.
- rtc_pick 0x0e8e20 0%nat 8%nat.
- rtc_pick 0x0e80b0 0%nat 8%nat.
- rtc_pick 0x0e8e20 8%nat 8%nat.
- rtc_pick 0x0ea078 0%nat 8%nat.
- apply bytes_at_app; split; [rtc_pick 0x0e8fc0 0%nat 8%nat| rtc_pick 0x0e8fc0 8%nat 8%nat].
- apply bytes_at_app; split; [rtc_pick 0x0e4ab8 0%nat 8%nat| rtc_pick 0x0e4ab8 8%nat 8%nat].
- apply bytes_at_app; split; [rtc_pick 0x0e8188 0%nat 8%nat| rtc_pick 0x0e8188 8%nat 8%nat].
- rtc_pick 0x0ea020 0%nat 8%nat.
- apply bytes_at_app; split; [rtc_pick 0x0e8198 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e81a0 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e81a8 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e81a8 8%nat 8%nat| apply bytes_at_app; split; [exact SB0| apply bytes_at_app; split; [rtc_pick 0x0e81c0 0%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e81c0 8%nat 8%nat| apply bytes_at_app; split; [rtc_pick 0x0e81c0 16%nat 8%nat| rtc_pick 0x0e81c0 24%nat 8%nat]]]]]]]].
- apply bytes_at_app; split; [rtc_pick 0x0e8ec0 0%nat 8%nat| rtc_pick 0x0e8ec0 8%nat 8%nat].
- rtc_pick 0x0e8e58 0%nat 8%nat.
- rtc_pick 0x0e8e88 0%nat 8%nat.
- rtc_pick 0x183de5 0%nat 1%nat.
- rtc_pick 0x0ea050 0%nat 8%nat.
- rtc_pick 0x0e8e38 0%nat 8%nat.
- rtc_pick 0x0e8e40 0%nat 8%nat.
- rtc_pick 0x0e8e48 0%nat 8%nat.
- rtc_pick 0x0e8e68 0%nat 8%nat.
- rtc_pick 0x0e8e98 0%nat 8%nat.
- rtc_pick 0x0e8ea0 0%nat 8%nat.
- rtc_pick 0x0e8eb0 0%nat 8%nat.
- rtc_pick 0x0e8e60 0%nat 8%nat.
- rtc_pick 0x0e8e70 0%nat 8%nat.
- rtc_pick 0x0e8e78 0%nat 8%nat.
- rtc_pick 0x0e8050 0%nat 8%nat.
- rtc_pick 0x0e4ec8 0%nat 8%nat.
- rtc_pick 0x0e4ed0 0%nat 8%nat.
- rtc_pick 0x0e4ed8 0%nat 8%nat.
- rtc_pick 0x0e4ee0 0%nat 8%nat.
- rtc_pick 0x0e4ee8 0%nat 8%nat.
- rtc_pick 0x0e4ef0 0%nat 8%nat.
- rtc_pick 0x0e81c0 24%nat 8%nat.
- rtc_pick 0x0e8e80 0%nat 8%nat.
- rtc_pick 0x0e8e50 0%nat 8%nat.
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
(AI : @RA.alloc_ifaceA (Band_RC guard) QZzg.asegs atn RA.a_alayout) :
donor_core Q6q3.alloc_ceiling QZzg.asegs atn (@DL_AR (Band_RC guard)) :=
@DCo_AR (Band_RC guard) atn AI.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5bV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QClx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Definition DCo_jo {RC__ : Q6q3.RunConsts} (guard : word) (LV : Qsn5.lvp) :
donor_core Q6q3.alloc_ceiling QZzg.asegs
(QBrp.at_nodeA LV QZzg.asegs) (@DL_AR (Band_RC guard)) :=
DCo_AR_rc guard _ (@Q5bV.Mq0.a_alloc_iface (Band_RC guard) LV).

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma DFs_jo {RC__ : Q6q3.RunConsts} (guard : word) (LV : Qsn5.lvp) :
donor_fs Q6q3.alloc_ceiling QZzg.asegs
(QBrp.at_nodeA LV QZzg.asegs) (@DL_AR (Band_RC guard)) (DCo_jo guard LV)
(fun k => if k =? 0 then 0x4a9bc else if k =? 1 then 0x4ab30 else if k =? 2 then 0x4acc0 else if k =? 3 then 0x4ae5c else 0) 4096.
Proof.
pose (AIj := @Q5bV.Mq0.a_alloc_iface (Band_RC guard) LV).
pose (aC := @Q5bV.Mq0.aC (Band_RC guard)).
constructor; unfold DCo_jo, DCo_AR_rc, DCo_AR, run_AR; cbn [dc_run].
- intros s LB FS RE m H. pose proof (RA.ai_entry_facts _ _ _ AIj s LB FS (toRA RE) m H) as (_ & _ & E1 & E2 & _). split; [exact E1| exact E2].
- intros s LB FS RE m f. exact (RA.ai_fframe_range _ _ _ AIj s LB FS (toRA RE) m f).
- intros s LB FS RE m c0 f. exact (@QpY2.Mqa.ARUN_fframe_align (Band_RC guard) aC (@Q5bV.Mq0.aC_RF (Band_RC guard)) c0 s LB FS (toRA RE) m f).
- intros s LB FS RE m f1 f2. exact (RA.ai_fframes_disjoint _ _ _ AIj s LB FS (toRA RE) m f1 f2).
- intros s LB FS RE m f b. exact (RA.ai_fframe_block_disjoint _ _ _ AIj s LB FS (toRA RE) m f b).
- intros s LB FS RE m b. exact (@QpY2.Mqa.ARUN_fs_block_disjoint (Band_RC guard) aC s LB FS (toRA RE) m b).
- intros s LB FS RE m. exact (RA.ai_fframes_nodup _ _ _ AIj s LB FS (toRA RE) m).
- intros c0 s LB FS RE m f flag. exact (RA.ai_fframe_release0 _ _ _ AIj c0 s LB FS (toRA RE) m f flag).
- intros c0 s LB FS RE m f. exact (RA.ai_fframe_flag0 _ _ _ AIj c0 s LB FS (toRA RE) m f).
- intros k Hk. assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia. unfold astack_mallocA_stmt. destruct Ek as [-> | [-> | [-> | ->]]]; cbn [Z.eqb]; intros.
+ eapply (RA.ai_stack_malloc_0 _ _ _ AIj) with (RE := toRA RE); eassumption.
+ eapply (RA.ai_stack_malloc_1 _ _ _ AIj) with (RE := toRA RE); eassumption.
+ eapply (RA.ai_stack_malloc_2 _ _ _ AIj) with (RE := toRA RE); eassumption.
+ eapply (@QClx.ai_stack_malloc_3 (Band_RC guard)) with (RE := toRA RE); eassumption.
- intros s LB FS RE m p A n. exact (@QNQk.Mq7.ARUN_blk_slack (Band_RC guard) aC (@Q5bV.Mq0.aC_RC (Band_RC guard)) s LB FS (toRA RE) m p A n).
- intros s LB FS RE m p n. exact (RA.ai_nbhd _ _ _ AIj s LB FS (toRA RE) m p n).
Qed.
