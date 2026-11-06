(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QUZl Qfya Qatc Q3o5 Q9kF QnDM_c1 QGeV Q8zf QEoy Q9O6 QnPO QXEH QCwx QkLq Qsn5 QJFf QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QvSK QvQl Qn7S QlHe Qb5q QMhO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QvSK.Mq0 QvQl Qn7S QlHe.Mq0 Qb5q.Mq1 QMhO.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma PIECES_A : forall ch, HSCLASS_S true ch -> pieces_check_A (kn_view ch) = true.
Proof. intros ch [-> | ->]; [exact PIECES_HS2sA_1_ok | exact PIECES_HS2sA_2_ok]. Qed.
Lemma PIECES_B : forall ch, HSCLASS_S false ch -> pieces_check_B (kn_view ch) = true.
Proof. intros ch [-> | ->]; [exact PIECES_HS2sB_3_ok | exact PIECES_HS2sB_4_ok]. Qed.

Lemma STATICS_w : img_w_b JOB6SEGS QXEH.RMLOCK 4 = true /\ img_w_b JOB6SEGS QXEH.RNEED_LOCKS 1 = true /\ img_w_b JOB6SEGS QXEH.RPAGE_SIZE 8 = true
/\ img_w_b JOB6SEGS QXEH.RGOT_SSP 8 = true /\ img_w_b JOB6SEGS QXEH.RSSP_GUARD 8 = true /\ img_w_b JOB6SEGS QXEH.RVMLOCK 4 = true
/\ img_w_b JOB6SEGS QXEH.RCTX 928 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma bytes_eq_u : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|a r IH]; intros [|b s] H; try discriminate; [reflexivity|]. cbn [map] in H. injection H as H1 H2.
f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac bytes_vm := apply bytes_eq_u; vm_compute; reflexivity.

Definition ACT_O : list QUZl.optr := [None; None; Some (0%N, 4120); None; None; None; None; None; None; None; None; None; None; None; None; Some (0%N, 4160); None; None; None; Some (0%N, 4200); None; None; None; Some (0%N, 4240); None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None].
Definition USE_Aw : list word := [QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 10; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0].

Lemma l2m_none : forall {K A} `{Countable K} (l : list (K * A)) (k : K), ~ In k (map fst l) -> (list_to_map l : gmap K A) !! k = None.
Proof. intros K A ? ? l k Hn. apply not_elem_of_list_to_map_1. rewrite list_elem_of_In. exact Hn. Qed.
Lemma l2m_some : forall {K A} `{Countable K} (l : list (K * A)) (k : K) (v : A), (list_to_map l : gmap K A) !! k = Some v -> In (k, v) l.
Proof. intros K A ? ? l k v Hl. apply list_elem_of_In. apply elem_of_list_to_map_2. exact Hl. Qed.

Lemma meta0_bytes : forall st, QbVh.cells_bytes (QnDM_c1.Mq0.meta_cells st QUZl.meta0) = repeat (Z_to_bv 8 0) 40.
Proof. intros st. unfold QnDM_c1.Mq0.meta_cells, QnDM_c1.Mq0.pw. cbn [QUZl.meta0 QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed QUZl.oconc]. bytes_vm. Qed.

Definition mng_shadow_ok (sh : QUZl.shadow) (cs : list scell) (n : nat) : bool :=
forallb (fun i => match QUZl.cell_read sh (Z.of_nat i) with
| QUZl.Known v => match sc_lit_byte cs i with Some v' => (v' =? v) && (0 <=? v) && (v <? 256) | None => false end
| QUZl.Unknown _ => true
end) (seq 0 n).
Lemma mng_shadow_ok_sound : forall sh cs n o v, mng_shadow_ok sh cs n = true -> 0 <= o < Z.of_nat n -> QUZl.cell_read sh o = QUZl.Known v ->
sc_lit_byte cs (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof.
intros sh cs n o v OK Ho Hc. unfold mng_shadow_ok in OK. rewrite forallb_forall in OK.
specialize (OK (Z.to_nat o) ltac:(apply in_seq; lia)). cbv beta in OK. rewrite Z2Nat.id in OK by lia. rewrite Hc in OK.
destruct (sc_lit_byte cs (Z.to_nat o)) as [v'|]; [|discriminate].
apply andb_prop in OK as [OK V2]. apply andb_prop in OK as [V0 V1]. apply Z.eqb_eq in V0. subst v'. apply Z.leb_le in V1. apply Z.ltb_lt in V2.
split; [reflexivity | lia].
Qed.

Lemma hull_apart_free : forall b n, b + n <= 0x10000 \/ 0x647000 <= b -> QUZl.ranges_free QXEH.ref_reserved b n = true.
Proof.
intros b n H. unfold QUZl.ranges_free, QXEH.ref_reserved. cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; apply orb_true_iff; destruct H; [left|right|left|right|left|right|left|right]; apply Z.leb_le; lia.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7S. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qxua.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qxua.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb5q.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8BV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8BV.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma PIECES_A : forall ch, HSCLASS_S true ch -> pieces_check_A (kn_view ch) = true.
Proof. intros ch [-> | ->]; [exact PIECES_HS2sA_1_ok | exact PIECES_HS2sA_2_ok]. Qed.
Lemma PIECES_B : forall ch, HSCLASS_S false ch -> pieces_check_B (kn_view ch) = true.
Proof. intros ch [-> | ->]; [exact PIECES_HS2sB_3_ok | exact PIECES_HS2sB_4_ok]. Qed.

Lemma STATICS_w : img_w_b JO6SEGS QW7x.Mq0.RMLOCK 4 = true /\ img_w_b JO6SEGS QW7x.Mq0.RNEED_LOCKS 1 = true /\ img_w_b JO6SEGS QW7x.Mq0.RPAGE_SIZE 8 = true
/\ img_w_b JO6SEGS QW7x.Mq0.RGOT_SSP 8 = true /\ img_w_b JO6SEGS QW7x.Mq0.RSSP_GUARD 8 = true /\ img_w_b JO6SEGS QW7x.Mq0.RVMLOCK 4 = true
/\ img_w_b JO6SEGS QW7x.Mq0.RCTX 928 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma bytes_eq_u : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|a r IH]; intros [|b s] H; try discriminate; [reflexivity|]. cbn [map] in H. injection H as H1 H2.
f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac bytes_vm := apply bytes_eq_u; vm_compute; reflexivity.

Definition ACT_O : list QUZl.optr := [None; None; Some (0%N, 4120); None; None; None; None; None; None; None; None; None; None; None; None; Some (0%N, 4160); None; None; None; Some (0%N, 4200); None; None; None; Some (0%N, 4240); None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None; None].
Definition USE_Aw : list word := [QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 10; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 2; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0; QnDM_c1.Mq0.wz 0].

Lemma l2m_none : forall {K A} `{Countable K} (l : list (K * A)) (k : K), ~ In k (map fst l) -> (list_to_map l : gmap K A) !! k = None.
Proof. intros K A ? ? l k Hn. apply not_elem_of_list_to_map_1. rewrite list_elem_of_In. exact Hn. Qed.
Lemma l2m_some : forall {K A} `{Countable K} (l : list (K * A)) (k : K) (v : A), (list_to_map l : gmap K A) !! k = Some v -> In (k, v) l.
Proof. intros K A ? ? l k v Hl. apply list_elem_of_In. apply elem_of_list_to_map_2. exact Hl. Qed.

Lemma meta0_bytes : forall st, QbVh.cells_bytes (QnDM_c1.Mq0.meta_cells st QUZl.meta0) = repeat (Z_to_bv 8 0) 40.
Proof. intros st. unfold QnDM_c1.Mq0.meta_cells, QnDM_c1.Mq0.pw. cbn [QUZl.meta0 QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed QUZl.oconc]. bytes_vm. Qed.

Definition mng_shadow_ok (sh : QUZl.shadow) (cs : list scell) (n : nat) : bool :=
forallb (fun i => match QUZl.cell_read sh (Z.of_nat i) with
| QUZl.Known v => match sc_lit_byte cs i with Some v' => (v' =? v) && (0 <=? v) && (v <? 256) | None => false end
| QUZl.Unknown _ => true
end) (seq 0 n).
Lemma mng_shadow_ok_sound : forall sh cs n o v, mng_shadow_ok sh cs n = true -> 0 <= o < Z.of_nat n -> QUZl.cell_read sh o = QUZl.Known v ->
sc_lit_byte cs (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof.
intros sh cs n o v OK Ho Hc. unfold mng_shadow_ok in OK. rewrite forallb_forall in OK.
specialize (OK (Z.to_nat o) ltac:(apply in_seq; lia)). cbv beta in OK. rewrite Z2Nat.id in OK by lia. rewrite Hc in OK.
destruct (sc_lit_byte cs (Z.to_nat o)) as [v'|]; [|discriminate].
apply andb_prop in OK as [OK V2]. apply andb_prop in OK as [V0 V1]. apply Z.eqb_eq in V0. subst v'. apply Z.leb_le in V1. apply Z.ltb_lt in V2.
split; [reflexivity | lia].
Qed.

Lemma hull_apart_free : forall b n, b + n <= 0x10000 \/ 0x645000 <= b -> QUZl.ranges_free QW7x.Mq0.ref_reserved b n = true.
Proof.
intros b n H. unfold QUZl.ranges_free, QW7x.Mq0.ref_reserved. cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; apply orb_true_iff; destruct H; [left|right|left|right|left|right|left|right]; apply Z.leb_le; lia.
Qed.
