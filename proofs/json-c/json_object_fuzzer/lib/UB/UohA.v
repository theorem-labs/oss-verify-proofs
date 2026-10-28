(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rclient_write_ok2 (LB : list block) (iv : Z * Z) : Prop :=
rclient_write_ok LB iv \/ (RLIBC + 0x68 <= fst iv /\ snd iv <= RMLOCK).

#[using="Type"] Lemma RHEAP_frame2 : forall s LB m m' W,
RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok2 LB) W -> RHEAP s LB m'.
Proof.
intros s LB m m' W (st & LB0 & HP & Hst & MR & HI) MU WM FW. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
split; [|exact HI].
destruct HI as [_ AR]. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
eapply (rmrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (rrepfoot_where st m a MR RF) as [AC AW].
destruct CW as [[CW|[CW|(b & Hb & B1 & B2)]]|CW]; cbn [fst snd] in *.
- unfold alloc_ceiling in *. lia.
- unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, alloc_ceiling in *. lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
+ unfold RCTX in R1. lia.
+ unfold RMLOCK in R2. lia.
+ unfold RNEED_LOCKS in R3. lia.
+ unfold RPAGE_SIZE in R4'. lia.
+ destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
+ unfold RGOT_SSP in R8. lia.
+ unfold RSSP_GUARD in R9. lia.
-
unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, alloc_ceiling in *. lia.
Qed.

End RC__1.
