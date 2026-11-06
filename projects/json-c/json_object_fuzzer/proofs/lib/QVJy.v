(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaJW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaJW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaJW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaJW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq4.
Import ListNotations.
Open Scope Z_scope.

Section TcpsFBind.
Variable node : Type.
Variable segs : list Segment.
Variable LV : lvp.
Variable at_node : node -> machine_state -> Prop.
Variable nstep_raw : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit_raw : node -> Model -> word -> Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable is_spin : node -> bool.
Variable F : word -> bool.
Notation tcpsx := (tcpsF node LV at_node nstep_raw nexit_raw nsafe is_spin F).

Lemma tcpsF_bind {A B} (t : itree node A) (f : A -> itree node B) : forall mo,
tcpsx t mo -> (forall a mo', tpath (nstepA LV nstep_raw) t mo [] a mo' -> tcpsx (f a) mo') -> tcpsx (Qc6I.bind node t f) mo.
Proof.
induction t as [r|n k IH]; intros mo Ht Hf.
- cbn. apply Hf. cbn. auto.
- cbn in Ht |- *. destruct Ht as (Hsp & Hns & Hmono & Hnx & Hk). repeat split; auto.
+ destruct (Hk rsp mo' evs H) as [He _]. exact He.
+ destruct (Hk rsp mo' evs H) as (_ & Ho & _). exact (proj1 (Ho v)).
+ destruct (Hk rsp mo' evs H) as (_ & Ho & _). exact (proj2 (Ho v)).
+ destruct (Hk rsp mo' evs H) as (-> & _ & Hc). apply IH; [exact Hc|].
intros a mo2 Hp. apply Hf. cbn. exists rsp, mo', [], []. auto.
Qed.
End TcpsFBind.

Section AllocCpsF.
Variable segs : list Segment.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.
Variable FR : list (Z * Z).
Hypothesis HFR : Forall (fr_ok L PERM) FR.

Notation KIx := (KI LV BUDGET PERM TOT0 N0).
Notation F := (Fof LV FR).
Notation tcpsFA := (tcpsF node LV (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) is_spinA F).

Lemma at_nodeA_unhide : forall e ms, at_nodeA LV segs (node_of e) (restrict F ms) -> at_nodeA LV segs (node_of e) ms.
Proof.
intros [len avoid|addr len|addr len|addr len] ms H; cbn [node_of at_nodeA] in *; try exact H.
destruct H as [H1 H2]. split; [exact H1|]. intros x Hx. specialize (H2 x Hx). cbn [restrict ms_mem] in H2. unfold mrestrict in H2.
destruct (F x); [congruence| exact H2].
Qed.

Theorem membedA_tcpsF {R} (t : T R) (P : R -> Prop) (RG : ghost -> R -> Prop) (g : ghost) (s : PStateA) (mo0 : Model) :
tall (aokG) (rokS P) t -> teva L BUDGET (aokG) RG g t -> KIx g mo0 ->
tcpsFA (membedA t s) mo0.
Proof.
revert g mo0. induction t as [[r| |w]|e k IH]; intros g mo0 Ht Hg K.
- cbn. exact I.
- destruct Ht.
- destruct Ht.
- cbn [membedA]. rewrite ev_stepA_eq. destruct Hg as [Ge Gk].
change (forall a, aokG e a -> tall aokG (rokS P) (k a)) in Ht.
unfold Qpj5.Mq1.mbind, Qpj5.Mq1.msys. cbn -[node_of nstep_raw nsafeA is_spinA nexit_raw dec_of membedA at_nodeA restrict].
split; [apply node_of_not_spin|]. split; [exact (ev_safe L LV BUDGET PERM TOT0 N0 LL g mo0 e K Ge)|].
split; [apply at_nodeA_unhide|].
split; [intros mo1 code mo' _; apply node_of_no_exit|].
intros rsp mo' evs (mo1 & Hd & Hst).
split; [exact (node_of_silent LV e mo1 rsp mo' evs Hst)|].
pose proof (KI_drift LV BUDGET PERM TOT0 N0 g mo0 mo1 Hd K) as K1.
split; [exact (ev_rsp_off L LV BUDGET PERM TOT0 N0 LL g mo1 e rsp mo' evs FR K1 Ge HFR Hst)|].
destruct (ev_step L LV BUDGET PERM TOT0 N0 LL g mo1 e rsp mo' evs K1 Ge Hst) as (a & Hdec & Ha & K').
rewrite Hdec. cbn.
destruct (ev_step_grant LV e mo1 rsp mo' evs a Hst Hdec) as [b Hb].
assert (HaG : aokG e a) by (split; [exact Ha| eauto]).
exact (IH a (gstep g e a) mo' (Ht a HaG) (Gk a HaG) K').
Qed.

Theorem raw_malloc_A_tcpsF X n g (ps : PStateA) (mo0 : Model) :
0 <= n -> n <= kMaxReq -> too_big n = false ->
ainv X (ps_a ps) -> GS (ps_a ps) g -> malloc_room X (ps_a ps) n ->
CAPS + as_spent (ps_a ps) + mcost n <= BUDGET -> zlen (as_reg (ps_a ps)) + 1 <= kMaxCnt -> KIx g mo0 ->
tcpsFA (raw_malloc_A L n ps) mo0.
Proof.
intros Hn H39 Htb AI G [R1 R2] HB Hcnt K. unfold raw_malloc_A, Qpj5.Mq1.mbind, Qpj5.Mq1.mget. cbn [Qc6I.ebind Qc6I.bind].
apply tcpsF_bind.
- eapply membedA_tcpsF.
+ apply tall_rokS; [apply (asan_malloc_inv L X (ps_a ps) n AI Hn Htb R1 R2)| apply asan_malloc_ns].
+ apply teva_aokG. apply (asan_malloc_teva L BUDGET aok0 (llo_lay _ _ _ _ _ _ LL) (aok_anon astate0) X g (ps_a ps) n AI Hn H39 R1 G HB Hcnt).
+ exact K.
- intros [|[[r a'] s1]] mo' _; cbn; exact I.
Qed.

Theorem raw_free_A_tcpsF X X' p g (ps : PStateA) (mo0 : Model) :
ainv X (ps_a ps) -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 (ps_a ps) kBatchClass + 17) <= kFreeArrayOffset ->
GS (ps_a ps) g -> CAPS + as_spent (ps_a ps) <= BUDGET -> KIx g mo0 ->
tcpsFA (raw_free_A L p ps) mo0.
Proof.
intros AI HP Hroom G HB K. unfold raw_free_A, Qpj5.Mq1.mbind, Qpj5.Mq1.mget. cbn [Qc6I.ebind Qc6I.bind].
apply tcpsF_bind.
- eapply membedA_tcpsF.
+ apply tall_rokS; [apply (asan_free_inv L X X' p (ps_a ps) AI HP Hroom)| apply asan_free_ns].
+ apply teva_aokG. apply (asan_free_teva L BUDGET aok0 (llo_lay _ _ _ _ _ _ LL) X X' p g (ps_a ps) AI HP Hroom G HB).
+ exact K.
- intros [|[a' s1]] mo' _; cbn; exact I.
Qed.

End AllocCpsF.

Section RulesF.
Variable segs : list Segment.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Variable FR : list (Z * Z).
Hypothesis HFR : Forall (fr_ok L PERM) FR.
Hypothesis F_off : H_off_segments segs (Fof LV FR).

End RulesF.
