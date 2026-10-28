(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq Lib.GwApply Qfw3 Q9A7 QlEo Q5Rg UEQM Qy5Y UKNz Uv2Y UXT6 UotY UGNu QZAi QUZl Qfya QGeV QRjH Q9ox QBxa QSpR QsRG QuJV UFeQ Um90 UJvR QHnV Qsw7 QCcH QEpW QbVh QZDE QeZD QqWy UmAj Uc9I U4FC Uqqm UDH9 U5Hp QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Qy5Y.Mq4.
Import UKNz Uv2Y UXT6 UotY UGNu.
Import QZAi.Mq1 QUZl Qfya QGeV.
Import QRjH Q9ox.Mq2 QBxa.Mq5.

Import QHnV Qsw7.

Import QEpW QWxq QlEo QbVh QZDE.
Import QeZD QqWy.
Import UmAj Uc9I.
Import U4FC Uqqm UDH9 U5Hp.
Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition FREE_SYM : Z := 0x520b4.
Definition MAIN_FREE_RET : Z := 0x20d80.

Section Tail.
Context {AMB : Amb}.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Notation B := usp0.
Notation LO := (usp0 - 8388608).
Notation SP := (usp0 - 128).

Definition STDOUT (m : mem) (md : Model) (pending : list byte) : Prop :=
(pending = [] /\ exists wp1 rp1 : word, UFeQ.Mq0.file_clean m 0x66e28 wp1 rp1)
\/ (exists (wp : Z) (rp1 can : word),
Um90.stdout_pending m 0x98350 wp (Z_to_bv 64 0x98350) (Z_to_bv 64 1024) rp1 can pending
/\ wp <= 0x98750
/\ fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))).

Definition STDERR (m : mem) : Prop :=
(forall a, 0x66d38 <= a < 0x66e20 -> m (wa a) = None)
\/ (exists wp rp : word, UFeQ.Mq0.file_clean m 0x66d38 wp rp).

Record TINV (status buf cap : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate) (pending : list byte) : Prop := MKT {
t_dfx   : DFX usp0 pp tid path m;
t_heap  : HEAPc B A ((buf, cap) :: LK) m md;
t_errno : exists errv, rw_cells rsegs m RERRNO [C4 errv];
t_fs    : m_fs md = fs;
t_out   : STDOUT m md pending;
t_err   : STDERR m;
t_status: 0 <= status < 256 }.

Definition tail_stmt : Prop :=
forall (status buf cap : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate) (pending : list byte)
(gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TINV status buf cap LK m md A pending ->
tp = Z_to_bv 64 0x77c00 ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 MAIN_FREE_RET) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 status) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FREE_SYM) fc None m (seg_rom rsegs)) md)
(t_emit (W 1 pending) (t_exit (exit_code status) fs)).

#[using="Type"] Lemma rdn_agree : forall segs (m m' : mem) a n,
0 <= a -> a + Z.of_nat n <= 0x99000 ->
(forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) ->
QsRG.Mq0.rdn segs m' (Z_to_bv 64 a) n = QsRG.Mq0.rdn segs m (Z_to_bv 64 a) n.
Proof.
intros segs m m' a n H0 H1 EQ. apply QsRG.Mq0.rdn_ext; rewrite unsigned_lit by lia; [lia|].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply EQ. lia.
Qed.

Definition img_agree (m m' : mem) : Prop :=
forall x, 0x62000 <= x < 0x99000 -> ~ (RCTX <= x < RCTX + 928) -> ~ (RERRNO <= x < RERRNO + 4) -> m' (wa x) = m (wa x).

#[using="Type"] Lemma img_agree_of_pres : forall LB0 SP (m m' : mem), rheap_pres LB0 SP m m' -> img_agree m m'.
Proof.
intros LB0 SP m m' HP x Hx N1 N2. refine (proj1 (HP x ltac:(lia) _)). right; left. unfold ralloc_static. split; [lia|]. intros [X|X]; tauto.
Qed.

Ltac rdn_carry EQ H := lazymatch type of EQ with img_agree ?m ?m' =>
erewrite (rdn_agree _ m m'); [exact H| lia| lia| intros; apply EQ; unfold RCTX, RERRNO, RATP; lia] end.

Ltac in_list := cbn; repeat (first [left; reflexivity | right]).

#[using="Type"] Lemma map_unsigned_inj : forall n (l1 l2 : list (bv n)), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
#[using="Type"] Lemma rdn_val_eq : forall (l : option (list byte)) bs r, l = Some bs -> map bv_unsigned bs = map bv_unsigned r -> l = Some r.
Proof. intros l bs r -> H. f_equal. apply map_unsigned_inj. exact H. Qed.
Ltac rdn_img_solve := lazymatch goal with |- ?l = Some ?r =>
let v := eval vm_compute in l in lazymatch v with Some ?bs =>
apply (rdn_val_eq l bs r); [vm_compute; reflexivity | vm_compute; reflexivity] end end.

#[using="Type"] Lemma file_clean_pristine : forall (m : mem) (f : Z), (f = 0x66d38 \/ f = 0x66e28) ->
(forall a, f <= a < f + 232 -> m (wa a) = None) -> UFeQ.Mq0.file_clean m f (wz 0) (wz 0).
Proof.
intros m f Hf NONE. unfold UFeQ.Mq0.file_clean.
assert (R : forall segs a n, f <= a -> a + Z.of_nat n <= f + 232 -> QsRG.Mq0.rdn segs m (Z_to_bv 64 a) n = QsRG.Mq0.rdn segs (fun _ => None) (Z_to_bv 64 a) n).
{ intros segs a n H1 H2. apply (QBxa.Mq7.rdn_img segs m a n f (f + 232)); try lia. intros i Hi. apply (NONE i Hi). }
rewrite !R by lia. destruct Hf as [-> | ->]; repeat split; rdn_img_solve.
Qed.

#[using="Type"] Lemma stdout_pending_agree : forall (m m' : mem) wp rp1 can pending,
img_agree m m' -> wp <= 0x98750 ->
Um90.stdout_pending m 0x98350 wp (Z_to_bv 64 0x98350) (Z_to_bv 64 1024) rp1 can pending ->
Um90.stdout_pending m' 0x98350 wp (Z_to_bv 64 0x98350) (Z_to_bv 64 1024) rp1 can pending.
Proof.
intros m m' wp rp1 can pending EQ WP SP. destruct SP as [L1 L2 L3 L4 L5 L6 L7 L8 L9 RNG LEN MAX BY [SS1 SS2]].
constructor; try assumption.
all: try (rdn_carry EQ L1 || rdn_carry EQ L2 || rdn_carry EQ L3 || rdn_carry EQ L4 || rdn_carry EQ L5 || rdn_carry EQ L6 || rdn_carry EQ L7 || rdn_carry EQ L8 || rdn_carry EQ L9).
- rdn_carry EQ BY.
- split; [rdn_carry EQ SS1| rdn_carry EQ SS2].
Qed.

#[using="Type"] Lemma STDOUT_agree : forall m m' md md' pending, img_agree m m' -> m_fds md' = m_fds md -> STDOUT m md pending -> STDOUT m' md' pending.
Proof.
intros m m' md md' pending EQ FDS [[-> (wp1 & rp1 & C1 & C2 & C3 & C4 & C5)]|(wp & rp1 & can & SP & WP & FD)].
- left. split; [reflexivity|]. exists wp1, rp1. unfold UFeQ.Mq0.file_clean. repeat split; [rdn_carry EQ C1| rdn_carry EQ C2| rdn_carry EQ C3| rdn_carry EQ C4| rdn_carry EQ C5].
- right. exists wp, rp1, can. split; [exact (stdout_pending_agree m m' wp rp1 can pending EQ WP SP)|]. split; [exact WP|]. rewrite FDS. exact FD.
Qed.

#[using="Type"] Lemma STDERR_agree : forall m m', img_agree m m' -> STDERR m -> STDERR m'.
Proof.
intros m m' EQ [NONE|(wp & rp & C1 & C2 & C3 & C4 & C5)].
- left. intros a Ha. rewrite EQ; [apply NONE; lia| lia| unfold RCTX; lia| unfold RERRNO, RATP; lia].
- right. exists wp, rp. unfold UFeQ.Mq0.file_clean. repeat split; [rdn_carry EQ C1| rdn_carry EQ C2| rdn_carry EQ C3| rdn_carry EQ C4| rdn_carry EQ C5].
Qed.

#[using="Type"] Theorem tail_ok : tail_stmt.
Proof.
unfold tail_stmt. intros until fc. intros TI Htp. subst tp.
destruct TI as [D HP (errv & ERR) Hfs OUT ERR2 Hst].
pose proof (x_sp _ _ _ _ _ D) as SPB. pose proof (x_ceil _ _ _ _ _ D) as CEIL.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
destruct (stk_split rsegs m LO SP usp0 (x_stk _ _ _ _ _ D) ltac:(lia)) as [ST1 _].
eapply (heapc_free B RFREE_SYM (rfree_stmt_at_sym rfree_spec_proof)
(Z_to_bv 64 MAIN_FREE_RET) (Z_to_bv 64 SP) gp (Z_to_bv 64 0x77c00)
t0 t1 t2 (Z_to_bv 64 status) s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m md _ A ((buf, cap) :: LK) buf cap LO errv HP ltac:(left; reflexivity));
[rewrite unsigned_lit by lia; exact ST1| unfold alloc_ceiling; lia| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite unsigned_lit by lia; lia| unfold RATP, RERRNO in *; exact ERR| reflexivity| reflexivity|].
intros ms' m' md' A' r RS VM ST' (LBx & PLBx & PRES) ERR' HP'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DFX usp0 pp tid path m') by (eapply (DFX_alloc usp0 pp tid path m m' LBx SP LO D PRES MI' ST' eq_refl ltac:(lia))).
pose proof (img_agree_of_pres _ _ _ _ PRES) as IA.
pose proof (STDOUT_agree m m' md md' pending IA (vm_only_fds md md' VM) OUT) as OUT'.
pose proof (STDERR_agree m m' IA ERR2) as ERR2'.
clear IA OUT ERR2 PRES ST1 ERR MI MOK HP D.
pose proof (x_frame _ _ _ _ _ D') as FR. unfold main_frame in FR.
replace (usp0 - 120) with (SP + 8) in FR by lia.
unfold MAIN_FREE_RET. reenter MOK'.
do 12 step.
apply evt_RZ_done.
replace (ret_pc (Z_to_bv 64 0x508ac)) with (Z_to_bv 64 0x508ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
replace (exit_code status) with (bv_and (Z_to_bv 64 status) (Z_to_bv 64 255)).
2:{ unfold exit_code. apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
rewrite <- Hfs, <- (vm_only_fs md md' VM).
apply UJvR.ref_main_ret_MS.

pose proof D' as [SPB' STK' FRM' [TID1 TID2] SELF' PRS' STG' PTH' PTH8' LOC' CEIL' ATX'].
assert (EC2 : exists wp2 rp2, UFeQ.Mq0.file_clean m' 0x66d38 wp2 rp2).
{ destruct ERR2' as [NONE|(wp & rp & FC)]; [| exists wp, rp; exact FC]. exists (wz 0), (wz 0). apply file_clean_pristine; [left; reflexivity| exact NONE]. }
destruct EC2 as (wp2 & rp2 & EC2).
exists (Z_to_bv 64 (SP + 80)), (Z_to_bv 64 0x77c00), tid, wp2, rp2.
split; [| split; [exact (proj1 MOK')| split; [exact (proj2 MOK')|]]].
- constructor; try reflexivity; rewrite ?unsigned_lit by lia; try lia; try exact EC2.
+
apply (QuJV.Mq0.wr_at_store_ok rsegs m' (SP + 80 - 144) 144).
destruct STK' as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S3 (SP + 80 - 144 + i) ltac:(lia))).
+  replace (490496 - 168) with 0x77b58 by reflexivity. exact (QuJV.Mq0.bytes_at_rdn0 rsegs m' 0x77b58 _ TID1).
+ rewrite (prisx_rdn m' 0x97d70 0x97e70 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x659d8 0x66a30 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x659d8 0x66a30 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x10000 0x658d8 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x66f31 0x66f79 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x10000 0x658d8 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+ rewrite (prisx_rdn m' 0x10000 0x658d8 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+  unfold UFeQ.Mq0.stdio_globals.
split. { pose proof (heapc_need_locks B _ _ _ _ HP') as NL. unfold RLIBC in NL. exact (QuJV.Mq0.bytes_at_rdn0 rsegs m' _ _ NL). }
rewrite (prisx_rdn m' 0x98320 0x98350 0x98338 _ PRS' ltac:(in_list)) by lia.
rewrite (prisx_rdn m' 0x98320 0x98350 0x98328 _ PRS' ltac:(in_list)) by lia.
rewrite (prisx_rdn m' 0x66f10 0x66f20 _ _ PRS' ltac:(in_list)) by lia.
rewrite (prisx_rdn m' 0x66e20 0x66e28 _ _ PRS' ltac:(in_list)) by lia.
repeat split; rdn_img_solve.
+  rewrite (prisx_rdn m' 0x659d8 0x66a30 _ _ PRS' ltac:(in_list)) by lia. rdn_img_solve.
+  exact ATX'.
- destruct OUT' as [[-> FC]|(wp & rp1 & can & SP & WP & FD)].
+ left. split; [reflexivity| exact FC].
+ right. exists 0x98350, wp, (Z_to_bv 64 0x98350), (Z_to_bv 64 1024), rp1, can. split; [exact SP| exact FD].
Qed.
End Tail.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UotY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UotY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGNu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGNu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaOl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaOl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4FC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U56U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U56U.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition LOOP : Z := 0x20c0c.

Lemma vm_only_fds : forall md md', vm_only md md' -> m_fds md' = m_fds md.
Proof. intros md md' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
Lemma vm_only_fs : forall md md', vm_only md md' -> m_fs md' = m_fs md.
Proof. intros md md' (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.

Lemma rw_cells_CB0 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[WF BA] WR]. split; [split; [cbn; split; [reflexivity| exact WF]| cbn; exact BA]| cbn; exact WR]. Qed.

Lemma pres_block : forall LB LB0 SP m m' a n cs,
Permutation LB (map zblk LB0) -> In (a, n) LB -> rheap_pres LB0 SP m m' ->
rw_cells rsegs m a cs -> Z.of_nat (cells_size cs) <= n -> rw_cells rsegs m' a cs.
Proof.
intros LB LB0 SP m m' a n cs PLB HIN HP RW SZ.
pose proof (Permutation_in _ PLB HIN) as H. apply in_map_iff in H as (b & Eb & Hb).
eapply rheap_pres_rw_cells; [exact HP| exact RW|]. right; right. exists b. split; [exact Hb|].
unfold zblk in Eb. injection Eb as E1 E2. unfold blk_addr, blk_size in *. rewrite E1, E2. lia.
Qed.

Lemma rw_cells_head_bytes : forall m a n bs cs, rw_cells rsegs m a (CB n bs :: cs) -> bytes_at rsegs m a bs /\ length bs = n.
Proof.
intros m a n bs cs [[[WF1 WF2] BA] _]. cbn in WF1. cbn [cells_bytes cbytes] in BA. apply bytes_at_app in BA as [BA _]. exact (conj BA WF1).
Qed.

Lemma rw_cells_CB_split : forall m a n1 n2 junk,
rw_cells rsegs m a [CB (n1 + n2) junk] ->
rw_cells rsegs m a [CB n1 (firstn n1 junk); CB n2 (skipn n1 junk)].
Proof.
intros m a n1 n2 junk RW. pose proof RW as [[[WF _] _] _]. cbn in WF.
eapply Qsw7.rw_cells_recast; [exact RW| | |].
- cbn. rewrite length_firstn, length_skipn. repeat split; lia.
- cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
- cbn. lia.
Qed.

Lemma outside_low : forall usp0 W x,
Forall (fun iv : Z * Z => snd iv <= usp0 - 8388608 /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv) /\ fst iv <= snd iv) W ->
(usp0 - 8388608 <= x \/ (0x10000 <= x < 0x99000)) -> outside W x.
Proof.
intros usp0 W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[F1 [F2 F3]] FW]. cbn [fst snd] in *.
split; [lia| apply IH; exact FW].
Qed.

Section AmbM.
Context {AMB : Amb}.
#[using="Type"] Lemma DF_munch_low : forall usp0 pp tid path m m' W,
DF usp0 pp tid path m -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => snd iv <= usp0 - 8388608 /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv) /\ fst iv <= snd iv) W ->
DF usp0 pp tid path m'.
Proof.
intros usp0 pp tid path m m' W D MU WM FW. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL].
pose proof (outside_low usp0 W) as OUT0. assert (OUT : forall x, (usp0 - 8388608 <= x \/ (0x10000 <= x < 0x99000)) -> outside W x) by (intros; apply OUT0; assumption).
assert (EQ : forall x, (usp0 - 8388608 <= x \/ (0x10000 <= x < 0x99000)) -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT. exact Hx. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- eapply stk_transport; [exact STK| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. apply EQ; [left; lia|]. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. lia.
+ destruct WR as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. apply W3. exact Hi.
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- unfold pris in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ; [right|];
unfold PRIS in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- eapply stk_transport; [exact STG| exact MU| exact WM|]. intros x Hx. left. apply OUT. right. unfold RSTAGE, RSTAGE_SZ in Hx. lia.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; [left; lia| lia].
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- exact CEIL.
Qed.

Definition stage_iv (iv : Z * Z) : Prop := RSTAGE <= fst iv /\ snd iv <= RSTAGE + RSTAGE_SZ.

#[using="Type"] Lemma DF_munch : forall usp0 pp tid path m m' W,
DF usp0 pp tid path m -> munch W m m' -> wmono rsegs m m' -> stk rsegs m' (usp0 - 8388608) (usp0 - 128) ->
stk rsegs m' RSTAGE (RSTAGE + RSTAGE_SZ) ->
Forall (fun iv => snd iv <= usp0 - 128 /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv \/ stage_iv iv) /\ fst iv <= snd iv) W ->
DF usp0 pp tid path m'.
Proof.
intros usp0 pp tid path m m' W D MU WM ST' STG' FW. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL].
assert (OUT : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ (RSTAGE <= x < RSTAGE + RSTAGE_SZ))) -> outside W x).
{ intros x Hx. clear -FW Hx. unfold stage_iv in FW. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[F1 [F2 F3]] FW]. cbn [fst snd] in *.
split; [lia| apply IH; exact FW]. }
assert (EQ : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ (RSTAGE <= x < RSTAGE + RSTAGE_SZ))) -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT. exact Hx. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- destruct (stk_split rsegs m (usp0 - 8388608) (usp0 - 128) usp0 STK ltac:(lia)) as [_ S2].
apply (stk_merge rsegs m' (usp0 - 8388608) (usp0 - 128) usp0 ST'); [| lia].
eapply stk_transport; [exact S2| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. apply EQ; [left; lia|]. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. lia.
+ destruct WR as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. apply W3. exact Hi.
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RSTAGE, RSTAGE_SZ; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RSTAGE, RSTAGE_SZ; lia| lia].
- unfold pris in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ; [right|];
unfold PRIS, RSTAGE, RSTAGE_SZ in *; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- exact STG'.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; [left; lia| lia].
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RSTAGE, RSTAGE_SZ; lia| lia].
- exact CEIL.
Qed.

#[using="Type"] Lemma stage_keep : forall usp0 pp tid path m m' W,
DF usp0 pp tid path m -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => snd iv <= usp0 - 128 /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv) /\ fst iv <= snd iv) W ->
stk rsegs m' RSTAGE (RSTAGE + RSTAGE_SZ).
Proof.
intros usp0 pp tid path m m' W D MU WM FW. pose proof (f_sp _ _ _ _ _ D) as SPB.
eapply stk_transport; [exact (f_stage _ _ _ _ _ D)| exact MU| exact WM|]. intros x Hx. left.
clear -FW Hx SPB. unfold RSTAGE, RSTAGE_SZ in Hx. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[F1 [F2 F3]] FW]. cbn [fst snd] in *.
split; [unfold alloc_ceiling in *; lia| apply IH; exact FW].
Qed.

End AmbM.

Lemma lit_add64 : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma file_read_lits : forall data len cnt, 0 <= len < 2^64 -> 0 <= cnt < 2^64 ->
file_read data (Z_to_bv 64 len) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data).
Proof. intros. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma firstn_len_firstn {X} : forall (c : nat) (s : list X), firstn (length (firstn c s)) s = firstn c s.
Proof. intros c s. rewrite length_firstn, <- List.firstn_firstn, List.firstn_all. reflexivity. Qed.

Lemma firstn_app_read : forall (l : list byte) a c,
firstn a l ++ firstn c (skipn a l) = firstn (a + length (firstn c (skipn a l))) l.
Proof. intros l a c. rewrite Qn1e.firstn_add, firstn_len_firstn. reflexivity. Qed.

Section Read.
Context {AMB : Amb}.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (data : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Variables (fds0 : list (word * FdEntry)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Hypothesis LOOM : leaf_oom_stmt usp0 pp tid path.
Hypothesis LREF : leaf_refused_stmt usp0 pp tid path.

Definition LFDS (fds : list (word * FdEntry)) (len : Z) : Prop :=
fd_lookup fds (Z_to_bv 64 3) = Some (FdFile path (Z_to_bv 64 len)) /\
forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.

Definition CFDS (fds : list (word * FdEntry)) : Prop :=
forall fd', fd' <> Z_to_bv 64 3 -> fd_lookup fds fd' = fd_lookup fds0 fd'.

#[using="Type"] Lemma neq23 : Z_to_bv 64 2 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 2) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.
#[using="FD2"] Lemma LFDS_2 : forall fds len, LFDS fds len -> fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros fds len [_ H]. rewrite (H _ neq23). exact FD2. Qed.
#[using="FD2"] Lemma CFDS_2 : forall fds, CFDS fds -> fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros fds H. rewrite (H _ neq23). exact FD2. Qed.
#[using="Type"] Lemma LFDS_init : LFDS (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) 0.
Proof. split; [apply Qn1e.fd_lookup_insert_eq| intros fd' NE; apply Qn1e.fd_lookup_insert_neq; exact NE]. Qed.
#[using="Type"] Lemma LFDS_read : forall fds len len', LFDS fds len -> LFDS (fd_insert fds (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 len'))) len'.
Proof.
intros fds len len' [H1 H2]. split; [apply Qn1e.fd_lookup_insert_eq|]. intros fd' NE. rewrite Qn1e.fd_lookup_insert_neq by exact NE. apply H2. exact NE.
Qed.
#[using="Type"] Lemma LFDS_close : forall fds len, LFDS fds len -> CFDS (fd_remove fds (Z_to_bv 64 3)).
Proof. intros fds len [H1 H2] fd' NE. rewrite Qn1e.fd_lookup_remove_neq by exact NE. apply H2. exact NE. Qed.
Hypothesis FS : fs_lookup fs path = Some data.
Notation B := usp0.
Notation LO := (usp0 - 8388608).
Notation SP := (usp0 - 128).

Definition WL (k : nat) : Z := DRV_W - FRESHW 0 - 262144 * (2 ^ Z.of_nat k - 1).
Definition DL (k : nat) : nat := (DRV_D - FRESHD - k * 7)%nat.

#[using="Type"] Lemma WL_0 : WL 0 = DRV_W - FRESHW 0.
Proof. unfold WL. change (2 ^ Z.of_nat 0) with 1. lia. Qed.
#[using="Type"] Lemma WL_10_le : forall k, (k <= 10)%nat -> 0 <= WL 10 <= WL k.
Proof.
intros k Hk. unfold WL, DRV_W. replace (FRESHW 0) with 1064960 by reflexivity.
pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 10 ltac:(lia) ltac:(lia)) as P2.
change (2 ^ Z.of_nat 10) with 1024. change (2 ^ 10) with 1024 in P2. change (2 ^ 31) with 2147483648. lia.
Qed.
#[using="Type"] Lemma WL_step : forall k cap, cap = 65536 * 2 ^ Z.of_nat k -> (k <= 9)%nat ->
0 <= WL (S k) /\ WL (S k) + 4 * cap = WL k.
Proof.
intros k cap -> Hk. unfold WL, DRV_W. replace (FRESHW 0) with 1064960 by reflexivity.
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 9 ltac:(lia) ltac:(lia)) as P2. change (2 ^ 9) with 512 in P2.
pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P0.
change (2 ^ 31) with 2147483648. set (p := 2 ^ Z.of_nat k) in *. lia.
Qed.

#[using="Type"] Lemma BIGW_grow_le : forall k cap, cap = 65536 * 2 ^ Z.of_nat k ->
0 <= BIGW (Z.of_nat k + 1) (cap * 2) <= 4 * cap.
Proof.
intros k cap ->. unfold BIGW, AMW, IB, UNIT, PGSZ.
pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P0.
replace (2 ^ (Z.of_nat k + 1 + 1)) with (4 * 2 ^ Z.of_nat k) by (rewrite !Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
set (p := 2 ^ Z.of_nat k) in *.
pose proof (QYTG.Mq0.round_up_pg_ge (65536 * p * 2 + 4 + 16)) as R1.
assert (R2 : round_up_pg (65536 * p * 2 + 4 + 16) <= 65536 * p * 2 + 4096).
{ apply round_up_pg_le_al; [lia|]. replace (65536 * p * 2 + 4096) with ((32 * p + 1) * 4096) by lia. apply Z.mod_mul. lia. }
lia.
Qed.

Record LINV (k : nat) (len cap buf : Z) (m : mem) (md : Model) (A : hstate) : Prop := MKL {
l_df   : DF usp0 pp tid path m;
l_heap : HEAPc B A [(buf, cap)] m md;
l_dsh  : DSH A;
l_sh   : hshift A <= Z.of_nat k + 1;
l_cap  : cap = 65536 * 2 ^ Z.of_nat k /\ (k <= 10)%nat;
l_len  : 0 <= len <= cap /\ len <= Z.of_nat (length data);
l_blk  : exists junk, rw_cells rsegs m buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk];
l_errno: exists errv, rw_cells rsegs m RERRNO [C4 errv];
l_fds  : LFDS (m_fds md) len;
l_fs   : m_fs md = fs;
l_bud  : BUD md (WL k) (DL k)
}.

Definition READPT : Z := 0x20c50.

Definition readpt_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : mem) (md : Model) (A : hstate)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
ppw (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READPT) fc None m (seg_rom rsegs)) md)
(T_rem data fs (10 - k) cap).

Definition loopk_stmt (k : nat) (len cap : Z) : Prop :=
forall (buf : Z) (m : mem) (md : Model) (A : hstate)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
ppw (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 LOOP) fc None m (seg_rom rsegs)) md)
(T_rem data fs (10 - k) cap).
Definition loop_stmt : Prop := forall k len cap, loopk_stmt k len cap.

#[using="Type"] Lemma carry : forall A LB m m' md W errv,
DF B pp tid path m -> HEAPc B A LB m md -> rw_cells rsegs m RERRNO [C4 errv] ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' LO SP -> stk rsegs m' RSTAGE (RSTAGE + RSTAGE_SZ) ->
Forall (fun iv => fst iv <= snd iv /\ ((LO <= fst iv /\ snd iv <= SP) \/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n) \/ stage_iv iv)) W ->
DF B pp tid path m' /\ HEAPc B A LB m' md /\ rw_cells rsegs m' RERRNO [C4 errv].
Proof.
intros A LB m m' md W errv D HP ERR MU WM MI' ST' STG' FW.
pose proof (f_sp _ _ _ _ _ D) as SPB. pose proof (f_ceil _ _ _ _ _ D) as CEIL. pose proof stage_bounds as (SB1 & SB2 & SB3 & SB4).
assert (BLKF : forall b n, In (b, n) LB -> 0 <= n /\ 0 < b /\ b + n <= alloc_ceiling /\ (b + n <= RIMG_LO \/ RIMG_HI <= b)).
{ intros b n HIN. pose proof (heapc_blk B _ _ _ _ b n HP HIN). tauto. }
split; [| split].
- eapply DF_munch; [exact D| exact MU| exact WM| exact ST'| exact STG'|].
eapply Forall_impl; [| exact FW]. intros [lo hi] [H1 [[H2 H3]|[(b & n & HIN & H2 & H3)|[H2 H3]]]]; cbn [fst snd] in *.
+ unfold alloc_ceiling in *. lia.
+ destruct (BLKF b n HIN) as (F1 & F2 & F3 & F4). unfold alloc_ceiling, RIMG_LO, RIMG_HI in *. lia.
+ split; [unfold alloc_ceiling in *; lia|]. split; [right; right; exact (conj H2 H3)| lia].
- eapply (heapc_frame B); [exact HP| | exact WM| exact MI']. intros a Ha NCW. apply MU. unfold wa. rewrite unsigned_lit by lia.
clear -FW NCW Ha SPB CEIL BLKF SB1 SB2 SB3 SB4. unfold stage_iv in FW. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [fst snd] in *.
split; [| apply IH; exact FW]. intros [X1 X2]. apply NCW. destruct HC as [[H2 H3]|[(b & n & HIN & H2 & H3)|[H2 H3]]].
+ right; left. unfold alloc_ceiling in *. lia.
+ left. exists (b, n). split; [exact HIN|]. cbn. lia.
+ right; right. split; [unfold RDATA_LO, RIMG_HI; lia|].
unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RHEX_GOT, RHEX_PTR, RSTAGE, RSTAGE_SZ in *. lia.
- eapply rw_cells_transport; [exact ERR| exact MU| exact WM|].
clear -FW SPB BLKF SB4. unfold stage_iv in FW. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [fst snd disjoint_from cells_size csize Nat.add] in *.
split; [| apply IH; exact FW]. unfold RERRNO, RATP. destruct HC as [[H2 H3]|[(b & n & HIN & H2 & H3)|[H2 H3]]].
+ lia.
+ destruct (BLKF b n HIN) as (F1 & F2 & F3 & F4). unfold RIMG_LO, RIMG_HI in *. lia.
+ unfold RERRNO, RSTAGE, RSTAGE_SZ in *. lia.
Qed.

Definition HDRPT : Z := 0x20c80.
Record HINV (cap buf : Z) (m : mem) (md : Model) (A : hstate) : Prop := MKH {
h_df   : DF usp0 pp tid path m;
h_heap : HEAPc B A [(buf, cap)] m md;
h_dsh  : DSH A;
h_sh   : hshift A <= 12;
h_cap  : 65536 <= cap <= 2^26;
h_len  : Z.of_nat (length data) < cap;
h_blk  : exists junk, rw_cells rsegs m buf [CB (length data) data; CB (Z.to_nat (cap - Z.of_nat (length data))) junk];
h_errno: exists errv, rw_cells rsegs m RERRNO [C4 errv];
h_fds  : CFDS (m_fds md);
h_fs   : m_fs md = fs;
h_bud  : BUD md (WL 10) (DL 10)
}.
Definition hdr_stmt : Prop :=
forall (cap buf : Z) (m : mem) (md : Model) (A : hstate)
(ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINV cap buf m md A ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
ppw (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 3) (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 HDRPT) fc None m (seg_rom rsegs)) md)
(t_body data fs).

#[using="Type"] Lemma cap_bounds : forall k cap, cap = 65536 * 2 ^ Z.of_nat k -> (k <= 10)%nat -> 65536 <= cap <= 2^26.
Proof.
intros k cap -> Hk. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P1.
pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 10 ltac:(lia) ltac:(lia)) as P2. change (2^0) with 1 in P1. change (2^26) with (65536 * 2^10). nia.
Qed.

Definition READCALL : Z := 0x20c60.
#[using="FS"] Lemma seg_read2 : forall k len cap cnt, hdr_stmt ->
len < cap -> 1 <= cnt <= 65536 -> cnt <= cap - len ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
forall (buf : Z) (m : mem) (md : Model) (A : hstate)
(ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
LINV k len cap buf m md A ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 -> QCcH.frm0 fc ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 (Z_to_bv 64 cnt) a3 a4 a5 a6 a7
ppw (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READCALL) fc None m (seg_rom rsegs)) md)
(T_rem data fs (10 - k) cap).
Proof.
intros k len cap cnt HDR LT Hcnt Hcnt2 NEXT. intros until fc. intros LI Hgp Htp FRM. subst gp tp.
destruct LI as [D HP DSH SH [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) Hfds Hfs HBUD].
pose proof (f_sp _ _ _ _ _ D) as SPB. pose proof (f_ceil _ _ _ _ _ D) as CEIL. pose proof stage_bounds as (SB1 & SB2 & SB3 & SB4).
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (heapc_blk B _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
unfold alloc_ceiling in Bhi. unfold RIMG_LO, RIMG_HI in Bimg.
word_range ppw PPR.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
destruct (stk_split rsegs m LO SP usp0 (f_stk _ _ _ _ _ D) ltac:(lia)) as [ST1 _].
assert (LJ : length junk = Z.to_nat (cap - len)) by (destruct BLK as [[WF _] _]; cbn in WF; tauto).

destruct (stk_carve_lo m RSTAGE (RSTAGE + RSTAGE_SZ) (Z.to_nat cnt) (f_stage _ _ _ _ _ D) ltac:(unfold RSTAGE_SZ; lia)) as [STGH (sjunk & DST)].
apply rz_evt; [exact MOK|]. unfold READCALL.
step. step. step. apply evt_RZ_done.
eapply (read_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ path (Z_to_bv 64 len) data sjunk RSTAGE cnt LO MOK
eq_refl eq_refl eq_refl (proj1 Hfds)); [rewrite Hfs; exact FS| lia| unfold RSTAGE; lia| unfold RSTAGE, alloc_ceiling in *; lia| exact DST
| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI| reflexivity|].
intros a1' a2' a3' a4' a5' a6' a7' m2. cbv zeta. rewrite !unsigned_lit by lia. intros MU2 WM2 MI2 ST2 DST2.
rewrite file_read_lits in * by lia. rewrite lit_add64. unfold len_word.
set (bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat len) data)) in *.
assert (LBS : length bs = Nat.min (Z.to_nat cnt) (length data - Z.to_nat len)) by (subst bs; rewrite length_firstn, length_skipn; reflexivity).
set (nb := length bs) in *.

assert (STG2 : stk rsegs m2 RSTAGE (RSTAGE + RSTAGE_SZ)).
{ apply (stk_merge rsegs m2 RSTAGE (RSTAGE + Z.of_nat (Z.to_nat cnt)) (RSTAGE + RSTAGE_SZ)); [| | unfold RSTAGE_SZ; lia].
- replace (RSTAGE + Z.of_nat (Z.to_nat cnt)) with (RSTAGE + Z.of_nat (cells_size [CB nb bs; CB (Z.to_nat cnt - nb) (skipn nb sjunk)])) by (cbn; lia).
apply stk_of_rw_cells. exact DST2.
- eapply stk_transport; [exact STGH| exact MU2| exact WM2|]. intros x Hx. left. cbn. unfold alloc_ceiling in *. lia. }

destruct (carry A [(buf, cap)] m m2 md _ errv D HP ERR MU2 WM2 MI2 ST2 STG2) as (D2 & HP2 & ERR2).
{ constructor; [| constructor; [| constructor]]; cbn [fst snd]; [split; [lia| left; lia]| split; [lia| right; right; unfold stage_iv; cbn; unfold RSTAGE_SZ; lia]]. }
assert (BLK2 : rw_cells rsegs m2 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. unfold RSTAGE, alloc_ceiling in *. repeat split; lia. }
destruct (rw_cells_head_bytes m2 RSTAGE _ _ _ DST2) as [SRC SLEN].
clear DST DST2 MU2 WM2 ST1 STGH.
clearbody nb.
assert (MOK2 : model_ok (with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + Z.of_nat nb)))) md)) by exact MOK.
reenter MOK2. step. if_falsex. step. step.
destruct (Nat.eq_dec nb 0) as [NB0|NBP].
-
if_falsex. step. step. apply evt_RZ_done.
eapply (close_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 _ _ (FdFile path (Z_to_bv 64 (len + Z.of_nat nb))) LO MOK2 eq_refl);
[exact (Qn1e.fd_lookup_insert_eq _ _ _)| rewrite unsigned_lit by lia; exact ST2| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI2| reflexivity|].
intros b1 b2 b3 b4 b5 b6 b7 m3. rewrite !unsigned_lit by lia. intros MU3 WM3 MI3 ST3.
pose proof (stage_keep B pp tid path m2 m3 _ D2 MU3 WM3 ltac:(constructor; [cbn; lia| constructor])) as STG3.
destruct (carry A [(buf, cap)] m2 m3 _ _ errv D2 HP2 ERR2 MU3 WM3 MI3 ST3 STG3) as (D3 & HP3 & ERR3).
{ constructor; [| constructor]. cbn [fst snd]. split; [lia| left; lia]. }
assert (BLK3 : rw_cells rsegs m3 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. split; [left; unfold alloc_ceiling in *; lia| exact I]. }
assert (MOK3 : model_ok (with_fds (fd_remove (m_fds (with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + Z.of_nat nb)))) md)) (Z_to_bv 64 3))
(with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + Z.of_nat nb)))) md))) by exact MOK.
reenter MOK3. apply evt_RZ_done.
assert (LEND : len = Z.of_nat (length data)) by lia.
rewrite T_rem_small by lia.
subst len.
apply (HDR cap buf m3 _ A); [| reflexivity| reflexivity| exact FRM].
constructor.
+ exact D3.
+ eapply (heapc_model_frame B); [exact HP3| reflexivity| reflexivity| exact (proj1 MOK)].
+ exact DSH.
+ lia.
+ exact CAPB.
+ lia.
+ exists junk. rewrite firstn_all2 in BLK3 by lia. rewrite Nat2Z.id in BLK3. exact BLK3.
+ exists errv. exact ERR3.
+ exact (LFDS_close _ _ (LFDS_read _ _ _ Hfds)).
+ exact Hfs.
+ eapply BUD_frame; [| reflexivity| reflexivity| reflexivity]. eapply BUD_mono; [exact HBUD| |].
{ exact (WL_10_le k Hk). } { unfold DL, DRV_D, FRESHD. lia. }
-
if_truex.

apply (proj1 (QULt.Mq2.rw_cells_app rsegs m2 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] _)) in BLK2 as [PRE REST].
cbn [cells_size csize Nat.add] in REST. rewrite Nat.add_0_r, Z2Nat.id in REST by lia.
replace (Z.to_nat (cap - len)) with (nb + (Z.to_nat (cap - len) - nb))%nat in REST by lia.
pose proof (rw_cells_CB_split m2 (buf + len) _ _ junk REST) as REST2.
apply (proj1 (QULt.Mq2.rw_cells_app rsegs m2 (buf + len) [CB nb (firstn nb junk)] _)) in REST2 as [CDST TAIL].
cbn [cells_size csize Nat.add] in TAIL. rewrite Nat.add_0_r in TAIL.
clear REST.
step. try rewrite lit_add64. step. step. step.
eapply evt_cut; [eapply memcpy_spec; rewrite ?unsigned_lit by (unfold RSTAGE; lia); [exact SRC| rewrite Nat2Z.id; exact SLEN| rewrite Nat2Z.id; exact CDST| unfold RSTAGE in *; lia| exact MI2]|].
intros ms3 PO3. destruct PO3 as (w0 & w1 & w2 & wa1 & wa2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & m3 & -> & MU3 & WM3 & MI3 & CDST3 & _).
rewrite !unsigned_lit in MU3, CDST3 by (unfold RSTAGE; lia). rewrite Nat2Z.id in CDST3.

assert (HP3 : HEAPc B A [(buf, cap)] m3 (with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + Z.of_nat nb)))) md)).
{ eapply (heapc_frame B); [eapply (heapc_model_frame B); [exact HP2| reflexivity| reflexivity| exact (proj1 MOK)]| | exact WM3| exact MI3].
intros a Ha NCW. apply MU3. unfold wa. rewrite unsigned_lit by lia. cbn. split; [| exact I].
intros [X1 X2]. apply NCW. left. exists (buf, cap). split; [left; reflexivity|]. cbn. lia. }
assert (D3 : DF B pp tid path m3).
{ eapply DF_munch_low; [exact D2| exact MU3| exact WM3|]. constructor; [cbn; unfold alloc_ceiling in *; lia| constructor]. }
assert (PRE3 : rw_cells rsegs m3 buf [CB (Z.to_nat len) (firstn (Z.to_nat len) data)]).
{ eapply rw_cells_transport; [exact PRE| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (TAIL3 : rw_cells rsegs m3 (buf + len + Z.of_nat nb) [CB (Z.to_nat (cap - len) - nb) (skipn nb junk)]).
{ eapply rw_cells_transport; [exact TAIL| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (ERR3 : rw_cells rsegs m3 RERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. unfold RERRNO, RATP. repeat split; lia. }
assert (STK3 : stk rsegs m3 LO SP) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; unfold alloc_ceiling in *; lia]).

assert (BLK3 : rw_cells rsegs m3 buf [CB (Z.to_nat (len + Z.of_nat nb)) (firstn (Z.to_nat (len + Z.of_nat nb)) data);
CB (Z.to_nat (cap - (len + Z.of_nat nb))) (skipn nb junk)]).
{ assert (J : rw_cells rsegs m3 buf ([CB (Z.to_nat len) (firstn (Z.to_nat len) data)] ++ ([CB nb bs] ++ [CB (Z.to_nat (cap - len) - nb) (skipn nb junk)]))).
{ apply (proj2 (QULt.Mq2.rw_cells_app rsegs m3 buf _ _)). split; [exact PRE3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
apply (proj2 (QULt.Mq2.rw_cells_app rsegs m3 (buf + len) _ _)). split; [exact CDST3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact TAIL3. }
cbn [app] in J.
eapply Qsw7.rw_cells_recast; [exact J| | |].
- cbn. rewrite length_firstn, !List.length_skipn. repeat split; lia.
- cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite (app_assoc (firstn (Z.to_nat len) data) bs). f_equal.
subst bs. rewrite firstn_app_read. f_equal. lia.
- cbn. lia. }
clear PRE PRE3 TAIL TAIL3 CDST CDST3 MU3 WM3.
assert (MOK3 : model_ok (with_fds (fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + Z.of_nat nb)))) md)) by exact MOK.
replace (ret_pc (Z_to_bv 64 134148)) with (Z_to_bv 64 134148 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. try rewrite lit_add64. step. apply evt_RZ_done.
replace (Z.of_nat nb + len) with (len + Z.of_nat nb) by lia.
apply (NEXT (Z.of_nat nb) ltac:(lia) ltac:(lia) buf m3 _ A); [| reflexivity| reflexivity| exact FRM].
constructor.
+ exact D3.
+ exact HP3.
+ exact DSH.
+ exact SH.
+ split; [exact Hcap| exact Hk].
+ lia.
+ eexists. exact BLK3.
+ exists errv. exact ERR3.
+ exact (LFDS_read _ _ _ Hfds).
+ exact Hfs.
+ eapply BUD_frame; [exact HBUD| reflexivity| reflexivity| reflexivity].
Qed.

#[using="FS"] Lemma seg_read : forall k len cap, hdr_stmt -> len < cap ->
(forall n, 1 <= n -> len + n <= cap -> loopk_stmt k (len + n) cap) ->
readpt_stmt k len cap.
Proof.
intros k len cap HDR LT NEXT. unfold readpt_stmt. intros until fc. intros LI Hgp Htp FRM. subst gp tp.
pose proof (heapc_model_ok B _ _ _ _ (l_heap _ _ _ _ _ _ _ LI)) as MOK.
pose proof (l_cap _ _ _ _ _ _ _ LI) as [Hcap Hk]. pose proof (l_len _ _ _ _ _ _ _ LI) as [Hlen Hlen2].
pose proof (f_sp _ _ _ _ _ (l_df _ _ _ _ _ _ _ LI)) as SPB. pose proof (f_ceil _ _ _ _ _ (l_df _ _ _ _ _ _ _ LI)) as CEIL.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
word_range ppw PPR.
apply rz_evt; [exact MOK|]. unfold READPT.
step. rewrite (unsigned_lit len) by lia. replace (cap + - len) with (cap - len) by lia. step. step.
destruct (Z_lt_dec (cap - len) 65536) as [SM|BG].
- if_truex. apply evt_RZ_done.
eapply (seg_read2 k len cap (cap - len) HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A); [exact LI| reflexivity| reflexivity| exact FRM].
- if_falsex. step. apply evt_RZ_done.
eapply (seg_read2 k len cap 65536 HDR LT ltac:(lia) ltac:(lia) NEXT buf m md A); [exact LI| reflexivity| reflexivity| exact FRM].
Qed.

#[using="FD2 LOOM LREF"] Lemma seg_loop : forall k len cap,
(len < cap -> readpt_stmt k len cap) ->
(len = cap -> (k < 10)%nat -> 65536 <= cap -> readpt_stmt (S k) len (2 * cap)) ->
loopk_stmt k len cap.
Proof.
intros k len cap RD GROW. unfold loopk_stmt.
intros until fc. intros LI Hgp Htp FRM. subst gp tp. destruct LI as [D HP DSH SH [Hcap Hk] [Hlen Hlen2] (junk & BLK) (errv & ERR) Hfds Hfs HBUD].
pose proof (f_sp _ _ _ _ _ D) as SPB. pose proof (f_ceil _ _ _ _ _ D) as CEIL.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (cap_bounds k cap Hcap Hk) as CAPB.
word_range ppw PPR.
apply rz_evt; [exact MOK|].
step.
destruct (Z.eq_dec len cap) as [FULL|NFULL].
2:{
if_falsex. step. step. apply evt_RZ_done.
apply (RD ltac:(lia) buf m md A); [| reflexivity| reflexivity| exact FRM].
constructor; auto. exists junk; exact BLK. exists errv; exact ERR. }

if_truex. subst len. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftr_div_pow2 by lia.
destruct (Nat.eq_dec k 10) as [K10|KLT].
{
assert (Hc : cap = 2^26) by (rewrite Hcap, K10; reflexivity).
replace (cap / 2 ^ 26) with 1 by (rewrite Hc; reflexivity).
step. if_truex. apply evt_RZ_done.
replace (T_rem data fs (10 - k) cap) with (t_die msg_refused (m_fs md)).
2:{ rewrite K10. cbn [T_rem Nat.sub]. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true; [rewrite Hfs; reflexivity|].
symmetry. apply Z.leb_le. unfold MAX_INPUT. lia. }
eapply LREF; [exact D| exact HP| reflexivity| reflexivity| exact (LFDS_2 _ _ Hfds)]. }

assert (Hc : cap <= 2^25).
{ rewrite Hcap. change (2^25) with (65536 * 2^9). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
replace (cap / 2 ^ 26) with 0 by (symmetry; apply Z.div_small; lia).
step. if_falsex. step. rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
step. step. apply evt_RZ_done.

assert (NK : (10 - k)%nat = S (10 - S k)) by lia. rewrite NK, T_rem_grow by lia.
replace (2 * cap) with (cap * 2) by lia.
assert (BIG : 0 <= BIGW (Z.of_nat k + 1) (cap * 2) <= 4 * cap) by (exact (BIGW_grow_le k cap Hcap)).
pose proof (WL_step k cap Hcap ltac:(lia)) as [WLS0 WLS1].
destruct (stk_split rsegs m LO SP usp0 (f_stk _ _ _ _ _ D) ltac:(lia)) as [ST1 ST2].
eapply (heapc_malloc_big_dsh B rmalloc_spec
(Z_to_bv 64 0x20c2c) (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00)
t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 (cap * 2)) a1 a2 a3 a4 a5 a6 a7 ppw (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (cap * 2))
(Z_to_bv 64 RSTAGE) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6
F fc m md (t_die msg_oom fs) _ A [(buf, cap)] (cap * 2) LO errv (Z.of_nat k + 1) (WL (S k)) (S (DL (S k))) HP DSH);
[lia| lia| unfold MMAP_THRESHOLD; lia| unfold IB, UNIT; lia| | exact WLS0
| rewrite unsigned_lit by lia; exact ST1| unfold alloc_ceiling; lia| rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia
| rewrite unsigned_lit by lia; lia| unfold RATP, RERRNO in *; exact ERR| reflexivity| reflexivity| |].
{ eapply BUD_mono; [exact HBUD| |]. { lia. } { unfold DL, BIGD, DRV_D, FRESHD. lia. } }
-
intros ms' m' md' A' errv' RS VM ST' (LB0 & PLB & PRES) ERR' HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES (heapc_mem_inv B _ _ _ _ HP') ST' eq_refl ltac:(lia))).
reenter MOK'. step. if_truex. apply evt_RZ_done.
rewrite <- Hfs, <- (vm_only_fs md md' VM).
eapply LOOM; [exact D'| exact HP'| reflexivity| reflexivity| | left; reflexivity].
rewrite (vm_only_fds md md' VM). exact (LFDS_2 _ _ Hfds).
-
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' Hr (junk2 & BLK2) RNG HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES MI' ST' eq_refl ltac:(lia))).
destruct RNG as (R1 & R2 & R3 & R4 & R5).

pose proof (pres_block [(buf, cap)] LB0 SP m m' buf cap _ PLB ltac:(left; reflexivity) PRES BLK ltac:(cbn; lia)) as BLK'.
destruct (rw_cells_head_bytes m' buf _ _ _ BLK') as [SRC SLEN].

replace (Z.to_nat (cap * 2)) with (Z.to_nat cap + Z.to_nat cap)%nat in BLK2 by lia.
pose proof (rw_cells_CB_split m' r _ _ junk2 BLK2) as BLK2s.
apply (proj1 (QULt.Mq2.rw_cells_app rsegs m' r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk2)] _)) in BLK2s as [NB1 NB2].
cbn [cells_size csize Nat.add] in NB2. rewrite Nat.add_0_r in NB2.
pose proof (heapc_blk_disjoint B _ _ _ _ r (cap * 2) buf cap HP' ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as DISJ.
pose proof (heapc_blk_nodup B _ _ _ _ HP') as ND. cbn [map fst] in ND.
assert (NE : r <> buf) by (inversion ND; subst; cbn in *; intros E; subst; tauto).
specialize (DISJ NE).
reenter MOK'. step. if_falsex. step. step. if_falsex. step. step. step. step.
pose proof (heapc_blk B _ _ _ _ buf cap HP' ltac:(right; left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
pose proof (heapc_blk B _ _ _ _ r (cap * 2) HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _ & Rimg).
unfold alloc_ceiling in Bhi, Rhi. unfold RIMG_LO, RIMG_HI in Bimg, Rimg.
eapply evt_cut; [eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact SRC| exact SLEN| exact NB1| lia| exact MI']|].
intros ms2 PO2. destruct PO2 as (w0 & w1 & w2 & wa1 & wa2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & m2 & -> & MU2 & WM2 & MI2 & DST2 & _).
rewrite !unsigned_lit in MU2, DST2 by lia.
replace (ret_pc (Z_to_bv 64 134216)) with (Z_to_bv 64 134216 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (HP2 : HEAPc B A' [(r, cap * 2); (buf, cap)] m2 md').
{ eapply (heapc_frame B); [exact HP'| | exact WM2| exact MI2]. intros a Ha NCW. apply MU2. unfold wa. rewrite unsigned_lit by lia. cbn. split; [| exact I].
intros [X1 X2]. apply NCW. left. exists (r, cap * 2). split; [left; reflexivity|]. cbn. lia. }
assert (D2 : DF B pp tid path m2).
{ eapply DF_munch_low; [exact D'| exact MU2| exact WM2|]. constructor; [cbn; lia| constructor]. }
assert (NB2' : rw_cells rsegs m2 (r + Z.of_nat (Z.to_nat cap)) [CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ eapply rw_cells_transport; [exact NB2| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia| exact I]. }
assert (STK2 : stk rsegs m2 LO SP) by (eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2| cbn; unfold alloc_ceiling in *; lia]).
assert (ERR2 : rw_cells rsegs m2 (RATP - 164) [C4 errv']) by (eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2| cbn; unfold RATP; lia]).
clear MU2 WM2 SRC BLK' NB1 NB2 ST' ERR' D' MI'.

step. step. apply evt_RZ_done.
eapply (heapc_free_dsh B rfree_spec_proof
(Z_to_bv 64 0x20c50) (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00)
w0 w1 w2 (Z_to_bv 64 2) (Z_to_bv 64 r) (Z_to_bv 64 buf) wa1 wa2 w3 w4 w5 w6 w7 ppw (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (cap * 2))
(Z_to_bv 64 RSTAGE) (Z_to_bv 64 buf) s8 s9 s10 s11 w8 w9 w10 w11
F fc m2 md' _ A' [(r, cap * 2); (buf, cap)] buf cap LO errv' (WL (S k)) (DL (S k)) HP2 ltac:(right; left; reflexivity) DSH' BUD');
[exact WLS0
| rewrite unsigned_lit by lia; exact STK2| unfold alloc_ceiling; lia| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite unsigned_lit by lia; lia| exact ERR2| reflexivity| reflexivity|].
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 (LBx & PLBx & PRES3) ERR3 HP3 SH3 DSH3 BUD3.
replace (zlb_remove buf [(r, cap * 2); (buf, cap)]) with [(r, cap * 2)] in *
by (cbn [zlb_remove fst]; rewrite (proj2 (Z.eqb_neq _ _) NE), Z.eqb_refl; reflexivity).
open_ret RS3. pose proof (heapc_model_ok B _ _ _ _ HP3) as MOK3. pose proof (heapc_mem_inv B _ _ _ _ HP3) as MI3.
rewrite unsigned_lit in ST3, PRES3 by lia.
assert (D3 : DF B pp tid path m3) by (eapply (DF_alloc B pp tid path m2 m3 LBx SP LO D2 PRES3 MI3 ST3 eq_refl ltac:(lia))).

assert (NBLK : rw_cells rsegs m2 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)]).
{ apply (proj2 (QULt.Mq2.rw_cells_app rsegs m2 r [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _)). split; [exact DST2|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact NB2'. }
pose proof (pres_block [(r, cap * 2)] LBx SP m2 m3 r (cap * 2) _ PLBx ltac:(left; reflexivity) PRES3 NBLK ltac:(cbn; lia)) as NBLK3.

replace (ret_pc (Z_to_bv 64 0x20c50)) with (Z_to_bv 64 0x20c50 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite (Z.mul_comm cap 2) in *.
apply (GROW eq_refl ltac:(lia) ltac:(lia) r m3 md3 A3); [| reflexivity| reflexivity| exact FRM].
constructor.
+ exact D3.
+ exact HP3.
+ exact DSH3.
+ rewrite SH3. rewrite Nat2Z.inj_succ. lia.
+ split; [| lia]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
+ lia.
+ exists (skipn (Z.to_nat cap) junk2). replace (Z.to_nat (2 * cap - cap)) with (Z.to_nat cap) by lia. exact NBLK3.
+ exists errv'. unfold RATP, RERRNO in *. exact ERR3.
+ rewrite (vm_only_fds md' md3 VM3), (vm_only_fds md md' VM). exact Hfds.
+ rewrite (vm_only_fs md' md3 VM3), (vm_only_fs md md' VM). exact Hfs.
+ exact BUD3.
Qed.

#[using="Type"] Lemma loop_vacuous : forall k len cap, (10 < k)%nat -> loopk_stmt k len cap.
Proof. intros k len cap Hk. unfold loopk_stmt. intros until fc. intros LI. pose proof (l_cap _ _ _ _ _ _ _ LI). lia. Qed.

#[using="FD2 LOOM LREF FS"] Lemma loop_inner : hdr_stmt -> forall k cap, (forall len' cap', loopk_stmt (S k) len' cap') ->
forall n len, (Z.to_nat (cap - len) <= n)%nat -> loopk_stmt k len cap.
Proof.
intros HDR k cap QS. induction n as [|n IH]; intros len Hn.
- apply seg_loop.
+ intros LT. lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n _ _. apply QS.
- apply seg_loop.
+ intros LT. apply (seg_read k len cap HDR LT). intros n' H1 H2. apply IH. lia.
+ intros -> Hk Hc. apply (seg_read (S k) cap (2 * cap) HDR ltac:(lia)). intros n' _ _. apply QS.
Qed.

#[using="FD2 LOOM LREF FS"] Lemma loop_all : hdr_stmt -> loop_stmt.
Proof.
intros HDR.
assert (DOWN : forall j k, (k = 11 - j)%nat -> (j <= 11)%nat -> forall len cap, loopk_stmt k len cap).
{ induction j as [|j IH]; intros k -> Hj len cap.
- apply loop_vacuous. lia.
- apply (loop_inner HDR (11 - S j) cap) with (n := Z.to_nat (cap - len)); [| lia].
intros len' cap'. apply (IH (S (11 - S j))); lia. }
unfold loop_stmt. intros k.
destruct (Nat.le_gt_cases k 10) as [Hk|Hk].
- exact (DOWN (11 - k)%nat k ltac:(lia) ltac:(lia)).
- intros len cap. exact (loop_vacuous k len cap ltac:(lia)).
Qed.

#[using="FD2 LOOM LREF FS"] Lemma readpt_first : hdr_stmt -> readpt_stmt 0 0 65536.
Proof.
intros HDR. apply (seg_read 0 0 65536 HDR ltac:(lia)). intros n _ _. apply (loop_all HDR).
Qed.

#[using="FD2 LOOM LREF FS"] Lemma seg_first : hdr_stmt ->
read_entry_stmt usp0 tid ppw path (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) fs (t_opened data fs).
Proof.
intros HDR. unfold read_entry_stmt.
intros F fc t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m md DE HP HBUD Hfds Hfs FRM.
pose proof (DF_of_entry _ _ _ _ _ DE) as D. destruct DE as [SPB STK FRMc ERRC _ _ _ _ _ _ MI _ _ _ _ _ PTH _ _ CEIL].

eapply rz_conseq; [| apply (T_rem_oom_eq data fs 10 65536)].
eapply (heapc_malloc_first B rmalloc_spec
(Z_to_bv 64 0x20bd8) (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00)
t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 ppw s3 (Z_to_bv 64 3) (Z_to_bv 64 65536)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6
F fc m md (t_die msg_oom fs) _ A0 [] 65536 LO (wz 0) 0 (DRV_W - FRESHW 0) (DRV_D - FRESHD)%nat HP A0_GSH).
- rewrite A0_hshift. lia.
- lia.
- apply first_req_65536.
- eapply BUD_mono; [exact HBUD| |]. { unfold DRV_W, FRESHW, AMW, PGSZ. cbn. lia. } { unfold DRV_D, FRESHD. lia. }
- unfold DRV_W, FRESHW, AMW, PGSZ. cbn. lia.
- destruct (stk_split rsegs m LO SP usp0 STK ltac:(lia)) as [S1 _]. rewrite unsigned_lit by lia. exact S1.
- unfold alloc_ceiling. lia.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite unsigned_lit by lia. lia.
- unfold RATP, RERRNO in *. exact ERRC.
- reflexivity.
- reflexivity.
-
intros ms' m' md' A' errv' RS VM ST' (LB0 & PLB & PRES) ERR' HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES (heapc_mem_inv B _ _ _ _ HP') ST' eq_refl ltac:(lia))).
reenter MOK'. step. if_truex. apply evt_RZ_done.
rewrite <- Hfs, <- (vm_only_fs md md' VM).
eapply LOOM; [exact D'| exact HP'| reflexivity| reflexivity| | right; reflexivity].
rewrite (vm_only_fds md md' VM), Hfds. exact (LFDS_2 _ _ LFDS_init).
-
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' Hr (junk & BLK) RNG HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES (heapc_mem_inv B _ _ _ _ HP') ST' eq_refl ltac:(lia))).
destruct RNG as (R1 & R2 & R3 & R4 & R5).
reenter MOK'. step. if_falsex. step. step. step. step. step. if_truex. step. step. apply evt_RZ_done.
apply (readpt_first HDR r m' md' A'); [| reflexivity| reflexivity| exact FRM].
constructor.
+ exact D'.
+ exact HP'.
+ exact DSH'.
+ cbn [Z.of_nat]. lia.
+ split; [reflexivity| lia].
+ split; [lia| lia].
+ exists junk. cbn [Z.to_nat firstn Z.sub Pos.to_nat]. apply rw_cells_CB0. replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity. exact BLK.
+ exists errv'. unfold RATP, RERRNO in *. exact ERR'.
+ rewrite (vm_only_fds md md' VM), Hfds. exact LFDS_init.
+ rewrite (vm_only_fs md md' VM). exact Hfs.
+ rewrite WL_0. unfold DL. cbn [Z.of_nat Nat.mul Nat.sub]. rewrite Nat.sub_0_r. exact BUD'.
Qed.

#[using="FD2 LOOM LREF FS"] Theorem read_entry_ok : hdr_stmt ->
read_entry_stmt usp0 tid ppw path (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) fs (t_opened data fs).
Proof. intros HDR. apply seg_first. exact HDR. Qed.
End Read.
