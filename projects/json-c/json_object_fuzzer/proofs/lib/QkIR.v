(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE Q6q3 QGcC Qwm6 QZsi Qsn5 QJFf QPUe QrOY QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QvSK QvQl Qn7S Qk85 QXDj Q45h QOTx Q25t QNDM Q7DP QMhO Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QvSK.Mq0 QvQl.Mq0 QvQl Qn7S Qk85.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QMhO Qb5q.Mq1.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition REGSJ : list (Z * Z * Z) :=
if existsb (fun r => Z.eqb (fst (fst r)) 0xed040) QGcC.tokA_reg_globals then QGcC.tokA_reg_globals
else QGcC.tokA_reg_globals ++ [(0xed040, 0, 6848)].
Definition SBJ : Z := 0x7fff8000.
Definition GLOJ : Z := 8192.
Definition GHIJ : Z := 822784.

Definition shimg_check (ch : acs) : bool :=
walk REGSJ SBJ (ivs_of (GLOJ + SBJ) (GHIJ + SBJ) (kn_view ch)) (GLOJ + SBJ) (GHIJ + SBJ) 400.
Lemma SHIMG_HS2sA_1_ok : shimg_check HS2sA_1 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sA_2_ok : shimg_check HS2sA_2 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sB_3_ok : shimg_check HS2sB_3 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sB_4_ok : shimg_check HS2sB_4 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_CHECKS : forall w ch, HSCLASS_S w ch -> shimg_check ch = true.
Proof. intros [|] ch [-> | ->]; [exact SHIMG_HS2sA_1_ok | exact SHIMG_HS2sA_2_ok | exact SHIMG_HS2sB_3_ok | exact SHIMG_HS2sB_4_ok]. Qed.

Lemma REGS_EQ {RC__ : Q6q3.RunConsts} : QZsi.hl_reg_globals Qwm6.Mq4.A4L = REGSJ.
Proof. change (QZsi.hl_reg_globals Qwm6.Mq4.A4L) with QGcC.tokA_reg_globals. vm_compute. reflexivity. Qed.

Definition CANc : list scell := [SCw 8 (EVar 45)].
Lemma CAN_CHECKS : forall w ch, HSCLASS_S w ch -> cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x625510 CANc = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stat.
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
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation usp := (bv_unsigned sp).

Theorem img_shadow_main : forall g, 0x10000 <= 8 * g -> 8 * g + 8 <= 0x647000 ->
QZDE.bytes_at JOB6SEGS m (g + 0x7fff8000) [Z_to_bv 8 (QZsi.img_shadow_val REGSJ g)].
Proof.
intros g G1 G2.
exact (img_shadow_closed JOB6SEGS E m (kn_view ch) (MV4 main_know_view) REGSJ SBJ GLOJ GHIJ 400 (SHIMG_CHECKS w ch HCL)
ltac:(unfold GLOJ, SBJ; lia) ltac:(unfold GHIJ, SBJ; lia) g ltac:(unfold GLOJ, GHIJ; lia)).
Qed.

Theorem stack_shadow_main : forall g, (atopE E + 4096) / 8 <= g -> 8 * g < 2^47 ->
QZDE.bytes_at JOB6SEGS m (g + 0x7fff8000) [Z_to_bv 8 0].
Proof.
intros g G1 G2.
pose proof (MV4 kz_band_view) as KZ. unfold KZ_BAND_V in KZ. cbn [kentry_ok] in KZ. destruct KZ as [_ KZ].
destruct (MV4 estart_VB) as (ES & EL). rewrite ES, EL in KZ. unfold GHI in KZ.
pose proof (MA main_atop_bounds) as AB.
assert (D : (atopE E + 4096) / 8 = atopE E / 8 + 512) by (replace (atopE E + 4096) with (atopE E + 512 * 8) by lia; apply Z.div_add; lia).
apply bytes_at_intro; [lia | cbn [length]; lia |].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r.
apply mrd_some. specialize (KZ (g + 0x7fff8000 - (0x7fff8000 + atopE E / 8 + 512)) ltac:(lia)).
replace (0x7fff8000 + atopE E / 8 + 512 + (g + 0x7fff8000 - (0x7fff8000 + atopE E / 8 + 512))) with (g + 0x7fff8000) in KZ by lia. exact KZ.
Qed.

Definition BSTAR : Z := Z.max (atopE E) (TOPP usp - 8388608).
Lemma BSTAR_facts : atopE E <= BSTAR <= atopE E + 3935 /\ BSTAR mod 8 = 0 /\ BSTAR <= 0x7fffff800000 /\ TOPP usp - 8388608 <= BSTAR.
Proof.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4). unfold STACK_MAX, CEIL in T4.
pose proof (MV4 atop_val) as AV. destruct Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2.
unfold BSTAR. rewrite AV.
split; [lia|]. split; [| split; lia].
destruct (Z.max_spec (usp - 8388608) (TOPP usp - 8388608)) as [[_ ->]|[_ ->]]; Z.div_mod_to_equations; lia.
Qed.
Theorem stack_shadow_main2 : forall g, BSTAR / 8 <= g -> 8 * g < 2^47 ->
QZDE.bytes_at JOB6SEGS m (g + 0x7fff8000) [Z_to_bv 8 0].
Proof.
intros g G1 G2. destruct BSTAR_facts as ((B1 & B2) & B3 & B4 & B5). pose proof (MA main_atop_bounds) as AB.
destruct (MV4 band_sh) as (S1 & S2).
assert (D1 : atopE E / 8 <= g) by (assert (atopE E / 8 <= BSTAR / 8) by (apply Z.div_le_mono; lia); lia).
assert (D2 : (TOPP usp - 8388608) / 8 <= g) by (assert ((TOPP usp - 8388608) / 8 <= BSTAR / 8) by (apply Z.div_le_mono; lia); lia).
apply bytes_at_intro; [lia | cbn [length]; lia |].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r.
apply mrd_some. unfold view, QQIi.mrestrict.
rewrite (MV4 view_stack_shadow) by (unfold GHI; lia).
apply (MA stack_shadow_zero). rewrite S1, S2. unfold GLO. rewrite u64_lit by lia. lia.
Qed.

Theorem vmlock_main : QZDE.bytes_at JOB6SEGS m 0x646db8 (QZDE.le4 (Z_to_bv 64 0)).
Proof.
destruct (MV4 small_bytes) as (_ & _ & _ & _ & [B _]).
replace (QZDE.le4 (Z_to_bv 64 0)) with (sc_bytes JOB6SEGS E 0x646db8 (VMLc w)); [exact B|]. destruct w; vm_compute; reflexivity.
Qed.
Theorem need_locks_main : QZDE.bytes_at JOB6SEGS m 0x6457b3 [Z_to_bv 8 0].
Proof.
destruct (MV4 small_bytes) as ([B _] & _).
replace [Z_to_bv 8 0] with (sc_bytes JOB6SEGS E 0x6457b3 (NLc w)); [exact B|]. destruct w; vm_compute; reflexivity.
Qed.
Theorem canary_copy_main : QZDE.bytes_at JOB6SEGS m 0x625510 (QZDE.le8 (ev E 45)).
Proof.
pose proof (cells_check_sound JOB6SEGS E m (kn_view ch) (MV4 main_know_view) CANc (ELit 0) 0x625510 (CAN_CHECKS w ch HCL)) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. specialize (X ltac:(lia) ltac:(cbn; lia)).
cbn [sc_bytes CANc edenot] in X. rewrite app_nil_r in X. exact X.
Qed.

Section StatA.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Theorem stat_main : QPUe.STAT_A Qwm6.Mq4.A4L (atopE E + 4096) (usp - 32)
QrOY.jo_STATC m.
Proof.
unfold QPUe.STAT_A. split; [| split].
- unfold QrOY.jo_STATC.
apply Forall_cons; [exact vmlock_main|]. apply Forall_cons; [cbn [fst snd]; rewrite HCAN; exact canary_copy_main|].
apply Forall_cons; [exact need_locks_main| apply Forall_nil].
- intros g G1 G2 G3. exact (stack_shadow_main g G1 G3).
- intros g G1 G2. rewrite REGS_EQ. exact (img_shadow_main g G1 G2).
Qed.

Theorem stat_main2 : QPUe.STAT_A Qwm6.Mq4.A4L BSTAR (usp - 32)
QrOY.jo_STATC m.
Proof.
destruct stat_main as (SC & _ & SI). split; [exact SC| split; [| exact SI]].
intros g G1 G2 G3. exact (stack_shadow_main2 g G1 G3).
Qed.
End StatA.
End Stat.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7S. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qk85.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8BV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8BV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb5q.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition REGSJ : list (Z * Z * Z) :=
if existsb (fun r => Z.eqb (fst (fst r)) 0xea960) QGcC.Mq0.tokA_reg_globals then QGcC.Mq0.tokA_reg_globals
else QGcC.Mq0.tokA_reg_globals ++ [(0xea960, 0, 6848)].
Definition SBJ : Z := 0x7fff8000.
Definition GLOJ : Z := 8192.
Definition GHIJ : Z := 821760.

Definition shimg_check (ch : acs) : bool :=
walk REGSJ SBJ (ivs_of (GLOJ + SBJ) (GHIJ + SBJ) (kn_view ch)) (GLOJ + SBJ) (GHIJ + SBJ) 400.
Lemma SHIMG_HS2sA_1_ok : shimg_check HS2sA_1 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sA_2_ok : shimg_check HS2sA_2 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sB_3_ok : shimg_check HS2sB_3 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_HS2sB_4_ok : shimg_check HS2sB_4 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma SHIMG_CHECKS : forall w ch, HSCLASS_S w ch -> shimg_check ch = true.
Proof. intros [|] ch [-> | ->]; [exact SHIMG_HS2sA_1_ok | exact SHIMG_HS2sA_2_ok | exact SHIMG_HS2sB_3_ok | exact SHIMG_HS2sB_4_ok]. Qed.

Lemma REGS_EQ {RC__ : Q6q3.RunConsts} : QZsi.hl_reg_globals Qwm6.Mq0.A4L = REGSJ.
Proof. change (QZsi.hl_reg_globals Qwm6.Mq0.A4L) with QGcC.Mq0.tokA_reg_globals. vm_compute. reflexivity. Qed.

Definition CANc : list scell := [SCw 8 (EVar 45)].
Lemma CAN_CHECKS : forall w ch, HSCLASS_S w ch -> cells_check JO6SEGS (kn_view ch) (ELit 0) 0x622e50 CANc = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Stat.
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
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation usp := (bv_unsigned sp).

Theorem img_shadow_main : forall g, 0x10000 <= 8 * g -> 8 * g + 8 <= 0x645000 ->
QZDE.bytes_at JO6SEGS m (g + 0x7fff8000) [Z_to_bv 8 (QZsi.img_shadow_val REGSJ g)].
Proof.
intros g G1 G2.
exact (img_shadow_closed JO6SEGS E m (kn_view ch) (MV4 main_know_view) REGSJ SBJ GLOJ GHIJ 400 (SHIMG_CHECKS w ch HCL)
ltac:(unfold GLOJ, SBJ; lia) ltac:(unfold GHIJ, SBJ; lia) g ltac:(unfold GLOJ, GHIJ; lia)).
Qed.

Theorem stack_shadow_main : forall g, (atopE E + 4096) / 8 <= g -> 8 * g < 2^47 ->
QZDE.bytes_at JO6SEGS m (g + 0x7fff8000) [Z_to_bv 8 0].
Proof.
intros g G1 G2.
pose proof (MV4 kz_band_view) as KZ. unfold KZ_BAND_V in KZ. cbn [kentry_ok] in KZ. destruct KZ as [_ KZ].
destruct (MV4 estart_VB) as (ES & EL). rewrite ES, EL in KZ. unfold GHI in KZ.
pose proof (MA main_atop_bounds) as AB.
assert (D : (atopE E + 4096) / 8 = atopE E / 8 + 512) by (replace (atopE E + 4096) with (atopE E + 512 * 8) by lia; apply Z.div_add; lia).
apply bytes_at_intro; [lia | cbn [length]; lia |].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r.
apply mrd_some. specialize (KZ (g + 0x7fff8000 - (0x7fff8000 + atopE E / 8 + 512)) ltac:(lia)).
replace (0x7fff8000 + atopE E / 8 + 512 + (g + 0x7fff8000 - (0x7fff8000 + atopE E / 8 + 512))) with (g + 0x7fff8000) in KZ by lia. exact KZ.
Qed.

Definition BSTAR : Z := Z.max (atopE E) (TOPP usp - 8388608).
Lemma BSTAR_facts : atopE E <= BSTAR <= atopE E + 3935 /\ BSTAR mod 8 = 0 /\ BSTAR <= 0x7fffff800000 /\ TOPP usp - 8388608 <= BSTAR.
Proof.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4). unfold STACK_MAX, CEIL in T4.
pose proof (MV4 atop_val) as AV. destruct Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2.
unfold BSTAR. rewrite AV.
split; [lia|]. split; [| split; lia].
destruct (Z.max_spec (usp - 8388608) (TOPP usp - 8388608)) as [[_ ->]|[_ ->]]; Z.div_mod_to_equations; lia.
Qed.
Theorem stack_shadow_main2 : forall g, BSTAR / 8 <= g -> 8 * g < 2^47 ->
QZDE.bytes_at JO6SEGS m (g + 0x7fff8000) [Z_to_bv 8 0].
Proof.
intros g G1 G2. destruct BSTAR_facts as ((B1 & B2) & B3 & B4 & B5). pose proof (MA main_atop_bounds) as AB.
destruct (MV4 band_sh) as (S1 & S2).
assert (D1 : atopE E / 8 <= g) by (assert (atopE E / 8 <= BSTAR / 8) by (apply Z.div_le_mono; lia); lia).
assert (D2 : (TOPP usp - 8388608) / 8 <= g) by (assert ((TOPP usp - 8388608) / 8 <= BSTAR / 8) by (apply Z.div_le_mono; lia); lia).
apply bytes_at_intro; [lia | cbn [length]; lia |].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r.
apply mrd_some. unfold view, QQIi.mrestrict.
rewrite (MV4 view_stack_shadow) by (unfold GHI; lia).
apply (MA stack_shadow_zero). rewrite S1, S2. unfold GLO. rewrite u64_lit by lia. lia.
Qed.

Theorem vmlock_main : QZDE.bytes_at JO6SEGS m 0x6446f8 (QZDE.le4 (Z_to_bv 64 0)).
Proof.
destruct (MV4 small_bytes) as (_ & _ & _ & _ & [B _]).
replace (QZDE.le4 (Z_to_bv 64 0)) with (sc_bytes JO6SEGS E 0x6446f8 (VMLc w)); [exact B|]. destruct w; vm_compute; reflexivity.
Qed.
Theorem need_locks_main : QZDE.bytes_at JO6SEGS m 0x6430f3 [Z_to_bv 8 0].
Proof.
destruct (MV4 small_bytes) as ([B _] & _).
replace [Z_to_bv 8 0] with (sc_bytes JO6SEGS E 0x6430f3 (NLc w)); [exact B|]. destruct w; vm_compute; reflexivity.
Qed.
Theorem canary_copy_main : QZDE.bytes_at JO6SEGS m 0x622e50 (QZDE.le8 (ev E 45)).
Proof.
pose proof (cells_check_sound JO6SEGS E m (kn_view ch) (MV4 main_know_view) CANc (ELit 0) 0x622e50 (CAN_CHECKS w ch HCL)) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. specialize (X ltac:(lia) ltac:(cbn; lia)).
cbn [sc_bytes CANc edenot] in X. rewrite app_nil_r in X. exact X.
Qed.

Section StatA.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Theorem stat_main : QPUe.STAT_A Qwm6.Mq0.A4L (atopE E + 4096) (usp - 32)
QrOY.Mq0.jo_STATC m.
Proof.
unfold QPUe.STAT_A. split; [| split].
- unfold QrOY.Mq0.jo_STATC.
apply Forall_cons; [exact vmlock_main|]. apply Forall_cons; [cbn [fst snd]; rewrite HCAN; exact canary_copy_main|].
apply Forall_cons; [exact need_locks_main| apply Forall_nil].
- intros g G1 G2 G3. exact (stack_shadow_main g G1 G3).
- intros g G1 G2. rewrite REGS_EQ. exact (img_shadow_main g G1 G2).
Qed.

Theorem stat_main2 : QPUe.STAT_A Qwm6.Mq0.A4L BSTAR (usp - 32)
QrOY.Mq0.jo_STATC m.
Proof.
destruct stat_main as (SC & _ & SI). split; [exact SC| split; [| exact SI]].
intros g G1 G2 G3. exact (stack_shadow_main2 g G1 G3).
Qed.
End StatA.
End Stat.
