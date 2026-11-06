(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QCcH Q7UD Qwm6 QGcC QZsi QYZ0 QQIi Qsn5 QBrp QCUT QoSL QMow QlES Q6sh QzgH QgTJ QCrt QcGV QNLn QtIP QU91 QuLP QPUe QrOY QvG1 Qp4j QDw3 QpY2 Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi.
Import Qsn5 QBrp.

Import QlES.

Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition zone_zero (lo : Z) (n : nat) : bool :=
forallb (fun i => Z.eqb (QZsi.img_shadow_val QGcC.Mq0.tokA_reg_globals (lo + Z.of_nat i)) 0) (seq 0 n).
Lemma zone_zero_sound : forall lo n g, zone_zero lo n = true -> lo <= g < lo + Z.of_nat n -> QZsi.img_shadow_val QGcC.Mq0.tokA_reg_globals g = 0.
Proof.
intros lo n g H Hg. unfold zone_zero in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (g - lo)) ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. replace (lo + Z.of_nat (Z.to_nat (g - lo))) with g in H by lia. exact H.
Qed.
Lemma ZONE1 : zone_zero 0x2000 0x2610 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma ZONE3 : zone_zero 0xc86b8 0x88 = true.  Proof. vm_compute. reflexivity. Qed.

Section Pfrt.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX RE FR0.
Hypothesis RUN_botj : Q6q3.alloc_ceiling <= BOTJ.
Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.

Definition BANDP : Band := mkBand BOTJ (conj (Z.le_trans _ _ _ (proj1 (@Q6q3.alloc_ceiling_range RC__)) RUN_botj) BOT_cap) Q6q3.rc_canary.

Notation DLj := (@QuLP.DL_AR (QuLP.Band_RC Q6q3.rc_canary)).
Notation DCoj := (QuLP.DCo_jo Q6q3.rc_canary LV).
Notation H63 := (QU91.HEAPA63 Qwm6.Mq0.A4L LV PERM0 TMAX NMAX DLj RE DCoj FR0 QrOY.Mq0.MJ.S_AJ BAUX (QPUe.STAT_A Qwm6.Mq0.A4L BOTJ TOPJ QrOY.Mq0.jo_STATC)).

Theorem ish_of_heapA63 : forall A LB LM FR B m c, H63 A LB LM FR B m c -> @Q9Ho.Mq0.ISH BANDP m.
Proof.
intros A LB LM FR B m c ((g & Lg & H & Bc & Tc & Nc & s & LB0 & (ps & LBd & FSd & RUN & _) & KL & HP) & _).
do 14 (destruct HP as [_ HP]). destruct HP as (SC & SS & SI).
destruct HS as (LL0 & _ & Hsegs & _ & _ & _ & _ & SEGLOW & _ & FR0_off & _ & _).
pose proof (QU91.KLA_F_off Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX LL0 Hsegs SEGLOW FR0 FR0_off _ Lg g c H m Bc Tc Nc KL) as FOFF.
unfold QuLP.DCo_jo, QuLP.DCo_AR_rc, QuLP.DCo_AR in RUN. cbn [QCrt.dc_run] in RUN. unfold QuLP.run_AR in RUN.
pose proof (QDw3.ai_rt_consts _ _ _ _ _ _ _ _ _ RUN) as RTC.
pose proof (QDw3.ai_shadow_base _ _ _ _ _ _ _ _ _ RUN) as SHB.
assert (RO : forall a cs, QoSL.ro_cells QvG1.asegs (mrestrict (QgTJ.Mq1.Fof LV (QtIP.FRof FR0 Lg)) m) a cs ->
QoSL.ro_cells QvG1.asegs m a cs).
{ intros a cs [WF BA]. split; [exact WF| exact (QcGV.bytes_at_unhide _ _ FOFF m _ _ BA)]. }
assert (RW : forall a cs, QoSL.rw_cells QvG1.asegs (mrestrict (QgTJ.Mq1.Fof LV (QtIP.FRof FR0 Lg)) m) a cs ->
QoSL.rw_cells QvG1.asegs m a cs).
{ intros a cs [R W]. split; [exact (RO a cs R)| exact (QcGV.wr_at_unhide _ _ FOFF m _ _ W)]. }
clear RUN KL.
split; [| split].
-
unfold Q9Ho.Mq0.ash. cbn [band_lo BANDP].
change (QtIP.JH.hl_sb Qwm6.Mq0.A4L) with 0x7fff8000 in SS, SI.
change (QtIP.JH.hl_reg_globals Qwm6.Mq0.A4L) with QGcC.Mq0.tokA_reg_globals in SI.
change (QtIP.HI.hl_img_lo (QtIP.JH.hla_base Qwm6.Mq0.A4L)) with 0x10000 in SI. change (QtIP.HI.hl_img_hi (QtIP.JH.hla_base Qwm6.Mq0.A4L)) with 0x645000 in SI.
split; [| split]; intros i Hi.
+ pose proof (SI (0x2000 + i) ltac:(lia) ltac:(lia)) as X. rewrite (zone_zero_sound 0x2000 0x2610 _ ZONE1) in X by lia.
replace (0x7fffa000 + i) with (0x2000 + i + 0x7fff8000) by lia. exact X.
+ unfold Qp4j.SH, QvG1.A_SHADOW_OFS, QzgH.KHI, Qqcs.Mq0.kHighMemBeg in *.
pose proof (@Q6q3.alloc_ceiling_range RC__) as ACR.
assert (0 <= BOTJ / 8) by (apply Z.div_pos; lia).
unfold QvG1.KHI in Hi.
pose proof (SS (BOTJ / 8 + i) ltac:(lia) ltac:(lia) ltac:(lia)) as X.
replace (BOTJ / 8 + 0x7fff8000 + i) with (BOTJ / 8 + i + 0x7fff8000) by lia. exact X.
+ pose proof (SI (0xc86b8 + i) ltac:(lia) ltac:(lia)) as X. rewrite (zone_zero_sound 0xc86b8 0x88 _ ZONE3) in X by lia.
replace (0x800c06b8 + i) with (0xc86b8 + i + 0x7fff8000) by lia. exact X.
-
unfold QDw3.rt_consts_at in *. cbn [band_guard BANDP QuLP.Band_RC] in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end; first [apply RO; assumption | apply RW; assumption].
- destruct SHB as [S1 S2]. split; apply RO; assumption.
Qed.
End Pfrt.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBzu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition zone_zero (lo : Z) (n : nat) : bool :=
forallb (fun i => Z.eqb (QZsi.img_shadow_val QGcC.tokA_reg_globals (lo + Z.of_nat i)) 0) (seq 0 n).
Lemma zone_zero_sound : forall lo n g, zone_zero lo n = true -> lo <= g < lo + Z.of_nat n -> QZsi.img_shadow_val QGcC.tokA_reg_globals g = 0.
Proof.
intros lo n g H Hg. unfold zone_zero in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (g - lo)) ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. replace (lo + Z.of_nat (Z.to_nat (g - lo))) with g in H by lia. exact H.
Qed.
Lemma ZONE1 : zone_zero 0x2000 0x2618 = true.  Proof. vm_compute. reflexivity. Qed.
Lemma ZONE3 : zone_zero 0xc8b90 0x88 = true.  Proof. vm_compute. reflexivity. Qed.

Section Pfrt.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq4.A4L LA LV PERM0 TMAX NMAX RE FR0.
Hypothesis RUN_botj : Q6q3.alloc_ceiling <= BOTJ.
Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.

Definition BANDP : Band := mkBand BOTJ (conj (Z.le_trans _ _ _ (proj1 (@Q6q3.alloc_ceiling_range RC__)) RUN_botj) BOT_cap) Q6q3.rc_canary.

Notation DLj := (@QBzu.DL_AR (QBzu.Band_RC Q6q3.rc_canary)).
Notation DCoj := (QBzu.DCo_jo Q6q3.rc_canary LV).
Notation H63 := (QU91.HEAPA63 Qwm6.Mq4.A4L LV PERM0 TMAX NMAX DLj RE DCoj FR0 QrOY.MJ.S_AJU BAUX (QPUe.STAT_A Qwm6.Mq4.A4L BOTJ TOPJ QrOY.jo_STATC)).

Theorem ish_of_heapA63 : forall A LB LM FR B m c, H63 A LB LM FR B m c -> @Q9Ho.ISH BANDP m.
Proof.
intros A LB LM FR B m c ((g & Lg & H & Bc & Tc & Nc & s & LB0 & (ps & LBd & FSd & RUN & _) & KL & HP) & _).
do 14 (destruct HP as [_ HP]). destruct HP as (SC & SS & SI).
destruct HS as (LL0 & _ & Hsegs & _ & _ & _ & _ & SEGLOW & _ & FR0_off & _ & _).
pose proof (QU91.KLA_F_off Qwm6.Mq4.A4L LA LV PERM0 TMAX NMAX LL0 Hsegs SEGLOW FR0 FR0_off _ Lg g c H m Bc Tc Nc KL) as FOFF.
unfold QBzu.DCo_jo, QBzu.DCo_AR_rc, QBzu.DCo_AR in RUN. cbn [QCrt.dc_run] in RUN. unfold QBzu.run_AR in RUN.
pose proof (QWRO.ai_rt_consts _ _ _ _ _ _ _ _ _ RUN) as RTC.
pose proof (QWRO.ai_shadow_base _ _ _ _ _ _ _ _ _ RUN) as SHB.
assert (RO : forall a cs, QoSL.ro_cells QZzg.asegs (mrestrict (QgTJ.Mq1.Fof LV (QtIP.FRof FR0 Lg)) m) a cs ->
QoSL.ro_cells QZzg.asegs m a cs).
{ intros a cs [WF BA]. split; [exact WF| exact (QcGV.bytes_at_unhide _ _ FOFF m _ _ BA)]. }
assert (RW : forall a cs, QoSL.rw_cells QZzg.asegs (mrestrict (QgTJ.Mq1.Fof LV (QtIP.FRof FR0 Lg)) m) a cs ->
QoSL.rw_cells QZzg.asegs m a cs).
{ intros a cs [R W]. split; [exact (RO a cs R)| exact (QcGV.wr_at_unhide _ _ FOFF m _ _ W)]. }
clear RUN KL.
split; [| split].
-
unfold Q9Ho.ash. cbn [band_lo BANDP].
change (QtIP.JH.hl_sb Qwm6.Mq4.A4L) with 0x7fff8000 in SS, SI.
change (QtIP.JH.hl_reg_globals Qwm6.Mq4.A4L) with QGcC.tokA_reg_globals in SI.
change (QtIP.HI.hl_img_lo (QtIP.JH.hla_base Qwm6.Mq4.A4L)) with 0x10000 in SI. change (QtIP.HI.hl_img_hi (QtIP.JH.hla_base Qwm6.Mq4.A4L)) with 0x647000 in SI.
split; [| split]; intros i Hi.
+ pose proof (SI (0x2000 + i) ltac:(lia) ltac:(lia)) as X. rewrite (zone_zero_sound 0x2000 0x2618 _ ZONE1) in X by lia.
replace (0x7fffa000 + i) with (0x2000 + i + 0x7fff8000) by lia. exact X.
+ unfold Q61C.SH, QZzg.A_SHADOW_OFS, QzgH.KHI, Qqcs.Mq0.kHighMemBeg in *.
pose proof (@Q6q3.alloc_ceiling_range RC__) as ACR.
assert (0 <= BOTJ / 8) by (apply Z.div_pos; lia).
unfold QZzg.KHI in Hi.
pose proof (SS (BOTJ / 8 + i) ltac:(lia) ltac:(lia) ltac:(lia)) as X.
replace (BOTJ / 8 + 0x7fff8000 + i) with (BOTJ / 8 + i + 0x7fff8000) by lia. exact X.
+ pose proof (SI (0xc8b90 + i) ltac:(lia) ltac:(lia)) as X. rewrite (zone_zero_sound 0xc8b90 0x88 _ ZONE3) in X by lia.
replace (0x800c0b90 + i) with (0xc8b90 + i + 0x7fff8000) by lia. exact X.
-
unfold QWRO.rt_consts_at in *. cbn [band_guard BANDP QBzu.Band_RC] in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end; first [apply RO; assumption | apply RW; assumption].
- destruct SHB as [S1 S2]. split; apply RO; assumption.
Qed.
End Pfrt.
