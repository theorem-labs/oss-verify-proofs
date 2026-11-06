(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition gtab (g0 : Z) : list byte := map (fun i => Z_to_bv 8 (QZsi.img_shadow_val QGcC.tokA_reg_globals (g0 + Z.of_nat i))) (seq 0 8).
Lemma GTAB1 : gtab 0x46e0 = QXE1.GSHW1.  Proof. vm_compute. reflexivity. Qed.
Lemma GTAB2 : gtab 0x46e8 = QXE1.GSHW2.  Proof. vm_compute. reflexivity. Qed.
Lemma GTAB3 : gtab 0x46f0 = QXE1.GSHW3.  Proof. vm_compute. reflexivity. Qed.

Lemma bytes_at_octet : forall (m : word -> option byte) (g0 : Z),
0 <= g0 -> g0 + 0x7fff8000 + 8 <= 2^64 ->
(forall i, (i < 8)%nat -> QCUT.bytes_at QZzg.asegs m (g0 + Z.of_nat i + 0x7fff8000) [Z_to_bv 8 (QZsi.img_shadow_val QGcC.tokA_reg_globals (g0 + Z.of_nat i))]) ->
QCUT.bytes_at QZzg.asegs m (g0 + 0x7fff8000) (gtab g0).
Proof.
intros m g0 H0 H1 H. split; [lia|]. split; [unfold gtab; rewrite length_map, length_seq; lia|].
intros i Hi. unfold gtab in Hi. rewrite length_map, length_seq in Hi.
destruct (H i Hi) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in HB. rewrite Z.add_0_r in HB.
replace (g0 + 0x7fff8000 + Z.of_nat i) with (g0 + Z.of_nat i + 0x7fff8000) by lia. rewrite HB.
unfold gtab. rewrite nth_error_map, nth_error_seq. replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add]. reflexivity.
Qed.

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

Notation BANDP := (QJny.BANDP BOTJ RUN_botj BOT_cap).
Notation DLj := (@QBzu.DL_AR (QBzu.Band_RC Q6q3.rc_canary)).
Notation DCoj := (QBzu.DCo_jo Q6q3.rc_canary LV).
Notation H63 := (QU91.HEAPA63 Qwm6.Mq4.A4L LV PERM0 TMAX NMAX DLj RE DCoj FR0 QrOY.MJ.S_AJU BAUX (QPUe.STAT_A Qwm6.Mq4.A4L BOTJ TOPJ QrOY.jo_STATC)).

Theorem ishG_of_heapA63 : forall A LB LM FR B m c, H63 A LB LM FR B m c -> @QXE1.ISH BANDP m.
Proof.
intros A LB LM FR B m c HP.
apply QXE1.ISH_of_AR; [exact (QJny.ish_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS RUN_botj BOT_cap A LB LM FR B m c HP)|].
destruct HP as ((g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & KL & HP) & _).
do 14 (destruct HP as [_ HP]). destruct HP as (SC & SS & SI).
change (QtIP.JH.hl_sb Qwm6.Mq4.A4L) with 0x7fff8000 in SI.
change (QtIP.JH.hl_reg_globals Qwm6.Mq4.A4L) with QGcC.tokA_reg_globals in SI.
change (QtIP.HI.hl_img_lo (QtIP.JH.hla_base Qwm6.Mq4.A4L)) with 0x10000 in SI. change (QtIP.HI.hl_img_hi (QtIP.JH.hla_base Qwm6.Mq4.A4L)) with 0x647000 in SI.
unfold QXE1.gsh. rewrite <- GTAB1, <- GTAB2, <- GTAB3. split; [| split].
- change 0x7fffc6e0 with (0x46e0 + 0x7fff8000). apply bytes_at_octet; [lia | lia |]. intros i Hi. apply SI; lia.
- change 0x7fffc6e8 with (0x46e8 + 0x7fff8000). apply bytes_at_octet; [lia | lia |]. intros i Hi. apply SI; lia.
- change 0x7fffc6f0 with (0x46f0 + 0x7fff8000). apply bytes_at_octet; [lia | lia |]. intros i Hi. apply SI; lia.
Qed.
End Pfrt.
