(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiu2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3k2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRcT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJny. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section GetString.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq4.A4L LA LV PERM0 TMAX NMAX RE FR0.
Variable r1 : exists iv, In iv (lv_base LV) /\ fst iv <= QCcH.hl_img_lo (QZsi.hla_base Qwm6.Mq4.A4L) /\ QCcH.hl_img_hi (QZsi.hla_base Qwm6.Mq4.A4L) <= snd iv.
Variable r2 : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Variable r3 : forall x, QgTJ.Mq1.Fof LV FR0 x = true ->
~ (QYZ0.mg_data_lo QrOY.MJ.S_AJU <= bv_unsigned x < QYZ0.mg_img_hi QrOY.MJ.S_AJU).
Variable r4 : Q6q3.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Variable r5 : Q6q3.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Variable r6 : TOPJ + 64 <= BAUX.
Variable r7 : TOPJ + 64 <= QCrt.ae_stack_top RE + 4096.
Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.
Hypothesis BOT_near : BOTJ <= Q6q3.alloc_ceiling + 4096.

Definition H6_gs : QZsi.heap_iface_A Qwm6.Mq4.A4L := QrOY.hiA_jo LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7.
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6_gs).
#[local] Notation BANDP := (QJny.BANDP BOTJ (proj1 r4) BOT_cap).

Lemma obl_pfrt_gs : forall A LB LM FRS B m md, Qhd4.HEAPA Qwm6.Mq4.A4L HIx A LB LM FRS B m md -> @QXE1.ISH BANDP m.
Proof.
intros A LB LM FRS B m md (B6 & HP6 & _).
exact (Qvsj.ishG_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS (proj1 r4) BOT_cap A LB LM FRS B6 m md HP6).
Qed.

Theorem serval_jo : Q9O6.Mq5.SERVALA HIx.
Proof.
exact (QRcT.Mq2.servalA HIx (Qiu2.realloc_nf_of_v6 H6_gs)
(@QXE1.ISH BANDP) Q6q3.alloc_ceiling obl_pfrt_gs (Z.le_refl _)
(@Q3k2.isnprintf_ld_inst RC__ BANDP BOT_near) (@Q3k2.isnprintf_lu_inst RC__ BANDP BOT_near) (@Q3k2.isnprintf_u00cc_inst RC__ BANDP BOT_near)).
Qed.

Theorem get_string_jo :
QJZd.Mq9.jo_get_string_A_stmt HIx QC6R.JO_GET_STRING_A
QiVi.Mq6.AGET_STRING_STACK QiVi.Mq6.gsB.
Proof. exact (QiVi.Mq6.get_string_A HIx serval_jo). Qed.
End GetString.
