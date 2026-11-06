(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QCcH Q0Ek Q7UD Qwm6 QZsi Qhd4 QYZ0 QgHv Qiu2 Q9O6 QlKV Q3k2 QRcT QiVi QJZd QOmG QQIi Qsn5 QBrp QlES Q6sh QgTJ QCrt QU91 QrOY QXE1 QJny Qv81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi.
Import Qsn5 QBrp.
Import QlES.

Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX RE FR0.
Variable r1 : exists iv, In iv (lv_base LV) /\ fst iv <= QCcH.hl_img_lo (QZsi.hla_base Qwm6.Mq0.A4L) /\ QCcH.hl_img_hi (QZsi.hla_base Qwm6.Mq0.A4L) <= snd iv.
Variable r2 : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Variable r3 : forall x, QgTJ.Mq1.Fof LV FR0 x = true ->
~ (QYZ0.mg_data_lo QrOY.Mq0.MJ.S_AJ <= bv_unsigned x < QYZ0.mg_img_hi QrOY.Mq0.MJ.S_AJ).
Variable r4 : Q6q3.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Variable r5 : Q6q3.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Variable r6 : TOPJ + 64 <= BAUX.
Variable r7 : TOPJ + 64 <= QCrt.ae_stack_top RE + 4096.
Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.
Hypothesis BOT_near : BOTJ <= Q6q3.alloc_ceiling + 4096.

Definition H6_gs : QZsi.heap_iface_A Qwm6.Mq0.A4L := QrOY.Mq0.hiA_jo LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7.
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6_gs).
#[local] Notation BANDP := (QJny.Mq0.BANDP BOTJ (proj1 r4) BOT_cap).

Lemma obl_pfrt_gs : forall A LB LM FRS B m md, Qhd4.HEAPA Qwm6.Mq0.A4L HIx A LB LM FRS B m md -> @QXE1.Mq0.ISH BANDP m.
Proof.
intros A LB LM FRS B m md (B6 & HP6 & _).
exact (Qv81.ishG_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS (proj1 r4) BOT_cap A LB LM FRS B6 m md HP6).
Qed.

Theorem serval_jo : Q9O6.Mq2.SERVALA HIx.
Proof.
exact (QRcT.servalA HIx (Qiu2.Mq0.realloc_nf_of_v6 H6_gs)
(@QXE1.Mq0.ISH BANDP) Q6q3.alloc_ceiling obl_pfrt_gs (Z.le_refl _)
(@Q3k2.Mq0.isnprintf_ld_inst RC__ BANDP BOT_near) (@Q3k2.Mq0.isnprintf_lu_inst RC__ BANDP BOT_near) (@Q3k2.Mq0.isnprintf_u00cc_inst RC__ BANDP BOT_near)).
Qed.

Theorem get_string_jo :
QJZd.Mq0.jo_get_string_A_stmt HIx QOmG.JO_GET_STRING_A
QiVi.Mq3.AGET_STRING_STACK QiVi.Mq3.gsB.
Proof. exact (QiVi.Mq3.get_string_A HIx serval_jo). Qed.
End GetString.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QupI QdM4 QXcG QBzu QPUe Q8dS QdSl Q1LT QpvH QVWI QXVi QyaF Q45h QOTx Q25t QoL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.

Import Qsn5.

Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section PerState.
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
Variables (E : Qt8n.AX2.env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : QOTP.AP.acs.
Hypothesis HCL : Q45h.HSCLASS_S w ch.
Hypothesis CS : Q1LT.APS.cs_ok QXVi.JOB6SEGS QyaF.BJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QXVi.JOB6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QXVi.JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Let RCJ : Q6q3.RunConsts := QoL1.Mq0.RCJ sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
#[local] Existing Instance RCJ.
#[local] Notation LV := (Q25t.LV_J E).
#[local] Notation usp := (bv_unsigned sp).

Variable LA : Q6sh.ALay.
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

Definition H6_jo : QZsi.heap_iface_A Qwm6.Mq4.A4L := QrOY.hiA_jo LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7.
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6_jo).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : QupI.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv0 USP A LB LM FR B m md, @QupI.drvA_mem argv0 USP m -> Qhd4.HEAPA Qwm6.Mq4.A4L HIx A LB LM FR B m md -> GA m.

Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.

Variable LM0 : list QCcH.blk.
Variable B0 : QZsi.bud.
Variable LO : Z.
Variable ms0 : machine_state.
Hypothesis Hms0 : ms_mem ms0 = FULL.
Hypothesis HH : QU91.Mq0.handoff_heap Qwm6.Mq4.A4L LV PERM0 TMAX NMAX (@QBzu.DL_AR (QBzu.Band_RC Q6q3.rc_canary)) RE
(QBzu.DCo_jo Q6q3.rc_canary LV) FR0 QrOY.MJ.S_AJU BAUX (QPUe.STAT_A Qwm6.Mq4.A4L BOTJ TOPJ QrOY.jo_STATC)
(QZsi.bM B0) LM0 B0 (mkCfg ms0 mo).
Hypothesis HLM40 : Forall (fun b : QCcH.blk => snd b < 2^40) LM0.
Hypothesis HLMS : Z.of_nat (length LM0) < 8.
Hypothesis HBB39 : QZsi.bB B0 + 2^23 <= 2^39.
Hypothesis HBQ0 : 0 <= QZsi.bQ B0.
Hypothesis HBQ : QXcG.Mq0.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0.
Hypothesis HBB : QXcG.Mq0.DRVA6_BB TGT_BB_A <= QZsi.bB B0.
Hypothesis HBN : QXcG.Mq0.DRVA6_BN TGT_BB_A <= QZsi.bN B0.
Hypothesis HBD : QXcG.Mq0.DRVA6_BD TGT_BD_A <= QZsi.bD B0.
Hypothesis HBM : QXcG.Mq0.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0.
Hypothesis HTS : 0 <= TGT_STACK_A <= 2^21.
Hypothesis HTB : 0 <= TGT_BB_A.
Hypothesis HTB6 : 1536 + 4 * TGT_BB_A <= 2^30.
Hypothesis HTD : 0 <= TGT_BD_A.
Hypothesis HTOP : usp <= TOPJ + 160.
Hypothesis HBOT : BOTJ <= LO.
Hypothesis HLO1 : usp - 8388608 <= LO.
Hypothesis HLO2 : LO + 2^22 <= usp - 48.

Theorem handoff_rest_jo : QoL1.Mq0.handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
refine (QoL1.Mq0.HandoffRest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(proj1 (proj2 HS)) (proj1 (proj2 (proj2 HS))) (proj1 (proj2 (proj2 (proj2 HS)))) (proj1 (proj2 (proj2 (proj2 (proj2 HS)))))
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))
H6_jo eq_refl GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of (QJny.BANDP BOTJ (proj1 r4) BOT_cap) _ (Z.le_refl BOTJ) tt LM0 B0 LO _ HLMS HBQ HBB HBN HBD HBM HTS HTB HTB6 HTD HTOP HBOT HLO1 HLO2).
- intros A LB LM FR B m md (B6 & HP6 & _).
exact (QJny.ish_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS (proj1 r4) BOT_cap A LB LM FR B6 m md HP6).
- intros ms Hms.
exact (Q8dS.hiA_jo_at_main LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7 LM0 B0 mo FULL ms0 Hms0 HH HLM40 HBB39 HBQ0 ms Hms).
Qed.
End PerState.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8dS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdSl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJny.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section PerState.
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
Variables (E : Qt8n.AX2.env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : QOTP.AP.acs.
Hypothesis HCL : QrQA.HSCLASS_S w ch.
Hypothesis CS : Q1LT.APS.cs_ok QLPb.JO6SEGS QCoy.AJO6
QVWI.Mq0.LIMIT (bv_unsigned sp) (QpvH.SINV0 QLPb.JO6PH sp rdraw brk0 argv envp uid hw)
(QpvH.argH0 QLPb.JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Let RCJ : Q6q3.RunConsts := QoL1.RCJ sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
#[local] Existing Instance RCJ.
#[local] Notation LV := (QFop.LV_J E).
#[local] Notation usp := (bv_unsigned sp).

Variable LA : Q6sh.ALay.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX RE FR0.
Variable r1 : exists iv, In iv (lv_base LV) /\ fst iv <= QCcH.hl_img_lo (QZsi.hla_base Qwm6.Mq0.A4L) /\ QCcH.hl_img_hi (QZsi.hla_base Qwm6.Mq0.A4L) <= snd iv.
Variable r2 : exists iv, In iv (lv_base LV) /\ fst iv <= BOTJ /\ 2^47 <= snd iv.
Variable r3 : forall x, QgTJ.Mq1.Fof LV FR0 x = true ->
~ (QYZ0.mg_data_lo QrOY.Mq0.MJ.S_AJ <= bv_unsigned x < QYZ0.mg_img_hi QrOY.Mq0.MJ.S_AJ).
Variable r4 : Q6q3.alloc_ceiling <= BOTJ /\ BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.
Variable r5 : Q6q3.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Variable r6 : TOPJ + 64 <= BAUX.
Variable r7 : TOPJ + 64 <= QCrt.ae_stack_top RE + 4096.

Definition H6_jo : QZsi.heap_iface_A Qwm6.Mq0.A4L := QrOY.Mq0.hiA_jo LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7.
#[local] Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6_jo).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : Q2y2.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv0 USP A LB LM FR B m md, @Q2y2.drvA_mem argv0 USP m -> Qhd4.HEAPA Qwm6.Mq0.A4L HIx A LB LM FR B m md -> GA m.

Hypothesis BOT_cap : BOTJ <= 0x7fffff800000.

Variable LM0 : list QCcH.blk.
Variable B0 : QZsi.bud.
Variable LO : Z.
Variable ms0 : machine_state.
Hypothesis Hms0 : ms_mem ms0 = FULL.
Hypothesis HH : QU91.Mq0.handoff_heap Qwm6.Mq0.A4L LV PERM0 TMAX NMAX (@QuLP.DL_AR (QuLP.Band_RC Q6q3.rc_canary)) RE
(QuLP.DCo_jo Q6q3.rc_canary LV) FR0 QrOY.Mq0.MJ.S_AJ BAUX (QPUe.STAT_A Qwm6.Mq0.A4L BOTJ TOPJ QrOY.Mq0.jo_STATC)
(QZsi.bM B0) LM0 B0 (mkCfg ms0 mo).
Hypothesis HLM40 : Forall (fun b : QCcH.blk => snd b < 2^40) LM0.
Hypothesis HLMS : Z.of_nat (length LM0) < 8.
Hypothesis HBB39 : QZsi.bB B0 + 2^23 <= 2^39.
Hypothesis HBQ0 : 0 <= QZsi.bQ B0.
Hypothesis HBQ : QXcG.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0.
Hypothesis HBB : QXcG.DRVA6_BB TGT_BB_A <= QZsi.bB B0.
Hypothesis HBN : QXcG.DRVA6_BN TGT_BB_A <= QZsi.bN B0.
Hypothesis HBD : QXcG.DRVA6_BD TGT_BD_A <= QZsi.bD B0.
Hypothesis HBM : QXcG.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0.
Hypothesis HTS : 0 <= TGT_STACK_A <= 2^21.
Hypothesis HTB : 0 <= TGT_BB_A.
Hypothesis HTB6 : 1536 + 4 * TGT_BB_A <= 2^30.
Hypothesis HTD : 0 <= TGT_BD_A.
Hypothesis HTOP : usp <= TOPJ + 160.
Hypothesis HBOT : BOTJ <= LO.
Hypothesis HLO1 : usp - 8388608 <= LO.
Hypothesis HLO2 : LO + 2^22 <= usp - 48.

Theorem handoff_rest_jo : QoL1.handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.
Proof.
refine (QoL1.HandoffRest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS
(proj1 (proj2 HS)) (proj1 (proj2 (proj2 HS))) (proj1 (proj2 (proj2 (proj2 HS)))) (proj1 (proj2 (proj2 (proj2 (proj2 HS)))))
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))
H6_jo eq_refl GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of (QJny.Mq0.BANDP BOTJ (proj1 r4) BOT_cap) _ (Z.le_refl BOTJ) tt LM0 B0 LO _ HLMS HBQ HBB HBN HBD HBM HTS HTB HTB6 HTD HTOP HBOT HLO1 HLO2).
- intros A LB LM FR B m md (B6 & HP6 & _).
exact (QJny.Mq0.ish_of_heapA63 LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS (proj1 r4) BOT_cap A LB LM FR B6 m md HP6).
- intros ms Hms.
exact (Q8dS.Mq0.hiA_jo_at_main LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS r1 r2 r3 r4 r5 r6 r7 LM0 B0 mo FULL ms0 Hms0 HH HLM40 HBB39 HBQ0 ms Hms).
Qed.
End PerState.
