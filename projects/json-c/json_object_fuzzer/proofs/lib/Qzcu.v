(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QBxa Q6q3 QWxq_c1 QsjA QCcH Q7UD Qwm6 QZsi Qhd4 Q0TL Q2y2 QdM4 QXcG QbKA QQIi QdTb Q1lV Qcrs QUcd QCUT QwAs Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO Q6sh QNqr QLiw QCrt QRGF QlES Q9Ho QX7n QcGV QtIP QU91 QrOY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi QdTb Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.

Import QNqr QNqr.Mq0 QLiw.Mq0.

Import QRGF.

Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section MainPhase.
Context {RC__ : Q6q3.RunConsts}.
Notation asegs := Q7UD.asegs.

Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap asegs.
Hypothesis Hsegs : segs_in_base LV asegs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Variable H6 : QZsi.heap_iface_A Qwm6.Mq0.A4L.
Hypothesis H6_J : QZsi.hiA_J Qwm6.Mq0.A4L H6 = aj_base_vj asegs LV Hwx Hsegs.
Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6).
Notation Jx := (Qhd4.hiA_J Qwm6.Mq0.A4L HIx).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : Q2y2.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv USP A LB LM FR B m md, Q2y2.drvA_mem argv USP m -> Qhd4.HEAPA Qwm6.Mq0.A4L HIx A LB LM FR B m md -> GA m.

Variable BANDS : QlES.Band.
Hypothesis OBL_ISH : forall A LB LM FR B m md, Qhd4.HEAPA Qwm6.Mq0.A4L HIx A LB LM FR B m md -> @Q9Ho.Mq0.ISH BANDS m.
Hypothesis OBL_BLO : @QlES.band_lo BANDS <= Qhd4.hiA_bot Qwm6.Mq0.A4L HIx.

Lemma SYS_jo : forall (F : QsRG.Mq0.FPF) (fc : QsRG.Mq0.FPC),
@Q0TL.aj_sys F fc asegs Jx.
Proof.
intros F fc. change Jx with (QZsi.hiA_J Qwm6.Mq0.A4L H6). rewrite H6_J.
exact (@QbKA.Mq1.aj_sys_vj F fc asegs LV Hwx Hsegs Hsh Hbx Hbc).
Qed.

Theorem main_phase_jo : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A0 : QZsi.ASA Qwm6.Mq0.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (argv : list (list byte)) (USP LO : Z),

cinvA LV (cfg_ms md) (cfg_model md) -> m_halted (cfg_model md) = None ->
msview LV (cfg_model md) (cfg_ms md) =
MS (QWxq_c1.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 Q2y2.MAIN_A) fc None m (seg_rom asegs) ->

valid_argv argv ->
Q2y2.drvA_pre argv USP LO m (cfg_model md) ->
QZsi.HEAPA Qwm6.Mq0.A4L H6 A0 [] LM0 [] B0 m md ->
Z.of_nat (length LM0) < 8 ->
QXcG.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
USP <= QZsi.hiA_top Qwm6.Mq0.A4L H6 + 160 -> QZsi.hiA_bot Qwm6.Mq0.A4L H6 <= LO ->
ra = Z_to_bv 64 Q2y2.RA_MAIN -> sp = Z_to_bv 64 (USP - 48) ->
gp = Z_to_bv 64 Q2y2.A_GP -> tp = Z_to_bv 64 Qwm6.Mq0.A_TP ->
a0 = Z_to_bv 64 (Z.of_nat (length argv)) -> a1 = Z_to_bv 64 (USP + 8) ->
Qc3B.frm0 fc ->
srealizes asegs md (QBxa.Mq5.spec argv (m_fs (cfg_model md))).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A0 LM0 B0 argv USP LO
HC Hh HV VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT Era Esp Egp Etp Ea0 Ea1 FRM.
apply (main_phase_cps asegs LV _ md HC Hh). rewrite HV.
assert (STD : forall (P : QZsi.aj_base asegs -> Prop), P (aj_base_vj asegs LV Hwx Hsegs) -> P Jx)
by (intros P HPx; change Jx with (QZsi.hiA_J Qwm6.Mq0.A4L H6); rewrite H6_J; exact HPx).
pose proof (QXcG.driver_A_ok6 H6 SYS_jo GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of (@Q9Ho.Mq0.ISH BANDS) (@QlES.band_lo BANDS) OBL_ISH OBL_BLO
(STD (fun J => QdM4.Mq0.emitpf1_stmt J _ _) (@QX7n.Mq0.pf1_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq0.emitpfk_stmt J _ _) (@QX7n.Mq0.pfk_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq0.fprintf_u_stmt J _ _) (@QX7n.Mq0.fprintf_u_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq0.fwrite_stmt J _ _) (@QX7n.Mq0.fwrite_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq0.fprintf_s_stmt J _ _) (@QX7n.Mq0.fprintf_s_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A0 LM0 B0 argv USP LO
VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT Era Esp Egp Etp Ea0 Ea1 FRM) as HD.
unfold Qhd4.AJ5of in HD. change (Qhd4.hiA_J Qwm6.Mq0.A4L HIx) with (QZsi.hiA_J Qwm6.Mq0.A4L H6) in HD. rewrite H6_J in HD.
apply HD. unfold Qhd4.gp_ok5, Qhd4.ms_gp. rewrite Egp. reflexivity.
Qed.
End MainPhase.

Section MainPhaseInst.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq0.A4L LA LV PERM0 TMAX NMAX RE FR0.

Definition main_phase_jo_inst :=
fun RUN_base_img RUN_base_stack RUN_FR0_off_data RUN_botj RUN_topj RUN_baux RUN_top_re =>
main_phase_jo LV (proj1 (proj2 HS)) (proj1 (proj2 (proj2 HS))) (proj1 (proj2 (proj2 (proj2 HS)))) (proj1 (proj2 (proj2 (proj2 (proj2 HS)))))
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))
(@QrOY.Mq0.hiA_jo RC__ LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS RUN_base_img RUN_base_stack RUN_FR0_off_data RUN_botj RUN_topj RUN_baux RUN_top_re)
eq_refl.
End MainPhaseInst.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX7n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section MainPhase.
Context {RC__ : Q6q3.RunConsts}.
Notation asegs := QbFI.asegs.

Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap asegs.
Hypothesis Hsegs : segs_in_base LV asegs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Variable H6 : QZsi.heap_iface_A Qwm6.Mq4.A4L.
Hypothesis H6_J : QZsi.hiA_J Qwm6.Mq4.A4L H6 = aj_base_vj asegs LV Hwx Hsegs.
Notation HIx := (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6).
Notation Jx := (Qhd4.hiA_J Qwm6.Mq4.A4L HIx).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : QupI.target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv USP A LB LM FR B m md, QupI.drvA_mem argv USP m -> Qhd4.HEAPA Qwm6.Mq4.A4L HIx A LB LM FR B m md -> GA m.

Variable BANDS : QlES.Band.
Hypothesis OBL_ISH : forall A LB LM FR B m md, Qhd4.HEAPA Qwm6.Mq4.A4L HIx A LB LM FR B m md -> @Q9Ho.ISH BANDS m.
Hypothesis OBL_BLO : @QlES.band_lo BANDS <= Qhd4.hiA_bot Qwm6.Mq4.A4L HIx.

Lemma SYS_jo : forall (F : QsRG.Mq0.FPF) (fc : QsRG.Mq0.FPC),
@Qfub.aj_sys F fc asegs Jx.
Proof.
intros F fc. change Jx with (QZsi.hiA_J Qwm6.Mq4.A4L H6). rewrite H6_J.
exact (@QbKA.Mq4.aj_sys_vj F fc asegs LV Hwx Hsegs Hsh Hbx Hbc).
Qed.

Theorem main_phase_jo : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A0 : QZsi.ASA Qwm6.Mq4.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (argv : list (list byte)) (USP LO : Z),

cinvA LV (cfg_ms md) (cfg_model md) -> m_halted (cfg_model md) = None ->
msview LV (cfg_model md) (cfg_ms md) =
MS (QWxq_c1.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 QupI.MAIN_A) fc None m (seg_rom asegs) ->

valid_argv argv ->
QupI.drvA_pre argv USP LO m (cfg_model md) ->
QZsi.HEAPA Qwm6.Mq4.A4L H6 A0 [] LM0 [] B0 m md ->
Z.of_nat (length LM0) < 8 ->
QXcG.Mq0.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.Mq0.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.Mq0.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.Mq0.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.Mq0.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
USP <= QZsi.hiA_top Qwm6.Mq4.A4L H6 + 160 -> QZsi.hiA_bot Qwm6.Mq4.A4L H6 <= LO ->
ra = Z_to_bv 64 QupI.RA_MAIN -> sp = Z_to_bv 64 (USP - 48) ->
gp = Z_to_bv 64 QupI.A_GP -> tp = Z_to_bv 64 Qwm6.Mq4.A_TP ->
a0 = Z_to_bv 64 (Z.of_nat (length argv)) -> a1 = Z_to_bv 64 (USP + 8) ->
Qc3B.frm0 fc ->
srealizes asegs md (QBxa.Mq5.spec argv (m_fs (cfg_model md))).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A0 LM0 B0 argv USP LO
HC Hh HV VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT Era Esp Egp Etp Ea0 Ea1 FRM.
apply (main_phase_cps asegs LV _ md HC Hh). rewrite HV.
assert (STD : forall (P : QZsi.aj_base asegs -> Prop), P (aj_base_vj asegs LV Hwx Hsegs) -> P Jx)
by (intros P HPx; change Jx with (QZsi.hiA_J Qwm6.Mq4.A4L H6); rewrite H6_J; exact HPx).
pose proof (QXcG.Mq0.driver_A_ok6 H6 SYS_jo GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT OBL_GA_of (@Q9Ho.ISH BANDS) (@QlES.band_lo BANDS) OBL_ISH OBL_BLO
(STD (fun J => QdM4.Mq3.emitpf1_stmt J _ _) (@QX7n.pf1_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq3.emitpfk_stmt J _ _) (@QX7n.pfk_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq3.fprintf_u_stmt J _ _) (@QX7n.fprintf_u_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq3.fwrite_stmt J _ _) (@QX7n.fwrite_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
(STD (fun J => QdM4.Mq3.fprintf_s_stmt J _ _) (@QX7n.fprintf_s_inst RC__ BANDS LV Hwx Hsegs Hsh Hbx Hbc))
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A0 LM0 B0 argv USP LO
VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT Era Esp Egp Etp Ea0 Ea1 FRM) as HD.
unfold Qhd4.AJ5of in HD. change (Qhd4.hiA_J Qwm6.Mq4.A4L HIx) with (QZsi.hiA_J Qwm6.Mq4.A4L H6) in HD. rewrite H6_J in HD.
apply HD. unfold Qhd4.gp_ok5, Qhd4.ms_gp. rewrite Egp. reflexivity.
Qed.
End MainPhase.

Section MainPhaseInst.
Context {RC__ : Q6q3.RunConsts}.
Variable LA : Q6sh.ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable RE : QCrt.aentry.
Variable FR0 : list (Z * Z).
Variables BAUX BOTJ TOPJ : Z.
Variable HS : QU91.Mq0.handoff_static Qwm6.Mq4.A4L LA LV PERM0 TMAX NMAX RE FR0.

Definition main_phase_jo_inst :=
fun RUN_base_img RUN_base_stack RUN_FR0_off_data RUN_botj RUN_topj RUN_baux RUN_top_re =>
main_phase_jo LV (proj1 (proj2 HS)) (proj1 (proj2 (proj2 HS))) (proj1 (proj2 (proj2 (proj2 HS)))) (proj1 (proj2 (proj2 (proj2 (proj2 HS)))))
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HS))))))
(@QrOY.hiA_jo RC__ LA LV PERM0 TMAX NMAX RE FR0 BAUX BOTJ TOPJ HS RUN_base_img RUN_base_stack RUN_FR0_off_data RUN_botj RUN_topj RUN_baux RUN_top_re)
eq_refl.
End MainPhaseInst.
