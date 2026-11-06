(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qhd4 QsRG QRjH QBxa QMz4 QXup QWxq_c1 QHnV QCcH QfLs Qsw7 QJjn Qwm6 Qfub QupI QdM4 QscU QVmF QaDa QOcx Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QsRG.Mq0 QRjH QBxa.Mq5 QMz4.
Import QXup QWxq_c1.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq4.
Import Qfub QupI QdM4.Mq4 QdM4.Mq3.
Import QscU QVmF QaDa.Mq0 QOcx.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.

Section Top6.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv USP A LB LM FR B m md, drvA_mem argv USP m -> HEAPA A4L HIx A LB LM FR B m md -> GA m.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Definition DRVA6_BQ : Z := RDQ 0 65536 + (65536 + 8192) + BQR TGT_BB_A.
Definition DRVA6_BB : Z := RDB 0 65536 + (3 * 65536 + 45101) + BBR TGT_BB_A.
Definition DRVA6_BN : Z := 11 + BNR TGT_BB_A.
Definition DRVA6_BD : Z := BDR TGT_BD_A.

Definition driver_A_stmt6 : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A0 : QZsi.ASA A4L H6) (LM0 : list blk) (B0 : QZsi.bud) (argv : list (list byte)) (USP LO : Z),
valid_argv argv ->
drvA_pre argv USP LO m (cfg_model md) ->
QZsi.HEAPA A4L H6 A0 [] LM0 [] B0 m md ->
Z.of_nat (length LM0) < 8 ->
DRVA6_BQ <= QZsi.bQ B0 -> DRVA6_BB <= QZsi.bB B0 -> DRVA6_BN <= QZsi.bN B0 -> DRVA6_BD <= QZsi.bD B0 ->
DRVA6_BD <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
USP <= QZsi.hiA_top A4L H6 + 160 -> QZsi.hiA_bot A4L H6 <= LO ->
ra = Z_to_bv 64 RA_MAIN -> sp = Z_to_bv 64 (USP - 48) -> gp = Z_to_bv 64 A_GP -> tp = Z_to_bv 64 A_TP ->
a0 = Z_to_bv 64 (Z.of_nat (length argv)) -> a1 = Z_to_bv 64 (USP + 8) ->
frm0 fc ->
AJ5 A4L HIx A0 (spec argv (m_fs (cfg_model md))) md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MAIN_A) fc None m (seg_rom asegs)).

Theorem driver_A_ok6 : driver_A_stmt6.
Proof.
unfold driver_A_stmt6. intros until LO. intros VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT -> -> -> -> -> -> FRM.
pose proof (dp_usp _ _ _ _ _ PRE) as USPF. pose proof (dp_lo _ _ _ _ _ PRE) as LOF.
eapply (main_ok H6 SYS (fun _ => 0) (OBL_MALLOC_N6_ok H6) (OBL_FREE_N6_ok H6) (OBL_FREE_NN_ok HIx) (OBL_CLIENT_FRAME_ok HIx) OBL_CS_WIDE_ok (OBL_CLIENT_FRAME6_ok H6)
argv USP LO (m_fs (cfg_model md)) LM0 USPF LOF (conj TOP BOT) VA GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT (OBL_GA_of argv USP)
ltac:(lia) PFRT PFLO OBL_PFRT OBL_PFLO PF1 PFK FPU FWR FPS ltac:(unfold TRV_BB; exact TB6) HLM);
[exact PRE | exact HP | cbv beta; lia | exact HBQ | exact HBB | exact HBN | exact HBD | exact HBM | reflexivity | exact FRM].
Qed.
End Top6.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVmF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVmF.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaDa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaDa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOcx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOcx.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Section Top6.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.
Hypothesis OBL_GA_of : forall argv USP A LB LM FR B m md, drvA_mem argv USP m -> HEAPA A4L HIx A LB LM FR B m md -> GA m.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Definition DRVA6_BQ : Z := RDQ 0 65536 + (65536 + 8192) + BQR TGT_BB_A.
Definition DRVA6_BB : Z := RDB 0 65536 + (3 * 65536 + 45101) + BBR TGT_BB_A.
Definition DRVA6_BN : Z := 11 + BNR TGT_BB_A.
Definition DRVA6_BD : Z := BDR TGT_BD_A.

Definition driver_A_stmt6 : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A0 : QZsi.ASA A4L H6) (LM0 : list blk) (B0 : QZsi.bud) (argv : list (list byte)) (USP LO : Z),
valid_argv argv ->
drvA_pre argv USP LO m (cfg_model md) ->
QZsi.HEAPA A4L H6 A0 [] LM0 [] B0 m md ->
Z.of_nat (length LM0) < 8 ->
DRVA6_BQ <= QZsi.bQ B0 -> DRVA6_BB <= QZsi.bB B0 -> DRVA6_BN <= QZsi.bN B0 -> DRVA6_BD <= QZsi.bD B0 ->
DRVA6_BD <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
USP <= QZsi.hiA_top A4L H6 + 160 -> QZsi.hiA_bot A4L H6 <= LO ->
ra = Z_to_bv 64 RA_MAIN -> sp = Z_to_bv 64 (USP - 48) -> gp = Z_to_bv 64 A_GP -> tp = Z_to_bv 64 A_TP ->
a0 = Z_to_bv 64 (Z.of_nat (length argv)) -> a1 = Z_to_bv 64 (USP + 8) ->
frm0 fc ->
AJ5 A4L HIx A0 (spec argv (m_fs (cfg_model md))) md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MAIN_A) fc None m (seg_rom asegs)).

Theorem driver_A_ok6 : driver_A_stmt6.
Proof.
unfold driver_A_stmt6. intros until LO. intros VA PRE HP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT -> -> -> -> -> -> FRM.
pose proof (dp_usp _ _ _ _ _ PRE) as USPF. pose proof (dp_lo _ _ _ _ _ PRE) as LOF.
eapply (main_ok H6 SYS (fun _ => 0) (OBL_MALLOC_N6_ok H6) (OBL_FREE_N6_ok H6) (OBL_FREE_NN_ok HIx) (OBL_CLIENT_FRAME_ok HIx) OBL_CS_WIDE_ok (OBL_CLIENT_FRAME6_ok H6)
argv USP LO (m_fs (cfg_model md)) LM0 USPF LOF (conj TOP BOT) VA GA TGT_STACK_A TGT_BB_A TGT_BD_A TGT (OBL_GA_of argv USP)
ltac:(lia) PFRT PFLO OBL_PFRT OBL_PFLO PF1 PFK FPU FWR FPS ltac:(unfold TRV_BB; exact TB6) HLM);
[exact PRE | exact HP | cbv beta; lia | exact HBQ | exact HBB | exact HBN | exact HBD | exact HBM | reflexivity | exact FRM].
Qed.
End Top6.
